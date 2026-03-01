#!/usr/bin/env seiscomp-python
"""
scalert Earthquake Email Notifier — MC Earthquake Notifier
Standalone earthquake notification script for SeisComP scalert.

Unlike filter_mceqnotifier.py (which is a GDS filter), this script:
  - Is called directly by scalert with event parameters as CLI arguments
  - Uses scxmldump to fetch the full event XML from the database
  - Sends rich HTML email directly via SMTP (no GDS required)
  - Supports magnitude threshold and new/update event filtering

SCALERT CONFIGURATION (in scalert.cfg or via scconfig):
  scripts.event = @CONFIGDIR@/scalert_mceqnotifier.py

scalert calls this script as:
  scalert_mceqnotifier.py <message> <is_new> <event_id> <n_arrivals> [magnitude]
    $1  message     : human-readable description string
    $2  is_new      : 1 = new event, 0 = update
    $3  event_id    : SeisComP event public ID
    $4  n_arrivals  : number of arrivals at time of trigger
    $5  magnitude   : magnitude value (optional, only when set)

CONFIG FILE: scalert_mceqnotifier.cfg (same directory as this script)
"""

from __future__ import absolute_import, division, print_function

import configparser
import math
import os
import smtplib
import subprocess
import sys
import tempfile
import traceback
from email import encoders
from email.mime.base import MIMEBase
from email.mime.image import MIMEImage
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import formatdate, make_msgid

from seiscomp import datamodel, io


# ---------------------------------------------------------------------------
# Default configuration
# ---------------------------------------------------------------------------
_DEFAULTS = {
    "smtp": {
        "server":   "smtp.gmail.com",
        "port":     "587",
        "ssl":      "false",
        "tls":      "true",
        "user":     "",
        "pw":       "",
        "from":     "",
        "to":       "",          # comma-separated recipient list
    },
    "filter": {
        "min_magnitude":   "4.0",   # ignore events below this magnitude
        "new_events_only": "false",  # if true, skip updates (is_new=0)
    },
    "seiscomp": {
        # Direct database connection for scxmldump (leave empty to use messaging)
        "database": "mysql://sysop:sysop@localhost/seiscomp",
    },
    "map": {
        "width":      "512",
        "height":     "512",
        "radius_min": "5",
        "radius_max": "40",
        "auto_radius": "true",
    },
    "content": {
        "bulletin_format":        "autoloc3",
        "bulletin_enhanced":      "true",
        "attach_kml":             "true",
        "include_maps_link":      "true",
        "footer":                 "Automated Earthquake Notification",
        "generate_travel_curves": "true",
        "generate_waveforms":     "false",
        "fdsnws_url":             "http://localhost:8081",
        "waveform_pre_secs":      "30",
        "waveform_post_secs":     "300",
        "waveform_max_stations":  "8",
        "max_arrivals_table":     "30",
    },
    "cities": {
        # Path to cities.xml; leave empty to auto-detect from $SEISCOMP_ROOT
        "xml":            "",
        # Search radius in km — cities beyond this are excluded unless fewer
        # than max_count are found within it (fallback: nearest max_count)
        "radius_km":      "1000",
        # Maximum rows to show in the distance table
        "max_count":      "10",
        # Non-capital cities below this population are skipped
        "min_population": "10000",
    },
}

# Module-level caches
_taup_model   = None
_cities_cache = None   # populated on first call to _load_cities_xml()


# ---------------------------------------------------------------------------
# Pure helpers (identical to filter_mceqnotifier.py)
# ---------------------------------------------------------------------------
def _haversine(lat1, lon1, lat2, lon2):
    R = 6371.0
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlam = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlam / 2) ** 2
    return R * 2 * math.asin(math.sqrt(a))


def _compass(lat1, lon1, lat2, lon2):
    dlam = math.radians(lon2 - lon1)
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    x = math.sin(dlam) * math.cos(phi2)
    y = math.cos(phi1) * math.sin(phi2) - math.sin(phi1) * math.cos(phi2) * math.cos(dlam)
    bearing = math.degrees(math.atan2(x, y)) % 360
    dirs = ["N", "NE", "E", "SE", "S", "SW", "W", "NW"]
    return dirs[round(bearing / 45) % 8]


def _he(s):
    return (str(s).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))


def _fmt_time(iso):
    return (iso.replace("T", " ").split(".")[0] + " UTC") if "T" in iso else iso


def _depth_info(depth_km):
    if depth_km is None:
        return "Unknown", False
    if depth_km < 70:
        return "Shallow", True
    elif depth_km < 300:
        return "Intermediate", False
    return "Deep", False


def _load_cities_xml(cfg) -> list:
    """Parse cities.xml and return list of (name, lat, lon, population, is_capital).
    Uses a module-level cache so the file is parsed at most once per process."""
    global _cities_cache
    if _cities_cache is not None:
        return _cities_cache

    xml_path = cfg.get("cities", "xml").strip()
    if not xml_path:
        root = os.environ.get("SEISCOMP_ROOT", "/opt/seiscomp")
        xml_path = os.path.join(root, "share", "cities.xml")

    if not os.path.isfile(xml_path):
        print(f"[warning] cities.xml not found: {xml_path}", file=sys.stderr)
        _cities_cache = []
        return []

    import xml.etree.ElementTree as ET
    cities = []
    try:
        for _, elem in ET.iterparse(xml_path, events=("end",)):
            if elem.tag == "City":
                try:
                    name   = (elem.findtext("name")      or "").strip()
                    lat    = float(elem.findtext("latitude")  or "0")
                    lon    = float(elem.findtext("longitude") or "0")
                    pop    = int(elem.findtext("population")  or "0")
                    is_cap = elem.get("category") == "C"
                    if name:
                        cities.append((name, lat, lon, pop, is_cap))
                except (ValueError, TypeError):
                    pass
                elem.clear()
    except Exception as e:
        print(f"[warning] cities.xml parse error: {e}", file=sys.stderr)
        _cities_cache = []
        return []

    _cities_cache = cities
    return cities


def _city_distances(lat, lon, cfg) -> list:
    """Return nearest cities from cities.xml as (name, dist_km, compass, is_capital).

    Cities within radius_km are returned sorted by distance.
    If fewer than max_count qualify, falls back to the global nearest max_count
    (useful for ocean events far from any populated area).
    Non-capital cities below min_population are skipped.
    """
    cities    = _load_cities_xml(cfg)
    radius_km = cfg.getfloat("cities", "radius_km")
    max_count = cfg.getint("cities",  "max_count")
    min_pop   = cfg.getint("cities",  "min_population")

    rows = []
    for name, clat, clon, pop, is_cap in cities:
        if pop < min_pop and not is_cap:
            continue
        d = _haversine(lat, lon, clat, clon)
        rows.append((name, d, _compass(lat, lon, clat, clon), is_cap))

    rows.sort(key=lambda x: x[1])
    within = [r for r in rows if r[1] <= radius_km]
    return (within if len(within) >= max_count else rows)[:max_count]


def _get_taup_model():
    global _taup_model
    if _taup_model is None:
        from obspy.taup import TauPyModel
        _taup_model = TauPyModel(model="iasp91")
    return _taup_model


def _log(msg):
    print(f"[scalert_mceqnotifier] {msg}", file=sys.stderr)


# ---------------------------------------------------------------------------
def _load_cfg():
    cfg = configparser.ConfigParser()
    for sec, opts in _DEFAULTS.items():
        cfg.add_section(sec)
        for k, v in opts.items():
            cfg.set(sec, k, v)
    cfg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "scalert_mceqnotifier.cfg")
    if os.path.isfile(cfg_path):
        cfg.read(cfg_path)
        _log(f"loaded config: {cfg_path}")
    else:
        _log(f"no config file at {cfg_path} — using defaults")
    return cfg


# ---------------------------------------------------------------------------
class ScalertNotifier:
    """
    Standalone scalert earthquake email notifier.
    Fetches event XML, builds rich HTML email, sends via SMTP.
    """

    def __init__(self):
        self._cfg = _load_cfg()

    # -----------------------------------------------------------------------
    def run(self, argv):
        """
        Entry point.  argv matches sys.argv:
          argv[1] = message
          argv[2] = is_new (1/0)
          argv[3] = event_id
          argv[4] = n_arrivals
          argv[5] = magnitude (optional)
        """
        if len(argv) < 5:
            _log(f"usage: {argv[0]} <message> <is_new> <event_id> <n_arrivals> [magnitude]")
            return 1

        message   = argv[1]
        is_new    = argv[2].strip() == "1"
        event_id  = argv[3].strip()
        magnitude = float(argv[5]) if len(argv) > 5 and argv[5].strip() else None

        _log(f"triggered — event={event_id}  is_new={is_new}  mag={magnitude}")

        # ── Filters ─────────────────────────────────────────────────────
        if self._cfg.getboolean("filter", "new_events_only") and not is_new:
            _log(f"skipping update for {event_id} (new_events_only=true)")
            return 0

        min_mag = self._cfg.getfloat("filter", "min_magnitude")
        if magnitude is not None and magnitude < min_mag:
            _log(f"skipping {event_id} M{magnitude:.1f} < threshold {min_mag}")
            return 0

        # ── Fetch event ──────────────────────────────────────────────────
        ep = self._fetch_event(event_id)
        if not ep:
            _log(f"could not fetch event {event_id}")
            return 1

        # ── Parse event data ─────────────────────────────────────────────
        try:
            ed = self._parse_event(ep)
        except Exception as e:
            _log(f"parse error: {e}")
            _log(traceback.format_exc())
            return 1

        # ── Build content ────────────────────────────────────────────────
        subject  = self._build_subject(ed)
        map_att  = self._gen_map(ed)           # (name, bytes, mime, cid) or None
        plain    = self._build_plain(ep, ed)
        html     = self._build_html(ep, ed, map_att)
        ttc_att  = None
        wfm_att  = None
        kml_att  = None

        if self._cfg.getboolean("content", "generate_travel_curves"):
            ttc_att = self._gen_travel_curves(ed)
        if self._cfg.getboolean("content", "generate_waveforms"):
            wfm_att = self._gen_waveforms(ed)
        if self._cfg.getboolean("content", "attach_kml"):
            kml_att = self._gen_kml(ep)

        attachments = [a for a in [map_att, ttc_att, wfm_att, kml_att] if a]

        # ── Send ─────────────────────────────────────────────────────────
        try:
            self._send(subject, plain, html, attachments)
        except Exception as e:
            _log(f"send failed: {e}")
            _log(traceback.format_exc())
            return 1

        return 0

    # -----------------------------------------------------------------------
    # Event fetching
    # -----------------------------------------------------------------------
    def _fetch_event(self, event_id):
        """Dump event XML via scxmldump and parse into EventParameters."""
        tmp = tempfile.mktemp(suffix=".xml", prefix="scalert_mceq_")
        try:
            db  = self._cfg.get("seiscomp", "database").strip()
            cmd = ["scxmldump", "-E", event_id, "-p", "-P", "-M", "-A", "-o", tmp]
            if db:
                cmd += ["-d", db]

            _log(f"running: {' '.join(cmd)}")
            result = subprocess.run(cmd, capture_output=True, timeout=30)
            if result.returncode != 0:
                _log("scxmldump error: " + result.stderr.decode(errors="replace"))
                return None

            # Enable public-object lookup before reading XML
            datamodel.PublicObject.SetRegistrationEnabled(True)

            ar = io.XMLArchive()
            if not ar.open(tmp):
                _log("cannot open XML archive")
                return None
            obj = ar.readObject()
            ar.close()

            if not obj:
                _log("no object in XML")
                return None

            ep = datamodel.EventParameters.Cast(obj)
            if not ep:
                _log("object is not EventParameters")
                return None

            _log(f"fetched {event_id}: {ep.eventCount()} event(s)")
            return ep

        except subprocess.TimeoutExpired:
            _log("scxmldump timed out")
            return None
        except Exception as e:
            _log(f"fetch error: {e}")
            _log(traceback.format_exc())
            return None
        finally:
            if os.path.isfile(tmp):
                os.remove(tmp)

    # -----------------------------------------------------------------------
    # Event parsing (same logic as filter_mceqnotifier.py)
    # -----------------------------------------------------------------------
    def _parse_event(self, ep) -> dict:
        if ep.eventCount() < 1:
            raise Exception("no event in XML")

        event = ep.event(0)
        ed = {
            "id":       event.publicID(),
            "region":   "",
            "lat":      0.0,
            "lon":      0.0,
            "depth":    None,
            "phases":   0,
            "time":     "",
            "mag_val":  None,
            "mag_type": "",
            "arrivals": [],
            "map_cid":  None,
        }

        for i in range(event.eventDescriptionCount()):
            desc = event.eventDescription(i)
            if desc.type() == datamodel.REGION_NAME:
                ed["region"] = desc.text()
                break

        mag = datamodel.Magnitude.Find(event.preferredMagnitudeID())
        if mag:
            ed["mag_val"]  = mag.magnitude().value()
            ed["mag_type"] = mag.type()

        origin = datamodel.Origin.Find(event.preferredOriginID())
        if not origin:
            raise Exception("preferred origin not found")

        ed["time"]   = origin.time().value().iso()
        ed["lat"]    = origin.latitude().value()
        ed["lon"]    = origin.longitude().value()
        ed["phases"] = origin.arrivalCount()

        try:
            ed["depth"] = origin.depth().value()
        except ValueError:
            pass

        arrivals = []
        for i in range(origin.arrivalCount()):
            arr  = origin.arrival(i)
            pick = datamodel.Pick.Find(arr.pickID())
            row  = {
                "sta": "?", "net": "?", "cha": "?",
                "phase":       arr.phase().code(),
                "dist_deg":    None, "dist_km":  None,
                "azimuth":     None, "residual": None, "travel_time": None,
            }
            if pick:
                wfid         = pick.waveformID()
                row["sta"]   = wfid.stationCode()
                row["net"]   = wfid.networkCode()
                row["cha"]   = wfid.channelCode()
                try:
                    row["travel_time"] = float(
                        pick.time().value() - origin.time().value())
                except Exception:
                    pass
            try:
                row["dist_deg"] = arr.distance()
                row["dist_km"]  = row["dist_deg"] * 111.195
            except ValueError:
                pass
            try:
                row["azimuth"] = arr.azimuth()
            except ValueError:
                pass
            try:
                row["residual"] = arr.timeResidual()
            except ValueError:
                pass
            arrivals.append(row)

        arrivals.sort(key=lambda x: (x["dist_deg"] or 9999))
        ed["arrivals"] = arrivals
        return ed

    # -----------------------------------------------------------------------
    # Subject
    # -----------------------------------------------------------------------
    def _build_subject(self, ed) -> str:
        mag_val = ed["mag_val"]
        depth   = ed["depth"]

        if mag_val is not None and mag_val >= 6.0:
            urgency = "🔴 URGENT"
        elif mag_val is not None and mag_val >= 5.0:
            urgency = "🟠"
        elif mag_val is not None and mag_val >= 4.0:
            urgency = "🟡"
        else:
            urgency = "🟢"

        _, tsunami_risk = _depth_info(depth)
        tsunami_flag = " ⚠️TSUNAMI?" if (tsunami_risk and mag_val and mag_val >= 7.0) else ""

        mag_str   = f"M{mag_val:.1f} {ed['mag_type']}".strip() if mag_val is not None else "M?"
        depth_str = f"[{depth:.0f}km]" if depth is not None else ""

        raw = ed["time"]
        time_str = f"{raw[:10]} {raw[11:16]} UTC" if "T" in raw else ""

        region   = ed["region"] or "Unknown region"
        short_id = ed["id"].split("/")[-1] if "/" in ed["id"] else ed["id"]
        short_id = short_id[:20]

        parts = [urgency + tsunami_flag, f"🚨 {mag_str}", depth_str]
        if time_str:
            parts.append(f"@ {time_str}")
        parts += [f"- {region}", f"[{short_id}]"]

        subject = " ".join(p for p in parts if p)
        _log(f"subject: {subject}")
        return subject

    # -----------------------------------------------------------------------
    # Plain text
    # -----------------------------------------------------------------------
    def _build_plain(self, ep, ed) -> str:
        lat        = ed["lat"]
        lon        = ed["lon"]
        mag_val    = ed["mag_val"]
        depth      = ed["depth"]
        depth_str  = f"{depth:.1f} km" if depth is not None else "N/A"
        mag_str    = f"M{mag_val:.1f} {ed['mag_type']}".strip() if mag_val is not None else "M?"
        maps_link  = f"https://maps.google.com/maps?q={lat},{lon}&z=8"
        depth_class, tsunami_risk = _depth_info(depth)

        lines = [
            "EARTHQUAKE NOTIFICATION",
            "=" * 56,
            "",
            f"EVENT ID  : {ed['id']}",
            f"TIME (UTC): {_fmt_time(ed['time'])}",
            f"REGION    : {ed['region'] or 'N/A'}",
            f"LATITUDE  : {lat:.4f}°",
            f"LONGITUDE : {lon:.4f}°",
            f"DEPTH     : {depth_str} ({depth_class})",
            f"MAGNITUDE : {mag_str}",
            f"PHASES    : {ed['phases']}",
            "",
        ]

        if tsunami_risk and mag_val and mag_val >= 7.0:
            lines += [
                "⚠️  TSUNAMI ADVISORY: Large shallow earthquake detected.",
                "   Monitor official warnings (PTWC and regional agencies).",
                "",
            ]

        if self._cfg.getboolean("content", "include_maps_link"):
            lines += [f"GOOGLE MAPS: {maps_link}", ""]

        city_rows = _city_distances(lat, lon, self._cfg)
        lines += ["DISTANCES TO KEY LOCATIONS", "-" * 40]
        for name, dist_km, bearing, is_cap in city_rows:
            cap_mark = "★" if is_cap else " "
            lines.append(f"  {cap_mark} {name:<18} {dist_km:>7.0f} km  {bearing}")
        lines += ["", "★ = capital city", ""]

        max_arr  = self._cfg.getint("content", "max_arrivals_table")
        arrivals = ed["arrivals"][:max_arr]
        if arrivals:
            lines += ["PHASE ARRIVALS", "-" * 60]
            lines.append(
                f"  {'NET':<6} {'STA':<8} {'PH':<6} {'DIST°':>6} {'DIST km':>8} "
                f"{'AZ°':>6} {'TT(s)':>7} {'RES(s)':>7}")
            lines.append("  " + "-" * 65)
            for a in arrivals:
                d_deg = f"{a['dist_deg']:.2f}"    if a["dist_deg"]    is not None else "  N/A"
                d_km  = f"{a['dist_km']:.0f}"     if a["dist_km"]     is not None else "  N/A"
                az    = f"{a['azimuth']:.0f}"     if a["azimuth"]     is not None else " N/A"
                tt    = f"{a['travel_time']:.1f}" if a["travel_time"] is not None else "  N/A"
                res   = f"{a['residual']:.2f}"    if a["residual"]    is not None else "  N/A"
                lines.append(
                    f"  {a['net']:<6} {a['sta']:<8} {a['phase']:<6} {d_deg:>6} {d_km:>8} "
                    f"{az:>6} {tt:>7} {res:>7}")
            if ed["phases"] > max_arr:
                lines.append(f"  ... and {ed['phases'] - max_arr} more arrivals")
            lines.append("")

        lines += ["=" * 56, "OFFICIAL BULLETIN", "=" * 56, ""]
        try:
            from seiscomp.scbulletin import Bulletin as SCBulletin
            scb = SCBulletin(None)
            scb.enhanced = self._cfg.getboolean("content", "bulletin_enhanced")
            scb.format   = self._cfg.get("content", "bulletin_format")
            if ep.eventCount() > 0:
                text = scb.printEvent(ep.event(0))
                lines.append(text or "(empty bulletin)")
        except Exception as e:
            _log(f"scbulletin failed: {e}")
            lines.append(f"(scbulletin error: {e})")

        footer = self._cfg.get("content", "footer")
        if footer:
            lines += ["", "=" * 56, footer]

        return "\n".join(lines)

    # -----------------------------------------------------------------------
    # HTML body
    # -----------------------------------------------------------------------
    def _build_html(self, ep, ed, map_att) -> str:
        mag_val  = ed["mag_val"]
        depth    = ed["depth"]
        lat, lon = ed["lat"], ed["lon"]
        region   = _he(ed["region"] or "Unknown region")
        depth_class, tsunami_risk = _depth_info(depth)
        show_tsunami = tsunami_risk and mag_val is not None and mag_val >= 7.0

        if mag_val is not None and mag_val >= 6.0:
            hdr_c1, hdr_c2 = "#c0392b", "#e74c3c"
        elif mag_val is not None and mag_val >= 5.0:
            hdr_c1, hdr_c2 = "#d35400", "#e67e22"
        elif mag_val is not None and mag_val >= 4.0:
            hdr_c1, hdr_c2 = "#b7950b", "#d4ac0d"
        else:
            hdr_c1, hdr_c2 = "#1e8449", "#27ae60"

        if mag_val is not None and mag_val >= 6.0:
            urgency_emoji = "🔴"
        elif mag_val is not None and mag_val >= 5.0:
            urgency_emoji = "🟠"
        elif mag_val is not None and mag_val >= 4.0:
            urgency_emoji = "🟡"
        else:
            urgency_emoji = "🟢"

        mag_str   = f"M{mag_val:.1f} {ed['mag_type']}".strip() if mag_val is not None else "M?"
        depth_str = f"{depth:.1f} km" if depth is not None else "N/A"
        maps_url  = f"https://maps.google.com/maps?q={lat},{lon}&z=8"
        time_disp = _he(_fmt_time(ed["time"]))
        short_id  = ed["id"].split("/")[-1] if "/" in ed["id"] else ed["id"]

        depth_badge_bg = {
            "Shallow": "#e74c3c",
            "Intermediate": "#e67e22",
            "Deep": "#3498db",
        }.get(depth_class, "#95a5a6")

        css = (
            "<style>"
            "body{margin:0;padding:0;background:#ececec;"
            "font-family:Arial,Helvetica,sans-serif;}"
            ".wrap{max-width:820px;margin:0 auto;background:#fff;}"
            f".hdr{{padding:28px 20px;text-align:center;"
            f"background:linear-gradient(135deg,{hdr_c1},{hdr_c2});color:#fff;}}"
            ".hdr h1{margin:0 0 6px;font-size:12px;letter-spacing:3px;"
            "text-transform:uppercase;opacity:.85;}"
            ".hdr h2{margin:0 0 4px;font-size:34px;font-weight:bold;}"
            ".hdr p{margin:0;font-size:14px;opacity:.9;}"
            ".tsunami{background:#c0392b;color:#fff;padding:14px 20px;"
            "text-align:center;font-size:15px;font-weight:bold;}"
            ".body{padding:20px 26px;}"
            "h3{font-size:14px;color:#2c3e50;border-bottom:2px solid #eee;"
            "padding-bottom:5px;margin:22px 0 10px;}"
            "table{width:100%;border-collapse:collapse;margin:0 0 18px;font-size:13px;}"
            "th{padding:8px 11px;text-align:left;color:#fff;}"
            "td{padding:6px 11px;border-bottom:1px solid #eee;}"
            "tr:last-child td{border-bottom:none;}"
            "tr:nth-child(even) td{background:#fafafa;}"
            ".ev th{background:#2c3e50;}"
            ".ci th{background:#1e6f3e;}"
            ".ph th{background:#154360;}"
            ".lbl{color:#888;font-weight:600;width:170px;white-space:nowrap;}"
            ".badge{display:inline-block;padding:1px 8px;border-radius:3px;"
            "font-size:11px;font-weight:bold;color:#fff;}"
            ".mapbox{text-align:center;margin:14px 0;}"
            ".mapbox img{max-width:100%;border:1px solid #ddd;border-radius:4px;}"
            ".gbtn{display:inline-block;margin:8px 0;padding:8px 18px;"
            "background:#4285F4;color:#fff;text-decoration:none;"
            "border-radius:4px;font-size:13px;font-weight:bold;}"
            ".bul{background:#1a1a2e;color:#00e676;font-family:monospace;"
            "font-size:11.5px;padding:16px;border-radius:4px;"
            "white-space:pre;overflow-x:auto;margin:0 0 18px;}"
            ".cap{font-weight:bold;}"
            ".res-ok{color:#27ae60;}"
            ".res-med{color:#d35400;}"
            ".res-bad{color:#c0392b;font-weight:bold;}"
            ".p-ph{color:#c0392b;font-weight:bold;}"
            ".s-ph{color:#1a5276;font-weight:bold;}"
            ".foot{text-align:center;color:#aaa;font-size:11px;"
            "padding:14px;border-top:1px solid #eee;}"
            "</style>")

        hdr = (
            '<div class="hdr">'
            "<h1>🌏 Earthquake Notification</h1>"
            f"<h2>{urgency_emoji} {_he(mag_str)}</h2>"
            f"<p>{time_disp}</p><p>{region}</p>"
            "</div>")

        tsunami_banner = (
            '<div class="tsunami">'
            "⚠️ TSUNAMI ADVISORY — Large shallow earthquake detected. "
            "Monitor official warnings from PTWC and regional agencies."
            "</div>"
        ) if show_tsunami else ""

        evt_tbl = (
            "<h3>Event Parameters</h3>"
            '<table class="ev">'
            f'<tr><td class="lbl">Event ID</td><td>{_he(short_id)}</td></tr>'
            f'<tr><td class="lbl">Origin Time (UTC)</td><td>{time_disp}</td></tr>'
            f'<tr><td class="lbl">Region</td><td>{region}</td></tr>'
            f'<tr><td class="lbl">Latitude</td><td>{lat:.4f}&deg;</td></tr>'
            f'<tr><td class="lbl">Longitude</td><td>{lon:.4f}&deg;</td></tr>'
            f'<tr><td class="lbl">Depth</td><td>{_he(depth_str)}&nbsp;'
            f'<span class="badge" style="background:{depth_badge_bg}">{depth_class}</span></td></tr>'
            f'<tr><td class="lbl">Magnitude</td><td>{_he(mag_str)}</td></tr>'
            f'<tr><td class="lbl">Phases Used</td><td>{ed["phases"]}</td></tr>'
            "</table>")

        # Map section — use CID from map_att if available
        map_cid = map_att[3] if map_att else None
        if map_cid:
            map_sec = (
                "<h3>Epicenter Map</h3>"
                '<div class="mapbox">'
                f'<img src="cid:{map_cid}" alt="Epicenter Map" width="512"><br>'
                f'<a class="gbtn" href="{maps_url}">🗺️ Open in Google Maps</a>'
                "</div>")
        else:
            map_sec = (
                "<h3>Location</h3>"
                '<div class="mapbox">'
                f'<a class="gbtn" href="{maps_url}">🗺️ Open in Google Maps</a>'
                "</div>")

        city_rows_html = ""
        for name, dist_km, bearing, is_cap in _city_distances(lat, lon, self._cfg):
            cls  = ' class="cap"' if is_cap else ""
            star = " ★" if is_cap else ""
            city_rows_html += (
                f"<tr><td{cls}>{_he(name)}{star}</td>"
                f"<td>{dist_km:.0f} km</td><td>{bearing}</td></tr>")

        cities_sec = (
            "<h3>Distance to Key Locations</h3>"
            '<table class="ci">'
            "<tr><th>Location</th><th>Distance</th><th>Direction</th></tr>"
            f"{city_rows_html}</table>")

        max_arr  = self._cfg.getint("content", "max_arrivals_table")
        arrivals = ed["arrivals"][:max_arr]
        arr_rows_html = ""
        for a in arrivals:
            d_deg = f"{a['dist_deg']:.2f}&deg;" if a["dist_deg"]    is not None else "—"
            d_km  = f"{a['dist_km']:.0f}"       if a["dist_km"]     is not None else "—"
            az    = f"{a['azimuth']:.0f}&deg;"  if a["azimuth"]     is not None else "—"
            tt    = f"{a['travel_time']:.1f}"   if a["travel_time"] is not None else "—"
            if a["residual"] is not None:
                r   = a["residual"]
                cls = "res-ok" if abs(r) <= 1.0 else ("res-med" if abs(r) <= 2.0 else "res-bad")
                res_cell = f'<td class="{cls}">{r:.2f}</td>'
            else:
                res_cell = "<td>—</td>"
            ph_cls = "p-ph" if a["phase"].startswith("P") else (
                     "s-ph" if a["phase"].startswith("S") else "")
            arr_rows_html += (
                f"<tr><td>{_he(a['net'])}</td>"
                f"<td>{_he(a['sta'])}</td>"
                f'<td class="{ph_cls}">{_he(a["phase"])}</td>'
                f"<td>{d_deg}</td><td>{d_km}</td><td>{az}</td><td>{tt}</td>"
                f"{res_cell}</tr>")

        n_shown = len(arrivals)
        n_total = ed["phases"]
        more    = f" <small>(showing {n_shown} of {n_total})</small>" if n_total > n_shown else ""
        arrivals_sec = (
            f"<h3>Phase Arrivals{more}</h3>"
            '<table class="ph">'
            "<tr><th>Net</th><th>Station</th><th>Phase</th><th>Distance</th><th>km</th>"
            "<th>Azimuth</th><th>Travel Time (s)</th><th>Residual (s)</th></tr>"
            f"{arr_rows_html}</table>"
        ) if arr_rows_html else ""

        bul_text = ""
        try:
            from seiscomp.scbulletin import Bulletin as SCBulletin
            scb = SCBulletin(None)
            scb.enhanced = self._cfg.getboolean("content", "bulletin_enhanced")
            scb.format   = self._cfg.get("content", "bulletin_format")
            if ep.eventCount() > 0:
                bul_text = _he(scb.printEvent(ep.event(0)) or "(empty bulletin)")
        except Exception as e:
            _log(f"scbulletin failed: {e}")
            bul_text = _he(f"(scbulletin error: {e})")

        bul_sec = (
            "<h3>Official Bulletin</h3>"
            f'<div class="bul">{bul_text}</div>')

        footer_text = _he(self._cfg.get("content", "footer"))

        return (
            "<!DOCTYPE html><html>"
            '<head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            f"{css}</head>"
            '<body><div class="wrap">'
            f"{hdr}{tsunami_banner}"
            '<div class="body">'
            f"{evt_tbl}{map_sec}{cities_sec}{arrivals_sec}{bul_sec}"
            f'<div class="foot">{footer_text}</div>'
            "</div></div></body></html>")

    # -----------------------------------------------------------------------
    # Map generation — returns (name, bytes, mime_type, cid) or None
    # -----------------------------------------------------------------------
    def _map_radius(self, mag_val):
        r_min = self._cfg.getfloat("map", "radius_min")
        r_max = self._cfg.getfloat("map", "radius_max")
        if not self._cfg.getboolean("map", "auto_radius") or mag_val is None:
            return (r_min + r_max) / 2.0
        if mag_val >= 7.5:   r = r_max
        elif mag_val >= 7.0: r = 35.0
        elif mag_val >= 6.0: r = 25.0
        elif mag_val >= 5.0: r = 15.0
        elif mag_val >= 4.0: r = 10.0
        else:                r = r_min
        return max(r_min, min(r_max, r))

    def _gen_map(self, ed):
        lat     = ed["lat"]
        lon     = ed["lon"]
        mag_val = ed["mag_val"]
        depth   = ed["depth"] if ed["depth"] is not None else 10.0
        radius  = self._map_radius(mag_val)
        width   = self._cfg.get("map", "width")
        height  = self._cfg.get("map", "height")

        img_path = tempfile.mktemp(suffix=".jpg", prefix="scalert_mceq_map_")
        try:
            cmd = [
                "scmapcut", "-o", img_path, "-d", f"{width}x{height}",
                "--lat", str(lat), "--lon", str(lon), "--depth", str(depth),
                "-m", f"{radius / 2:.2f}",
            ]
            if mag_val is not None:
                cmd += ["--mag", f"{mag_val:.1f}"]

            result = subprocess.run(cmd, capture_output=True, timeout=20)
            if result.returncode != 0 or not os.path.isfile(img_path):
                _log("scmapcut failed: " + result.stderr.decode(errors="replace"))
                return None

            with open(img_path, "rb") as f:
                data = f.read()

            import random, time, urllib.parse
            cid = f"{random.randint(0, 99999)}.{os.getpid()}.{time.time()}@gds.local"
            _log(f"map generated ({len(data)} B)")
            return ("epicenter.jpg", data, "image/jpeg", cid)

        except subprocess.TimeoutExpired:
            _log("scmapcut timed out")
            return None
        except Exception as e:
            _log(f"map failed: {e}")
            return None
        finally:
            if os.path.isfile(img_path):
                os.remove(img_path)

    # -----------------------------------------------------------------------
    # Travel-time curves — returns (name, bytes, mime_type, None) or None
    # -----------------------------------------------------------------------
    def _gen_travel_curves(self, ed):
        img_path = tempfile.mktemp(suffix=".png", prefix="scalert_mceq_ttc_")
        try:
            import numpy as np
            import matplotlib
            matplotlib.use("Agg")
            import matplotlib.pyplot as plt

            model = _get_taup_model()
            depth = ed["depth"] if ed["depth"] is not None else 10.0

            dists_obs = [a["dist_deg"] for a in ed["arrivals"]
                         if a["dist_deg"] is not None]
            max_dist  = min(max(dists_obs) * 1.25 if dists_obs else 90.0, 180.0)
            dist_grid = np.linspace(0.5, max_dist, 60)

            phase_styles = {
                "P":  ("red",     "-",  1.5),
                "S":  ("blue",    "-",  1.5),
                "Pn": ("orange",  "--", 1.1),
                "Sn": ("#00aacc", "--", 1.1),
                "PP": ("#8b0000", ":",  1.0),
                "SS": ("#00008b", ":",  1.0),
            }

            fig, ax = plt.subplots(figsize=(10, 6))
            for phase, (color, ls, lw) in phase_styles.items():
                tt_list, d_list = [], []
                for d in dist_grid:
                    try:
                        arrs = model.get_travel_times(
                            source_depth_in_km=depth,
                            distance_in_degree=float(d),
                            phase_list=[phase])
                        if arrs:
                            tt_list.append(arrs[0].time / 60.0)
                            d_list.append(d)
                    except Exception:
                        pass
                if tt_list:
                    ax.plot(d_list, tt_list, color=color, ls=ls, lw=lw, label=phase)

            for a in ed["arrivals"]:
                if a["dist_deg"] is None or a["travel_time"] is None:
                    continue
                ph    = a["phase"]
                color = "red" if ph.startswith("P") else ("blue" if ph.startswith("S") else "#666")
                ax.scatter(a["dist_deg"], a["travel_time"] / 60.0,
                           color=color, s=18, zorder=5, alpha=0.7, linewidths=0)

            mag_str = f"M{ed['mag_val']:.1f} {ed['mag_type']}".strip() if ed["mag_val"] else "M?"
            ax.set_xlabel("Epicentral Distance (°)", fontsize=12)
            ax.set_ylabel("Travel Time (min)", fontsize=12)
            ax.set_title(
                f"Travel Time Curves  —  {mag_str}  |  {ed['region'] or ''}\n"
                f"{_fmt_time(ed['time'])}   Depth: {depth:.0f} km  (IASP91)", fontsize=12)
            ax.legend(loc="upper left", fontsize=9, framealpha=0.9)
            ax.set_xlim(0, max_dist)
            ax.grid(alpha=0.3)
            fig.tight_layout()
            fig.savefig(img_path, dpi=150, facecolor="white")
            plt.close(fig)

            with open(img_path, "rb") as f:
                data = f.read()
            _log(f"travel-time curves generated ({len(data)} B)")
            return ("travel_time_curves.png", data, "image/png", None)

        except Exception as e:
            _log(f"travel-time curves failed: {e}")
            _log(traceback.format_exc())
            return None
        finally:
            if os.path.isfile(img_path):
                os.remove(img_path)

    # -----------------------------------------------------------------------
    # Waveform plot — optional, disabled by default
    # -----------------------------------------------------------------------
    def _gen_waveforms(self, ed):
        img_path = tempfile.mktemp(suffix=".png", prefix="scalert_mceq_wfm_")
        try:
            from obspy.clients.fdsn import Client
            from obspy import UTCDateTime
            import matplotlib
            matplotlib.use("Agg")
            import matplotlib.pyplot as plt

            fdsnws  = self._cfg.get("content", "fdsnws_url")
            pre_s   = self._cfg.getfloat("content", "waveform_pre_secs")
            post_s  = self._cfg.getfloat("content", "waveform_post_secs")
            max_sta = self._cfg.getint("content", "waveform_max_stations")

            t0      = UTCDateTime(ed["time"].replace(" ", "T"))
            client  = Client(fdsnws, timeout=20)

            seen, tasks = set(), []
            for a in ed["arrivals"]:
                sta = a["sta"]
                if sta == "?" or sta in seen or len(tasks) >= max_sta:
                    continue
                seen.add(sta)
                tasks.append((a["net"], sta, a))

            streams = []
            for net, sta, arr_info in tasks:
                for ch in ["BHZ", "HHZ", "SHZ", "EHZ", "*Z"]:
                    try:
                        st = client.get_waveforms(
                            network=net if net != "?" else "*",
                            station=sta, location="*", channel=ch,
                            starttime=t0 - pre_s, endtime=t0 + post_s)
                        if st:
                            tr = st[0]
                            tr.detrend("demean")
                            tr.taper(max_percentage=0.05)
                            streams.append((sta, arr_info, tr))
                            break
                    except Exception:
                        pass

            if not streams:
                _log("no waveforms retrieved")
                return None

            n     = len(streams)
            fig, axes = plt.subplots(n, 1, figsize=(12, max(3, n * 1.9)), sharex=False)
            if n == 1:
                axes = [axes]

            for ax, (sta, arr_info, tr) in zip(axes, streams):
                times = tr.times(reftime=t0)
                data  = tr.data.astype(float)
                norm  = max(abs(data)) or 1.0
                ax.plot(times, data / norm, "k-", lw=0.6, alpha=0.85)
                for a in ed["arrivals"]:
                    if a["sta"] != sta or a["travel_time"] is None:
                        continue
                    tt, ph = a["travel_time"], a["phase"]
                    if ph.startswith("P"):
                        ax.axvline(tt, color="red",  lw=1.2, ls="--", alpha=0.8)
                        ax.text(tt, 0.85, ph, color="red",  fontsize=7,
                                transform=ax.get_xaxis_transform(), ha="left")
                    elif ph.startswith("S"):
                        ax.axvline(tt, color="blue", lw=1.2, ls="--", alpha=0.8)
                        ax.text(tt, 0.70, ph, color="blue", fontsize=7,
                                transform=ax.get_xaxis_transform(), ha="left")
                dist_lbl = f" | {arr_info['dist_deg']:.1f}°" if arr_info["dist_deg"] else ""
                ax.set_ylabel(f"{sta}{dist_lbl}", fontsize=9, rotation=0, labelpad=60, va="center")
                ax.set_xlim(times[0], times[-1])
                ax.set_yticks([])
                ax.axvline(0, color="gray", lw=0.8, ls=":")
                ax.grid(alpha=0.2, axis="x")

            axes[-1].set_xlabel("Time relative to origin (s)", fontsize=11)
            mag_str = f"M{ed['mag_val']:.1f} {ed['mag_type']}".strip() if ed["mag_val"] else "M?"
            fig.suptitle(f"Waveforms  —  {mag_str}  |  {ed['region'] or ''}", fontsize=13, y=1.0)
            fig.tight_layout(rect=[0, 0, 1, 0.98])
            fig.savefig(img_path, dpi=120, facecolor="white", bbox_inches="tight")
            plt.close(fig)

            with open(img_path, "rb") as f:
                data = f.read()
            _log(f"waveform plot generated ({len(data)} B)")
            return ("waveforms.png", data, "image/png", None)

        except Exception as e:
            _log(f"waveform plot failed: {e}")
            _log(traceback.format_exc())
            return None
        finally:
            if os.path.isfile(img_path):
                os.remove(img_path)

    # -----------------------------------------------------------------------
    # KML generation — returns (name, bytes, mime_type, None) or None
    # -----------------------------------------------------------------------
    def _gen_kml(self, ep):
        kml_path = tempfile.mktemp(suffix=".kml", prefix="scalert_mceq_kml_")
        try:
            # Serialise EP back to SCML, pipe into scbulletin --kml
            scml_tmp = tempfile.mktemp(suffix=".xml", prefix="scalert_mceq_scml_")
            ar = io.XMLArchive()
            ar.create(scml_tmp)
            ar.writeObject(ep)
            ar.close()

            with open(scml_tmp, "rb") as f:
                scml_bytes = f.read()
            os.remove(scml_tmp)

            result = subprocess.run(
                ["scbulletin", "--kml", "-i", "-", "-o", kml_path],
                input=scml_bytes, capture_output=True, timeout=15)

            if result.returncode != 0 or not os.path.isfile(kml_path):
                _log("scbulletin --kml failed: " + result.stderr.decode(errors="replace"))
                return None

            with open(kml_path, "rb") as f:
                data = f.read()
            _log(f"KML generated ({len(data)} B)")
            return ("event_location.kml", data,
                    "application/vnd.google-earth.kml+xml", None)

        except Exception as e:
            _log(f"KML failed: {e}")
            return None
        finally:
            if os.path.isfile(kml_path):
                os.remove(kml_path)

    # -----------------------------------------------------------------------
    # SMTP sending
    # -----------------------------------------------------------------------
    def _send(self, subject, plain, html, attachments):
        """Build MIME message and send via SMTP."""
        s   = self._cfg
        srv = s.get("smtp", "server")
        port = s.getint("smtp", "port")
        use_ssl = s.getboolean("smtp", "ssl")
        use_tls = s.getboolean("smtp", "tls")
        user    = s.get("smtp", "user")
        pw      = s.get("smtp", "pw")
        sender  = s.get("smtp", "from") or user
        to_raw  = s.get("smtp", "to")
        recipients = [r.strip() for r in to_raw.split(",") if r.strip()]

        if not recipients:
            _log("no recipients configured in [smtp] to =")
            return

        msg = self._build_mime(subject, sender, recipients, plain, html, attachments)

        _log(f"connecting to {srv}:{port}")
        if use_ssl:
            server = smtplib.SMTP_SSL(srv, port)
        else:
            server = smtplib.SMTP(srv, port)
            if use_tls:
                server.starttls()

        if user:
            server.login(user, pw)

        server.sendmail(sender, recipients, msg.as_bytes())
        server.quit()
        _log(f"email sent to {recipients}")

    @staticmethod
    def _build_mime(subject, sender, recipients, plain, html, attachments):
        """
        Assemble MIME message.
        attachments = list of (name, bytes, mime_type, cid_or_None)
        Attachments with a cid that appears as 'cid:<cid>' in html are embedded inline.
        """
        plain_part = MIMEText(plain, "plain", "utf-8")
        html_part  = MIMEText(html,  "html",  "utf-8")

        inlines  = [(n, d, m, c) for n, d, m, c in attachments
                    if c and f"cid:{c}" in html]
        regulars = [(n, d, m, c) for n, d, m, c in attachments
                    if not (c and f"cid:{c}" in html)]

        # Wrap HTML + inline images in multipart/related if needed
        if inlines:
            related = MIMEMultipart("related")
            related.attach(html_part)
            for name, data, mime_type, cid in inlines:
                main_t, sub_t = mime_type.split("/", 1)
                if main_t == "image":
                    part = MIMEImage(data, _subtype=sub_t, name=name)
                else:
                    part = MIMEBase(main_t, sub_t)
                    part.set_payload(data)
                    encoders.encode_base64(part)
                part.add_header("Content-ID", f"<{cid}>")
                part.add_header("Content-Disposition", "inline")
                related.attach(part)
            html_part = related

        # Combine plain + html in multipart/alternative
        alt = MIMEMultipart("alternative")
        alt.attach(plain_part)
        alt.attach(html_part)

        # Wrap in multipart/mixed if there are regular (non-inline) attachments
        if regulars:
            msg = MIMEMultipart("mixed")
            msg.attach(alt)
            for name, data, mime_type, _cid in regulars:
                main_t, sub_t = mime_type.split("/", 1)
                part = MIMEBase(main_t, sub_t)
                part.set_payload(data)
                encoders.encode_base64(part)
                part.add_header("Content-Disposition", f'attachment; filename="{name}"')
                msg.attach(part)
        else:
            msg = alt

        to_str = ", ".join(recipients) if isinstance(recipients, list) else recipients
        msg["From"]       = sender
        msg["To"]         = to_str
        msg["Subject"]    = subject
        msg["Date"]       = formatdate(localtime=True)
        msg["Message-ID"] = make_msgid(domain="seiscomp.local")

        return msg


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    notifier = ScalertNotifier()
    sys.exit(notifier.run(sys.argv))
