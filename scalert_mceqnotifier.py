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
        "timeout":  "30",        # SMTP connection timeout in seconds
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

# Static CSS for HTML emails (header gradient is injected dynamically)
_EMAIL_CSS = (
    "body{margin:0;padding:0;background:#ececec;"
    "font-family:Arial,Helvetica,sans-serif;}"
    ".wrap{max-width:820px;margin:0 auto;background:#fff;}"
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
)

# Tiered tsunami risk messages (USGS/PTWC criteria)
_TSUNAMI_MESSAGES = {
    "POSSIBLE": "Shallow earthquake — tsunami possible but unlikely to be destructive.",
    "LIKELY":   "Large shallow earthquake — destructive local tsunami likely.",
    "EXPECTED": "Major shallow earthquake — destructive regional tsunami expected.",
}


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
    """Classify earthquake depth."""
    if depth_km is None:
        return "Unknown"
    if depth_km < 70:
        return "Shallow"
    if depth_km < 300:
        return "Intermediate"
    return "Deep"


def _tsunami_risk(mag_val, depth_km):
    """Estimate tsunami risk based on USGS/PTWC initial-assessment criteria.

    Returns: None | "POSSIBLE" | "LIKELY" | "EXPECTED"

    Thresholds (shallow marine events only, depth < 100 km):
      M < 6.5  → None   (very unlikely to trigger tsunami)
      M 6.5–7.5 → POSSIBLE (rarely destructive, local effects)
      M 7.6–7.8 → LIKELY   (destructive local tsunami)
      M ≥ 7.9   → EXPECTED (destructive regional tsunami)
    """
    if mag_val is None or depth_km is None:
        return None
    if depth_km >= 100:
        return None
    if mag_val >= 7.9:
        return "EXPECTED"
    if mag_val >= 7.6:
        return "LIKELY"
    if mag_val >= 6.5:
        return "POSSIBLE"
    return None


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


def _urgency(mag_val):
    """Return (emoji, label, color1, color2) aligned with tsunami.gov alert colors."""
    if mag_val is not None and mag_val >= 6.0:
        return ("🔴", "WARNING",  "#c0392b", "#e74c3c")
    if mag_val is not None and mag_val >= 5.0:
        return ("🟠", "ADVISORY", "#d35400", "#e67e22")
    if mag_val is not None and mag_val >= 4.0:
        return ("🟡", "WATCH",    "#b7950b", "#d4ac0d")
    return ("🟢", "INFO",         "#1e8449", "#27ae60")


def _log(msg):
    print(f"[scalert_mceqnotifier] {msg}", file=sys.stderr)


def _run_sc_tool(cmd, input_data=None, output_suffix=None, timeout=30):
    """Run a SeisComP CLI tool, optionally writing output to a temp file.

    Returns (file_bytes, None) on success when output_suffix is given,
    or (None, stderr_str) on failure.  Without output_suffix, returns
    (True, None) / (False, stderr_str).
    """
    out_path = (tempfile.mktemp(suffix=output_suffix, prefix="scalert_mceq_")
                if output_suffix else None)
    try:
        if out_path:
            cmd = [c.replace("{OUT}", out_path) for c in cmd]
        _log(f"running: {' '.join(cmd)}")
        result = subprocess.run(
            cmd, input=input_data, capture_output=True, timeout=timeout)
        if result.returncode != 0:
            err = result.stderr.decode(errors="replace")
            _log(f"{cmd[0]} error: {err}")
            return (None if out_path else False, err)
        if out_path:
            if not os.path.isfile(out_path):
                return (None, f"{cmd[0]} produced no output file")
            with open(out_path, "rb") as f:
                return (f.read(), None)
        return (True, None)
    except subprocess.TimeoutExpired:
        _log(f"{cmd[0]} timed out")
        return (None if out_path else False, "timeout")
    except Exception as e:
        _log(f"{cmd[0]} failed: {e}")
        return (None if out_path else False, str(e))
    finally:
        if out_path and os.path.isfile(out_path):
            os.remove(out_path)


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
        bd       = self._prepare_body_data(ed)
        bulletin = self._get_bulletin_text(ep)
        map_att  = self._gen_map(ed)
        plain    = self._build_plain(ed, bd, bulletin)
        html     = self._build_html(ed, bd, bulletin, map_att)

        generators = [
            ("generate_travel_curves", self._gen_travel_curves, (ed,)),
            ("generate_waveforms",     self._gen_waveforms,     (ed,)),
            ("attach_kml",             self._gen_kml,           (ep,)),
        ]
        attachments = [map_att] if map_att else []
        for key, fn, args in generators:
            if self._cfg.getboolean("content", key):
                att = fn(*args)
                if att:
                    attachments.append(att)

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
        db  = self._cfg.get("seiscomp", "database").strip()
        cmd = ["scxmldump", "-E", event_id, "-p", "-P", "-M", "-A", "-o", "{OUT}"]
        if db:
            cmd += ["-d", db]

        xml_bytes, err = _run_sc_tool(cmd, output_suffix=".xml")
        if xml_bytes is None:
            return None

        try:
            tmp = tempfile.mktemp(suffix=".xml", prefix="scalert_mceq_parse_")
            with open(tmp, "wb") as f:
                f.write(xml_bytes)

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

        emoji, label, _, _ = _urgency(mag_val)
        urgency = f"{emoji} {label}".strip()

        risk = _tsunami_risk(mag_val, depth)
        tsunami_flag = f" ⚠️TSUNAMI {risk}" if risk else ""

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
    # Shared data prep
    # -----------------------------------------------------------------------
    def _get_bulletin_text(self, ep):
        """Return bulletin string (or error message)."""
        try:
            from seiscomp.scbulletin import Bulletin as SCBulletin
            scb = SCBulletin(None)
            scb.enhanced = self._cfg.getboolean("content", "bulletin_enhanced")
            scb.format   = self._cfg.get("content", "bulletin_format")
            if ep.eventCount() > 0:
                return scb.printEvent(ep.event(0)) or "(empty bulletin)"
            return "(no event)"
        except Exception as e:
            _log(f"scbulletin failed: {e}")
            return f"(scbulletin error: {e})"

    def _prepare_body_data(self, ed):
        """Pre-compute values shared by plain-text and HTML body builders."""
        mag_val = ed["mag_val"]
        depth   = ed["depth"]
        lat, lon = ed["lat"], ed["lon"]
        depth_class = _depth_info(depth)
        return {
            "mag_str":       f"M{mag_val:.1f} {ed['mag_type']}".strip() if mag_val is not None else "M?",
            "depth_str":     f"{depth:.1f} km" if depth is not None else "N/A",
            "depth_class":   depth_class,
            "tsunami_risk":  _tsunami_risk(mag_val, depth),
            "maps_url":      f"https://maps.google.com/maps?q={lat},{lon}&z=8",
            "short_id":      ed["id"].split("/")[-1] if "/" in ed["id"] else ed["id"],
            "city_rows":     _city_distances(lat, lon, self._cfg),
            "arrivals":      ed["arrivals"][:self._cfg.getint("content", "max_arrivals_table")],
            "footer":        self._cfg.get("content", "footer"),
        }

    # -----------------------------------------------------------------------
    # Plain text
    # -----------------------------------------------------------------------
    def _build_plain(self, ed, bd, bulletin) -> str:
        lines = [
            "EARTHQUAKE NOTIFICATION",
            "=" * 56,
            "",
            f"EVENT ID  : {ed['id']}",
            f"TIME (UTC): {_fmt_time(ed['time'])}",
            f"REGION    : {ed['region'] or 'N/A'}",
            f"LATITUDE  : {ed['lat']:.4f}°",
            f"LONGITUDE : {ed['lon']:.4f}°",
            f"DEPTH     : {bd['depth_str']} ({bd['depth_class']})",
            f"MAGNITUDE : {bd['mag_str']}",
            f"PHASES    : {ed['phases']}",
            "",
        ]

        if bd["tsunami_risk"]:
            lines += [
                f"⚠️  TSUNAMI {bd['tsunami_risk']}: {_TSUNAMI_MESSAGES[bd['tsunami_risk']]}",
                "   Monitor official warnings (PTWC, NTWC, and regional agencies).",
                "",
            ]

        if self._cfg.getboolean("content", "include_maps_link"):
            lines += [f"GOOGLE MAPS: {bd['maps_url']}", ""]

        lines += ["DISTANCES TO KEY LOCATIONS", "-" * 40]
        for name, dist_km, bearing, is_cap in bd["city_rows"]:
            cap_mark = "★" if is_cap else " "
            lines.append(f"  {cap_mark} {name:<18} {dist_km:>7.0f} km  {bearing}")
        lines += ["", "★ = capital city", ""]

        arrivals = bd["arrivals"]
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
            if ed["phases"] > len(arrivals):
                lines.append(f"  ... and {ed['phases'] - len(arrivals)} more arrivals")
            lines.append("")

        lines += ["=" * 56, "OFFICIAL BULLETIN", "=" * 56, "", bulletin]

        if bd["footer"]:
            lines += ["", "=" * 56, bd["footer"]]

        return "\n".join(lines)

    # -----------------------------------------------------------------------
    # HTML body
    # -----------------------------------------------------------------------
    def _build_html(self, ed, bd, bulletin, map_att) -> str:
        lat, lon = ed["lat"], ed["lon"]
        region   = _he(ed["region"] or "Unknown region")
        time_disp = _he(_fmt_time(ed["time"]))

        urgency_emoji, _, hdr_c1, hdr_c2 = _urgency(ed["mag_val"])

        depth_badge_bg = {
            "Shallow": "#e74c3c",
            "Intermediate": "#e67e22",
            "Deep": "#3498db",
        }.get(bd["depth_class"], "#95a5a6")

        hdr_rule = (f".hdr{{padding:28px 20px;text-align:center;"
                    f"background:linear-gradient(135deg,{hdr_c1},{hdr_c2});color:#fff;}}")
        css = f"<style>{_EMAIL_CSS}{hdr_rule}</style>"

        hdr = (
            '<div class="hdr">'
            "<h1>🌏 Earthquake Notification</h1>"
            f"<h2>{urgency_emoji} {_he(bd['mag_str'])}</h2>"
            f"<p>{time_disp}</p><p>{region}</p>"
            "</div>")

        tsunami_banner = (
            '<div class="tsunami">'
            f"⚠️ TSUNAMI {bd['tsunami_risk']} — "
            f"{_TSUNAMI_MESSAGES[bd['tsunami_risk']]} "
            "Monitor official warnings from PTWC, NTWC, and regional agencies."
            "</div>"
        ) if bd["tsunami_risk"] else ""

        evt_tbl = (
            "<h3>Event Parameters</h3>"
            '<table class="ev">'
            f'<tr><td class="lbl">Event ID</td><td>{_he(bd["short_id"])}</td></tr>'
            f'<tr><td class="lbl">Origin Time (UTC)</td><td>{time_disp}</td></tr>'
            f'<tr><td class="lbl">Region</td><td>{region}</td></tr>'
            f'<tr><td class="lbl">Latitude</td><td>{lat:.4f}&deg;</td></tr>'
            f'<tr><td class="lbl">Longitude</td><td>{lon:.4f}&deg;</td></tr>'
            f'<tr><td class="lbl">Depth</td><td>{_he(bd["depth_str"])}&nbsp;'
            f'<span class="badge" style="background:{depth_badge_bg}">{bd["depth_class"]}</span></td></tr>'
            f'<tr><td class="lbl">Magnitude</td><td>{_he(bd["mag_str"])}</td></tr>'
            f'<tr><td class="lbl">Phases Used</td><td>{ed["phases"]}</td></tr>'
            "</table>")

        # Map section
        map_cid = map_att[3] if map_att else None
        maps_url = bd["maps_url"]
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
        for name, dist_km, bearing, is_cap in bd["city_rows"]:
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

        arrivals = bd["arrivals"]
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

        bul_sec = (
            "<h3>Official Bulletin</h3>"
            f'<div class="bul">{_he(bulletin)}</div>')

        footer_text = _he(bd["footer"])

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

        cmd = [
            "scmapcut", "-o", "{OUT}", "-d", f"{width}x{height}",
            "--lat", str(lat), "--lon", str(lon), "--depth", str(depth),
            "-m", f"{radius / 2:.2f}",
        ]
        if mag_val is not None:
            cmd += ["--mag", f"{mag_val:.1f}"]

        data, err = _run_sc_tool(cmd, output_suffix=".jpg", timeout=20)
        if data is None:
            return None

        import random, time
        cid = f"{random.randint(0, 99999)}.{os.getpid()}.{time.time()}@gds.local"
        _log(f"map generated ({len(data)} B)")
        return ("epicenter.jpg", data, "image/jpeg", cid)

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
        # Serialise EP back to SCML
        scml_tmp = tempfile.mktemp(suffix=".xml", prefix="scalert_mceq_scml_")
        try:
            ar = io.XMLArchive()
            ar.create(scml_tmp)
            ar.writeObject(ep)
            ar.close()
            with open(scml_tmp, "rb") as f:
                scml_bytes = f.read()
        finally:
            if os.path.isfile(scml_tmp):
                os.remove(scml_tmp)

        cmd = ["scbulletin", "--kml", "-i", "-", "-o", "{OUT}"]
        data, err = _run_sc_tool(cmd, input_data=scml_bytes,
                                 output_suffix=".kml", timeout=15)
        if data is None:
            return None

        _log(f"KML generated ({len(data)} B)")
        return ("event_location.kml", data,
                "application/vnd.google-earth.kml+xml", None)

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

        smtp_timeout = s.getint("smtp", "timeout", fallback=30)
        _log(f"connecting to {srv}:{port} (timeout={smtp_timeout}s)")
        try:
            if use_ssl:
                server = smtplib.SMTP_SSL(srv, port, timeout=smtp_timeout)
            else:
                server = smtplib.SMTP(srv, port, timeout=smtp_timeout)
                if use_tls:
                    server.starttls()

            if user:
                server.login(user, pw)

            server.sendmail(sender, recipients, msg.as_bytes())
            server.quit()
            _log(f"email sent to {recipients}")
        except (smtplib.SMTPException, OSError) as exc:
            _log(f"SMTP error: {exc}")

    @staticmethod
    def _make_part(name, data, mime_type, cid=None, disposition="attachment"):
        """Create a MIME part from raw bytes."""
        main_t, sub_t = mime_type.split("/", 1)
        if main_t == "image":
            part = MIMEImage(data, _subtype=sub_t, name=name)
        else:
            part = MIMEBase(main_t, sub_t)
            part.set_payload(data)
            encoders.encode_base64(part)
        if cid:
            part.add_header("Content-ID", f"<{cid}>")
        part.add_header("Content-Disposition",
                        disposition if disposition == "inline"
                        else f'attachment; filename="{name}"')
        return part

    @staticmethod
    def _build_mime(subject, sender, recipients, plain, html, attachments):
        """Assemble MIME message with inline and regular attachments."""
        is_inline = lambda c: c and f"cid:{c}" in html
        inlines  = [a for a in attachments if is_inline(a[3])]
        regulars = [a for a in attachments if not is_inline(a[3])]

        html_part = MIMEText(html, "html", "utf-8")
        if inlines:
            related = MIMEMultipart("related")
            related.attach(html_part)
            for name, data, mime_type, cid in inlines:
                related.attach(ScalertNotifier._make_part(
                    name, data, mime_type, cid, "inline"))
            html_part = related

        alt = MIMEMultipart("alternative")
        alt.attach(MIMEText(plain, "plain", "utf-8"))
        alt.attach(html_part)

        if regulars:
            msg = MIMEMultipart("mixed")
            msg.attach(alt)
            for name, data, mime_type, _cid in regulars:
                msg.attach(ScalertNotifier._make_part(name, data, mime_type))
        else:
            msg = alt

        msg["From"]       = sender
        msg["To"]         = ", ".join(recipients) if isinstance(recipients, list) else recipients
        msg["Subject"]    = subject
        msg["Date"]       = formatdate(localtime=True)
        msg["Message-ID"] = make_msgid(domain="seiscomp.local")
        return msg


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    notifier = ScalertNotifier()
    sys.exit(notifier.run(sys.argv))
