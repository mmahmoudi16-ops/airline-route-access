"""
Airline Route Access - Air Travel Database web application
CIS 51 Vibe Coding Assignment (De Anza College)

Run:  python app.py      then open  http://localhost:8080
Uses only the Python standard library (no installs needed).
"""

import csv
import html
import json
import math
import os
from collections import Counter
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

# ---------------------------------------------------------------------------
# Site owner (Report 2.3) - edit student_info.py, not this file
# ---------------------------------------------------------------------------
try:
    from student_info import STUDENT_NAME, STUDENT_ID
except ImportError:
    STUDENT_NAME = "YOUR NAME HERE"
    STUDENT_ID = "YOUR DE ANZA STUDENT ID HERE"

LINKEDIN_URL = "https://www.linkedin.com/in/maryam-mahmoudi-ab5422304"
PHOTO_NAMES = ["photo.jpg", "photo.jpeg", "photo.png", "photo.webp"]
APP_DIR = os.path.dirname(os.path.abspath(__file__))


def find_photo():
    """Path of the owner's photo if one has been placed next to app.py."""
    for name in PHOTO_NAMES:
        path = os.path.join(APP_DIR, name)
        if os.path.isfile(path):
            return path
    return None


DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
PORT = int(os.environ.get("PORT", 8080))


def clean(value):
    """OpenFlights uses \\N for 'no value'."""
    value = (value or "").strip()
    return "" if value == "\\N" else value


# ---------------------------------------------------------------------------
# Domain classes
# ---------------------------------------------------------------------------
class Airline:
    FIELDS = ["OpenFlights ID", "Name", "Alias", "IATA", "ICAO",
              "Callsign", "Country", "Active"]

    def __init__(self, row):
        (self.id, self.name, self.alias, self.iata, self.icao,
         self.callsign, self.country, self.active) = [clean(v) for v in row]

    def values(self):
        return [self.id, self.name, self.alias, self.iata, self.icao,
                self.callsign, self.country, self.active]


class Airport:
    FIELDS = ["OpenFlights ID", "Name", "City", "Country", "IATA", "ICAO",
              "Latitude", "Longitude", "Altitude (ft)", "UTC Offset",
              "DST", "Timezone", "Type", "Source"]

    def __init__(self, row):
        (self.id, self.name, self.city, self.country, self.iata, self.icao,
         self.latitude, self.longitude, self.altitude, self.utc_offset,
         self.dst, self.timezone, self.type, self.source) = [clean(v) for v in row]
        self.lat = float(self.latitude or 0)
        self.lng = float(self.longitude or 0)

    def miles_to(self, other):
        """Great-circle (air) distance in statute miles, from GPS coordinates."""
        la1, lo1, la2, lo2 = map(math.radians, [self.lat, self.lng, other.lat, other.lng])
        h = (math.sin((la2 - la1) / 2) ** 2
             + math.cos(la1) * math.cos(la2) * math.sin((lo2 - lo1) / 2) ** 2)
        return 2 * 3958.8 * math.asin(math.sqrt(h))

    def map_info(self):
        return [round(self.lat, 4), round(self.lng, 4), self.name, self.city, self.country]

    def values(self):
        return [self.id, self.name, self.city, self.country, self.iata,
                self.icao, self.latitude, self.longitude, self.altitude,
                self.utc_offset, self.dst, self.timezone, self.type,
                self.source]


class Route:
    def __init__(self, row):
        (self.airline_code, self.airline_id, self.source_code,
         self.source_id, self.dest_code, self.dest_id, self.codeshare,
         self.stops, self.equipment) = [clean(v) for v in row]
        self.stops = int(self.stops or 0)
        self.equipment = " ".join(self.equipment.split())


class AviationDatabase:
    """Loads the three CSV files and answers every report query."""

    def __init__(self, data_dir):
        self.airlines_by_id, self.airlines_by_iata = {}, {}
        self.airports_by_id, self.airports_by_iata = {}, {}
        self.routes = []

        for row in self._read(data_dir, "SB-airlines.txt"):
            a = Airline(row)
            self.airlines_by_id[a.id] = a
            self.airlines_by_iata[a.iata.upper()] = a

        for row in self._read(data_dir, "SB-airports.txt"):
            a = Airport(row)
            self.airports_by_id[a.id] = a
            self.airports_by_iata[a.iata.upper()] = a

        for row in self._read(data_dir, "SB-routes.txt"):
            self.routes.append(Route(row))

    @staticmethod
    def _read(data_dir, name):
        with open(os.path.join(data_dir, name), encoding="utf-8", newline="") as f:
            return [row for row in csv.reader(f) if row]

    # 1.1 / 1.2
    def get_airline(self, iata):
        return self.airlines_by_iata.get(iata.strip().upper())

    def get_airport(self, iata):
        return self.airports_by_iata.get(iata.strip().upper())

    # 2.1a  airports reached by an airline, ordered by # routes
    def airports_for_airline(self, airline):
        counts = Counter()
        for r in self.routes:
            if r.airline_id == airline.id:
                counts[r.source_id] += 1
                counts[r.dest_id] += 1
        rows = [(self.airports_by_id[i], n) for i, n in counts.items()
                if i in self.airports_by_id]
        return sorted(rows, key=lambda x: (-x[1], x[0].iata))

    # 2.1b  airlines serving an airport, ordered by # routes
    def airlines_for_airport(self, airport):
        counts = Counter()
        for r in self.routes:
            if airport.id in (r.source_id, r.dest_id):
                counts[r.airline_id] += 1
        rows = [(self.airlines_by_id[i], n) for i, n in counts.items()
                if i in self.airlines_by_id]
        return sorted(rows, key=lambda x: (-x[1], x[0].iata))

    # Data for the globe: routes as [source IATA, dest IATA, airline IATA]
    def map_data(self, routes, focus=None):
        airports, segs = {}, []
        for r in routes:
            s, d = self.airports_by_id.get(r.source_id), self.airports_by_id.get(r.dest_id)
            al = self.airlines_by_id.get(r.airline_id)
            if not (s and d and al):
                continue
            airports[s.iata] = s.map_info()
            airports[d.iata] = d.map_info()
            segs.append([s.iata, d.iata, al.iata, r.stops])
        airline_names = {a.iata: a.name for a in self.airlines_by_iata.values()}
        return {"airports": airports, "routes": segs, "focus": focus,
                "airlines": airline_names}

    def routes_of_airline(self, airline):
        return [r for r in self.routes if r.airline_id == airline.id]

    def routes_at_airport(self, airport):
        return [r for r in self.routes if airport.id in (r.source_id, r.dest_id)]

    # Additional 1: One-hop report
    def one_hop(self, source, dest, airline_filter="ANY"):
        """
        All 0-stop route pairs S->X and X->D (X is neither S nor D).
        airline_filter: "ANY" (mix allowed), "SAME" (both legs same airline),
                        or an airline IATA code (both legs by that airline).
        Returns (pairs sorted by total miles, top-5 intermediate airports by # pairs).
        """
        legs_out, legs_in = {}, {}
        for r in self.routes:
            if r.stops != 0:
                continue
            if r.source_id == source.id and r.dest_id != dest.id:
                legs_out.setdefault(r.dest_id, []).append(r)
            if r.dest_id == dest.id and r.source_id != source.id:
                legs_in.setdefault(r.source_id, []).append(r)

        pairs = []
        for via_id in legs_out.keys() & legs_in.keys():
            via = self.airports_by_id.get(via_id)
            if via is None:
                continue
            leg1, leg2 = source.miles_to(via), via.miles_to(dest)
            for a in legs_out[via_id]:
                for b in legs_in[via_id]:
                    al1, al2 = self.airlines_by_id.get(a.airline_id), self.airlines_by_id.get(b.airline_id)
                    if not (al1 and al2):
                        continue
                    if airline_filter == "SAME" and al1 is not al2:
                        continue
                    if airline_filter not in ("ANY", "SAME") and not (
                            al1.iata == airline_filter and al2.iata == airline_filter):
                        continue
                    pairs.append({"via": via, "airline1": al1, "airline2": al2,
                                  "leg1": leg1, "leg2": leg2, "total": leg1 + leg2})
        pairs.sort(key=lambda p: (p["total"], p["via"].iata, p["airline1"].iata, p["airline2"].iata))

        per_via = {}
        for p in pairs:
            entry = per_via.setdefault(p["via"].iata, {"via": p["via"], "count": 0, "total": p["total"]})
            entry["count"] += 1
        top5 = sorted(per_via.values(), key=lambda e: (-e["count"], e["total"], e["via"].iata))[:5]
        return pairs, top5

    def airlines_serving_airports(self):
        """{airport id: set of airline IATA codes with a route to/from it}"""
        served = {}
        for r in self.routes:
            al = self.airlines_by_id.get(r.airline_id)
            if al:
                served.setdefault(r.source_id, set()).add(al.iata)
                served.setdefault(r.dest_id, set()).add(al.iata)
        return served

    def direct_routes(self, source, dest):
        return [self.airlines_by_id[r.airline_id] for r in self.routes
                if r.source_id == source.id and r.dest_id == dest.id
                and r.stops == 0 and r.airline_id in self.airlines_by_id]

    # 2.2a / 2.2b
    def all_airlines(self):
        return sorted(self.airlines_by_iata.values(), key=lambda a: a.iata)

    def all_airports(self):
        return sorted(self.airports_by_iata.values(), key=lambda a: a.iata)


class _Leg:
    """A lightweight route-like object so one-hop legs can be drawn on the globe."""
    def __init__(self, a, b, airline):
        self.source_id, self.dest_id, self.airline_id, self.stops = a.id, b.id, airline.id, 0


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------
class Page:
    CSS = """
    body{font-family:system-ui,Segoe UI,Arial,sans-serif;margin:0;background:#f5f7fa;color:#1d2330}
    header{background:#1f3a5f;color:#fff;padding:14px 24px}
    header a{color:#fff;text-decoration:none;font-size:20px;font-weight:600}
    nav{background:#fff;border-bottom:1px solid #dde3ea;padding:8px 24px;display:flex;flex-wrap:wrap;gap:14px}
    nav a{color:#1f3a5f;text-decoration:none;font-size:14px}
    nav a:hover{text-decoration:underline}
    main{padding:20px 24px;max-width:1200px}
    h2{margin-top:0}
    form{margin:10px 0 18px}
    select{padding:7px 8px;font-size:15px;border:1px solid #b8c2cf;border-radius:4px;background:#fff}
    .onehop-form{display:flex;flex-wrap:wrap;gap:10px 16px;align-items:center}
    .summary{display:flex;flex-wrap:wrap;gap:10px;margin:0 0 12px}
    .chip{background:#fff;border:1px solid #dde3ea;border-radius:16px;padding:5px 12px;font-size:14px}
    .chip b{color:#1f3a5f}
    .filters{display:flex;flex-wrap:wrap;gap:10px 14px;align-items:center;background:#fff;border:1px solid #dde3ea;border-radius:8px;padding:12px 14px;margin:0 0 12px}
    .filters input[type=search]{padding:7px 10px;font-size:15px;width:240px;border:1px solid #b8c2cf;border-radius:4px}
    .filters .clear{background:#e8edf3;color:#1f3a5f}
    .noresult td{color:#888;text-align:center;padding:18px}
    input[type=text]{padding:7px 10px;font-size:15px;width:120px;text-transform:uppercase;border:1px solid #b8c2cf;border-radius:4px}
    button{padding:7px 14px;font-size:15px;background:#1f3a5f;color:#fff;border:0;border-radius:4px;cursor:pointer}
    .scroll{max-height:70vh;overflow:auto;border:1px solid #dde3ea;background:#fff}
    table{border-collapse:collapse;width:100%;font-size:14px}
    th,td{padding:6px 10px;border-bottom:1px solid #eef1f5;text-align:left;white-space:nowrap}
    th{background:#e8edf3;position:sticky;top:0}
    tr:hover td{background:#f8fafc}
    .err{color:#b00020}
    .count{color:#555;font-size:14px}
    .cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:14px}
    .card{background:#fff;border:1px solid #dde3ea;border-radius:6px;padding:14px}
    .card a{font-weight:600;color:#1f3a5f}
    .globe-wrap{position:relative;background:#000814;border-radius:8px;overflow:hidden;margin:6px 0 14px;height:460px}
    #globe{width:100%;height:100%}
    .globe-info{position:absolute;left:12px;top:10px;color:#fff;background:rgba(0,8,20,.7);padding:8px 12px;border-radius:6px;font-size:14px;max-width:70%;pointer-events:none}
    .globe-info b{color:#ffd166}
    .globe-msg{color:#cfd8e3;padding:60px 20px 20px}
    .hint{color:#555;font-size:13px;margin:-6px 0 8px}
    .hero{position:relative;border-radius:10px;overflow:hidden;margin-bottom:18px;line-height:0;box-shadow:0 2px 10px rgba(0,0,0,.12)}
    .hero svg{width:100%;height:auto;display:block}
    .hero-text{position:absolute;left:clamp(14px,3vw,36px);top:clamp(12px,3vw,32px);color:#fff;line-height:1.25;text-shadow:0 2px 6px rgba(0,0,0,.35)}
    .hero-text h1{margin:0;font-size:clamp(20px,3.6vw,40px)}
    .hero-text p{margin:6px 0 0;font-size:clamp(12px,1.5vw,17px);opacity:.95}
    @media(max-width:600px){.hero-text p{display:none}}
    .about{display:flex;flex-wrap:wrap;gap:28px;align-items:flex-start;background:#fff;border:1px solid #dde3ea;border-radius:10px;padding:28px;max-width:860px}
    .about .avatar{width:170px;height:170px;border-radius:50%;object-fit:cover;border:4px solid #e8edf3;flex:none}
    .about .initials{display:flex;align-items:center;justify-content:center;background:linear-gradient(135deg,#1f3a5f,#4f97c9);color:#fff;font-size:56px;font-weight:700}
    .about .bio{flex:1;min-width:260px;line-height:1.6}
    .about h2{margin:0 0 4px}
    .about .role{color:#4f6b8a;margin:0 0 14px}
    .btn-li{display:inline-block;background:#0a66c2;color:#fff;text-decoration:none;padding:8px 16px;border-radius:20px;font-weight:600;margin-top:6px}
    .project{margin-top:18px;padding-top:6px;border-top:1px solid #eef1f5;color:#444}
    .project p{margin:8px 0}
    .project a{color:#1f3a5f}
    tr.pick{cursor:pointer}
    tr.pick.sel td{background:#fff3c4 !important}
    """

    # Home page illustration: an airliner taking off past an airport (hand-drawn SVG, animated)
    HERO_SVG = """
<svg viewBox="0 0 1200 340" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="Airplane taking off from an airport">
  <defs>
    <linearGradient id="sky" x1="0" y1="0" x2="0" y2="1">
      <stop offset="0" stop-color="#0b3d6e"/><stop offset=".55" stop-color="#4f97c9"/><stop offset="1" stop-color="#cfe8f5"/>
    </linearGradient>
    <radialGradient id="sun"><stop offset="0" stop-color="#fff3c4"/><stop offset=".45" stop-color="#ffd166"/><stop offset="1" stop-color="#ffd166" stop-opacity="0"/></radialGradient>
    <linearGradient id="body" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#ffffff"/><stop offset="1" stop-color="#d9e2ec"/></linearGradient>
    <g id="cloud" fill="#fff"><ellipse cx="0" cy="0" rx="46" ry="16"/><ellipse cx="-22" cy="-10" rx="22" ry="16"/><ellipse cx="14" cy="-16" rx="26" ry="20"/></g>
  </defs>
  <rect width="1200" height="340" fill="url(#sky)"/>
  <circle cx="960" cy="86" r="90" fill="url(#sun)"/>
  <circle cx="960" cy="86" r="34" fill="#ffe08a"/>

  <!-- drifting clouds -->
  <use href="#cloud" opacity=".85"><animateTransform attributeName="transform" type="translate" from="-80 70" to="1300 70" dur="70s" repeatCount="indefinite"/></use>
  <use href="#cloud" opacity=".7"><animateTransform attributeName="transform" type="translate" from="420 120" to="1300 120" dur="55s" repeatCount="indefinite"/></use>
  <use href="#cloud" opacity=".6"><animateTransform attributeName="transform" type="translate" from="-80 175" to="1300 175" dur="90s" begin="-40s" repeatCount="indefinite"/></use>

  <!-- distant hills -->
  <path d="M0,272 Q150,236 300,262 Q460,226 620,262 Q760,240 900,264 Q1050,238 1200,262 L1200,276 L0,276 Z" fill="#6f9cbd" opacity=".6"/>

  <!-- ground and runway -->
  <rect y="272" width="1200" height="68" fill="#5f8f55"/>
  <rect y="288" width="1200" height="32" fill="#3a434f"/>
  <line x1="70" y1="304" x2="1200" y2="304" stroke="#fff" stroke-width="3" stroke-dasharray="28 20"/>
  <g fill="#fff"><rect x="18" y="292" width="34" height="4"/><rect x="18" y="300" width="34" height="4"/><rect x="18" y="308" width="34" height="4"/><rect x="18" y="316" width="34" height="2"/></g>
  <g fill="#ffd166">
    <circle cx="70" cy="290" r="2"/><circle cx="170" cy="290" r="2"/><circle cx="270" cy="290" r="2"/><circle cx="370" cy="290" r="2"/><circle cx="470" cy="290" r="2"/><circle cx="570" cy="290" r="2"/><circle cx="670" cy="290" r="2"/><circle cx="770" cy="290" r="2"/><circle cx="870" cy="290" r="2"/><circle cx="970" cy="290" r="2"/><circle cx="1070" cy="290" r="2"/><circle cx="1170" cy="290" r="2"/>
    <circle cx="70" cy="318" r="2"/><circle cx="170" cy="318" r="2"/><circle cx="270" cy="318" r="2"/><circle cx="370" cy="318" r="2"/><circle cx="470" cy="318" r="2"/><circle cx="570" cy="318" r="2"/><circle cx="670" cy="318" r="2"/><circle cx="770" cy="318" r="2"/><circle cx="870" cy="318" r="2"/><circle cx="970" cy="318" r="2"/><circle cx="1070" cy="318" r="2"/><circle cx="1170" cy="318" r="2"/>
  </g>

  <!-- terminal building -->
  <rect x="760" y="218" width="270" height="56" fill="#e9eef4"/>
  <rect x="770" y="230" width="250" height="30" fill="#7fb8e0"/>
  <g stroke="#e9eef4" stroke-width="3"><line x1="800" y1="230" x2="800" y2="260"/><line x1="830" y1="230" x2="830" y2="260"/><line x1="860" y1="230" x2="860" y2="260"/><line x1="890" y1="230" x2="890" y2="260"/><line x1="920" y1="230" x2="920" y2="260"/><line x1="950" y1="230" x2="950" y2="260"/><line x1="980" y1="230" x2="980" y2="260"/><line x1="770" y1="245" x2="1020" y2="245"/></g>
  <path d="M748,222 Q895,186 1042,222 L1042,228 Q895,194 748,228 Z" fill="#b9c6d4"/>
  <rect x="880" y="262" width="30" height="12" fill="#2b4d74"/>

  <!-- control tower -->
  <rect x="1083" y="150" width="24" height="124" fill="#dfe6ee"/>
  <rect x="1083" y="150" width="7" height="124" fill="#c7d1dc"/>
  <path d="M1066,150 L1124,150 L1132,120 L1058,120 Z" fill="#2b4d74"/>
  <rect x="1064" y="124" width="62" height="16" fill="#9fd3f7"/>
  <rect x="1060" y="111" width="70" height="10" fill="#b9c6d4"/>
  <line x1="1095" y1="111" x2="1095" y2="88" stroke="#b9c6d4" stroke-width="3"/>
  <circle cx="1095" cy="86" r="4" fill="#ef476f"><animate attributeName="opacity" values="1;.15;1" dur="1.6s" repeatCount="indefinite"/></circle>

  <!-- contrail: soft white trail that fades out behind the plane -->
  <defs>
    <linearGradient id="trail" gradientUnits="userSpaceOnUse" x1="180" y1="280" x2="600" y2="196">
      <stop offset="0" stop-color="#fff" stop-opacity="0"/><stop offset=".6" stop-color="#fff" stop-opacity=".45"/><stop offset="1" stop-color="#fff" stop-opacity=".9"/>
    </linearGradient>
    <filter id="soft" x="-10%" y="-50%" width="120%" height="200%"><feGaussianBlur stdDeviation="2.2"/></filter>
  </defs>
  <g filter="url(#soft)" fill="none" stroke="url(#trail)" stroke-linecap="round">
    <path d="M604,192 C500,214 360,246 180,280" stroke-width="7">
      <animate attributeName="stroke-width" values="7;9;7" dur="4s" repeatCount="indefinite"/>
    </path>
    <path d="M610,204 C506,228 368,260 190,294" stroke-width="4" opacity=".7"/>
  </g>

  <!-- airliner -->
  <g>
    <animateTransform attributeName="transform" type="translate" values="0 0; 0 -7; 0 0" dur="4s" repeatCount="indefinite"/>
    <g transform="translate(600,150) rotate(-12) scale(1.15)">
      <path d="M14,32 L0,-8 L22,-8 L60,22 Z" fill="#ef476f"/>
      <path d="M22,36 L-6,48 L14,48 L54,38 Z" fill="#c9d3de"/>
      <path d="M10,34 L32,20 L215,18 Q262,20 272,32 Q262,43 225,45 L40,45 Q18,43 10,34 Z" fill="url(#body)"/>
      <path d="M32,38 L230,37" stroke="#1f3a5f" stroke-width="3"/>
      <path d="M246,24 L258,26 L264,31 L249,31 Z" fill="#1f3a5f"/>
      <g fill="#1f3a5f">
        <circle cx="64" cy="28" r="2.2"/><circle cx="74" cy="28" r="2.2"/><circle cx="84" cy="28" r="2.2"/><circle cx="94" cy="28" r="2.2"/><circle cx="104" cy="28" r="2.2"/><circle cx="114" cy="28" r="2.2"/><circle cx="124" cy="28" r="2.2"/><circle cx="134" cy="28" r="2.2"/><circle cx="144" cy="28" r="2.2"/><circle cx="154" cy="28" r="2.2"/><circle cx="164" cy="28" r="2.2"/><circle cx="174" cy="28" r="2.2"/><circle cx="184" cy="28" r="2.2"/><circle cx="194" cy="28" r="2.2"/><circle cx="204" cy="28" r="2.2"/><circle cx="214" cy="28" r="2.2"/>
      </g>
      <path d="M118,40 L84,78 L108,78 L172,41 Z" fill="#c9d3de"/>
      <rect x="116" y="52" width="38" height="15" rx="7" fill="#9aa8b8"/>
      <rect x="148" y="54" width="7" height="11" rx="3" fill="#2b4d74"/>
    </g>
  </g>
</svg>
"""

    FILTER_JS = r"""
(function(){
  function norm(s){ return (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase(); }
  var text = document.getElementById('f-text'), field = document.getElementById('f-field');
  var country = document.getElementById('f-country'), airline = document.getElementById('f-airline');
  var count = document.getElementById('f-count'), rows = [].slice.call(document.querySelectorAll('tr.frow'));
  var fields = field ? [].slice.call(field.options).map(function(o){return o.value;}).filter(function(v){return v !== 'any';}) : [];
  var tbody = rows.length ? rows[0].parentNode : null, none = document.createElement('tr');
  none.className = 'noresult'; none.innerHTML = "<td colspan='99'>No matches. Try a different search.</td>";
  function apply(){
    var q = norm(text.value.trim()), f = field ? field.value : 'any';
    var c = country ? country.value : '', a = airline ? airline.value : '';
    var shown = 0;
    rows.forEach(function(r){
      var ok = true;
      if (q) {
        var look = f === 'any' ? fields : [f];
        ok = look.some(function(k){ return norm(r.dataset[k]).indexOf(q) !== -1; });
      }
      if (ok && c) ok = r.dataset.country === c;
      if (ok && a) ok = (' ' + r.dataset.airlines + ' ').indexOf(' ' + a + ' ') !== -1;
      r.style.display = ok ? '' : 'none';
      if (ok) shown++;
    });
    count.textContent = 'Showing ' + shown + ' of ' + rows.length;
    if (tbody) { if (!shown) tbody.appendChild(none); else if (none.parentNode) tbody.removeChild(none); }
  }
  [text, field, country, airline].forEach(function(e){ if (e) { e.addEventListener('input', apply); e.addEventListener('change', apply); } });
  var clear = document.getElementById('f-clear');
  if (clear) clear.addEventListener('click', function(){
    text.value = ''; if (field) field.value = 'any'; if (country) country.value = ''; if (airline) airline.value = ''; apply(); text.focus();
  });
  apply();
})();
"""

    @staticmethod
    def filter_bar(fields, countries, airlines=None):
        """fields: [(data-key, label)]; countries: sorted list; airlines: [(iata, name)] or None."""
        opts = "<option value='any'>Any field</option>" + "".join(
            f"<option value='{k}'>{html.escape(l)}</option>" for k, l in fields)
        cty = "<option value=''>All countries</option>" + "".join(
            f"<option value='{html.escape(c)}'>{html.escape(c)}</option>" for c in countries)
        bar = ("<div class='filters'>"
               "<label>Search: <input type='search' id='f-text' placeholder='Type to search...' autofocus></label>"
               f"<label>in <select id='f-field'>{opts}</select></label>"
               f"<label>Country: <select id='f-country'>{cty}</select></label>")
        if airlines:
            al = "<option value=''>Any airline</option>" + "".join(
                f"<option value='{i}'>{i} - {html.escape(n)}</option>" for i, n in airlines)
            bar += f"<label>Served by: <select id='f-airline'>{al}</select></label>"
        return bar + "<button type='button' class='clear' id='f-clear'>Clear</button>" \
                     "<span class='count' id='f-count'></span></div>"

    GLOBE_JS = r"""
(function(){
  var D = JSON.parse(document.getElementById('globe-data').textContent);
  var el = document.getElementById('globe'), info = document.getElementById('globe-info');
  if (typeof Globe === 'undefined') {
    el.innerHTML = "<div class='globe-msg'>The 3D globe needs an internet connection (it loads from cdn.jsdelivr.net).</div>";
    return;
  }
  var R = Math.PI/180;
  function miles(a, b){
    var p = D.airports[a], q = D.airports[b];
    var h = Math.pow(Math.sin((q[0]-p[0])*R/2),2) + Math.cos(p[0]*R)*Math.cos(q[0]*R)*Math.pow(Math.sin((q[1]-p[1])*R/2),2);
    return Math.round(2*3958.8*Math.asin(Math.sqrt(h)));
  }
  // merge directional routes into one arc per airport pair
  var pairs = {};
  D.routes.forEach(function(r){
    var k = r[0] < r[1] ? r[0]+'|'+r[1] : r[1]+'|'+r[0];
    var p = pairs[k] || (pairs[k] = {a:k.split('|')[0], b:k.split('|')[1], lines:{}, list:[]});
    p.lines[r[2]] = 1; p.list.push(r);
  });
  var arcs = Object.keys(pairs).map(function(k){
    var p = pairs[k]; p.mi = miles(p.a, p.b); p.hl = false; return p;
  });
  function arcLabel(p){
    return '<b>' + p.a + ' &#8644; ' + p.b + '</b><br>' + p.mi.toLocaleString() + ' miles<br>' +
           Object.keys(p.lines).join(', ');
  }
  var g = Globe()(el)
    .globeImageUrl('https://cdn.jsdelivr.net/npm/three-globe/example/img/earth-blue-marble.jpg')
    .bumpImageUrl('https://cdn.jsdelivr.net/npm/three-globe/example/img/earth-topology.png')
    .backgroundImageUrl('https://cdn.jsdelivr.net/npm/three-globe/example/img/night-sky.png')
    .width(el.clientWidth).height(el.clientHeight)
    .arcStartLat(function(p){return D.airports[p.a][0];}).arcStartLng(function(p){return D.airports[p.a][1];})
    .arcEndLat(function(p){return D.airports[p.b][0];}).arcEndLng(function(p){return D.airports[p.b][1];})
    .arcColor(function(p){return p.hl ? ['#ffd166','#ef476f'] : 'rgba(120,200,255,0.35)';})
    .arcStroke(function(p){return p.hl ? 0.7 : 0.25;})
    .arcDashLength(function(p){return p.hl ? 0.5 : 1;})
    .arcDashGap(function(p){return p.hl ? 0.15 : 0;})
    .arcDashAnimateTime(function(p){return p.hl ? 2000 : 0;})
    .arcLabel(arcLabel)
    .pointLat(function(c){return D.airports[c][0];}).pointLng(function(c){return D.airports[c][1];})
    .pointColor(function(c){return c === sel || marks[c] ? '#ef476f' : (hot[c] ? '#ffd166' : '#ffffff');})
    .pointRadius(function(c){return c === sel || marks[c] ? 0.55 : (hot[c] ? 0.35 : 0.22);})
    .pointAltitude(0.01)
    .pointLabel(function(c){var a = D.airports[c]; return '<b>' + c + '</b> ' + a[2] + '<br>' + a[3] + ', ' + a[4];});
  window.addEventListener('resize', function(){ g.width(el.clientWidth).height(el.clientHeight); });

  var sel = null, hot = {};
  var marks = {}; (D.marks || []).concat(D.focus ? [D.focus] : []).forEach(function(c){ marks[c] = 1; });
  var base = null;  // optional: only these airports' arcs are shown when nothing is selected
  if (D.base) { base = {}; D.base.forEach(function(c){ base[c] = 1; }); }
  function inBase(p){ return !base || base[p.a] || base[p.b]; }
  var baseInfo = info.innerHTML;
  if (D.labels) {
    g.labelsData(D.labels)
      .labelLat(function(l){return D.airports[l[0]][0];}).labelLng(function(l){return D.airports[l[0]][1];})
      .labelText(function(l){return l[1];})
      .labelColor(function(l){return marks[l[0]] ? '#ff8fa3' : '#ffd166';})
      .labelSize(0.9).labelDotRadius(0.35).labelAltitude(0.012).labelResolution(2);
  }
  function draw(){
    var on = arcs.filter(function(p){return p.hl;});
    // when something is selected, show only its arcs so they stand out
    var shown = sel ? on : arcs.filter(inBase);
    g.arcsData(shown);
    var pts = {};
    shown.forEach(function(p){ pts[p.a] = 1; pts[p.b] = 1; });
    Object.keys(marks).forEach(function(c){ pts[c] = 1; });
    g.pointsData(Object.keys(pts));
  }
  function fly(code, alt){
    var a = D.airports[code]; if (a) g.pointOfView({lat:a[0], lng:a[1], altitude:alt || 1.8}, 1200);
  }
  window.showOnGlobe = function(key, kind){
    sel = key; hot = {};
    var count = 0;
    arcs.forEach(function(p){
      p.hl = key === null ? !!(base && inBase(p))
           : kind === 'airport' ? (p.a === key || p.b === key) : !!p.lines[key];
      if (p.hl) {
        hot[p.a] = 1; hot[p.b] = 1;
        p.list.forEach(function(r){ if (kind !== 'airline' || r[2] === key) count++; });
      }
    });
    if (key === null) hot = {};
    var n = arcs.filter(function(p){return p.hl;}).length;
    if (key === null) { info.innerHTML = baseInfo; }
    else if (kind === 'airport') {
      var a = D.airports[key];
      info.innerHTML = '<b>' + key + '</b> ' + a[2] + ' &mdash; ' + count + ' routes, ' + n + ' connected airports';
    } else {
      info.innerHTML = '<b>' + key + '</b> ' + (D.airlines[key] || '') + ' &mdash; ' + count + ' routes';
    }
    draw();
    if (key && kind === 'airport') fly(key, D.alt || 1.6);
    else if (D.focus) fly(D.focus, D.alt || 1.8);
  };
  window.showOnGlobe(null, null);
  if (D.focus) fly(D.focus, D.alt || 1.8);
  else if (arcs.length) fly(arcs[0].a, 2.2);
  g.controls().autoRotate = !D.focus;
  g.controls().autoRotateSpeed = 0.4;

  // clickable table rows
  document.querySelectorAll('tr.pick').forEach(function(tr){
    tr.addEventListener('click', function(){
      var was = tr.classList.contains('sel');
      document.querySelectorAll('tr.pick.sel').forEach(function(x){ x.classList.remove('sel'); });
      g.controls().autoRotate = false;
      if (was) { window.showOnGlobe(null, null); return; }
      tr.classList.add('sel');
      window.showOnGlobe(tr.dataset.key, tr.dataset.kind);
      if (tr.dataset.info) info.textContent = tr.dataset.info;
      document.getElementById('globe').scrollIntoView({behavior:'smooth', block:'nearest'});
    });
  });
})();
"""

    NAV = [("/airline", "1.1 Airline Lookup"),
           ("/airport", "1.2 Airport Lookup"),
           ("/report/airline-airports", "2.1a Airline → Airports"),
           ("/report/airport-airlines", "2.1b Airport → Airlines"),
           ("/report/airlines", "2.2a All Airlines"),
           ("/report/airports", "2.2b All Airports"),
           ("/id", "2.3 Get ID"),
           ("/onehop", "★ One Hop Routes"),
           ("/about", "About")]

    @classmethod
    def render(cls, title, body, globe_data=None, extra_js=""):
        nav = "".join(f'<a href="{u}">{html.escape(t)}</a>' for u, t in cls.NAV)
        scripts = f"<script>{extra_js}</script>" if extra_js else ""
        if globe_data is not None:
            data = json.dumps(globe_data).replace("</", "<\\/")
            scripts += (f"<script type='application/json' id='globe-data'>{data}</script>"
                       f"<script src='https://cdn.jsdelivr.net/npm/globe.gl@2'></script>"
                       f"<script>{cls.GLOBE_JS}</script>")
        return (f"<!doctype html><html><head><meta charset='utf-8'>"
                f"<meta name='viewport' content='width=device-width,initial-scale=1'>"
                f"<title>{html.escape(title)} - Airline Route Access</title>"
                f"<style>{cls.CSS}</style></head><body>"
                f"<header><a href='/'>✈ Airline Route Access</a></header>"
                f"<nav>{nav}</nav><main>{body}</main>{scripts}</body></html>")

    @staticmethod
    def globe(caption, hint=""):
        hint_html = f"<p class='hint'>{html.escape(hint)}</p>" if hint else ""
        return (f"<div class='globe-wrap'><div id='globe'></div>"
                f"<div class='globe-info' id='globe-info'>{caption}</div></div>{hint_html}")

    @staticmethod
    def form(action, label, value=""):
        return (f"<form action='{action}' method='get'>"
                f"<label>{html.escape(label)}: "
                f"<input type='text' name='code' value='{html.escape(value)}' autofocus></label> "
                f"<button type='submit'>Go</button></form>")

    @staticmethod
    def table(headers, rows, keys=None, kind=None, infos=None, row_data=None):
        """keys/kind make each row clickable to show it on the globe; infos = caption per row;
        row_data = list of {name: value} dicts, written as data-* attributes for the search bar."""
        head = "".join(f"<th>{html.escape(h)}</th>" for h in headers)
        body = ""
        for i, r in enumerate(rows):
            attr = ""
            if keys:
                attr = f" class='pick' data-key='{html.escape(keys[i])}' data-kind='{kind}'"
                if infos:
                    attr += f" data-info='{html.escape(infos[i])}'"
            elif row_data:
                attr = " class='frow'" + "".join(f" data-{k}='{html.escape(str(v))}'"
                                                 for k, v in row_data[i].items())
            body += f"<tr{attr}>" + "".join(f"<td>{html.escape(str(v))}</td>" for v in r) + "</tr>"
        return f"<div class='scroll'><table><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table></div>"

    @staticmethod
    def entity(fields, values):
        rows = "".join(f"<tr><th>{html.escape(f)}</th><td>{html.escape(v)}</td></tr>"
                       for f, v in zip(fields, values))
        return f"<div class='scroll' style='max-width:600px'><table>{rows}</table></div>"

    @staticmethod
    def error(msg):
        return f"<p class='err'>{html.escape(msg)}</p>"


# ---------------------------------------------------------------------------
# Web application (routing)
# ---------------------------------------------------------------------------
class AviationWebApp:
    def __init__(self, db):
        self.db = db
        self.routes = {
            "/": self.home,
            "/airline": self.airline_lookup,
            "/airport": self.airport_lookup,
            "/report/airline-airports": self.airline_airports_report,
            "/report/airport-airlines": self.airport_airlines_report,
            "/report/airlines": self.all_airlines_report,
            "/report/airports": self.all_airports_report,
            "/id": self.get_id,
            "/onehop": self.one_hop,
            "/about": self.about,
        }

    def handle(self, path, query):
        handler = self.routes.get(path)
        if handler is None:
            return 404, Page.render("Not found", Page.error("Page not found."))
        if handler == self.one_hop:
            return 200, handler(query)
        code = query.get("code", [""])[0].strip().upper()
        return 200, handler(code)

    def home(self, _):
        cards = "".join(f"<div class='card'><a href='{u}'>{html.escape(t)}</a></div>"
                        for u, t in Page.NAV)
        hero = (f"<div class='hero'>{Page.HERO_SVG}<div class='hero-text'>"
                f"<h1>Air Travel Database</h1>"
                f"<p>{len(self.db.airlines_by_iata)} airlines · {len(self.db.airports_by_iata)} airports · "
                f"{len(self.db.routes):,} routes</p></div></div>")
        return Page.render("Home", f"{hero}<div class='cards'>{cards}</div>")

    def airline_lookup(self, code):
        body = "<h2>1.1 Airline Lookup</h2>" + Page.form("/airline", "Airline IATA code", code)
        if code:
            a = self.db.get_airline(code)
            body += Page.entity(Airline.FIELDS, a.values()) if a else Page.error(f"No airline with IATA code '{code}'.")
        return Page.render("Airline Lookup", body)

    def airport_lookup(self, code):
        body = "<h2>1.2 Airport Lookup</h2>" + Page.form("/airport", "Airport IATA code", code)
        globe = None
        if code:
            a = self.db.get_airport(code)
            if not a:
                body += Page.error(f"No airport with IATA code '{code}'.")
            else:
                routes = self.db.routes_at_airport(a)
                body += (Page.globe(f"<b>{html.escape(a.iata)}</b> {html.escape(a.name)} &mdash; "
                                    f"{len(routes)} routes (all airlines)")
                         + Page.entity(Airport.FIELDS, a.values()))
                globe = self.db.map_data(routes, focus=a.iata)
        return Page.render("Airport Lookup", body, globe)

    def airline_airports_report(self, code):
        body = ("<h2>2.1a Airports served by an Airline (by # routes)</h2>"
                + Page.form("/report/airline-airports", "Airline IATA code", code))
        globe = None
        if code:
            airline = self.db.get_airline(code)
            if not airline:
                body += Page.error(f"No airline with IATA code '{code}'.")
            else:
                rows = self.db.airports_for_airline(airline)
                routes = self.db.routes_of_airline(airline)
                body += (f"<h3>{html.escape(airline.name)} ({html.escape(airline.iata)})</h3>"
                         + Page.globe(f"<b>{html.escape(airline.iata)}</b> {html.escape(airline.name)} &mdash; "
                                      f"{len(routes)} routes, {len(rows)} airports",
                                      "Click any airport row below to show its routes on the globe "
                                      "(click again to clear). Hover an arc for its distance.")
                         + f"<p class='count'>{len(rows)} airports</p>"
                         + Page.table(["# Routes"] + Airport.FIELDS,
                                      [[n] + ap.values() for ap, n in rows],
                                      keys=[ap.iata for ap, _ in rows], kind="airport"))
                globe = self.db.map_data(routes)
        return Page.render("Airline → Airports", body, globe)

    def airport_airlines_report(self, code):
        body = ("<h2>2.1b Airlines serving an Airport (by # routes)</h2>"
                + Page.form("/report/airport-airlines", "Airport IATA code", code))
        globe = None
        if code:
            airport = self.db.get_airport(code)
            if not airport:
                body += Page.error(f"No airport with IATA code '{code}'.")
            else:
                rows = self.db.airlines_for_airport(airport)
                routes = self.db.routes_at_airport(airport)
                body += (f"<h3>{html.escape(airport.name)} ({html.escape(airport.iata)})</h3>"
                         + Page.globe(f"<b>{html.escape(airport.iata)}</b> {html.escape(airport.name)} &mdash; "
                                      f"{len(routes)} routes, {len(rows)} airlines",
                                      "Click any airline row below to show only that airline's routes "
                                      "(click again to clear). Hover an arc for its distance.")
                         + f"<p class='count'>{len(rows)} airlines</p>"
                         + Page.table(["# Routes"] + Airline.FIELDS,
                                      [[n] + al.values() for al, n in rows],
                                      keys=[al.iata for al, _ in rows], kind="airline"))
                globe = self.db.map_data(routes, focus=airport.iata)
        return Page.render("Airport → Airlines", body, globe)

    def all_airlines_report(self, _):
        rows = self.db.all_airlines()
        bar = Page.filter_bar([("name", "Airline name"), ("country", "Country"), ("iata", "IATA / ICAO code"),
                               ("callsign", "Callsign")],
                              sorted({a.country for a in rows if a.country}))
        data = [{"name": a.name + " " + a.alias, "country": a.country, "iata": a.iata + " " + a.icao,
                 "callsign": a.callsign} for a in rows]
        body = (f"<h2>2.2a All Airlines (by IATA code)</h2>{bar}"
                + Page.table(Airline.FIELDS, [a.values() for a in rows], row_data=data))
        return Page.render("All Airlines", body, extra_js=Page.FILTER_JS)

    def all_airports_report(self, _):
        rows = self.db.all_airports()
        served = self.db.airlines_serving_airports()
        bar = Page.filter_bar([("city", "City"), ("country", "Country"), ("name", "Airport name"),
                               ("iata", "IATA / ICAO code")],
                              sorted({a.country for a in rows if a.country}),
                              airlines=[(a.iata, a.name) for a in self.db.all_airlines()])
        data = [{"name": a.name, "city": a.city, "country": a.country, "iata": a.iata + " " + a.icao,
                 "airlines": " ".join(sorted(served.get(a.id, ())))} for a in rows]
        body = (f"<h2>2.2b All Airports (by IATA code)</h2>{bar}"
                + Page.table(Airport.FIELDS, [a.values() for a in rows], row_data=data))
        return Page.render("All Airports", body, extra_js=Page.FILTER_JS)

    def one_hop(self, query):
        src = query.get("from", [""])[0].strip().upper()
        dst = query.get("to", [""])[0].strip().upper()
        flt = query.get("airline", ["ANY"])[0].strip().upper() or "ANY"

        opts = [("ANY", "Any airlines (mix allowed)"), ("SAME", "Same airline for both flights")]
        opts += [(a.iata, f"{a.iata} only - {a.name}") for a in self.db.all_airlines()]
        if flt not in dict(opts):
            flt = "ANY"
        options = "".join(f"<option value='{v}'{' selected' if v == flt else ''}>{html.escape(l)}</option>"
                          for v, l in opts)
        body = ("<h2>One Hop Routes</h2>"
                "<p class='hint'>Trips from S to D with exactly one stop at X (S&rarr;X, then X&rarr;D). "
                "Both flights must be non-stop. Ordered by total air miles (from GPS).</p>"
                "<form class='onehop-form' action='/onehop' method='get'>"
                f"<label>From: <input type='text' name='from' value='{html.escape(src)}' autofocus></label>"
                f"<label>To: <input type='text' name='to' value='{html.escape(dst)}'></label>"
                f"<label>Airline: <select name='airline'>{options}</select></label>"
                "<button type='submit'>Find routes</button></form>")
        globe = None
        if not (src or dst):
            return Page.render("One Hop", body)

        S, D = self.db.get_airport(src), self.db.get_airport(dst)
        if not src or not dst:
            return Page.render("One Hop", body + Page.error("Please enter both a From and a To airport code."))
        if not S:
            return Page.render("One Hop", body + Page.error(f"No airport with IATA code '{src}'."))
        if not D:
            return Page.render("One Hop", body + Page.error(f"No airport with IATA code '{dst}'."))
        if S is D:
            return Page.render("One Hop", body + Page.error("From and To must be different airports."))

        pairs, top5 = self.db.one_hop(S, D, flt)
        direct = self.db.direct_routes(S, D)
        direct_mi = S.miles_to(D)
        flt_label = dict(opts)[flt]

        body += (f"<h3>{html.escape(S.iata)} {html.escape(S.city)} &rarr; "
                 f"{html.escape(D.iata)} {html.escape(D.city)}</h3>")
        direct_txt = (", ".join(sorted({a.iata for a in direct})) if direct else "none")
        body += ("<div class='summary'>"
                 f"<span class='chip'>Filter: <b>{html.escape(flt_label)}</b></span>"
                 f"<span class='chip'>Route pairs: <b>{len(pairs)}</b></span>"
                 f"<span class='chip'>Via airports: <b>{len({p['via'].iata for p in pairs})}</b></span>"
                 f"<span class='chip'>Direct flights: <b>{html.escape(direct_txt)}</b> "
                 f"({direct_mi:,.0f} mi straight line)</span></div>")

        if not pairs:
            return Page.render("One Hop", body + Page.error(
                "No one-hop routes found for this airline choice. Try 'Any airlines'."))

        # globe: every via airport's two legs; top 5 shown and labelled at start
        seen, legs = set(), []
        for p in pairs:
            for x, y, al in ((S, p["via"], p["airline1"]), (p["via"], D, p["airline2"])):
                if (x.id, y.id, al.id) not in seen:
                    seen.add((x.id, y.id, al.id))
                    legs.append(_Leg(x, y, al))
        globe = self.db.map_data(legs)
        globe.update(marks=[S.iata, D.iata], base=[e["via"].iata for e in top5], alt=2.0,
                     labels=[[S.iata, S.iata], [D.iata, D.iata]] +
                            [[e["via"].iata, f"{i + 1}. {e['via'].iata}"] for i, e in enumerate(top5)])
        body += Page.globe(f"<b>Top {len(top5)}</b> intermediate cities between "
                           f"{html.escape(S.iata)} and {html.escape(D.iata)}",
                           "Click any row to show that connection on the globe (click again to go back to the top 5).")

        body += ("<h3>Top 5 intermediate cities (by # route pairs)</h3>"
                 + Page.table(["Rank", "Via", "Airport", "City", "Country", "# Route pairs", "Shortest total (mi)"],
                              [[i + 1, e["via"].iata, e["via"].name, e["via"].city, e["via"].country,
                                e["count"], f"{e['total']:,.0f}"] for i, e in enumerate(top5)],
                              keys=[e["via"].iata for e in top5], kind="airport",
                              infos=[f"{S.iata} → {e['via'].iata} → {D.iata}: {e['count']} route pairs, "
                                     f"{e['total']:,.0f} mi" for e in top5]))

        body += (f"<h3>All route pairs, shortest first ({len(pairs)})</h3>"
                 + Page.table(["#", "Total miles", "Via", "Via airport", "City", "Country",
                               f"Flight 1 ({S.iata}→X)", "Leg 1 mi", f"Flight 2 (X→{D.iata})", "Leg 2 mi",
                               "Extra vs straight line"],
                              [[i + 1, f"{p['total']:,.0f}", p["via"].iata, p["via"].name, p["via"].city,
                                p["via"].country, f"{p['airline1'].iata} {p['airline1'].name}", f"{p['leg1']:,.0f}",
                                f"{p['airline2'].iata} {p['airline2'].name}", f"{p['leg2']:,.0f}",
                                f"+{p['total'] - direct_mi:,.0f}"] for i, p in enumerate(pairs)],
                              keys=[p["via"].iata for p in pairs], kind="airport",
                              infos=[f"{S.iata} → {p['via'].iata} ({p['airline1'].iata}) → {D.iata} "
                                     f"({p['airline2'].iata}): {p['total']:,.0f} mi" for p in pairs]))
        return Page.render("One Hop", body, globe)

    def about(self, _):
        photo = find_photo()
        pic = ("<img class='avatar' src='/photo' alt='Maryam Mahmoudi'>" if photo
               else "<div class='avatar initials'>MM</div>")
        body = ("<div class='about'>" + pic + "<div class='bio'>"
                "<h2>Maryam Mahmoudi</h2>"
                "<p class='role'>IT Professional &middot; San Jose, CA</p>"
                "<p>IT professional with 25+ years of experience in systems architecture, networking, "
                "and IT leadership. She holds an M.Sc. in Computer Engineering, MCSE and Google IT "
                "certifications, and is currently a student at De Anza College.</p>"
                f"<a class='btn-li' href='{LINKEDIN_URL}' target='_blank' rel='noopener'>LinkedIn</a>"
                "<div class='project'>"
                "<p><b>About this project:</b> Airline Route Access lets you explore airlines, airports, "
                "and routes, including one-stop trip planning on an interactive 3D globe.</p>"
                f"<p><b>Data:</b> <a href='https://openflights.org/data' target='_blank' rel='noopener'>OpenFlights</a> "
                f"({len(self.db.airlines_by_iata)} US airlines, {len(self.db.airports_by_iata)} airports, "
                f"{len(self.db.routes):,} routes).</p>"
                "<p><b>Built with:</b> Python and globe.gl, created through Vibe Coding with an AI advisor "
                "for CIS 51 at De Anza College.</p></div>"
                "</div></div>")
        return Page.render("About", body)

    def get_id(self, _):
        body = ("<h2>2.3 Site Owner</h2>"
                + Page.entity(["Name", "De Anza Student ID"], [STUDENT_NAME, STUDENT_ID]))
        return Page.render("Get ID", body)


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------
class RequestHandler(BaseHTTPRequestHandler):
    app = None  # set in main()

    def do_GET(self):
        url = urlparse(self.path)
        path = url.path.rstrip("/") or "/"
        if path == "/photo":
            return self.send_photo()
        status, page = self.app.handle(path, parse_qs(url.query))
        data = page.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)


    def send_photo(self):
        photo = find_photo()
        if not photo:
            self.send_error(404)
            return
        kind = {"png": "image/png", "webp": "image/webp"}.get(photo.rsplit(".", 1)[-1].lower(), "image/jpeg")
        with open(photo, "rb") as f:
            data = f.read()
        self.send_response(200)
        self.send_header("Content-Type", kind)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)


def main():
    db = AviationDatabase(DATA_DIR)
    RequestHandler.app = AviationWebApp(db)
    server = ThreadingHTTPServer(("0.0.0.0", PORT), RequestHandler)
    print(f"Loaded {len(db.airlines_by_iata)} airlines, {len(db.airports_by_iata)} airports, "
          f"{len(db.routes)} routes")
    print(f"Open http://localhost:{PORT} in your browser (Ctrl+C to stop)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
