"""
Airline Route Access - Air Travel Database web application
CIS 51 Vibe Coding Assignment (De Anza College)

Run:  python app.py      then open  http://localhost:8080
Uses only the Python standard library (no installs needed).
"""

import ast
import copy
import csv
import html
import json
import math
import os
import secrets
import threading
import time
from collections import Counter
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, urlencode

# ---------------------------------------------------------------------------
# Site owner (Report 2.3) - edit student_info.py, not this file
# ---------------------------------------------------------------------------
try:
    from student_info import STUDENT_NAME, STUDENT_ID
except ImportError:
    STUDENT_NAME = "YOUR NAME HERE"
    STUDENT_ID = "YOUR DE ANZA STUDENT ID HERE"
try:  # optional, shown on the Contact page only if filled in
    from student_info import CONTACT_EMAIL
except ImportError:
    CONTACT_EMAIL = ""

LINKEDIN_URL = "https://www.linkedin.com/in/maryam-mahmoudi-ab5422304"
try:  # optional: link to the code on GitHub in the footer ("" hides it)
    from student_info import GITHUB_URL
except ImportError:
    GITHUB_URL = "https://github.com/mmahmoudi16-ops/airline-route-access"
APP_DIR = os.path.dirname(os.path.abspath(__file__))


def find_image(base):
    """Path of base.jpg / .jpeg / .png / .webp placed next to app.py, or None."""
    for ext in ("jpg", "jpeg", "png", "webp"):
        path = os.path.join(APP_DIR, f"{base}.{ext}")
        if os.path.isfile(path):
            return path
    return None


def find_photo():
    """The owner's photo for the About page (photo.jpg)."""
    return find_image("photo")


def find_hero():
    """Optional real photo for the home-page banner (hero.jpg); the drawn illustration is used if absent."""
    return find_image("hero")


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
    """One airline from SB-airlines.txt (users identify it by its IATA code)."""
    FIELDS = ["OpenFlights ID", "Name", "Alias", "IATA", "ICAO",
              "Callsign", "Country", "Active"]

    def __init__(self, row):
        (self.id, self.name, self.alias, self.iata, self.icao,
         self.callsign, self.country, self.active) = [clean(v) for v in row]

    def values(self):
        return [self.id, self.name, self.alias, self.iata, self.icao,
                self.callsign, self.country, self.active]


class Airport:
    """One airport from SB-airports.txt, with GPS position and air-distance calculation."""
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
    """One directional route: an airline flying from a source airport to a destination airport."""
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
        self.edits = []  # human-readable log of session-only changes

    @staticmethod
    def _read(data_dir, name):
        with open(os.path.join(data_dir, name), encoding="utf-8", newline="") as f:
            return [row for row in csv.reader(f) if row]

    # 1.1 / 1.2
    def get_airline(self, iata):
        return self.airlines_by_iata.get(iata.strip().upper())

    def get_airport(self, iata):
        return self.airports_by_iata.get(iata.strip().upper())

    # ---- Smart search: find airports / airlines from a city, name, country or code ----
    @staticmethod
    def _norm(s):
        import unicodedata
        s = unicodedata.normalize("NFD", s or "")
        return "".join(c for c in s if unicodedata.category(c) != "Mn").lower().strip()

    def search_airports(self, q, limit=8):
        q = self._norm(q)
        if not q:
            return []
        scored = []
        for a in self.airports_by_iata.values():
            iata, city, name, country = (self._norm(x) for x in (a.iata, a.city, a.name, a.country))
            if iata == q:
                s = 0
            elif city == q:
                s = 1
            elif city.startswith(q):
                s = 2
            elif iata.startswith(q) or self._norm(a.icao) == q:
                s = 3
            elif any(w.startswith(q) for w in name.split()) or name.startswith(q):
                s = 4
            elif country.startswith(q):
                s = 6
            elif q in city or q in name:
                s = 5
            else:
                continue
            scored.append((s, a.city, a.iata, a))
        scored.sort(key=lambda x: x[:3])
        return [x[3] for x in scored[:limit]]

    def search_airlines(self, q, limit=8):
        q = self._norm(q)
        if not q:
            return []
        scored = []
        for a in self.airlines_by_iata.values():
            iata, name, alias, country, cs = (self._norm(x) for x in (a.iata, a.name, a.alias, a.country, a.callsign))
            if iata == q or self._norm(a.icao) == q:
                s = 0
            elif name.startswith(q) or cs.startswith(q) or (alias and alias.startswith(q)):
                s = 1
            elif any(w.startswith(q) for w in name.split()):
                s = 2
            elif q in name:
                s = 3
            elif country.startswith(q):
                s = 4
            else:
                continue
            scored.append((s, a.iata, a))
        scored.sort(key=lambda x: x[:2])
        return [x[2] for x in scored[:limit]]

    def resolve_airport(self, q):
        """(airport, suggestions): exact IATA code first, else a single clear match by city/name."""
        a = self.get_airport(q)
        if a:
            return a, []
        found = self.search_airports(q)
        exact_city = [x for x in found if self._norm(x.city) == self._norm(q)]
        if len(found) == 1:
            return found[0], []
        if len(exact_city) == 1:
            return exact_city[0], []
        return None, found

    def resolve_airline(self, q):
        a = self.get_airline(q)
        if a:
            return a, []
        found = self.search_airlines(q)
        by_name = [x for x in found if self._norm(q) in self._norm(x.name)]
        if len(found) == 1:
            return found[0], []
        if len(by_name) == 1:
            return by_name[0], []
        return None, found

    def lookup_data(self):
        """Compact lists used by the search boxes' suggestions."""
        return {"airports": [[a.iata, a.name, a.city, a.country] for a in self.all_airports()],
                "airlines": [[a.iata, a.name, a.country] for a in self.all_airlines()]}

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

    def destinations(self, airport):
        """Every airport connected to this one, with # routes, airlines, direction and air miles."""
        info = {}
        for r in self.routes:
            if airport.id not in (r.source_id, r.dest_id):
                continue
            other_id = r.dest_id if r.source_id == airport.id else r.source_id
            other, al = self.airports_by_id.get(other_id), self.airlines_by_id.get(r.airline_id)
            if not other or not al or other is airport:
                continue
            d = info.setdefault(other_id, {"airport": other, "count": 0, "airlines": set(), "dirs": set()})
            d["count"] += 1
            d["airlines"].add(al.iata)
            d["dirs"].add("out" if r.source_id == airport.id else "in")
        rows = []
        for d in info.values():
            d["airlines"] = sorted(d["airlines"])
            d["direction"] = {frozenset({"out", "in"}): "Both ways", frozenset({"out"}): "Departing only",
                              frozenset({"in"}): "Arriving only"}[frozenset(d["dirs"])]
            d["miles"] = airport.miles_to(d["airport"])
            rows.append(d)
        return sorted(rows, key=lambda d: (-d["count"], d["airport"].iata))

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

    # ---- Session-only editing (applied to a per-browser copy of the database) ----
    AIRLINE_EDITABLE = ["name", "alias", "icao", "callsign", "country", "active"]
    AIRPORT_EDITABLE = ["name", "city", "country", "icao", "latitude", "longitude", "altitude",
                        "utc_offset", "dst", "timezone", "type", "source"]

    def update_airline(self, iata, form):
        a = self.get_airline(iata)
        if not a:
            raise ValueError(f"No airline with IATA code '{iata}'.")
        changed = [f for f in self.AIRLINE_EDITABLE if f in form and form[f].strip() != getattr(a, f)]
        for f in changed:
            setattr(a, f, form[f].strip())
        if changed:
            self.edits.append(f"Edited airline {a.iata}: {', '.join(changed)}")
        return changed

    def update_airport(self, iata, form):
        a = self.get_airport(iata)
        if not a:
            raise ValueError(f"No airport with IATA code '{iata}'.")
        try:
            lat = float(form.get("latitude", a.latitude))
            lng = float(form.get("longitude", a.longitude))
        except ValueError:
            raise ValueError("Latitude and longitude must be numbers.")
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            raise ValueError("Latitude must be -90..90 and longitude -180..180.")
        changed = [f for f in self.AIRPORT_EDITABLE if f in form and form[f].strip() != getattr(a, f)]
        for f in changed:
            setattr(a, f, form[f].strip())
        a.lat, a.lng = lat, lng
        if changed:
            self.edits.append(f"Edited airport {a.iata}: {', '.join(changed)}")
        return changed

    def add_route(self, airline_iata, src_iata, dst_iata, stops="0", equipment=""):
        al, s, d = self.get_airline(airline_iata), self.get_airport(src_iata), self.get_airport(dst_iata)
        if not al:
            raise ValueError(f"No airline with IATA code '{airline_iata}'.")
        if not s or not d:
            raise ValueError(f"Unknown airport '{src_iata if not s else dst_iata}'.")
        if s is d:
            raise ValueError("Source and destination must be different airports.")
        if not str(stops).strip().isdigit():
            raise ValueError("Stops must be a whole number (0 for non-stop).")
        self.routes.append(Route([al.iata, al.id, s.iata, s.id, d.iata, d.id, "", str(stops).strip(),
                                  equipment.strip()]))
        self.edits.append(f"Added route {al.iata} {s.iata} → {d.iata}")

    def delete_routes(self, airline_iata, src_iata, dst_iata):
        al, s, d = self.get_airline(airline_iata), self.get_airport(src_iata), self.get_airport(dst_iata)
        if not (al and s and d):
            raise ValueError("Please enter a valid airline and two valid airport codes.")
        before = len(self.routes)
        self.routes = [r for r in self.routes
                       if not (r.airline_id == al.id and r.source_id == s.id and r.dest_id == d.id)]
        removed = before - len(self.routes)
        if not removed:
            raise ValueError(f"No {al.iata} route from {s.iata} to {d.iata} exists.")
        self.edits.append(f"Deleted route {al.iata} {s.iata} → {d.iata}")
        return removed

    # ---- Statistics for the Charts page ----
    def stats(self, airline=None):
        """Numbers for the Charts page; with an airline, only that airline's routes are counted."""
        routes = [r for r in self.routes if airline is None or r.airline_id == airline.id]
        dist = {}
        per_airport = Counter()
        for r in routes:
            s, d = self.airports_by_id.get(r.source_id), self.airports_by_id.get(r.dest_id)
            if s and d:
                dist[(r.source_id, r.dest_id)] = (s, d, s.miles_to(d))
                per_airport[r.source_id] += 1
                per_airport[r.dest_id] += 1
        miles = [v[2] for v in dist.values()]
        longest = max(dist.values(), key=lambda v: v[2]) if dist else None
        per_airline = Counter(r.airline_id for r in self.routes)
        split = {}
        for r in self.routes:  # domestic vs international, always for every airline
            s, d = self.airports_by_id.get(r.source_id), self.airports_by_id.get(r.dest_id)
            if s and d and r.airline_id in self.airlines_by_id:
                dom, intl = split.get(r.airline_id, (0, 0))
                split[r.airline_id] = (dom + 1, intl) if s.country == d.country else (dom, intl + 1)
        buckets = [("under 500", 0, 500), ("500–1k", 500, 1000), ("1k–2k", 1000, 2000),
                   ("2k–3k", 2000, 3000), ("3k–5k", 3000, 5000), ("5k+", 5000, 1e9)]
        served = [self.airports_by_id[k] for k in per_airport if k in self.airports_by_id]
        pairs, foreign = {}, Counter()
        for r in routes:
            s, d = self.airports_by_id.get(r.source_id), self.airports_by_id.get(r.dest_id)
            al = self.airlines_by_id.get(r.airline_id)
            if not (s and d and al):
                continue
            a_, b_ = sorted((s, d), key=lambda x: x.iata)
            entry = pairs.setdefault((a_.iata, b_.iata), [a_, b_, s.miles_to(d), set()])
            entry[3].add(al.iata)
            if d.country != al.country:
                foreign[d.country] += 1
        return {
            "n_routes": len(routes),
            "n_airports": len(served),
            "n_countries": len({a.country for a in served}),
            "routes_per_airline": sorted(((self.airlines_by_id[k], n) for k, n in per_airline.items()
                                          if k in self.airlines_by_id), key=lambda x: -x[1]),
            "domestic_split": sorted(((self.airlines_by_id[k], dom, intl) for k, (dom, intl) in split.items()),
                                     key=lambda x: -(x[1] + x[2])),
            "busiest_airports": [(self.airports_by_id[k], n) for k, n in per_airport.most_common(15)
                                 if k in self.airports_by_id],
            "airport_counts": [(self.airports_by_id[k], n) for k, n in per_airport.items() if k in self.airports_by_id],
            "length_buckets": [(lbl, sum(1 for m in miles if lo <= m < hi)) for lbl, lo, hi in buckets],
            "longest": longest,
            "longest_routes": sorted(pairs.values(), key=lambda v: -v[2])[:10],
            "foreign_countries": foreign.most_common(10),
            "avg_miles": sum(miles) / len(miles) if miles else 0,
        }

    # 2.2a / 2.2b
    def all_airlines(self):
        return sorted(self.airlines_by_iata.values(), key=lambda a: a.iata)

    def all_airports(self):
        return sorted(self.airports_by_iata.values(), key=lambda a: a.iata)


class _Leg:
    """A lightweight route-like object so one-hop legs can be drawn on the globe."""
    def __init__(self, a, b, airline):
        self.source_id, self.dest_id, self.airline_id, self.stops = a.id, b.id, airline.id, 0


class SessionStore:
    """
    Per-browser copies of the database for session-only edits.
    A visitor gets a private copy only when they first edit something; the cookie has
    no expiry, so it disappears when the browser is closed. Other visitors never see it.
    """
    MAX_SESSIONS = 30
    IDLE_SECONDS = 2 * 60 * 60

    def __init__(self, base_db):
        self.base = base_db
        self.sessions = {}  # sid -> [db, last_used]
        self.lock = threading.Lock()

    def _expire(self):
        now = time.time()
        for sid in [s for s, (_, t) in self.sessions.items() if now - t > self.IDLE_SECONDS]:
            del self.sessions[sid]
        while len(self.sessions) >= self.MAX_SESSIONS:
            oldest = min(self.sessions, key=lambda s: self.sessions[s][1])
            del self.sessions[oldest]

    def get(self, sid):
        with self.lock:
            entry = self.sessions.get(sid) if sid else None
            if entry:
                entry[1] = time.time()
                return entry[0]
            return None

    def create(self):
        with self.lock:
            self._expire()
            sid = secrets.token_urlsafe(16)
            db = copy.deepcopy(self.base)
            db.edits = []
            self.sessions[sid] = [db, time.time()]
            return sid, db

    def reset(self, sid):
        with self.lock:
            self.sessions.pop(sid, None)


class EditActions:
    """Applies one posted edit form to a session database. Returns (message, error, extra query)."""

    @staticmethod
    def run(db, action, form):
        code = lambda k: form.get(k, "").strip().upper()
        try:
            if action == "update_airline":
                changed = db.update_airline(code("iata"), form)
                return (f"Airline {code('iata')} saved." if changed else "No changes to save."), "", {"airline": code("iata")}
            if action == "update_airport":
                changed = db.update_airport(code("iata"), form)
                return (f"Airport {code('iata')} saved." if changed else "No changes to save."), "", {"airport": code("iata")}
            if action == "add_route":
                db.add_route(code("airline"), code("src"), code("dst"), form.get("stops", "0"), form.get("equipment", ""))
                return f"Route {code('airline')} {code('src')} → {code('dst')} added.", "", {}
            if action == "delete_route":
                n = db.delete_routes(code("airline"), code("src"), code("dst"))
                return f"Deleted {n} route{'s' if n != 1 else ''} {code('airline')} {code('src')} → {code('dst')}.", "", {}
            return "", "Unknown action.", {}
        except ValueError as e:
            return "", str(e), {}


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------
class Page:
    """Builds the HTML: page layout, styles, tables, forms, the globe and the search bar."""
    CSS = """
    body{font-family:system-ui,Segoe UI,Arial,sans-serif;margin:0;background:#f5f7fa;color:#1d2330;min-height:100vh;display:flex;flex-direction:column}
    body>main{flex:1;width:100%}
    .hint a,.suggest a{color:#2f6fa3;font-weight:600}
    main{padding:20px 24px;max-width:1400px;margin:0 auto;box-sizing:border-box}
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
    input.ac{width:min(320px,100%);text-transform:none;padding:9px 12px;border-radius:8px;box-sizing:border-box}
    input.ac:focus{outline:2px solid #2f6fa3;outline-offset:0;border-color:#2f6fa3}
    .ac-wrap{position:relative;display:inline-block;vertical-align:middle;max-width:100%}
    .ac-list{position:absolute;left:0;top:calc(100% + 4px);z-index:40;width:max(100%,380px);max-width:calc(100vw - 32px);background:#fff;border:1px solid #dde3ea;border-radius:10px;box-shadow:0 12px 28px rgba(15,30,60,.16);list-style:none;margin:0;padding:6px;display:none}
    .ac-list.show{display:block}
    .ac-list li{display:flex;gap:10px;align-items:baseline;padding:7px 9px;border-radius:7px;cursor:pointer;font-size:14px}
    .ac-list li b{font-family:ui-monospace,Consolas,monospace;color:#1f3a5f;min-width:34px}
    .ac-list li span{color:#1d2330}
    .ac-list li small{color:#5b6b7d;margin-left:auto;white-space:nowrap;padding-left:8px}
    .ac-list li.on,.ac-list li:hover{background:#e8f0f9}
    .lookup-form{display:flex;flex-wrap:wrap;gap:10px 14px;align-items:flex-end;margin:6px 0 10px}
    .lookup-form label{display:flex;flex-direction:column;gap:4px;font-size:13px;color:#4f6b8a;font-weight:600}
    .lookup-form button{padding:9px 18px;border-radius:8px}
    .examples{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:0 0 16px;font-size:13px;color:#5b6b7d}
    .examples a{background:#fff;border:1px solid #c9d5e3;color:#1f3a5f;text-decoration:none;border-radius:16px;padding:4px 12px;font-weight:500}
    .examples a:hover{border-color:#1f3a5f;background:#f1f5fa}
    .suggest{background:#fff;border:1px solid #f0d77a;background:#fffbea;border-radius:10px;padding:12px 14px;margin:6px 0 16px}
    .suggest p{margin:0 0 8px;color:#6b5300}
    .suggest .examples{margin:0}
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
    header.topbar{background:#1f3a5f;position:sticky;top:0;z-index:60;box-shadow:0 2px 8px rgba(10,25,50,.25)}
    .topbar-in{display:flex;align-items:stretch;gap:20px;padding:0 max(24px, calc((100% - 1352px) / 2))}
    .brand{display:flex;align-items:center;gap:9px;color:#fff;font-weight:700;font-size:18px;text-decoration:none;white-space:nowrap;padding:12px 0}
    .brand svg{width:24px;height:24px;color:#ffd166}
    .page-head{display:flex;gap:14px;align-items:center;margin:4px 0 14px}
    .page-head .ic{flex:none;width:46px;height:46px;border-radius:12px;background:#1f3a5f;color:#fff;display:flex;align-items:center;justify-content:center}
    .page-head .ic svg{width:24px;height:24px}
    .page-head h1{margin:0;font-size:24px;line-height:1.2}
    .page-head h1 em{font-style:normal;font-size:12px;font-weight:600;color:#4f6b8a;background:#e8edf3;border-radius:5px;padding:2px 7px;margin-left:8px;vertical-align:4px}
    .page-head p{margin:3px 0 0;color:#5b6b7d;font-size:14px}
    footer.site-foot{background:#14284a;color:#cfd8e3;margin-top:36px}
    .foot-in{max-width:1352px;margin:0 auto;padding:26px 24px;display:grid;grid-template-columns:2fr 1fr 1fr;gap:24px;font-size:14px;line-height:1.6;box-sizing:border-box}
    .foot-in h4{margin:0 0 8px;color:#fff;font-size:14px}
    .foot-in a{color:#cfe3ff;text-decoration:none}
    .foot-in a:hover{text-decoration:underline}
    .foot-in .brand{padding:0 0 6px}
    .foot-bottom{border-top:1px solid rgba(255,255,255,.1);text-align:center;font-size:12.5px;padding:10px 24px;color:#9fb0c6}
    @media(max-width:700px){.foot-in{grid-template-columns:1fr}}
    .info-card{background:#fff;border:1px solid #dde3ea;border-radius:14px;padding:18px 20px;margin:4px 0 18px;box-shadow:0 2px 8px rgba(15,30,60,.05)}
    .ic-head{display:flex;gap:16px;align-items:center;margin-bottom:14px;flex-wrap:wrap}
    .code-badge{font:700 30px ui-monospace,Consolas,monospace;letter-spacing:1px;color:#fff;background:linear-gradient(135deg,#1f3a5f,#2f6fa3);border-radius:12px;padding:10px 16px;line-height:1}
    .ic-head h2{margin:0;font-size:22px}
    .ic-head p{margin:4px 0 0;color:#4f6b8a;font-size:14px}
    .pill{display:inline-block;font-size:12px;font-weight:600;border-radius:12px;padding:2px 9px;margin-left:6px;vertical-align:2px}
    .pill.on{background:#e6f4ea;color:#1e5b2c}
    .pill.off{background:#eef1f5;color:#5b6b7d}
    .localtime{font-weight:600;color:#1d2330}
    .facts{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:10px}
    .fact{background:#f6f8fb;border:1px solid #e6ebf2;border-radius:10px;padding:9px 12px}
    .fact .k{display:block;font-size:11.5px;text-transform:uppercase;letter-spacing:.4px;color:#5b6b7d;font-weight:600}
    .fact .v{display:block;font-size:15px;font-weight:600;color:#1d2330;margin-top:2px;word-break:break-word}
    .fact .v small{font-weight:500;color:#5b6b7d}
    .fact.stat{background:#e8f0f9;border-color:#d3e1f1}
    .fact.stat .v{font-size:20px;color:#1f3a5f}
    details.raw{margin-top:12px}
    details.raw summary{cursor:pointer;color:#1f3a5f;font-weight:600;font-size:14px;padding:4px 0}
    .trips{display:grid;grid-template-columns:repeat(auto-fit,minmax(330px,1fr));gap:12px;margin:0 0 16px}
    button.trip{display:block;text-align:left;width:100%;background:#fff;color:#1d2330;border:1px solid #dde3ea;border-radius:14px;padding:14px 16px;cursor:pointer;font:inherit;position:relative;overflow:hidden;box-shadow:0 2px 8px rgba(15,30,60,.05)}
    button.trip:hover{border-color:#9fb6d0}
    button.trip.sel{border-color:#1f3a5f;box-shadow:0 0 0 2px #1f3a5f inset}
    .trip-top{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px}
    .trip-rank{font-size:12px;font-weight:700;text-transform:uppercase;letter-spacing:.5px;color:#fff;background:#2f6fa3;border-radius:6px;padding:3px 8px}
    .trip-rank.best{background:#1e7a46}
    .trip-total{font-size:20px;font-weight:700;color:#1f3a5f}
    .trip-total small{display:block;font-size:12px;font-weight:500;color:#5b6b7d;text-align:right}
    .trip-path{display:flex;align-items:center;gap:6px}
    .trip-path .stop{text-align:center;min-width:54px}
    .trip-path .stop b{display:block;font:700 18px ui-monospace,Consolas,monospace;color:#1d2330}
    .trip-path .stop small{display:block;font-size:11.5px;color:#5b6b7d;max-width:90px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
    .trip-path .stop.mid b{color:#2f6fa3}
    .trip-path .leg{flex:1;text-align:center;font-size:11.5px;color:#5b6b7d}
    .trip-path .leg .line{display:block;height:2px;margin:4px 0;background:repeating-linear-gradient(90deg,#9fb6d0 0 6px,transparent 6px 10px);position:relative}
    .trip-path .leg .line:after{content:"✈";position:absolute;right:-2px;top:-9px;font-size:13px;color:#1f3a5f}
    .trip-path .leg .al{font-weight:700;color:#1f3a5f}
    .gtag{position:relative;top:-22px;pointer-events:none;background:rgba(8,18,40,.82);color:#fff;border:1px solid #ffd166;border-radius:7px;padding:3px 8px;font:12px system-ui,Segoe UI,Arial,sans-serif;white-space:nowrap;text-align:center;box-shadow:0 2px 6px rgba(0,0,0,.4)}
    .gtag b{display:block;font:700 13px ui-monospace,Consolas,monospace;letter-spacing:.5px}
    .gtag span{display:block;font-size:11px;opacity:.85}
    .gtag.mark{border-color:#ef476f}
    .globe-loading{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:12px;color:#cfd8e3;font-size:14px;z-index:1;pointer-events:none}
    .spin{width:34px;height:34px;border-radius:50%;border:3px solid rgba(255,255,255,.2);border-top-color:#ffd166;animation:spin 1s linear infinite}
    @keyframes spin{to{transform:rotate(360deg)}}
    @media(max-width:640px){
      table.rt thead{display:none}
      table.rt,table.rt tbody,table.rt tr{display:block;width:100%}
      table.rt tr{border-bottom:1px solid #dde3ea;padding:6px 0}
      table.rt td{display:flex;justify-content:space-between;gap:12px;white-space:normal;border:0;padding:3px 12px;text-align:right}
      table.rt td::before{content:attr(data-label);font-weight:600;color:#5b6b7d;text-align:left;flex:none;max-width:45%}
      .scroll{max-height:none}
      .page-head h1{font-size:20px}
      .trip-path .stop small{max-width:64px}
    }
    .hero{position:relative;border-radius:10px;overflow:hidden;margin-bottom:18px;line-height:0;box-shadow:0 2px 10px rgba(0,0,0,.12)}
    .hero svg{width:100%;height:auto;display:block}
    .hero-photo{position:relative;aspect-ratio:1200/462;overflow:hidden;background:#0b3d6e}
    .hero-photo img{width:100%;height:100%;object-fit:cover;object-position:center 20%;transform-origin:center 25%;display:block;animation:heroZoom 24s ease-in-out infinite alternate}
    .hero-photo::after{content:"";position:absolute;inset:0;background:linear-gradient(0deg,rgba(5,20,40,.78) 0%,rgba(5,20,40,.35) 28%,rgba(5,20,40,0) 50%)}
    .hero.has-photo .hero-text{top:auto;bottom:clamp(12px,3vw,30px)}
    @keyframes heroZoom{from{transform:scale(1)}to{transform:scale(1.08)}}
    @media(prefers-reduced-motion:reduce){.hero-photo img{animation:none}}
    @media(max-width:600px){.hero-photo{aspect-ratio:16/8}}
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
    nav.mainnav{display:flex;flex:1;min-width:0}
    .nav-list{list-style:none;margin:0;padding:0;display:flex;align-items:stretch;gap:2px;flex:1}
    .nav-item{position:relative;display:flex}
    .nav-item.right{margin-left:auto}
    .nav-top,button.nav-top{display:flex;align-items:center;gap:7px;padding:13px 12px;font:500 14.5px system-ui,Segoe UI,Arial,sans-serif;color:rgba(255,255,255,.88);background:none;border:0;border-radius:0;cursor:pointer;text-decoration:none;white-space:nowrap;box-sizing:border-box}
    .nav-top svg{width:19px;height:19px;flex:none}
    .nav-top .chev{width:14px;height:14px;opacity:.6;transition:transform .2s}
    .nav-top:hover,.has-sub:hover>.nav-top,.has-sub.open>.nav-top{background:rgba(255,255,255,.1);color:#fff}
    .nav-item.active>.nav-top{color:#fff;box-shadow:inset 0 -3px 0 #ffd166}
    .sub{position:absolute;top:100%;left:0;min-width:320px;margin-top:0;background:#fff;border:1px solid #dde3ea;border-radius:12px;box-shadow:0 14px 32px rgba(15,30,60,.18);padding:8px;display:none}
    .nav-item.right .sub{left:auto;right:0}
    .has-sub:hover>.sub,.has-sub:focus-within>.sub,.has-sub.open>.sub{display:block}
    .has-sub:hover .chev,.has-sub.open .chev{transform:rotate(180deg)}
    .sub-link{display:flex;gap:12px;align-items:center;padding:9px 10px;border-radius:9px;text-decoration:none;color:#1d2330}
    .sub-link:hover,.sub-link:focus{background:#f1f5fa;outline:none}
    .sub-link.active{background:#e8f0f9}
    .sub-link .ic{flex:none;width:38px;height:38px;border-radius:10px;background:#e8f0f9;color:#1f3a5f;display:flex;align-items:center;justify-content:center}
    .sub-link:hover .ic,.sub-link.active .ic{background:#1f3a5f;color:#fff}
    .sub-link .ic svg{width:20px;height:20px}
    .sub-link b{display:block;font-size:14px;font-weight:600}
    .sub-link em{font-style:normal;font-size:11px;font-weight:600;color:#4f6b8a;background:#eef1f5;border-radius:4px;padding:1px 6px;margin-left:7px;vertical-align:1px}
    .sub-link small{display:block;color:#5b6b7d;font-size:12.5px;margin-top:2px}
    .nav-toggle,button.nav-toggle{display:none;align-items:center;gap:8px;background:none;color:#fff;border:0;padding:12px 0;margin-left:auto;font:600 15px system-ui,Segoe UI,Arial,sans-serif;cursor:pointer}
    .nav-toggle svg{width:22px;height:22px}
    @media(max-width:1080px){
      .nav-toggle,button.nav-toggle{display:flex}
      nav.mainnav{position:static;justify-content:flex-end}
      .nav-list{display:none;flex-direction:column;position:absolute;top:100%;left:0;right:0;background:#fff;padding:8px 20px 14px;box-shadow:0 14px 28px rgba(10,25,50,.25);max-height:calc(100vh - 60px);overflow:auto}
      nav.mainnav.open .nav-list{display:flex}
      .nav-top,button.nav-top{color:#1f3a5f}
      .nav-top:hover,.has-sub:hover>.nav-top{background:#f1f5fa;color:#1f3a5f}
      .nav-item.active>.nav-top{color:#0b5cad}
      .nav-item.right{margin-left:0}
      .nav-item{display:block}
      .nav-top,button.nav-top{padding:10px 4px;width:100%}
      .nav-top .chev{display:none}
      .nav-item.active>.nav-top{box-shadow:none}
      .sub,.has-sub:hover>.sub{position:static;display:block;box-shadow:none;border:0;padding:0 0 4px 22px;min-width:0}
      .sub-link{padding:6px 8px}
      .sub-link small{display:none}
      .sub-link .ic{width:30px;height:30px;border-radius:8px}
      .sub-link .ic svg{width:17px;height:17px}
    }
    .home-group{margin:0 0 18px}
    .home-group h2{display:flex;align-items:center;gap:9px;font-size:17px;margin:0 0 10px;color:#1f3a5f}
    .home-group h2 svg{width:21px;height:21px}
    .home-cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:12px}
    .home-card{background:#fff;border:1px solid #dde3ea;border-radius:12px;padding:12px 14px;transition:box-shadow .15s,border-color .15s,transform .15s}
    .home-card:hover{border-color:#9fb6d0;box-shadow:0 6px 18px rgba(15,30,60,.10);transform:translateY(-1px)}    .panel{background:#fff;border:1px solid #dde3ea;border-radius:8px;padding:16px 18px;margin:0 0 16px}
    .panel h3{margin:0 0 10px}
    .grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(420px,1fr));gap:16px;align-items:start}
    .fields{display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:8px 14px;margin:8px 0 12px}
    .fields label{display:flex;flex-direction:column;font-size:13px;color:#4f6b8a;gap:3px}
    .fields input{padding:6px 8px;font-size:14px;border:1px solid #b8c2cf;border-radius:4px;text-transform:none;width:auto}
    .fields input[readonly]{background:#eef1f5;color:#666}
    .ok{background:#e6f4ea;border:1px solid #9cd3a8;color:#1e5b2c;padding:8px 12px;border-radius:6px}
    .err-box{background:#fde8ec;border:1px solid #f3a6b4;color:#8a1c2c;padding:8px 12px;border-radius:6px}
    .danger{background:#b3261e}
    .changes li{margin:3px 0}
    .tiles{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:12px;margin:0 0 16px}
    .tile{background:#fff;border:1px solid #dde3ea;border-radius:8px;padding:14px 16px}
    .tile .v{font-size:28px;font-weight:700;color:#1d2330;line-height:1.1}
    .tile .l{font-size:13px;color:#5b6b7d;margin-top:4px}
    .chart{background:#fff;border:1px solid #dde3ea;border-radius:8px;padding:16px 18px}
    .chart h3{margin:0 0 2px;font-size:16px}
    .chart .csub{margin:0 0 12px;color:#5b6b7d;font-size:13px}
    .bar-row{display:grid;grid-template-columns:150px 1fr;align-items:center;gap:10px;padding:3px 0;font-size:13px}
    .bar-row .lbl{color:#1d2330;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .bar-track{position:relative;height:18px}
    .bar{height:100%;background:#2f6fa3;border-radius:0 4px 4px 0;min-width:2px;position:relative}
    .bar-row:hover .bar{background:#1f3a5f}
    .bar-row.dim{opacity:.32}
    .cgrid{grid-template-columns:repeat(auto-fit,minmax(min(100%,520px),1fr))}
    .bar-track.stack{display:flex;align-items:center;gap:2px}
    .seg{display:block;height:18px;min-width:2px}
    .seg.dom{background:#2f6fa3;border-radius:0}
    .seg.intl{background:#e08a2e;border-radius:0 4px 4px 0}
    .seg-val{margin-left:6px;font-size:12px;color:#1d2330;white-space:nowrap}
    .legend{display:flex;gap:16px;font-size:12.5px;color:#4f6b8a;margin:-4px 0 10px}
    .legend .sw{display:inline-block;width:11px;height:11px;border-radius:3px;margin-right:6px;vertical-align:-1px}
    .sw.dom{background:#2f6fa3}.sw.intl{background:#e08a2e}
    .cols{display:flex;align-items:stretch;gap:10px;height:230px;padding:4px 4px 0}
    .col{flex:1;display:flex;flex-direction:column;align-items:center;justify-content:flex-end;min-width:0}
    .cbar{width:100%;max-width:64px;background:#2f6fa3;border-radius:4px 4px 0 0;transition:background .15s}
    .col:hover .cbar{background:#1f3a5f}
    .cval{font-size:12px;font-weight:600;color:#1d2330;margin-bottom:4px}
    .clbl{font-size:11.5px;color:#5b6b7d;margin-top:6px;text-align:center;white-space:nowrap}
    .filter-row{margin:0 0 6px}
    a.fchip{background:#fff;border:1px solid #c9d5e3;color:#1f3a5f;text-decoration:none;border-radius:16px;padding:5px 12px;font-size:13px}
    a.fchip:hover{border-color:#1f3a5f}
    a.fchip.on{background:#1f3a5f;color:#fff;border-color:#1f3a5f}
    h3.who{margin:10px 0 10px;color:#1f3a5f}
    .bar-val{position:absolute;top:0;line-height:18px;font-size:12px;color:#1d2330;margin-left:6px;white-space:nowrap}
    .bar-row .tip{display:none;position:absolute;left:0;top:-30px;background:#1d2330;color:#fff;padding:4px 8px;border-radius:4px;font-size:12px;white-space:nowrap;z-index:2}
    .bar-row:hover .tip{display:block}
    .contact-card{background:#fff;border:1px solid #dde3ea;border-radius:10px;padding:24px 28px;max-width:640px;line-height:1.7}
    .contact-card .row{display:flex;gap:10px;align-items:center;margin:8px 0}
    .btn-mail{display:inline-block;background:#1f3a5f;color:#fff;text-decoration:none;padding:8px 16px;border-radius:20px;font-weight:600}
    .class-list{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:12px;margin:0 0 16px;align-items:start}
    .cls{background:#fff;border:1px solid #dde3ea;border-radius:8px;padding:12px 14px}
    .cls h4{margin:0 0 4px;font-family:ui-monospace,Consolas,monospace;color:#1f3a5f}
    .cls p{margin:0 0 6px;color:#555;font-size:13px}
    .cls code{font-size:12px;background:#eef1f5;padding:1px 5px;border-radius:3px;display:inline-block;margin:2px 2px 0 0}
    details.src summary{cursor:pointer;font-weight:600;padding:8px 0}
    pre.code{margin:0;max-height:75vh;overflow:auto;border:1px solid #dde3ea;border-radius:8px;font-size:13px;line-height:1.45}
    pre.code code{padding:14px !important}
    @media(max-width:600px){.grid2{grid-template-columns:1fr}.bar-row{grid-template-columns:96px 1fr}}
    .banner{background:#fff3c4;border-bottom:1px solid #f0d77a;padding:8px max(24px, calc((100% - 1352px) / 2));font-size:14px}
    .banner a{color:#1f3a5f;font-weight:600}
    tr.pick{cursor:pointer}
    tr.pick.sel td{background:#fff3c4 !important}
    .chips{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:0 0 10px}
    .chips .lbl{font-size:13px;color:#5b6b7d;margin-right:2px}
    button.chip.pick{cursor:pointer;background:#fff;color:#1f3a5f;border:1px solid #b8c2cf;border-radius:16px;padding:5px 12px;font-size:13px}
    button.chip.pick:hover{border-color:#1f3a5f}
    button.chip.pick.sel{background:#1f3a5f;color:#fff;border-color:#1f3a5f}
    """

    # Home page illustration: an airliner climbing away from an airport at sunset (drawn as animated SVG)
    HERO_SVG = """
<svg viewBox="0 0 1200 440" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="Airliner climbing away from an airport at sunset">
<defs>
  <linearGradient id="hSky" x1="0" y1="0" x2="0" y2="1">
    <stop offset="0" stop-color="#101d45"/><stop offset=".32" stop-color="#2e3f7c"/>
    <stop offset=".58" stop-color="#8a5a8e"/><stop offset=".76" stop-color="#e3876f"/>
    <stop offset=".88" stop-color="#f7b56b"/><stop offset="1" stop-color="#ffd89a"/>
  </linearGradient>
  <radialGradient id="hSun" cx="0" cy="0" r="1" gradientUnits="userSpaceOnUse" gradientTransform="translate(670 250) scale(300 190)">
    <stop offset="0" stop-color="#fff4d2"/><stop offset=".12" stop-color="#ffe2a0" stop-opacity=".95"/>
    <stop offset=".45" stop-color="#ffb06a" stop-opacity=".45"/><stop offset="1" stop-color="#ff9a5c" stop-opacity="0"/>
  </radialGradient>
  <linearGradient id="hMtnFar" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#9a7aa6"/><stop offset="1" stop-color="#c48f98"/></linearGradient>
  <linearGradient id="hMtnMid" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#5d4f86"/><stop offset="1" stop-color="#7b6191"/></linearGradient>
  <linearGradient id="hGround" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#2a3352"/><stop offset="1" stop-color="#121a30"/></linearGradient>
  <linearGradient id="hRunway" x1="0" y1="1" x2="1" y2="0"><stop offset="0" stop-color="#2b2f3d"/><stop offset="1" stop-color="#4a4a5c"/></linearGradient>
  <linearGradient id="hBody" x1="0" y1="0" x2="0" y2="1">
    <stop offset="0" stop-color="#ffffff"/><stop offset=".55" stop-color="#eef1f6"/><stop offset="1" stop-color="#b9c2d3"/>
  </linearGradient>
  <linearGradient id="hBelly" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#1f3a5f"/><stop offset="1" stop-color="#14284a"/></linearGradient>
  <linearGradient id="hStripe" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#ef476f"/><stop offset="1" stop-color="#ffb35c"/></linearGradient>
  <linearGradient id="hTail" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#1f3a5f"/><stop offset="1" stop-color="#2f6fa3"/></linearGradient>
  <linearGradient id="hWing" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#dfe5ee"/><stop offset="1" stop-color="#9aa6b8"/></linearGradient>
  <linearGradient id="hEngine" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#f4f6fa"/><stop offset="1" stop-color="#8d98ab"/></linearGradient>
  <linearGradient id="hTrail" gradientUnits="userSpaceOnUse" x1="130" y1="420" x2="640" y2="214">
    <stop offset="0" stop-color="#fff" stop-opacity="0"/><stop offset=".55" stop-color="#fff" stop-opacity=".35"/><stop offset="1" stop-color="#fff" stop-opacity=".85"/>
  </linearGradient>
  <linearGradient id="hGlass" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#ffd58a"/><stop offset="1" stop-color="#f09a54"/></linearGradient>
  <linearGradient id="hCloud" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#ffe6c7"/><stop offset="1" stop-color="#e09a9a"/></linearGradient>
  <filter id="hBlur" x="-20%" y="-60%" width="140%" height="220%"><feGaussianBlur stdDeviation="2.4"/></filter>
  <filter id="hGlow" x="-200%" y="-200%" width="500%" height="500%"><feGaussianBlur stdDeviation="2"/></filter>
  <g id="hCl"><ellipse cx="0" cy="0" rx="70" ry="13"/><ellipse cx="-26" cy="-8" rx="34" ry="14"/><ellipse cx="18" cy="-12" rx="38" ry="17"/><ellipse cx="48" cy="-3" rx="26" ry="10"/></g>
</defs>
<rect width="1200" height="440" fill="url(#hSky)"/>
<g><circle cx="396" cy="22" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.7s" begin="-2.1s" repeatCount="indefinite"/></circle><circle cx="444" cy="12" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.6s" begin="-1.7s" repeatCount="indefinite"/></circle><circle cx="101" cy="15" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.6s" begin="-2.3s" repeatCount="indefinite"/></circle><circle cx="1119" cy="72" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.9s" begin="-1.6s" repeatCount="indefinite"/></circle><circle cx="1152" cy="11" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.2s" begin="-0.6s" repeatCount="indefinite"/></circle><circle cx="157" cy="38" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.8s" begin="-2.3s" repeatCount="indefinite"/></circle><circle cx="238" cy="16" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.9s" begin="-2.5s" repeatCount="indefinite"/></circle><circle cx="596" cy="61" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.7s" begin="-3.7s" repeatCount="indefinite"/></circle><circle cx="439" cy="32" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.2s" begin="-1.0s" repeatCount="indefinite"/></circle><circle cx="686" cy="61" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.3s" begin="-1.2s" repeatCount="indefinite"/></circle><circle cx="1157" cy="18" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.9s" begin="-1.4s" repeatCount="indefinite"/></circle><circle cx="1103" cy="50" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.4s" begin="-2.3s" repeatCount="indefinite"/></circle><circle cx="1036" cy="39" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.0s" begin="-2.3s" repeatCount="indefinite"/></circle><circle cx="549" cy="93" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.7s" begin="-2.7s" repeatCount="indefinite"/></circle><circle cx="90" cy="79" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.2s" begin="-1.5s" repeatCount="indefinite"/></circle><circle cx="796" cy="8" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.4s" begin="-2.4s" repeatCount="indefinite"/></circle><circle cx="593" cy="29" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.8s" begin="-1.0s" repeatCount="indefinite"/></circle><circle cx="474" cy="97" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.9s" begin="-1.6s" repeatCount="indefinite"/></circle><circle cx="342" cy="20" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.7s" begin="-1.1s" repeatCount="indefinite"/></circle><circle cx="502" cy="43" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.9s" begin="-0.6s" repeatCount="indefinite"/></circle><circle cx="224" cy="30" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.5s" begin="-3.3s" repeatCount="indefinite"/></circle><circle cx="232" cy="35" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.5s" begin="-1.5s" repeatCount="indefinite"/></circle><circle cx="677" cy="105" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.6s" begin="-3.5s" repeatCount="indefinite"/></circle><circle cx="1124" cy="77" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.5s" begin="-1.6s" repeatCount="indefinite"/></circle><circle cx="579" cy="48" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.7s" begin="-0.8s" repeatCount="indefinite"/></circle><circle cx="208" cy="41" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.8s" begin="-2.3s" repeatCount="indefinite"/></circle><circle cx="642" cy="105" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.7s" begin="-0.8s" repeatCount="indefinite"/></circle><circle cx="456" cy="72" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.0s" begin="-1.9s" repeatCount="indefinite"/></circle><circle cx="154" cy="57" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.7s" begin="-1.2s" repeatCount="indefinite"/></circle><circle cx="187" cy="84" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.7s" begin="-2.8s" repeatCount="indefinite"/></circle><circle cx="619" cy="27" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="2.9s" begin="-2.2s" repeatCount="indefinite"/></circle><circle cx="51" cy="61" r="0.6" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.2s" begin="-1.0s" repeatCount="indefinite"/></circle><circle cx="445" cy="23" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.8s" begin="-3.1s" repeatCount="indefinite"/></circle><circle cx="402" cy="29" r="0.8" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="4.5s" begin="-3.3s" repeatCount="indefinite"/></circle><circle cx="878" cy="30" r="1.2" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.4s" begin="-0.1s" repeatCount="indefinite"/></circle><circle cx="52" cy="35" r="1" fill="#fff" opacity=".7"><animate attributeName="opacity" values=".15;.85;.15" dur="3.0s" begin="-2.4s" repeatCount="indefinite"/></circle></g>
<rect width="1200" height="440" fill="url(#hSun)"><animate attributeName="opacity" values=".9;1;.9" dur="6s" repeatCount="indefinite"/></rect>
<use href="#hCl" fill="url(#hCloud)" opacity="0.55"><animateTransform attributeName="transform" type="translate" from="-200 150" to="1400 150" dur="140s" begin="-20s" repeatCount="indefinite" additive="sum"/><animateTransform attributeName="transform" type="scale" from="1.3" to="1.3" dur="1s" additive="sum" fill="freeze"/></use>
<use href="#hCl" fill="url(#hCloud)" opacity="0.5"><animateTransform attributeName="transform" type="translate" from="-200 205" to="1400 205" dur="110s" begin="-75s" repeatCount="indefinite" additive="sum"/><animateTransform attributeName="transform" type="scale" from="0.9" to="0.9" dur="1s" additive="sum" fill="freeze"/></use>
<use href="#hCl" fill="url(#hCloud)" opacity="0.4"><animateTransform attributeName="transform" type="translate" from="-200 120" to="1400 120" dur="170s" begin="-120s" repeatCount="indefinite" additive="sum"/><animateTransform attributeName="transform" type="scale" from="0.7" to="0.7" dur="1s" additive="sum" fill="freeze"/></use>
<use href="#hCl" fill="url(#hCloud)" opacity="0.45"><animateTransform attributeName="transform" type="translate" from="-200 245" to="1400 245" dur="95s" begin="-40s" repeatCount="indefinite" additive="sum"/><animateTransform attributeName="transform" type="scale" from="1.6" to="1.6" dur="1s" additive="sum" fill="freeze"/></use>
<circle cx="670" cy="250" r="30" fill="#fff1c9"/>
<path d="M0,300 L70,268 L130,284 L210,240 L280,272 L350,252 L430,280 L520,236 L600,266 L690,244 L770,276 L860,250 L940,282 L1020,248 L1110,276 L1200,256 L1200,330 L0,330 Z" fill="url(#hMtnFar)" opacity=".75"/>
<path d="M0,316 L90,290 L170,306 L260,276 L340,300 L420,284 L500,308 L590,282 L680,304 L760,290 L850,312 L960,292 L1060,310 L1200,294 L1200,340 L0,340 Z" fill="url(#hMtnMid)"/>
<g><rect x="40" y="292" width="29" height="50" fill="#2a2d55"/><rect x="51" y="304" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="58" y="304" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="51" y="318" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="58" y="325" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="72" y="270" width="31" height="72" fill="#2a2d55"/><rect x="83" y="275" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="90" y="282" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="97" y="282" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="90" y="289" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="97" y="296" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="90" y="303" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="97" y="310" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="76" y="317" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="83" y="317" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="83" y="324" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="109" y="286" width="22" height="56" fill="#2a2d55"/><rect x="113" y="291" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="120" y="291" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="120" y="305" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="120" y="333" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="133" y="308" width="25" height="34" fill="#2a2d55"/><rect x="137" y="313" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="163" y="305" width="34" height="37" fill="#2a2d55"/><rect x="188" y="310" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="174" y="317" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="181" y="317" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="167" y="324" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="174" y="324" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="181" y="324" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="174" y="331" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="201" y="291" width="22" height="51" fill="#2a2d55"/><rect x="205" y="296" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="212" y="310" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="205" y="331" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="212" y="331" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="228" y="275" width="32" height="67" fill="#2a2d55"/><rect x="232" y="280" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="246" y="280" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="253" y="280" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="239" y="287" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="246" y="287" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="253" y="287" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="239" y="308" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="246" y="308" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="253" y="308" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="246" y="315" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="253" y="315" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="232" y="329" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="239" y="329" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="246" y="329" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="264" y="309" width="19" height="33" fill="#2a2d55"/><rect x="268" y="314" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="275" y="321" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="275" y="328" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="285" y="319" width="18" height="23" fill="#2a2d55"/><rect x="289" y="331" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="296" y="331" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="305" y="268" width="39" height="74" fill="#2a2d55"/><rect x="309" y="280" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="330" y="287" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="337" y="287" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="316" y="294" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="323" y="294" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="316" y="301" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="330" y="301" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="337" y="301" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="309" y="308" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="337" y="308" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="309" y="315" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="316" y="315" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="323" y="315" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="337" y="315" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="316" y="322" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="323" y="322" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="330" y="322" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="337" y="322" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="309" y="329" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="330" y="329" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="350" y="272" width="30" height="70" fill="#2a2d55"/><rect x="368" y="277" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="354" y="284" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="361" y="291" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="361" y="298" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="368" y="305" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="375" y="305" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="361" y="312" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="375" y="319" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="354" y="333" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="383" y="272" width="41" height="70" fill="#2a2d55"/><rect x="387" y="277" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="415" y="277" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="387" y="284" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="408" y="284" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="408" y="291" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="415" y="291" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="394" y="298" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="408" y="298" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="415" y="298" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="394" y="305" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="401" y="305" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="415" y="305" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="387" y="312" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="408" y="312" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="394" y="319" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="401" y="319" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="408" y="319" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="415" y="319" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="408" y="326" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="387" y="333" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="429" y="313" width="28" height="29" fill="#2a2d55"/><rect x="440" y="318" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="433" y="325" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="433" y="332" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="440" y="332" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="463" y="297" width="20" height="45" fill="#2a2d55"/><rect x="474" y="309" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="474" y="316" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="467" y="323" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="467" y="330" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="488" y="269" width="18" height="73" fill="#2a2d55"/><rect x="492" y="288" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="499" y="288" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="492" y="302" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="492" y="316" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="492" y="323" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="509" y="290" width="27" height="52" fill="#2a2d55"/><rect x="527" y="295" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="513" y="302" width="3" height="3" fill="#ffd27a" opacity="0.95"/><rect x="513" y="309" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="513" y="316" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="520" y="316" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="513" y="323" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="513" y="330" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="541" y="287" width="41" height="55" fill="#2a2d55"/><rect x="545" y="292" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="559" y="292" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="573" y="299" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="566" y="306" width="3" height="3" fill="#ffd27a" opacity="0.55"/><rect x="573" y="306" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="573" y="313" width="3" height="3" fill="#ffd27a" opacity="0.75"/><rect x="552" y="327" width="3" height="3" fill="#ffd27a" opacity="0.55"/></g>
<rect y="336" width="1200" height="104" fill="url(#hGround)"/>
<g>
  <path d="M760,336 L760,304 Q880,284 1000,304 L1000,336 Z" fill="#33395e"/>
  <path d="M770,334 L770,309 Q880,292 990,309 L990,334 Z" fill="url(#hGlass)" opacity=".85"/>
<g stroke="#33395e" stroke-width="2"><line x1="790" y1="296" x2="790" y2="334"/><line x1="810" y1="296" x2="810" y2="334"/><line x1="830" y1="296" x2="830" y2="334"/><line x1="850" y1="296" x2="850" y2="334"/><line x1="870" y1="296" x2="870" y2="334"/><line x1="890" y1="296" x2="890" y2="334"/><line x1="910" y1="296" x2="910" y2="334"/><line x1="930" y1="296" x2="930" y2="334"/><line x1="950" y1="296" x2="950" y2="334"/><line x1="970" y1="296" x2="970" y2="334"/></g>
  <path d="M752,306 Q880,280 1008,306" fill="none" stroke="#c7cbe0" stroke-width="4"/>
  <rect x="842" y="326" width="70" height="5" fill="#33395e"/>
  <!-- parked plane at gate -->
  <g transform="translate(905,322)" fill="#3c4470">
    <path d="M0,10 L8,4 L66,4 Q80,5 84,10 Q80,14 66,14 L10,14 Z"/><path d="M6,8 L0,-6 L8,-6 L18,6 Z"/><path d="M34,10 L22,20 L32,20 L48,11 Z"/>
  </g>
</g>
<g>
  <rect x="1060" y="236" width="18" height="100" fill="#3c4470"/><rect x="1060" y="236" width="6" height="100" fill="#2e3560"/>
  <path d="M1044,236 L1094,236 L1100,212 L1038,212 Z" fill="#2e3560"/>
  <rect x="1043" y="215" width="52" height="15" fill="url(#hGlass)"/>
  <rect x="1038" y="204" width="62" height="9" fill="#4a5385"/>
  <line x1="1069" y1="204" x2="1069" y2="184" stroke="#4a5385" stroke-width="3"/>
  <circle cx="1069" cy="182" r="4" fill="#5cf2a0"><animate attributeName="opacity" values="1;.1;1" dur="1.8s" repeatCount="indefinite"/></circle>
  <circle cx="1069" cy="182" r="8" fill="#5cf2a0" filter="url(#hGlow)" opacity=".7"><animate attributeName="opacity" values=".8;0;.8" dur="1.8s" repeatCount="indefinite"/></circle>
</g>
<polygon points="-60,440 470,440 1000,346 960,346" fill="url(#hRunway)"/>
<polygon points="-60,440 -20,440 961,346 960,346" fill="#ffffff" opacity=".35"/>
<g><line x1="205.0" y1="440.0" x2="271.6" y2="431.9" stroke="#fff" stroke-width="5.1" stroke-linecap="round" opacity=".85"/><line x1="316.3" y1="426.5" x2="351.4" y2="422.2" stroke="#fff" stroke-width="4.8" stroke-linecap="round" opacity=".85"/><line x1="385.8" y1="418.1" x2="415.2" y2="414.5" stroke="#fff" stroke-width="4.5" stroke-linecap="round" opacity=".85"/><line x1="445.1" y1="410.9" x2="471.4" y2="407.7" stroke="#fff" stroke-width="4.3" stroke-linecap="round" opacity=".85"/><line x1="498.7" y1="404.4" x2="522.9" y2="401.4" stroke="#fff" stroke-width="4.0" stroke-linecap="round" opacity=".85"/><line x1="548.3" y1="398.4" x2="571.1" y2="395.6" stroke="#fff" stroke-width="3.7" stroke-linecap="round" opacity=".85"/><line x1="595.1" y1="392.7" x2="616.6" y2="390.1" stroke="#fff" stroke-width="3.4" stroke-linecap="round" opacity=".85"/><line x1="639.5" y1="387.3" x2="660.1" y2="384.8" stroke="#fff" stroke-width="3.1" stroke-linecap="round" opacity=".85"/><line x1="682.1" y1="382.1" x2="701.9" y2="379.7" stroke="#fff" stroke-width="2.9" stroke-linecap="round" opacity=".85"/><line x1="723.1" y1="377.2" x2="742.3" y2="374.8" stroke="#fff" stroke-width="2.6" stroke-linecap="round" opacity=".85"/><line x1="762.7" y1="372.4" x2="781.3" y2="370.1" stroke="#fff" stroke-width="2.3" stroke-linecap="round" opacity=".85"/><line x1="801.2" y1="367.7" x2="819.3" y2="365.5" stroke="#fff" stroke-width="2.0" stroke-linecap="round" opacity=".85"/><line x1="838.6" y1="363.1" x2="856.3" y2="361.0" stroke="#fff" stroke-width="1.7" stroke-linecap="round" opacity=".85"/><line x1="875.2" y1="358.7" x2="892.4" y2="356.6" stroke="#fff" stroke-width="1.4" stroke-linecap="round" opacity=".85"/><line x1="910.8" y1="354.4" x2="927.7" y2="352.3" stroke="#fff" stroke-width="1.2" stroke-linecap="round" opacity=".85"/><line x1="945.8" y1="350.2" x2="962.3" y2="348.1" stroke="#fff" stroke-width="0.9" stroke-linecap="round" opacity=".85"/></g>
<g><circle cx="-60.0" cy="440.0" r="4.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="0.0s" repeatCount="indefinite"/></circle><circle cx="470.0" cy="440.0" r="4.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="0.0s" repeatCount="indefinite"/></circle><circle cx="57.2" cy="429.2" r="3.6" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.1s" repeatCount="indefinite"/></circle><circle cx="530.9" cy="429.2" r="3.6" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.1s" repeatCount="indefinite"/></circle><circle cx="130.4" cy="422.5" r="3.4" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.2s" repeatCount="indefinite"/></circle><circle cx="568.9" cy="422.5" r="3.4" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.2s" repeatCount="indefinite"/></circle><circle cx="192.9" cy="416.7" r="3.2" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.3s" repeatCount="indefinite"/></circle><circle cx="601.4" cy="416.7" r="3.2" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.3s" repeatCount="indefinite"/></circle><circle cx="249.3" cy="411.5" r="3.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.4s" repeatCount="indefinite"/></circle><circle cx="630.7" cy="411.5" r="3.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.4s" repeatCount="indefinite"/></circle><circle cx="301.6" cy="406.7" r="2.9" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.5s" repeatCount="indefinite"/></circle><circle cx="657.9" cy="406.7" r="2.9" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.5s" repeatCount="indefinite"/></circle><circle cx="350.8" cy="402.1" r="2.7" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.6s" repeatCount="indefinite"/></circle><circle cx="683.4" cy="402.1" r="2.7" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.6s" repeatCount="indefinite"/></circle><circle cx="397.6" cy="397.8" r="2.6" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.7s" repeatCount="indefinite"/></circle><circle cx="707.8" cy="397.8" r="2.6" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.7s" repeatCount="indefinite"/></circle><circle cx="442.4" cy="393.7" r="2.4" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.8s" repeatCount="indefinite"/></circle><circle cx="731.1" cy="393.7" r="2.4" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.8s" repeatCount="indefinite"/></circle><circle cx="485.6" cy="389.7" r="2.3" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.9s" repeatCount="indefinite"/></circle><circle cx="753.5" cy="389.7" r="2.3" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-0.9s" repeatCount="indefinite"/></circle><circle cx="527.4" cy="385.9" r="2.2" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.0s" repeatCount="indefinite"/></circle><circle cx="775.2" cy="385.9" r="2.2" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.0s" repeatCount="indefinite"/></circle><circle cx="567.9" cy="382.1" r="2.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.1s" repeatCount="indefinite"/></circle><circle cx="796.3" cy="382.1" r="2.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.1s" repeatCount="indefinite"/></circle><circle cx="607.3" cy="378.5" r="1.9" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.2s" repeatCount="indefinite"/></circle><circle cx="816.7" cy="378.5" r="1.9" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.2s" repeatCount="indefinite"/></circle><circle cx="645.8" cy="375.0" r="1.8" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.3s" repeatCount="indefinite"/></circle><circle cx="836.7" cy="375.0" r="1.8" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.3s" repeatCount="indefinite"/></circle><circle cx="683.4" cy="371.5" r="1.7" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.4s" repeatCount="indefinite"/></circle><circle cx="856.3" cy="371.5" r="1.7" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.4s" repeatCount="indefinite"/></circle><circle cx="720.1" cy="368.1" r="1.6" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.5s" repeatCount="indefinite"/></circle><circle cx="875.4" cy="368.1" r="1.6" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.5s" repeatCount="indefinite"/></circle><circle cx="756.2" cy="364.8" r="1.4" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.6s" repeatCount="indefinite"/></circle><circle cx="894.1" cy="364.8" r="1.4" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.6s" repeatCount="indefinite"/></circle><circle cx="791.6" cy="361.5" r="1.3" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.7s" repeatCount="indefinite"/></circle><circle cx="912.5" cy="361.5" r="1.3" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.7s" repeatCount="indefinite"/></circle><circle cx="826.3" cy="358.3" r="1.2" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.8s" repeatCount="indefinite"/></circle><circle cx="930.5" cy="358.3" r="1.2" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.8s" repeatCount="indefinite"/></circle><circle cx="860.5" cy="355.2" r="1.1" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.9s" repeatCount="indefinite"/></circle><circle cx="948.3" cy="355.2" r="1.1" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-1.9s" repeatCount="indefinite"/></circle><circle cx="894.2" cy="352.1" r="1.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-2.0s" repeatCount="indefinite"/></circle><circle cx="965.8" cy="352.1" r="1.0" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-2.0s" repeatCount="indefinite"/></circle><circle cx="927.3" cy="349.0" r="0.9" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-2.1s" repeatCount="indefinite"/></circle><circle cx="983.0" cy="349.0" r="0.9" fill="#ffd166"><animate attributeName="opacity" values="1;.35;1" dur="2.2s" begin="-2.1s" repeatCount="indefinite"/></circle></g>
<g filter="url(#hGlow)"><circle cx="120" cy="440" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.00;0.04;0.10;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="154" cy="434" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.12;0.16;0.22;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="188" cy="428" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.24;0.28;0.34;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="222" cy="422" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.36;0.40;0.46;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="256" cy="416" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.48;0.52;0.58;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="290" cy="410" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.60;0.64;0.70;1" dur="1.6s" repeatCount="indefinite"/></circle></g><g><circle cx="120" cy="440" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.00;0.04;0.10;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="154" cy="434" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.12;0.16;0.22;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="188" cy="428" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.24;0.28;0.34;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="222" cy="422" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.36;0.40;0.46;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="256" cy="416" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.48;0.52;0.58;1" dur="1.6s" repeatCount="indefinite"/></circle><circle cx="290" cy="410" r="3" fill="#fff"><animate attributeName="opacity" values="0;0;1;0;0" keyTimes="0;0.60;0.64;0.70;1" dur="1.6s" repeatCount="indefinite"/></circle></g>
<g fill="none" stroke="url(#hTrail)" stroke-linecap="round" filter="url(#hBlur)">
  <path d="M628,224 C520,260 330,330 130,420" stroke-width="8"><animate attributeName="stroke-width" values="8;11;8" dur="5s" repeatCount="indefinite"/></path>
  <path d="M650,238 C548,276 360,346 170,436" stroke-width="5" opacity=".7"/>
</g>
<g fill="none" stroke="#1d2340" stroke-width="1.6" stroke-linecap="round" opacity=".7">
  <g><animateTransform attributeName="transform" type="translate" from="1250 120" to="-80 160" dur="38s" repeatCount="indefinite"/>
    <path d="M0,0 q5,-5 10,0 q5,-5 10,0"><animate attributeName="d" values="M0,0 q5,-5 10,0 q5,-5 10,0;M0,0 q5,3 10,0 q5,3 10,0;M0,0 q5,-5 10,0 q5,-5 10,0" dur=".9s" repeatCount="indefinite"/></path>
    <path d="M24,10 q4,-4 8,0 q4,-4 8,0"><animate attributeName="d" values="M24,10 q4,-4 8,0 q4,-4 8,0;M24,10 q4,3 8,0 q4,3 8,0;M24,10 q4,-4 8,0 q4,-4 8,0" dur=".8s" repeatCount="indefinite"/></path>
  </g>
</g>
<g fill="#e9ecf7" opacity=".8"><animateTransform attributeName="transform" type="translate" from="1260 70" to="-60 92" dur="60s" begin="-25s" repeatCount="indefinite"/>
  <g transform="scale(-1 1)">
  <path d="M0,4 L4,1 L26,1 Q31,2 32,4 Q31,6 26,6 L4,6 Z"/><path d="M3,3 L0,-3 L4,-3 L8,2 Z"/><path d="M14,4 L9,9 L13,9 L20,4 Z"/>
  <circle cx="32" cy="4" r="1.2" fill="#fff"><animate attributeName="opacity" values="1;0;0;1" dur="1.2s" repeatCount="indefinite"/></circle>
  </g>
</g>
<g>
  <animateTransform attributeName="transform" type="translate" values="0 0; 4 -8; 0 0" dur="6s" repeatCount="indefinite"/>
  <g transform="translate(760,180) rotate(-13)">
    <!-- far wing & engine -->
    <path d="M-30,8 L-78,-34 L-60,-34 L22,4 Z" fill="#8f9bb0"/>
    <!-- horizontal stabiliser far -->
    <path d="M-182,-4 L-210,-22 L-198,-22 L-160,-6 Z" fill="#8f9bb0"/>
    <!-- fuselage -->
    <path d="M-205,-2 Q-212,-14 -196,-16 L130,-16 Q180,-15 196,-2 Q200,4 192,10 Q178,18 130,18 L-170,18 Q-196,16 -205,-2 Z" fill="url(#hBody)"/>
    <path d="M-170,12 L130,12 Q170,12 186,10 Q176,18 130,18 L-170,18 Q-190,17 -198,8 Z" fill="url(#hBelly)"/>
    <path d="M-180,5 L150,5 Q172,5 188,1" fill="none" stroke="url(#hStripe)" stroke-width="3.4"/>
    <rect x="-150" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-141" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-132" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-123" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-114" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-105" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-96" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-87" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-78" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-69" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-60" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-51" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-42" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-33" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-24" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-15" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="-6" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="3" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="12" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="21" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="30" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="39" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="48" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="57" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="66" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="75" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="84" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="93" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="102" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="111" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/><rect x="120" y="-5.5" width="4.2" height="5" rx="1.6" fill="#24365a"/>
    <!-- cockpit -->
    <path d="M168,-9 L181,-8 L188,-3 L171,-3 Z" fill="#24365a"/>
    <!-- doors -->
    <rect x="140" y="-10" width="7" height="15" rx="2" fill="none" stroke="#9aa6b8" stroke-width="1"/>
    <rect x="-150" y="-10" width="7" height="15" rx="2" fill="none" stroke="#9aa6b8" stroke-width="1"/>
    <!-- tail fin with abstract logo -->
    <path d="M-150,-15 L-196,-82 L-172,-82 L-112,-15 Z" fill="url(#hTail)"/>
    <circle cx="-166" cy="-50" r="11" fill="none" stroke="#ffb35c" stroke-width="3"/>
    <path d="M-176,-44 Q-166,-62 -154,-54" fill="none" stroke="#ef476f" stroke-width="3" stroke-linecap="round"/>
    <!-- near horizontal stabiliser -->
    <path d="M-176,6 L-214,28 L-198,28 L-150,8 Z" fill="url(#hWing)"/>
    <!-- near wing -->
    <path d="M-40,6 L-102,62 L-80,64 L30,10 Z" fill="url(#hWing)"/>
    <path d="M-102,62 L-110,58 L-104,52" fill="none" stroke="#9aa6b8" stroke-width="3" stroke-linecap="round"/>
    <!-- engine -->
    <g transform="translate(-34,26)">
      <rect x="-26" y="-9" width="56" height="20" rx="10" fill="url(#hEngine)"/>
      <ellipse cx="29" cy="1" rx="4" ry="9.5" fill="#2b3550"/>
      <rect x="-32" y="-5" width="10" height="12" rx="4" fill="#6b768c"/>
      <path d="M-6,-9 L4,-9 L10,-15 L0,-15 Z" fill="#9aa6b8"/>
    </g>
    <!-- landing gear (retracting) -->
    <g stroke="#2b3550" stroke-width="3" stroke-linecap="round">
      <line x1="-20" y1="18" x2="-20" y2="30"><animate attributeName="y2" values="30;20;30" dur="6s" repeatCount="indefinite"/></line>
      <line x1="140" y1="18" x2="140" y2="28"><animate attributeName="y2" values="28;19;28" dur="6s" repeatCount="indefinite"/></line>
    </g>
    <!-- nav lights -->
    <circle cx="-104" cy="56" r="2.6" fill="#ff4d6d"/><circle cx="-104" cy="56" r="7" fill="#ff4d6d" filter="url(#hGlow)" opacity=".8"><animate attributeName="opacity" values=".9;.2;.9" dur="1.4s" repeatCount="indefinite"/></circle>
    <circle cx="-206" cy="-2" r="2.4" fill="#fff"><animate attributeName="opacity" values="1;0;0;0;1" dur="1.2s" repeatCount="indefinite"/></circle>
    <circle cx="10" cy="-17" r="2" fill="#ff4d6d"><animate attributeName="opacity" values="1;.1;1" dur="1s" repeatCount="indefinite"/></circle>
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
    el.innerHTML = "<div class='globe-msg'>The 3D globe could not load. It needs an internet connection (it loads from cdn.jsdelivr.net). Please refresh the page.</div>";
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
    var ab = k.split('|');
    if (D.focus && ab[1] === D.focus) ab.reverse();  // arcs flow outward from the focus airport
    var p = pairs[k] || (pairs[k] = {a:ab[0], b:ab[1], lines:{}, list:[]});
    p.lines[r[2]] = 1; p.list.push(r);
  });
  var arcs = Object.keys(pairs).map(function(k){
    var p = pairs[k]; p.mi = miles(p.a, p.b); p.hl = false; return p;
  });
  function arcLabel(p){
    var A = D.airports[p.a], B = D.airports[p.b];
    return '<b>' + p.a + ' &#8644; ' + p.b + '</b><br>' + A[3] + ' &#8594; ' + B[3] + '<br>' +
           p.mi.toLocaleString() + ' miles<br>Airlines: ' + Object.keys(p.lines).join(', ');
  }
  function midpoint(a, b){
    var p = D.airports[a], q = D.airports[b];
    function v(l){ return [Math.cos(l[0]*R)*Math.cos(l[1]*R), Math.cos(l[0]*R)*Math.sin(l[1]*R), Math.sin(l[0]*R)]; }
    var x = v(p), y = v(q), m = [x[0]+y[0], x[1]+y[1], x[2]+y[2]];
    return {lat: Math.atan2(m[2], Math.sqrt(m[0]*m[0]+m[1]*m[1]))/R, lng: Math.atan2(m[1], m[0])/R};
  }
  var g = Globe()(el)
    .globeImageUrl('https://cdn.jsdelivr.net/npm/three-globe/example/img/earth-blue-marble.jpg')
    .bumpImageUrl('https://cdn.jsdelivr.net/npm/three-globe/example/img/earth-topology.png')
    .backgroundImageUrl('https://cdn.jsdelivr.net/npm/three-globe/example/img/night-sky.png')
    .width(el.clientWidth).height(el.clientHeight)
    .arcStartLat(function(p){return D.airports[p.a][0];}).arcStartLng(function(p){return D.airports[p.a][1];})
    .arcEndLat(function(p){return D.airports[p.b][0];}).arcEndLng(function(p){return D.airports[p.b][1];})
    .arcColor(function(p){return p.hl ? ['#ffd166','#ef476f'] : 'rgba(120,200,255,0.35)';})
    .arcStroke(function(p){return p.hl ? (sel && selKind === 'route' ? 1.1 : 0.7) : 0.25;})
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
  function hideLoading(){ var l = document.getElementById('globe-loading'); if (l) l.remove(); }
  if (g.onGlobeReady) g.onGlobeReady(hideLoading);
  setTimeout(hideLoading, 9000);

  var sel = null, selKind = null, hot = {};
  var marks = {}; (D.marks || []).concat(D.focus ? [D.focus] : []).forEach(function(c){ marks[c] = 1; });
  var base = null;  // optional: only these airports' arcs are shown when nothing is selected
  if (D.base) { base = {}; D.base.forEach(function(c){ base[c] = 1; }); }
  function inBase(p){ return !base || base[p.a] || base[p.b]; }
  var baseInfo = info.innerHTML;
  // airport name tags: real page elements, so they stay the same readable size at any zoom
  function tag(l){
    var wrap = document.createElement('div'), el = document.createElement('div');
    el.className = 'gtag' + (marks[l[0]] || l[0] === sel ? ' mark' : '');
    el.innerHTML = '<b>' + l[1] + '</b><span>' + (D.airports[l[0]] ? D.airports[l[0]][3] : '') + '</span>';
    wrap.appendChild(el); return wrap;
  }
  function setTags(list){
    if (!g.htmlElementsData) return;
    g.htmlElementsData(list);
  }
  if (D.labels && g.htmlElementsData) {
    g.htmlLat(function(l){return D.airports[l[0]][0];}).htmlLng(function(l){return D.airports[l[0]][1];})
     .htmlAltitude(0.015).htmlElement(tag);
    if (g.htmlTransitionDuration) g.htmlTransitionDuration(0);
    if (g.htmlElementVisibilityModifier) {
      g.htmlElementVisibilityModifier(function(el, visible){ el.style.opacity = visible ? 1 : 0; });
    }
    setTags(D.labels.slice());
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
    sel = key; selKind = kind; hot = {};
    var count = 0;
    arcs.forEach(function(p){
      p.hl = key === null ? !!(base && inBase(p))
           : (kind === 'airport' || kind === 'route') ? (p.a === key || p.b === key) : !!p.lines[key];
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
    if (D.labels) {
      if (key && (kind === 'route' || kind === 'airport')) {
        // a single connection is selected: label only its end points and the selected airport
        var keep = D.labels.filter(function(l){ return marks[l[0]]; });
        setTags(keep.concat([[key, key]]));
      } else {
        setTags(D.labels.slice());
      }
    }
    draw();
    if (key && kind === 'route' && D.focus) {
      var on1 = arcs.filter(function(p){return p.hl;})[0], m = midpoint(D.focus, key);
      var mi = on1 ? on1.mi : 1000;
      g.pointOfView({lat: m.lat, lng: m.lng, altitude: Math.min(2.6, Math.max(0.9, 0.55 + mi/2600))}, 1300);
    }
    else if (key && kind === 'airport') fly(key, D.alt || 1.6);
    else if (D.focus) fly(D.focus, D.alt || 1.8);
  };
  window.showOnGlobe(null, null);
  if (D.focus) fly(D.focus, D.alt || 1.8);
  else if (arcs.length) fly(arcs[0].a, 2.2);
  g.controls().autoRotate = !D.focus;
  g.controls().autoRotateSpeed = 0.4;

  // clickable table rows
  document.querySelectorAll('.pick').forEach(function(tr){
    tr.addEventListener('click', function(){
      var was = tr.classList.contains('sel');
      document.querySelectorAll('.pick.sel').forEach(function(x){ x.classList.remove('sel'); });
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

    # Line icons (24x24, drawn with the text colour) used by the menu and the home page
    ICONS = {
        "home": '<path d="M3 11l9-7 9 7"/><path d="M5 9.5V20h5v-6h4v6h5V9.5"/>',
        "plane": '<path d="M21 15.5v-2l-8-5V3.8a1.5 1.5 0 0 0-3 0v4.7l-8 5v2l8-2.5v5l-2 1.5V21l3.5-1 3.5 1v-1.5l-2-1.5v-5z"/>',
        "tower": '<path d="M6 10h12l-1.6-4H7.6z"/><path d="M8 6V4h8v2"/><path d="M12 4V2"/><path d="M9 10v11M15 10v11"/><path d="M5 21h14"/>',
        "route": '<circle cx="6" cy="19" r="2"/><circle cx="18" cy="5" r="2"/><path d="M8 19h7.5a3.5 3.5 0 0 0 0-7h-7a3.5 3.5 0 0 1 0-7H16"/>',
        "data": '<ellipse cx="12" cy="5" rx="8" ry="3"/><path d="M4 5v14c0 1.7 3.6 3 8 3s8-1.3 8-3V5"/><path d="M4 12c0 1.7 3.6 3 8 3s8-1.3 8-3"/>',
        "info": '<circle cx="12" cy="12" r="9"/><path d="M12 11v6"/><path d="M12 7.5h.01"/>',
        "mail": '<rect x="3" y="5" width="18" height="14" rx="2"/><path d="M3.5 7l8.5 6 8.5-6"/>',
        "search": '<circle cx="11" cy="11" r="6"/><path d="M20 20l-4.5-4.5"/>',
        "list": '<path d="M9 6h11M9 12h11M9 18h11"/><path d="M4.5 6h.01M4.5 12h.01M4.5 18h.01"/>',
        "network": '<circle cx="12" cy="12" r="2.5"/><circle cx="4.5" cy="5" r="2"/><circle cx="19.5" cy="5" r="2"/><circle cx="4.5" cy="19" r="2"/><circle cx="19.5" cy="19" r="2"/><path d="M6 6.4l4.2 4M18 6.4l-4.2 4M6 17.6l4.2-4M18 17.6l-4.2-4"/>',
        "pin": '<path d="M12 21s-6.5-5.6-6.5-11a6.5 6.5 0 0 1 13 0c0 5.4-6.5 11-6.5 11z"/><circle cx="12" cy="10" r="2.3"/>',
        "hop": '<circle cx="4" cy="18" r="2"/><circle cx="12" cy="8" r="2"/><circle cx="20" cy="18" r="2"/><path d="M5.3 16.4l5.4-6.8M13.3 9.6l5.4 6.8"/>',
        "idcard": '<rect x="3" y="5" width="18" height="14" rx="2"/><circle cx="9" cy="11" r="2"/><path d="M5.8 16c.6-1.4 1.8-2 3.2-2s2.6.6 3.2 2"/><path d="M15 10h3.5M15 14h3.5"/>',
        "pencil": '<path d="M4 20h4L19 9l-4-4L4 16z"/><path d="M13.5 6.5l4 4"/>',
        "chart": '<path d="M4 20h16"/><path d="M7 16v-5M12 16V6M17 16v-8"/>',
        "code": '<path d="M8 8l-4 4 4 4M16 8l4 4-4 4M13.5 5l-3 14"/>',
        "user": '<circle cx="12" cy="8" r="4"/><path d="M4 21c1-4 4.4-6 8-6s7 2 8 6"/>',
        "chev": '<path d="M6 9l6 6 6-6"/>',
        "menu": '<path d="M4 6h16M4 12h16M4 18h16"/>',
    }

    # (icon, label, url or None, [(url, icon, title, assignment tag, description)], right-aligned)
    NAV_GROUPS = [
        ("home", "Home", "/", [], False),
        ("plane", "Airlines", None, [
            ("/airline", "search", "Airline Lookup", "1.1", "Find one airline by its IATA code"),
            ("/report/airlines", "list", "All Airlines", "2.2a", "Every airline, sorted and searchable")], False),
        ("tower", "Airports", None, [
            ("/airport", "search", "Airport Lookup", "1.2", "Airport details and its routes on the globe"),
            ("/report/airports", "list", "All Airports", "2.2b", "Filter by city, country or airline")], False),
        ("route", "Routes", None, [
            ("/report/airline-airports", "network", "Airline → Airports", "2.1a", "Airports an airline serves, by # routes"),
            ("/report/airport-airlines", "pin", "Airport → Airlines", "2.1b", "Airlines at an airport, by # routes"),
            ("/onehop", "hop", "One Hop Routes", "★", "One-stop trips ranked by air miles")], False),
        ("data", "Data Management", None, [
            ("/id", "idcard", "Get ID", "2.3", "Site owner name and student ID"),
            ("/edit", "pencil", "Edit Data", "", "Changes stay in your browser session only"),
            ("/charts", "chart", "Charts & Statistics", "", "Interactive charts, filter by airline")], False),
        ("info", "About", None, [
            ("/about", "user", "About", "", "The developer and this project"),
            ("/code", "code", "Technical Overview", "", "Classes and the full OO source code")], True),
        ("mail", "Contact", "/contact", [], False),
    ]
    NAV = [(u, t) for _, t, u, _, _ in NAV_GROUPS if u] + \
          [(u, title) for _, _, _, subs, _ in NAV_GROUPS for u, _, title, _, _ in subs]

    @classmethod
    def icon(cls, name, extra=""):
        return (f"<svg viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='1.8' "
                f"stroke-linecap='round' stroke-linejoin='round' aria-hidden='true'{extra}>{cls.ICONS[name]}</svg>")

    @classmethod
    def sub_link(cls, url, ic, title, tag, desc, css="sub-link"):
        tag_html = f"<em>{html.escape(tag)}</em>" if tag else ""
        return (f"<a class='{css}' href='{url}'><span class='ic'>{cls.icon(ic)}</span>"
                f"<span class='txt'><b>{html.escape(title)}{tag_html}</b><small>{html.escape(desc)}</small></span></a>")

    @classmethod
    def menu(cls):
        items = ""
        chev = cls.icon("chev", " class='chev'")
        for ic, label, url, subs, right in cls.NAV_GROUPS:
            r = " right" if right else ""
            if url:
                items += (f"<li class='nav-item{r}'><a class='nav-top' href='{url}'>{cls.icon(ic)}"
                          f"<span>{html.escape(label)}</span></a></li>")
            else:
                links = "".join(cls.sub_link(*s) for s in subs)
                items += (f"<li class='nav-item has-sub{r}'><button type='button' class='nav-top' aria-expanded='false'>"
                          f"{cls.icon(ic)}<span>{html.escape(label)}</span>{chev}</button>"
                          f"<div class='sub'>{links}</div></li>")
        return (f"<nav class='mainnav' aria-label='Main menu'><button type='button' class='nav-toggle' aria-expanded='false'>"
                f"{cls.icon('menu')}<span>Menu</span></button><ul class='nav-list'>{items}</ul></nav>")

    AC_JS = r"""
(function(){
  var inputs = document.querySelectorAll('input.ac'); if (!inputs.length) return;
  var data = null, loading = null;
  function load(){ if (!loading) loading = fetch('/api/lookup.json').then(function(r){ return r.json(); }).then(function(d){ data = d; }); return loading; }
  function norm(s){ return (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase(); }
  function score(kind, row, q){
    if (kind === 'airport') {
      var c = norm(row[0]), city = norm(row[2]), name = norm(row[1]), cty = norm(row[3]);
      if (c === q) return 0; if (city === q) return 1; if (city.indexOf(q) === 0) return 2; if (c.indexOf(q) === 0) return 3;
      if ((' ' + name).indexOf(' ' + q) !== -1) return 4; if (city.indexOf(q) !== -1 || name.indexOf(q) !== -1) return 5;
      if (cty.indexOf(q) === 0) return 6; return -1;
    }
    var c2 = norm(row[0]), n = norm(row[1]), ct = norm(row[2]);
    if (c2 === q) return 0; if (n.indexOf(q) === 0) return 1; if ((' ' + n).indexOf(' ' + q) !== -1) return 2;
    if (n.indexOf(q) !== -1) return 3; if (ct.indexOf(q) === 0) return 4; return -1;
  }
  inputs.forEach(function(inp){
    var kind = inp.dataset.ac, list = document.createElement('ul'), items = [], on = -1;
    list.className = 'ac-list'; list.setAttribute('role', 'listbox'); inp.parentNode.appendChild(list);
    function close(){ list.classList.remove('show'); on = -1; }
    function choose(i){ var r = items[i]; if (!r) return; inp.value = r[0]; close();
      if (inp.dataset.submit && inp.form) inp.form.submit(); }
    function render(){
      var q = norm(inp.value.trim()); if (!q || !data) { close(); return; }
      var rows = data[kind === 'airport' ? 'airports' : 'airlines'], hits = [];
      rows.forEach(function(r){ var s = score(kind, r, q); if (s >= 0) hits.push([s, r]); });
      hits.sort(function(a, b){ return a[0] - b[0] || (a[1][2] || '').localeCompare(b[1][2] || ''); });
      items = hits.slice(0, 8).map(function(h){ return h[1]; }); on = -1;
      if (!items.length) { list.innerHTML = "<li style='cursor:default'><span>No matches</span></li>"; items = []; list.classList.add('show'); return; }
      list.innerHTML = items.map(function(r, i){
        var main = kind === 'airport' ? r[2] + ' &middot; ' + r[1] : r[1];
        var right = kind === 'airport' ? r[3] : r[2];
        return "<li role='option' data-i='" + i + "'><b>" + r[0] + "</b><span>" + main.replace(/</g, '&lt;') + "</span><small>" + right + "</small></li>";
      }).join('');
      list.classList.add('show');
    }
    function mark(){ [].forEach.call(list.children, function(li, i){ li.classList.toggle('on', i === on); }); }
    inp.addEventListener('focus', function(){ load().then(render); });
    inp.addEventListener('input', function(){ load().then(render); });
    inp.addEventListener('keydown', function(e){
      if (!list.classList.contains('show') || !items.length) return;
      if (e.key === 'ArrowDown') { on = Math.min(items.length - 1, on + 1); mark(); e.preventDefault(); }
      else if (e.key === 'ArrowUp') { on = Math.max(0, on - 1); mark(); e.preventDefault(); }
      else if (e.key === 'Enter') { if (on < 0 && items.length) on = 0; e.preventDefault(); choose(on); }
      else if (e.key === 'Escape') close();
    });
    list.addEventListener('mousedown', function(e){ var li = e.target.closest('li[data-i]'); if (li) { e.preventDefault(); choose(+li.dataset.i); } });
    inp.addEventListener('blur', function(){ setTimeout(close, 120); });
  });
})();
"""

    LOCALTIME_JS = r"""
(function(){
  var els = document.querySelectorAll('.localtime'); if (!els.length) return;
  function tick(){
    els.forEach(function(el){
      var now = new Date(), txt = '';
      try { if (el.dataset.tz) txt = now.toLocaleTimeString([], {hour: 'numeric', minute: '2-digit', timeZone: el.dataset.tz}); } catch (e) {}
      if (!txt && el.dataset.offset) {
        var t = new Date(now.getTime() + parseFloat(el.dataset.offset) * 3600000);
        txt = t.toISOString().substr(11, 5) + ' (UTC' + (parseFloat(el.dataset.offset) >= 0 ? '+' : '') + el.dataset.offset + ')';
      }
      el.textContent = txt || '\u2014';
    });
  }
  tick(); setInterval(tick, 30000);
})();
"""

    MENU_JS = r"""
(function(){
  var nav = document.querySelector('nav.mainnav'); if (!nav) return;
  var p = location.pathname.replace(/\/$/, '') || '/';
  nav.querySelectorAll('a').forEach(function(a){
    if (a.getAttribute('href') === p) { a.classList.add('active'); a.closest('.nav-item').classList.add('active'); }
  });
  function closeAll(except){ nav.querySelectorAll('.has-sub.open').forEach(function(li){
    if (li !== except) { li.classList.remove('open'); li.querySelector('.nav-top').setAttribute('aria-expanded', 'false'); } }); }
  nav.querySelectorAll('.has-sub > .nav-top').forEach(function(b){
    b.addEventListener('click', function(e){
      var li = b.parentNode, open = !li.classList.contains('open');
      closeAll(li); li.classList.toggle('open', open); b.setAttribute('aria-expanded', open ? 'true' : 'false');
      e.stopPropagation();
    });
  });
  document.addEventListener('click', function(e){ if (!nav.contains(e.target)) closeAll(null); });
  document.addEventListener('keydown', function(e){ if (e.key === 'Escape') closeAll(null); });
  var tog = nav.querySelector('.nav-toggle');
  tog.addEventListener('click', function(){
    var open = !nav.classList.contains('open'); nav.classList.toggle('open', open);
    tog.setAttribute('aria-expanded', open ? 'true' : 'false');
  });
})();
"""

    @classmethod
    def render(cls, title, body, globe_data=None, extra_js="", banner="", extra_head=""):
        nav = cls.menu()
        scripts = f"<script>{cls.MENU_JS}</script><script>{cls.AC_JS}</script><script>{cls.LOCALTIME_JS}</script>"
        if extra_js:
            scripts += f"<script>{extra_js}</script>"
        if globe_data is not None:
            data = json.dumps(globe_data).replace("</", "<\\/")
            scripts += (f"<script type='application/json' id='globe-data'>{data}</script>"
                       f"<script src='https://cdn.jsdelivr.net/npm/globe.gl@2'></script>"
                       f"<script>{cls.GLOBE_JS}</script>")
        return (f"<!doctype html><html><head><meta charset='utf-8'>"
                f"<meta name='viewport' content='width=device-width,initial-scale=1'>"
                f"<title>{html.escape(title)} - Airline Route Access</title>"
                f"<style>{cls.CSS}</style>{extra_head}</head><body>"
                f"<header class='topbar'><div class='topbar-in'><a class='brand' href='/'>{cls.icon('plane')}"
                f"<span>Airline Route Access</span></a>{nav}</div></header>"
                f"{banner}<main>{body}</main>{cls.footer()}{scripts}</body></html>")

    @staticmethod
    def globe(caption, hint=""):
        hint_html = f"<p class='hint'>{html.escape(hint)}</p>" if hint else ""
        return (f"<div class='globe-wrap'><div id='globe'><div class='globe-loading' id='globe-loading'>"
                f"<span class='spin'></span>Loading 3D globe&hellip;</div></div>"
                f"<div class='globe-info' id='globe-info'>{caption}</div></div>{hint_html}")

    @staticmethod
    def ac_input(name, kind, value="", autofocus=False, submit=False):
        """A search box that suggests airports/airlines as you type (city, name or code)."""
        ph = "City, airport or code (e.g. San Jose or SJC)" if kind == "airport" else "Airline name or code (e.g. Delta or DL)"
        return (f"<span class='ac-wrap'><input type='text' class='ac' name='{name}' data-ac='{kind}'"
                f"{' data-submit=1' if submit else ''} value='{html.escape(value)}' placeholder='{ph}' "
                f"autocomplete='off' spellcheck='false'{' autofocus' if autofocus else ''}></span>")

    @classmethod
    def form(cls, action, label, value="", kind="airport"):
        return (f"<form class='lookup-form' action='{action}' method='get'><label>{html.escape(label)}"
                f"{cls.ac_input('code', kind, value, autofocus=not value, submit=True)}</label>"
                f"<button type='submit'>Search</button></form>")

    @staticmethod
    def examples(items, label="Examples:"):
        return ("<div class='examples'><span>" + html.escape(label) + "</span>"
                + "".join(f"<a href='{html.escape(u)}'>{html.escape(t)}</a>" for t, u in items) + "</div>")

    @classmethod
    def not_found(cls, what, q, suggestions, url_for):
        """Error box; when the text matched several things, offer them as links."""
        if suggestions:
            return ("<div class='suggest'><p>More than one " + what + " matches <b>" + html.escape(q)
                    + "</b>. Did you mean:</p>"
                    + cls.examples([(f"{s.iata} · {getattr(s, 'city', '') or s.name}", url_for(s)) for s in suggestions], "")
                    + "</div>")
        return cls.error(f"No {what} found for '{q}'. Try a city, a name, or a code.")

    DST_MEANING = {"E": "Europe", "A": "US / Canada", "S": "South America", "O": "Australia",
                   "Z": "New Zealand", "N": "None", "U": "Unknown"}

    @classmethod
    def airport_card(cls, a, stats=()):
        """Readable card that still shows every field of the airport record."""
        def fact(k, v, css="fact"):
            return f"<div class='{css}'><span class='k'>{html.escape(k)}</span><span class='v'>{v}</span></div>"
        esc = lambda v: html.escape(v) if v else "&mdash;"
        off = a.utc_offset
        offs = ("UTC" + ("+" if off and not off.startswith("-") else "") + off) if off else "&mdash;"
        dst = esc(a.dst) + (f" <small>({cls.DST_MEANING[a.dst]})</small>" if a.dst in cls.DST_MEANING else "")
        tz_attr = f" data-tz='{html.escape(a.timezone)}'" if a.timezone else ""
        facts = (fact("IATA", esc(a.iata)) + fact("ICAO", esc(a.icao)) + fact("OpenFlights ID", esc(a.id))
                 + fact("City", esc(a.city)) + fact("Country", esc(a.country))
                 + fact("Latitude", esc(a.latitude)) + fact("Longitude", esc(a.longitude))
                 + fact("Altitude", (esc(a.altitude) + " <small>ft</small>") if a.altitude else "&mdash;")
                 + fact("UTC offset", offs) + fact("DST", dst) + fact("Timezone", esc(a.timezone.replace("_", " ")))
                 + fact("Type", esc(a.type)) + fact("Source", esc(a.source))
                 + "".join(fact(k, v, "fact stat") for k, v in stats))
        return ("<div class='info-card'><div class='ic-head'>"
                f"<div class='code-badge'>{html.escape(a.iata)}</div><div><h2>{html.escape(a.name)}</h2>"
                f"<p>{html.escape(a.city)}, {html.escape(a.country)} &middot; Local time "
                f"<span class='localtime'{tz_attr} data-offset='{html.escape(off)}'>&mdash;</span></p></div></div>"
                f"<div class='facts'>{facts}</div>"
                f"<details class='raw'><summary>Show the full record as a table</summary>"
                f"{cls.entity(Airport.FIELDS, a.values())}</details></div>")

    @classmethod
    def airline_card(cls, a, stats=()):
        def fact(k, v, css="fact"):
            return f"<div class='{css}'><span class='k'>{html.escape(k)}</span><span class='v'>{v}</span></div>"
        esc = lambda v: html.escape(v) if v else "&mdash;"
        active = a.active.upper() == "Y"
        pill = f"<span class='pill {'on' if active else 'off'}'>{'Active' if active else 'Inactive'}</span>"
        facts = (fact("IATA", esc(a.iata)) + fact("ICAO", esc(a.icao)) + fact("OpenFlights ID", esc(a.id))
                 + fact("Callsign", esc(a.callsign)) + fact("Alias", esc(a.alias)) + fact("Country", esc(a.country))
                 + fact("Active", "Yes" if active else "No")
                 + "".join(fact(k, v, "fact stat") for k, v in stats))
        return ("<div class='info-card'><div class='ic-head'>"
                f"<div class='code-badge'>{html.escape(a.iata)}</div><div><h2>{html.escape(a.name)}{pill}</h2>"
                f"<p>{html.escape(a.country)}</p></div></div><div class='facts'>{facts}</div>"
                f"<details class='raw'><summary>Show the full record as a table</summary>"
                f"{cls.entity(Airline.FIELDS, a.values())}</details></div>")

    @classmethod
    def page_head(cls, path):
        for ic, label, url, subs, _ in cls.NAV_GROUPS:
            if url == path:
                desc = {"/contact": "Get in touch or connect on LinkedIn"}.get(path, "")
                return cls._head(ic, label, "", desc)
            for u, sic, title, tag, desc in subs:
                if u == path:
                    return cls._head(sic, title, tag, desc)
        return ""

    @classmethod
    def _head(cls, ic, title, tag, desc):
        tag_html = f"<em>{html.escape(tag)}</em>" if tag else ""
        desc_html = f"<p>{html.escape(desc)}</p>" if desc else ""
        return (f"<div class='page-head'><span class='ic'>{cls.icon(ic)}</span><div>"
                f"<h1>{html.escape(title)}{tag_html}</h1>{desc_html}</div></div>")

    @classmethod
    def footer(cls):
        gh = f"<a href='{GITHUB_URL}' target='_blank' rel='noopener'>Source code on GitHub</a><br>" if GITHUB_URL else ""
        return ("<footer class='site-foot'><div class='foot-in'>"
                f"<div><a class='brand' href='/'>{cls.icon('plane')}<span>Airline Route Access</span></a>"
                "Explore airlines, airports and routes, plan one-stop trips, and see every route on an "
                "interactive 3D globe.</div>"
                f"<div><h4>Built by</h4>{html.escape(STUDENT_NAME)}<br>CIS 51 &middot; De Anza College<br>"
                f"<a href='{LINKEDIN_URL}' target='_blank' rel='noopener'>LinkedIn</a></div>"
                f"<div><h4>Project</h4><a href='/about'>About</a><br><a href='/code'>Technical overview</a><br>{gh}"
                "<a href='https://openflights.org/data' target='_blank' rel='noopener'>Data: OpenFlights</a></div>"
                "</div><div class='foot-bottom'>Built with Vibe Coding &middot; Python &amp; globe.gl &middot; 2026</div></footer>")

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
            body += f"<tr{attr}>" + "".join(f"<td data-label='{html.escape(headers[j])}'>{html.escape(str(v))}</td>"
                                            for j, v in enumerate(r)) + "</tr>"
        return f"<div class='scroll'><table class='rt'><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table></div>"

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
    """Maps each URL to a page and builds that page from the database."""
    QUERY_HANDLERS = ("/onehop", "/edit", "/charts")  # these receive the whole query string

    def __init__(self, db, in_session=False):
        self.db = db
        self.in_session = in_session
        self.path = "/"
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
            "/charts": self.charts,
            "/edit": self.edit_page,
            "/code": self.code_page,
            "/contact": self.contact,
        }

    def render(self, title, body, globe_data=None, extra_js="", extra_head=""):
        """Page.render plus a notice when this browser session has its own edited data."""
        banner = ""
        if self.in_session and self.db.edits:
            n = len(self.db.edits)
            banner = (f"<div class='banner'>✎ You are viewing data with {n} change{'s' if n != 1 else ''} "
                      f"made in this browser session only. <a href='/edit'>See or reset changes</a></div>")
        head = Page.page_head(self.path) if self.path != "/" else ""
        if head:
            if body.startswith("<h2>"):
                body = head + body[body.index("</h2>") + 5:]
            else:
                body = head + body
        return Page.render(title, body, globe_data, extra_js, banner, extra_head)

    def handle(self, path, query):
        self.path = path
        handler = self.routes.get(path)
        if handler is None:
            return 404, self.render("Not found", Page.error("Page not found."))
        if path in self.QUERY_HANDLERS:
            return 200, handler(query)
        code = query.get("code", [""])[0].strip()[:60]
        return 200, handler(code)

    def home(self, _):
        cards = ""
        for ic, label, url, subs, _ in Page.NAV_GROUPS:
            if not subs:
                continue
            if label == "About":
                subs = subs + [("/contact", "mail", "Contact", "", "Get in touch or connect on LinkedIn")]
            cards += (f"<section class='home-group'><h2>{Page.icon(ic)}{html.escape(label)}</h2><div class='home-cards'>"
                      + "".join(Page.sub_link(*s, css="sub-link home-card") for s in subs) + "</div></section>")
        art = ("<div class='hero-photo'><img src='/hero' alt='Airplane at an airport'></div>"
               if find_hero() else Page.HERO_SVG)
        hero = (f"<div class='hero{' has-photo' if find_hero() else ''}'>{art}<div class='hero-text'>"
                f"<h1>Air Travel Database</h1>"
                f"<p>{len(self.db.airlines_by_iata)} airlines · {len(self.db.airports_by_iata)} airports · "
                f"{len(self.db.routes):,} routes</p></div></div>")
        return self.render("Home", f"{hero}{cards}")

    def airline_buttons(self, url):
        """One button per airline (there are only a few), labelled with code and short name."""
        short = lambda n: n.replace(" Air Lines", "").replace(" Airlines", "").replace(" Airways", "").strip() or n
        return Page.examples([(f"{a.iata} {short(a.name)}", f"{url}?code={a.iata}") for a in self.db.all_airlines()],
                             "Airlines:")
    AIRPORT_EXAMPLES = [("SJC San Jose", "SJC"), ("SFO San Francisco", "SFO"), ("LAX Los Angeles", "LAX"),
                        ("DEN Denver", "DEN"), ("ORD Chicago", "ORD"), ("ATL Atlanta", "ATL"),
                        ("JFK New York", "JFK"), ("LHR London", "LHR")]

    def airport_buttons(self, url):
        return Page.examples([(t, f"{url}?code={c}") for t, c in self.AIRPORT_EXAMPLES], "Popular airports:")

    def airline_lookup(self, code):
        a, sugg = self.db.resolve_airline(code) if code else (None, [])
        body = "<h2>1.1 Airline Lookup</h2>" + Page.form("/airline", "Airline", a.iata if a else code, "airline")
        if not code:
            body += self.airline_buttons("/airline")
        elif not a:
            body += Page.not_found("airline", code, sugg, lambda s: f"/airline?code={s.iata}")
        else:
            routes = self.db.routes_of_airline(a)
            n_airports = len(self.db.airports_for_airline(a))
            body += Page.airline_card(a, [("Routes", f"{len(routes):,}"), ("Airports served", f"{n_airports:,}")])
            body += (f"<p class='hint'>See this airline's network: <a href='/report/airline-airports?code={a.iata}'>"
                     f"{html.escape(a.iata)} airports on the globe &rarr;</a></p>")
        return self.render("Airline Lookup", body)

    def airport_lookup(self, code):
        a, sugg = self.db.resolve_airport(code) if code else (None, [])
        body = "<h2>1.2 Airport Lookup</h2>" + Page.form("/airport", "Airport", a.iata if a else code)
        globe = None
        if not code:
            body += self.airport_buttons("/airport")
        if code:
            if not a:
                body += Page.not_found("airport", code, sugg, lambda s: f"/airport?code={s.iata}")
            else:
                routes = self.db.routes_at_airport(a)
                dests = self.db.destinations(a)
                per_airline = Counter(self.db.airlines_by_id[r.airline_id].iata for r in routes
                                      if r.airline_id in self.db.airlines_by_id)
                chips = ("<div class='chips'><span class='lbl'>Show only:</span>"
                         + "".join(f"<button type='button' class='chip pick' data-key='{html.escape(c)}' data-kind='airline'>"
                                   f"{html.escape(c)} &middot; {n}</button>" for c, n in per_airline.most_common())
                         + "</div>")
                body += (Page.airport_card(a, [("Routes", f"{len(routes):,}"), ("Destinations", f"{len(dests):,}"),
                                               ("Airlines", f"{len(per_airline):,}")])
                         + Page.globe(f"<b>{html.escape(a.iata)}</b> {html.escape(a.name)} &mdash; "
                                      f"{len(routes)} routes to {len(dests)} airports",
                                      "Click an airline to show only its routes, or a destination row below to show "
                                      "that single route (click again to show all). Hover an arc for details.")
                         + chips
                         + f"<h3>Destinations ({len(dests)})</h3>"
                         + Page.table(["IATA", "Airport", "City", "Country", "Air miles", "# Routes", "Airlines", "Direction"],
                                      [[d["airport"].iata, d["airport"].name, d["airport"].city, d["airport"].country,
                                        f"{d['miles']:,.0f}", d["count"], ", ".join(d["airlines"]), d["direction"]]
                                       for d in dests],
                                      keys=[d["airport"].iata for d in dests], kind="route",
                                      infos=[f"{a.iata} ⇄ {d['airport'].iata} ({d['airport'].city}) · {d['miles']:,.0f} mi · "
                                             f"{d['count']} route{'s' if d['count'] != 1 else ''} · {', '.join(d['airlines'])}"
                                             for d in dests]))
                globe = self.db.map_data(routes, focus=a.iata)
                globe["labels"] = [[a.iata, a.iata]]
        return self.render("Airport Lookup", body, globe)

    def airline_airports_report(self, code):
        airline, sugg = self.db.resolve_airline(code) if code else (None, [])
        body = ("<h2>2.1a Airports served by an Airline (by # routes)</h2>"
                + Page.form("/report/airline-airports", "Airline", airline.iata if airline else code, "airline"))
        globe = None
        if not code:
            body += self.airline_buttons("/report/airline-airports")
        if code:
            if not airline:
                body += Page.not_found("airline", code, sugg, lambda s: f"/report/airline-airports?code={s.iata}")
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
        return self.render("Airline → Airports", body, globe)

    def airport_airlines_report(self, code):
        airport, sugg = self.db.resolve_airport(code) if code else (None, [])
        body = ("<h2>2.1b Airlines serving an Airport (by # routes)</h2>"
                + Page.form("/report/airport-airlines", "Airport", airport.iata if airport else code))
        globe = None
        if not code:
            body += self.airport_buttons("/report/airport-airlines")
        if code:
            if not airport:
                body += Page.not_found("airport", code, sugg, lambda s: f"/report/airport-airlines?code={s.iata}")
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
        return self.render("Airport → Airlines", body, globe)

    def all_airlines_report(self, _):
        rows = self.db.all_airlines()
        bar = Page.filter_bar([("name", "Airline name"), ("country", "Country"), ("iata", "IATA / ICAO code"),
                               ("callsign", "Callsign")],
                              sorted({a.country for a in rows if a.country}))
        data = [{"name": a.name + " " + a.alias, "country": a.country, "iata": a.iata + " " + a.icao,
                 "callsign": a.callsign} for a in rows]
        body = (f"<h2>2.2a All Airlines (by IATA code)</h2>{bar}"
                + Page.table(Airline.FIELDS, [a.values() for a in rows], row_data=data))
        return self.render("All Airlines", body, extra_js=Page.FILTER_JS)

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
        return self.render("All Airports", body, extra_js=Page.FILTER_JS)

    def one_hop(self, query):
        src = query.get("from", [""])[0].strip()[:60]
        dst = query.get("to", [""])[0].strip()[:60]
        S, s_sugg = self.db.resolve_airport(src) if src else (None, [])
        D, d_sugg = self.db.resolve_airport(dst) if dst else (None, [])
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
                "<form class='lookup-form' action='/onehop' method='get'>"
                f"<label>From{Page.ac_input('from', 'airport', S.iata if S else src, autofocus=not src)}</label>"
                f"<label>To{Page.ac_input('to', 'airport', D.iata if D else dst)}</label>"
                f"<label>Airline<select name='airline'>{options}</select></label>"
                "<button type='submit'>Find routes</button></form>")
        globe = None
        if not (src or dst):
            body += Page.examples([(f"{a} → {b}", f"/onehop?from={a}&to={b}") for a, b in
                                   [("SJC", "BOS"), ("SFO", "NRT"), ("LAX", "SYD"), ("SJC", "DXB"), ("SFO", "CDG")]])
            return self.render("One Hop", body)

        if not src or not dst:
            return self.render("One Hop", body + Page.error("Please enter both a From and a To airport."))
        keep = lambda **kw: "/onehop?" + urlencode({"from": kw.get("f", src), "to": kw.get("t", dst), "airline": flt})
        if not S:
            return self.render("One Hop", body + Page.not_found("airport", src, s_sugg, lambda s: keep(f=s.iata)))
        if not D:
            return self.render("One Hop", body + Page.not_found("airport", dst, d_sugg, lambda s: keep(t=s.iata)))
        if S is D:
            return self.render("One Hop", body + Page.error("From and To must be different airports."))

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
            return self.render("One Hop", body + Page.error(
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
        ranks = [("Shortest", "best"), ("2nd shortest", ""), ("3rd shortest", "")]
        cards = ""
        for (rank, css), p in zip(ranks, pairs[:3]):
            via = p["via"]
            info = (f"{S.iata} → {via.iata} ({p['airline1'].iata}) → {D.iata} ({p['airline2'].iata}): "
                    f"{p['total']:,.0f} mi")
            cards += (f"<button type='button' class='trip pick' data-key='{html.escape(via.iata)}' data-kind='airport' "
                      f"data-info='{html.escape(info)}'><div class='trip-top'><span class='trip-rank {css}'>{rank}</span>"
                      f"<span class='trip-total'>{p['total']:,.0f} mi<small>+{p['total'] - direct_mi:,.0f} mi vs straight line</small></span></div>"
                      f"<div class='trip-path'>"
                      f"<span class='stop'><b>{html.escape(S.iata)}</b><small>{html.escape(S.city)}</small></span>"
                      f"<span class='leg'><span class='al'>{html.escape(p['airline1'].iata)}</span><span class='line'></span>{p['leg1']:,.0f} mi</span>"
                      f"<span class='stop mid'><b>{html.escape(via.iata)}</b><small>{html.escape(via.city)}</small></span>"
                      f"<span class='leg'><span class='al'>{html.escape(p['airline2'].iata)}</span><span class='line'></span>{p['leg2']:,.0f} mi</span>"
                      f"<span class='stop'><b>{html.escape(D.iata)}</b><small>{html.escape(D.city)}</small></span>"
                      f"</div></button>")
        body += f"<div class='trips'>{cards}</div>"
        body += ("<p class='hint'>The cards above are the <b>shortest</b> trips. The globe and the table below show the "
                 "<b>top 5 connecting cities by number of route pairs</b> (the busiest places to change planes), "
                 "which are not always on the shortest path.</p>")
        body += Page.globe(f"<b>Top {len(top5)}</b> intermediate cities between "
                           f"{html.escape(S.iata)} and {html.escape(D.iata)}",
                           "Click a trip card or any row to show that connection on the globe (click again to go back to the top 5).")

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
        return self.render("One Hop", body, globe)

    # ---------------------------------------------------------------- Charts
    @staticmethod
    def bar_chart(title, sub, items, unit="", highlight=None, empty="No data."):
        """items: [(label, value, tooltip[, key])] - one series, one hue, value at the bar end.
        With highlight set, rows whose key differs are dimmed so the chosen one stands out."""
        top = max((it[1] for it in items), default=1) or 1
        rows = ""
        for it in items:
            label, value, tip = it[:3]
            dim = " dim" if highlight and (len(it) < 4 or it[3] != highlight) else ""
            pct = 100 * value / top
            rows += (f"<div class='bar-row{dim}'><div class='lbl' title='{html.escape(label)}'>{html.escape(label)}</div>"
                     f"<div class='bar-track'><div class='tip'>{html.escape(tip)}</div>"
                     f"<div class='bar' style='width:calc({pct:.2f}% - 60px * {pct / 100:.3f})'></div>"
                     f"<span class='bar-val' style='left:calc({pct:.2f}% - 60px * {pct / 100:.3f})'>{value:,}{unit}</span>"
                     f"</div></div>")
        if not items:
            rows = f"<p class='count'>{html.escape(empty)}</p>"
        return f"<div class='chart'><h3>{html.escape(title)}</h3><p class='csub'>{html.escape(sub)}</p>{rows}</div>"

    @staticmethod
    def stacked_chart(title, sub, items, highlight=None):
        """items: [(label, domestic, international, key)] - two-part bars with a legend and both numbers."""
        top = max((d + i for _, d, i, _ in items), default=1) or 1
        rows = ""
        for label, d, i, key in items:
            dim = " dim" if highlight and key != highlight else ""
            wd, wi = 100 * d / top, 100 * i / top
            share = 100 * i / (d + i) if d + i else 0
            rows += (f"<div class='bar-row{dim}'><div class='lbl' title='{html.escape(label)}'>{html.escape(label)}</div>"
                     f"<div class='bar-track stack'><div class='tip'>{html.escape(label)}: {d:,} domestic, {i:,} international "
                     f"({share:.0f}% international)</div>"
                     f"<span class='seg dom' style='width:calc({wd:.2f}% - 96px * {wd / 100:.3f})'></span>"
                     f"<span class='seg intl' style='width:calc({wi:.2f}% - 96px * {wi / 100:.3f})'></span>"
                     f"<span class='seg-val'>{d:,} · {i:,}</span></div></div>")
        legend = ("<div class='legend'><span><i class='sw dom'></i>Domestic (same country)</span>"
                  "<span><i class='sw intl'></i>International</span></div>")
        return (f"<div class='chart'><h3>{html.escape(title)}</h3><p class='csub'>{html.escape(sub)}</p>"
                f"{legend}{rows}</div>")

    @staticmethod
    def column_chart(title, sub, items):
        """items: [(label, value, tooltip)] - vertical columns for an ordered distribution."""
        top = max((v for _, v, _ in items), default=1) or 1
        cols = "".join(
            f"<div class='col'><span class='cval'>{v:,}</span>"
            f"<span class='cbar' style='height:{max(100 * v / top, 0.8):.1f}%' title='{html.escape(tip)}'></span>"
            f"<span class='clbl'>{html.escape(lbl)}</span></div>" for lbl, v, tip in items)
        cols += ""
        return (f"<div class='chart'><h3>{html.escape(title)}</h3><p class='csub'>{html.escape(sub)}</p>"
                f"<div class='cols'>{cols}</div></div>")

    def charts(self, query):
        code = query.get("airline", [""])[0].strip().upper()
        al = self.db.get_airline(code) if code else None
        s = self.db.stats(al)
        key = al.iata if al else None
        lg = s["longest"]
        short = lambda n: n.replace(" Air Lines", "").replace(" Airlines", "").replace(" Airways", "").strip() or n
        btns = [("All airlines", "/charts", not al)] + [
            (f"{a.iata} {short(a.name)}", f"/charts?airline={a.iata}", al is a) for a in self.db.all_airlines()]
        bar = ("<div class='chips filter-row'><span class='lbl'>Show:</span>"
               + "".join(f"<a class='fchip{' on' if on else ''}' href='{u}'>{html.escape(t)}</a>" for t, u, on in btns)
               + "</div>")
        who_plain = al.name if al else "All airlines"
        who = html.escape(who_plain)
        tiles = [(f"{s['n_routes']:,}", "Routes (one direction each)"),
                 (f"{s['n_airports']:,}", "Airports served"),
                 (f"{s['n_countries']}", "Countries served"),
                 (f"{s['avg_miles']:,.0f} mi", "Average route length"),
                 (f"{lg[2]:,.0f} mi" if lg else "-", f"Longest: {lg[0].iata} → {lg[1].iata}" if lg else "Longest route")]
        if not al:
            tiles.insert(0, (f"{len(self.db.airlines_by_iata)}", "Airlines"))
        body = (f"<h2>Charts</h2>{bar}<h3 class='who'>{who}</h3><div class='tiles'>"
                + "".join(f"<div class='tile'><div class='v'>{html.escape(v)}</div><div class='l'>{html.escape(l)}</div></div>"
                          for v, l in tiles) + "</div><div class='grid2 cgrid'>")
        body += self.bar_chart("Routes per airline", "Number of routes each airline flies",
                               [(f"{a.iata} {short(a.name)}", n, f"{a.name}: {n:,} routes", a.iata)
                                for a, n in s["routes_per_airline"]], highlight=key)
        body += self.stacked_chart("Domestic vs international", "Routes inside one country compared with routes "
                                   "between countries",
                                   [(f"{a.iata} {short(a.name)}", d, i, a.iata) for a, d, i in s["domestic_split"]],
                                   highlight=key)
        body += self.bar_chart("Busiest airports", f"Top 15 by routes to or from the airport · {who_plain}",
                               [(f"{a.iata} {a.city}", n, f"{a.name}: {n:,} routes") for a, n in s["busiest_airports"]])
        body += self.column_chart("Route lengths", f"Airport-to-airport connections by distance in air miles (k = 1,000) · {who_plain}",
                                  [(f"{lbl}", n, f"{n:,} connections, {lbl} miles") for lbl, n in s["length_buckets"]])
        body += self.bar_chart("Longest routes", f"Top 10 by air miles (both directions counted once) · {who_plain}",
                               [(f"{a.iata} ⇄ {b.iata}  {', '.join(sorted(als))}", round(mi),
                                 f"{a.city} ⇄ {b.city} · {', '.join(sorted(als))} · {mi:,.0f} mi")
                                for a, b, mi, als in s["longest_routes"]], unit=" mi")
        body += self.bar_chart("Top countries outside the US", f"Routes arriving in each foreign country · {who_plain}",
                               [(c, n, f"{c}: {n:,} routes") for c, n in s["foreign_countries"]],
                               empty="This airline has no international routes.")
        body += "</div>"
        return self.render("Charts", body)

    # ---------------------------------------------------------------- Edit Data
    def edit_page(self, query):
        q = lambda k: query.get(k, [""])[0].strip()
        msg, err = q("msg"), q("err")
        al_code, ap_code = q("airline").upper(), q("airport").upper()
        body = ("<h2>Edit Data</h2>"
                "<p class='hint'>Changes you make here affect <b>only your current browser session</b>. "
                "Other visitors always see the original data, and your changes disappear when you close "
                "the browser or click Reset.</p>")
        if msg:
            body += f"<p class='ok'>{html.escape(msg)}</p>"
        if err:
            body += f"<p class='err-box'>{html.escape(err)}</p>"

        nice = {"icao": "ICAO", "utc_offset": "UTC offset", "dst": "DST", "altitude": "Altitude (ft)"}

        def field(name, label, value, readonly=False):
            ro = " readonly" if readonly else ""
            return (f"<label>{html.escape(label)}<input name='{name}' value='{html.escape(value)}'{ro}></label>")

        # airline editor
        panel = ("<div class='panel'><h3>Edit an airline</h3>"
                 "<form method='get' action='/edit'><label>Airline IATA code: "
                 f"<input type='text' name='airline' value='{html.escape(al_code)}'></label> <button>Open</button></form>")
        if al_code:
            a = self.db.get_airline(al_code)
            if not a:
                panel += Page.error(f"No airline with IATA code '{al_code}'.")
            else:
                panel += ("<form method='post' action='/edit'><input type='hidden' name='action' value='update_airline'>"
                          f"<input type='hidden' name='iata' value='{html.escape(a.iata)}'><div class='fields'>"
                          + field("id", "OpenFlights ID", a.id, True) + field("iata_ro", "IATA", a.iata, True)
                          + "".join(field(f, nice.get(f, f.replace("_", " ").title()), getattr(a, f)) for f in AviationDatabase.AIRLINE_EDITABLE)
                          + "</div><button>Save airline</button></form>")
        panel += "</div>"
        # airport editor
        panel2 = ("<div class='panel'><h3>Edit an airport</h3>"
                  "<form method='get' action='/edit'><label>Airport IATA code: "
                  f"<input type='text' name='airport' value='{html.escape(ap_code)}'></label> <button>Open</button></form>")
        if ap_code:
            a = self.db.get_airport(ap_code)
            if not a:
                panel2 += Page.error(f"No airport with IATA code '{ap_code}'.")
            else:
                panel2 += ("<form method='post' action='/edit'><input type='hidden' name='action' value='update_airport'>"
                           f"<input type='hidden' name='iata' value='{html.escape(a.iata)}'><div class='fields'>"
                           + field("id", "OpenFlights ID", a.id, True) + field("iata_ro", "IATA", a.iata, True)
                           + "".join(field(f, nice.get(f, f.replace("_", " ").title()), getattr(a, f)) for f in AviationDatabase.AIRPORT_EDITABLE)
                           + "</div><button>Save airport</button></form>")
        panel2 += "</div>"

        route_form = lambda action, title, extra, btn, cls="": (
            f"<div class='panel'><h3>{title}</h3><form method='post' action='/edit'>"
            f"<input type='hidden' name='action' value='{action}'><div class='fields'>"
            "<label>Airline (IATA)<input name='airline' placeholder='AA'></label>"
            "<label>From airport (IATA)<input name='src' placeholder='SJC'></label>"
            "<label>To airport (IATA)<input name='dst' placeholder='BOS'></label>"
            f"{extra}</div><button{cls}>{btn}</button></form></div>")
        add = route_form("add_route", "Add a route",
                         "<label>Stops<input name='stops' value='0'></label>"
                         "<label>Equipment (optional)<input name='equipment' placeholder='738'></label>", "Add route")
        delete = route_form("delete_route", "Delete a route", "", "Delete route", " class='danger'")

        if self.in_session and self.db.edits:
            items = "".join(f"<li>{html.escape(e)}</li>" for e in self.db.edits)
            changes = (f"<div class='panel'><h3>Your changes in this session ({len(self.db.edits)})</h3>"
                       f"<ul class='changes'>{items}</ul>"
                       "<form method='post' action='/edit'><input type='hidden' name='action' value='reset'>"
                       "<button class='danger'>Reset - go back to the original data</button></form></div>")
        else:
            changes = "<div class='panel'><h3>Your changes in this session</h3><p class='count'>No changes yet.</p></div>"
        body += changes + f"<div class='grid2'>{panel}{panel2}{add}{delete}</div>"
        return self.render("Edit Data", body)

    # ---------------------------------------------------------------- OO Code
    def code_page(self, _):
        path = os.path.abspath(__file__)
        with open(path, encoding="utf-8") as f:
            source = f.read()
        classes = []
        for node in ast.parse(source).body:
            if isinstance(node, ast.ClassDef):
                methods = [n.name for n in node.body if isinstance(n, ast.FunctionDef)]
                doc = (ast.get_docstring(node) or "").strip().split("\n")[0]
                classes.append((node.name, doc, methods))
        cards = "".join(
            f"<div class='cls'><h4>class {html.escape(n)}</h4>"
            + (f"<p>{html.escape(d)}</p>" if d else "")
            + "".join(f"<code>{html.escape(m)}()</code>" for m in ms) + "</div>"
            for n, d, ms in classes)
        body = (f"<h2>Object-Oriented Code</h2>"
                f"<p class='hint'>The whole application is one Python file, <b>app.py</b> "
                f"({source.count(chr(10)):,} lines, {len(classes)} classes), using only the Python standard library.</p>"
                f"<h3>Classes</h3><div class='class-list'>{cards}</div>"
                f"<details class='src' open><summary>Full source code: app.py</summary>"
                f"<pre class='code'><code class='language-python'>{html.escape(source)}</code></pre></details>")
        head = ("<link rel='stylesheet' href='https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github.min.css'>"
                "<script src='https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js'></script>")
        js = "if (window.hljs) { document.querySelectorAll('pre.code code').forEach(function(b){ hljs.highlightElement(b); }); }"
        return self.render("OO Code", body, extra_js=js, extra_head=head)

    # ---------------------------------------------------------------- Contact
    def contact(self, _):
        mail = (f"<div class='row'><a class='btn-mail' href='mailto:{html.escape(CONTACT_EMAIL)}'>Email me</a>"
                f"<span>{html.escape(CONTACT_EMAIL)}</span></div>") if CONTACT_EMAIL else ""
        body = ("<h2>Contact</h2><div class='contact-card'>"
                f"<p>Questions about this project or interested in working together? I'd be glad to hear from you.</p>"
                f"<div class='row'><a class='btn-li' href='{LINKEDIN_URL}' target='_blank' rel='noopener'>"
                f"Connect on LinkedIn</a></div>{mail}"
                f"<p class='project'><b>{html.escape(STUDENT_NAME)}</b><br>CIS 51, De Anza College &middot; Cupertino, CA</p>"
                "</div>")
        return self.render("Contact", body)

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
        return self.render("About", body)

    def get_id(self, _):
        body = ("<h2>2.3 Site Owner</h2>"
                + Page.entity(["Name", "De Anza Student ID"], [STUDENT_NAME, STUDENT_ID]))
        return self.render("Get ID", body)


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------
class RequestHandler(BaseHTTPRequestHandler):
    """HTTP layer: picks the visitor's data (shared or session copy) and serves GET/POST requests."""
    base_db = None   # shared, never modified - set in main()
    sessions = None  # SessionStore - set in main()

    def session_id(self):
        for part in self.headers.get("Cookie", "").split(";"):
            k, _, v = part.strip().partition("=")
            if k == "sid":
                return v
        return None

    def app_for_request(self):
        db = self.sessions.get(self.session_id())
        return AviationWebApp(db or self.base_db, in_session=db is not None)

    def do_GET(self):
        url = urlparse(self.path)
        path = url.path.rstrip("/") or "/"
        if path == "/photo":
            return self.send_image(find_photo())
        if path == "/hero":
            return self.send_image(find_hero())
        if path == "/api/lookup.json":
            data = json.dumps(self.app_for_request().db.lookup_data()).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)
            return
        status, page = self.app_for_request().handle(path, parse_qs(url.query))
        data = page.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_POST(self):
        if (urlparse(self.path).path.rstrip("/") or "/") != "/edit":
            self.send_error(404)
            return
        length = min(int(self.headers.get("Content-Length") or 0), 100_000)
        form = {k: v[0] for k, v in parse_qs(self.rfile.read(length).decode("utf-8"),
                                             keep_blank_values=True).items()}
        action = form.get("action", "")
        sid = self.session_id()
        new_cookie = None
        back = {}
        if action == "reset":
            self.sessions.reset(sid)
            back["msg"] = "All your changes were removed. You are seeing the original data again."
        else:
            db = self.sessions.get(sid)
            if db is None:
                sid, db = self.sessions.create()
                new_cookie = sid
            msg, err, extra = EditActions.run(db, action, form)
            back.update(extra)
            if msg:
                back["msg"] = msg
            if err:
                back["err"] = err
                back.pop("msg", None)
        location = "/edit?" + urlencode({k: v for k, v in back.items() if v})
        self.send_response(303)
        self.send_header("Location", location)
        if new_cookie:
            # no Expires/Max-Age: a browser-session cookie, gone when the browser closes
            self.send_header("Set-Cookie", f"sid={new_cookie}; Path=/; HttpOnly; SameSite=Lax")
        self.send_header("Content-Length", "0")
        self.end_headers()


    def send_image(self, photo):
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
    RequestHandler.base_db = db
    RequestHandler.sessions = SessionStore(db)
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
