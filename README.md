# Airline Route Access

Air Travel Database web application (CIS 51 Vibe Coding assignment).

## Run locally

Requires Python 3.8 or newer. No extra packages.

```
python app.py
```

Then open http://localhost:8080 in a browser. Press Ctrl+C to stop.

## Before submitting

Open `student_info.py` and fill in `STUDENT_NAME` and `STUDENT_ID` (used by report 2.3).

## Features

- 1.1 Airline lookup by IATA code
- 1.2 Airport lookup by IATA code
- 2.1a Airports served by an airline, ordered by # routes
- 2.1b Airlines serving an airport, ordered by # routes
- 2.2a All airlines ordered by IATA code (live search by name, country, code, callsign)
- 2.2b All airports ordered by IATA code (live search by city, country, name, code; filter by country and by airline served)
- 2.3 Site owner name and student ID
- One Hop Routes (Additional 1): From/To airports + airline choice (any mix, same airline, or one specific airline); all non-stop route pairs S->X->D ordered by total GPS air miles; top 5 intermediate cities shown and labelled on the globe
- About page with LinkedIn link. To show your photo, put a file named photo.jpg (or photo.png) next to app.py
- Animated home-page illustration (airliner taking off past an airport)
- 3D globe (pages 1.2, 2.1a, 2.1b, One Hop): click a table row to show its routes as animated arcs; hover an arc for its air-mile distance. Needs internet (loads globe.gl from cdn.jsdelivr.net).

## Files

- `student_info.py` - your name and student ID
- `app.py` - the whole application (classes: Airline, Airport, Route, AviationDatabase, Page, AviationWebApp)
- `data/` - SB-airlines.txt, SB-airports.txt, SB-routes.txt (OpenFlights format)
