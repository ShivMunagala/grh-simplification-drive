#!/usr/bin/env python3
"""Draw the three dials over time from metrics/history.csv and refresh the block in README.md.

  tools/chart.py            write metrics/dials-light.svg, metrics/dials-dark.svg and the README block
  tools/chart.py --check    exit 1 if any of them is out of date (used by CI)

Each row of the history is one recorded change to the proof, with the time of its commit. The image
has one panel per dial, stacked on a shared time axis: a point where each commit happened, joined by
a stepped line because a dial keeps its value until the next change. The dials have different units,
so each panel has its own vertical axis; they are never drawn on one. No third-party packages needed.
"""
import argparse, csv, datetime, math, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HISTORY = os.path.join(ROOT, 'metrics', 'history.csv')
README = os.path.join(ROOT, 'README.md')
START, END = '<!-- dials:start -->', '<!-- dials:end -->'

# colours by role, light and dark
THEMES = {
    'light': {'surface': '#fcfcfb', 'ink': '#0b0b0b', 'ink2': '#52514e', 'muted': '#898781', 'grid': '#e1e0d9',
              'axis': '#c3c2b7', 'border': 'rgba(11,11,11,0.10)', 'accent': '#2a78d6', 'good': '#006300',
              'bad': '#d03b3b'},
    'dark': {'surface': '#1a1a19', 'ink': '#f0efec', 'ink2': '#c3c2b7', 'muted': '#898781', 'grid': '#2c2c2a',
             'axis': '#383835', 'border': 'rgba(255,255,255,0.10)', 'accent': '#3987e5', 'good': '#0ca30c',
             'bad': '#e66767'},
}
FONT = 'system-ui, -apple-system, &quot;Segoe UI&quot;, sans-serif'

DIALS = [
    ('source_tokens', 'Source size', 'tokens'),
    ('written_out_size', 'Written-out proof size', 'term nodes'),
    ('time_cpu_s', 'Time change', 'CPU seconds on recompiled files, running total'),
]


def compact(v):
    a = abs(v)
    for limit, suffix in ((1e9, 'B'), (1e6, 'M'), (1e3, 'K')):
        if a >= limit:
            x = v / limit
            return (f'{x:.2f}' if abs(x) < 10 else f'{x:.1f}') + suffix
    return f'{v:.1f}' if isinstance(v, float) and v != int(v) else f'{int(v)}'


def tick_label(v, step, top):
    """Label an axis tick with just enough decimals for neighbouring ticks to differ."""
    for limit, suffix in ((1e9, 'B'), (1e6, 'M'), (1e3, 'K'), (1, '')):
        if top >= limit:
            dec = max(0, min(6, math.ceil(-math.log10(step / limit) - 1e-9))) if step < limit else 0
            return f'{v / limit:.{dec}f}{suffix}'
    return f'{v:g}'


def nice_step(span):
    if span <= 0:
        return 1.0
    raw = span / 2.0
    mag = 10 ** math.floor(math.log10(raw))
    for m in (1, 2, 2.5, 5, 10):
        if raw <= m * mag:
            return m * mag
    return 10 * mag


def load(path=HISTORY):
    with open(path, newline='', encoding='utf-8') as fh:
        rows = list(csv.DictReader(fh))
    for r in rows:
        r['t'] = datetime.datetime.fromisoformat(r['time'].replace('Z', '+00:00'))
        r['source_tokens'] = int(r['source_tokens'])
        r['written_out_size'] = int(r['written_out_size'])
        r['time_cpu_s'] = float(r['time_cpu_s'])
        r['cone_declarations'] = int(r['cone_declarations'])
        r['cone_modules'] = int(r['cone_modules'])
    rows.sort(key=lambda r: r['t'])
    return rows


def delta_text(base, now):
    d = now - base
    if d == 0:
        return 'none', 'no change since baseline'
    direction = 'good' if d < 0 else 'bad'          # every dial is better when lower
    txt = f'{"▼" if d < 0 else "▲"} {compact(abs(d))}'
    if base:
        pct = 100.0 * d / base
        if abs(pct) >= 0.01:
            txt += f' ({abs(pct):.2f}%)'
    return direction, txt + ' since baseline'


def svg(rows, theme):
    t = THEMES[theme]
    W, PH, GAP, TOP, BOTTOM = 760, 150, 18, 8, 30
    X0, X1 = 70, 736                       # plot area, horizontal
    H = TOP + 3 * PH + 2 * GAP + BOTTOM
    base, now = rows[0], rows[-1]
    t0, t1 = rows[0]['t'], rows[-1]['t']
    if t1 == t0:
        t0, t1 = t0 - datetime.timedelta(hours=12), t1 + datetime.timedelta(hours=12)
    span_s = (t1 - t0).total_seconds()

    def xpos(when):
        return X0 + (X1 - X0) * (when - t0).total_seconds() / span_s

    summary = '; '.join(f'{label} {compact(now[key])}' for key, label, _ in DIALS)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" role="img" '
           f'font-family="{FONT}">',
           f'<title>Dials over time. Latest: {summary}</title>',
           f'<rect x="0.5" y="0.5" width="{W - 1}" height="{H - 1}" rx="8" fill="{t["surface"]}" stroke="{t["border"]}"/>']
    for k, (key, label, unit) in enumerate(DIALS):
        py = TOP + k * (PH + GAP)
        ya, yb = py + 40, py + PH - 8      # plot area, vertical (ya = top)
        vals = [r[key] for r in rows]
        lo, hi = min(vals), max(vals)
        if hi == lo:
            pad = max(abs(hi) * 0.01, 1.0)
            lo, hi = lo - pad, hi + pad
        step = nice_step(hi - lo)
        tlo, thi = math.floor(lo / step) * step, math.ceil(hi / step) * step
        ticks = []
        v = tlo
        while v <= thi + step * 1e-9:
            ticks.append(v)
            v += step

        def ypos(val):
            return yb - (yb - ya) * (val - tlo) / ((thi - tlo) or 1.0)

        # header: what it is on the left, where it stands on the right
        out.append(f'<text x="{X0}" y="{py + 22}" font-size="13" fill="{t["ink"]}" font-weight="600">{label}'
                   f'<tspan font-weight="400" fill="{t["muted"]}" dx="6">{unit}</tspan></text>')
        direction, dtxt = delta_text(base[key], now[key])
        dcol = {'good': t['good'], 'bad': t['bad'], 'none': t['muted']}[direction]
        value = (('+' if now[key] > 0 else '−' if now[key] < 0 else '') + compact(abs(now[key]))
                 if key == 'time_cpu_s' else compact(now[key]))
        out.append(f'<text x="{X1}" y="{py + 22}" font-size="12" text-anchor="end" fill="{dcol}">'
                   f'<tspan font-size="14" font-weight="600" fill="{t["ink"]}">{value}</tspan>'
                   f'<tspan dx="8">{dtxt}</tspan></text>')
        # gridlines and tick labels
        top = max(abs(tlo), abs(thi))
        for tv in ticks:
            y = ypos(tv)
            out.append(f'<line x1="{X0}" y1="{y:.1f}" x2="{X1}" y2="{y:.1f}" stroke="{t["grid"]}" stroke-width="1"/>')
            out.append(f'<text x="{X0 - 8}" y="{y + 4:.1f}" font-size="11" text-anchor="end" fill="{t["muted"]}" '
                       f'style="font-variant-numeric: tabular-nums">{tick_label(tv, step, top)}</text>')
        out.append(f'<line x1="{X0}" y1="{yb}" x2="{X1}" y2="{yb}" stroke="{t["axis"]}" stroke-width="1"/>')
        # stepped line through the commits
        pts = [(xpos(r['t']), ypos(r[key])) for r in rows]
        if len(pts) >= 2:
            d = [f'M{pts[0][0]:.1f},{pts[0][1]:.1f}']
            for (px, py_), (_, prev_y) in zip(pts[1:], pts[:-1]):
                d.append(f'L{px:.1f},{prev_y:.1f} L{px:.1f},{py_:.1f}')
            out.append(f'<path d="{" ".join(d)}" fill="none" stroke="{t["accent"]}" stroke-width="2" '
                       f'stroke-linejoin="round" stroke-linecap="round"/>')
        marks = pts if len(pts) <= 40 else [pts[0], pts[-1]]
        for px, py_ in marks:
            out.append(f'<circle cx="{px:.1f}" cy="{py_:.1f}" r="4" fill="{t["accent"]}" stroke="{t["surface"]}" '
                       f'stroke-width="2"/>')
    # shared time axis under the last panel
    axis_y = TOP + 3 * PH + 2 * GAP - 8
    fmt = '%d %b %H:%M' if span_s < 2 * 86400 else ('%d %b' if span_s < 300 * 86400 else '%b %Y')
    seen = set()
    n = 5
    for i in range(n):
        when = t0 + datetime.timedelta(seconds=span_s * i / (n - 1))
        lab = when.strftime(fmt)
        if lab in seen:
            continue
        seen.add(lab)
        x = xpos(when)
        anchor = 'start' if i == 0 else 'end' if i == n - 1 else 'middle'
        out.append(f'<line x1="{x:.1f}" y1="{axis_y}" x2="{x:.1f}" y2="{axis_y + 4}" stroke="{t["axis"]}" stroke-width="1"/>')
        out.append(f'<text x="{x:.1f}" y="{axis_y + 18}" font-size="11" text-anchor="{anchor}" fill="{t["muted"]}">{lab}</text>')
    out.append('</svg>')
    return '\n'.join(out) + '\n'


def readme_block(rows):
    base, now = rows[0], rows[-1]
    alt = ', '.join(f'{label.lower()} {compact(now[key])}' for key, label, _ in DIALS)
    lines = [START,
             '<picture>',
             '  <source media="(prefers-color-scheme: dark)" srcset="metrics/dials-dark.svg">',
             f'  <img alt="The three dials over time, one point per recorded commit. Latest: {alt}" '
             'src="metrics/dials-light.svg">',
             '</picture>',
             '',
             '| Dial | Baseline | Now | Change |',
             '|---|---:|---:|---:|']
    names = {'source_tokens': 'Source size (tokens)', 'written_out_size': 'Written-out proof size (term nodes)',
             'time_cpu_s': 'Time (CPU seconds on recompiled files, running total)'}
    for key, _, _ in DIALS:
        b, n = base[key], now[key]
        fmt = (lambda v: f'{v:,.1f}') if key == 'time_cpu_s' else (lambda v: f'{v:,}')
        d = n - b
        ch = '0' if d == 0 else ('−' if d < 0 else '+') + fmt(abs(d))
        lines.append(f'| {names[key]} | {fmt(b)} | {fmt(n)} | {ch} |')
    lines += ['',
              f'Cone: {now["cone_declarations"]:,} declarations in {now["cone_modules"]:,} files. '
              f'Recorded changes: {len(rows) - 1}. Latest row: {now["label"]} '
              f'({now["t"].strftime("%Y-%m-%d %H:%M UTC")}).',
              END]
    return '\n'.join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--preview', metavar='DIR', help='draw another history file into DIR; README untouched')
    ap.add_argument('--history', default=HISTORY)
    a = ap.parse_args()
    rows = load(a.history)
    if not rows:
        sys.exit('history has no rows')
    if a.preview:
        os.makedirs(a.preview, exist_ok=True)
        for th in THEMES:
            with open(os.path.join(a.preview, f'dials-{th}.svg'), 'w', encoding='utf-8') as fh:
                fh.write(svg(rows, th))
        print('preview written to', a.preview)
        return
    wanted = {os.path.join(ROOT, 'metrics', f'dials-{th}.svg'): svg(rows, th) for th in THEMES}
    with open(README, encoding='utf-8') as fh:
        readme = fh.read()
    if START not in readme or END not in readme:
        sys.exit('README.md has no dials block markers')
    wanted[README] = re.sub(re.escape(START) + r'.*?' + re.escape(END), lambda m: readme_block(rows), readme,
                            flags=re.S)
    stale = []
    for path, content in wanted.items():
        try:
            with open(path, encoding='utf-8') as fh:
                old = fh.read()
        except OSError:
            old = None
        if old != content:
            stale.append(os.path.relpath(path, ROOT))
            if not a.check:
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(content)
    if a.check and stale:
        print('out of date: ' + ', '.join(stale) + ' — run tools/chart.py and commit the result')
        sys.exit(1)
    print('up to date' if not stale else 'updated: ' + ', '.join(stale))


if __name__ == '__main__':
    main()
