# Shared wireframe vocabulary for the Holonic CAD design canvas.
# Matches the existing artboards' vocabulary: Instrument Sans / STIX Two Text / IBM Plex Mono,
# paper #f6f2ea, ink #292418, species colours transport #3c6ea5, face #a67a2e,
# construction #3e7d57, quotient #9c5480, refused #56503f.
import html as _html

FONT_LINK = ("https://fonts.googleapis.com/css2?family=Instrument+Sans:wght@400;500;600"
             "&family=STIX+Two+Text:ital,wght@0,400;0,600;1,400&family=IBM+Plex+Mono:wght@400;500&display=swap")

CSS = """
    body { margin: 0; background: #f6f2ea; color: #292418; font-family: 'Instrument Sans', 'Segoe UI', system-ui, sans-serif; font-size: 12px; }
    a { color: #8a5a1c; } a:hover { color: #6d4614; }
    .mono { font-family: 'IBM Plex Mono', 'Menlo', monospace; }
    .math { font-family: 'STIX Two Text', 'Georgia', serif; font-style: italic; }
    .serif { font-family: 'STIX Two Text', 'Georgia', serif; }
    .h1 { font-family: 'STIX Two Text', 'Georgia', serif; font-weight: 600; font-size: 22px; white-space: nowrap; flex: 0 0 auto; }
    .sub { font-size: 12px; color: #7a7060; flex: 1 1 auto; min-width: 0; }
    .meta { font-family: 'IBM Plex Mono', monospace; font-size: 10px; color: #7a7060; }
    .lbl { font-family: 'IBM Plex Mono', monospace; font-size: 9px; letter-spacing: 0.08em; text-transform: uppercase; color: #7a7060; }
    .panel { background: #fffdf8; border: 1.5px solid #8a8071; border-radius: 6px; padding: 8px 10px; box-sizing: border-box; display: flex; flex-direction: column; gap: 6px; min-height: 0; min-width: 0; overflow: hidden; }
    .panel-t { font-family: 'IBM Plex Mono', monospace; font-size: 9.5px; letter-spacing: 0.08em; text-transform: uppercase; color: #56503f; border-bottom: 1px solid #ddd5c5; padding-bottom: 4px; display: flex; justify-content: space-between; gap: 8px; }
    .tb { background: #efece4; border: 1px solid #d9d0bf; border-radius: 6px; padding: 5px 8px; display: flex; gap: 6px; align-items: center; flex-wrap: wrap; }
    .btn { min-height: 26px; padding: 3px 9px; border-radius: 6px; background: #fffdf8; border: 1.5px solid #8a8071; font-family: 'IBM Plex Mono', monospace; font-size: 10px; display: inline-flex; align-items: center; gap: 5px; }
    .btn-on { background: #292418; color: #fbf8f2; border-color: #292418; }
    .ph { background: repeating-linear-gradient(135deg, #efece4 0 6px, #f6f2ea 6px 12px); border: 1px dashed #b3a27d; border-radius: 4px; }
    .box { border-radius: 6px; padding: 6px 9px; box-sizing: border-box; font-size: 11.5px; line-height: 1.4; }
    .box-hyp { background: #efece4; border: 1px solid #d9d0bf; }
    .box-goal { background: #fffdf8; border: 1.5px solid #a67a2e; }
    .box-lean { background: #fffdf8; border: 1.5px solid #8a8071; }
    .box-carried { background: #eef3ee; border: 1.5px solid #3e7d57; }
    .box-obstructed { background: #f5ecef; border: 1.5px dashed #9c5480; }
    .box-refused { background: #eeece7; border: 1.5px dashed #56503f; }
    .box-type { background: #fffdf8; border: 1.5px solid #29426b; }
    .sp { font-family: 'IBM Plex Mono', monospace; font-size: 9px; letter-spacing: 0.06em; text-transform: uppercase; border-radius: 4px; padding: 2px 6px; color: #fbf8f2; display: inline-block; white-space: nowrap; }
    .sp-transport { background: #3c6ea5; } .sp-warn { background: #b3a27d; color: #292418; } .sp-face { background: #a67a2e; } .sp-construction { background: #3e7d57; } .sp-quotient { background: #9c5480; } .sp-refused { background: #56503f; } .sp-deposit { background: #29426b; } .sp-receiver { background: #7a7060; }
    .tag { font-family: 'IBM Plex Mono', monospace; font-size: 9px; letter-spacing: 0.06em; border-radius: 4px; padding: 1px 6px; display: inline-block; border: 1px solid #b3a27d; color: #56503f; background: #f6f2ea; white-space: nowrap; }
    .grade { font-family: 'IBM Plex Mono', monospace; font-size: 9px; border-radius: 4px; padding: 1px 6px; display: inline-block; background: #292418; color: #fbf8f2; white-space: nowrap; }
    .ln { font-family: 'IBM Plex Mono', monospace; font-size: 10.5px; color: #29426b; }
    .code { font-family: 'IBM Plex Mono', monospace; font-size: 10.5px; line-height: 1.5; white-space: pre; background: #fbf8f2; border: 1px solid #ddd5c5; border-radius: 4px; padding: 6px 8px; overflow: hidden; }
    table.tb2 { border-collapse: collapse; font-size: 10.5px; width: 100%; }
    table.tb2 td, table.tb2 th { border: 1px solid #ddd5c5; padding: 3px 6px; text-align: left; vertical-align: top; }
    table.tb2 th { font-family: 'IBM Plex Mono', monospace; font-size: 9px; text-transform: uppercase; color: #7a7060; background: #efece4; }
    .kv { display: grid; grid-template-columns: max-content 1fr; gap: 2px 10px; font-size: 11px; }
    .kv .k { font-family: 'IBM Plex Mono', monospace; font-size: 10px; color: #56503f; }
    .kv > div { min-width: 0; overflow-wrap: anywhere; }
    .row { display: flex; gap: 10px; min-height: 0; min-width: 0; }
    .row > * { min-width: 0; }
    .col { display: flex; flex-direction: column; gap: 8px; min-height: 0; min-width: 0; }
    .note { font-size: 11px; color: #56503f; line-height: 1.45; }
    .typ { background: #fffdf8; border: 1.5px solid #29426b; border-radius: 6px; padding: 6px 9px; box-sizing: border-box; font-size: 11px; display: flex; flex-direction: column; gap: 3px; }
    .typ .tn { font-family: 'IBM Plex Mono', monospace; font-size: 11px; font-weight: 500; color: #29426b; }
    .typ .tf { font-family: 'IBM Plex Mono', monospace; font-size: 10px; color: #292418; padding-left: 10px; line-height: 1.45; }
    .typ .tm { font-size: 10.5px; color: #7a7060; }
    .arrow { font-family: 'IBM Plex Mono', monospace; color: #3c6ea5; }
    .wire { stroke: #3c6ea5; stroke-width: 1.5; fill: none; }
    .ink { stroke: #292418; stroke-width: 1.5; fill: none; }
    .grey { stroke: #8a8071; stroke-width: 1; fill: none; }
    .fill-paper { fill: #fffdf8; }
    .svgtxt { font-family: 'IBM Plex Mono', monospace; font-size: 9px; fill: #56503f; }
    .svgmath { font-family: 'STIX Two Text', 'Georgia', serif; font-style: italic; font-size: 11px; fill: #292418; }
"""

def esc(s): return _html.escape(s, quote=False)

def artboard(title, subtitle, w, h, body, meta="", extra_css=""):
    return f"""<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <script src="./support.js"></script>
</head>
<body>
<x-dc>
<helmet>
  <link rel="stylesheet" href="{FONT_LINK}">
  <style>{CSS}{extra_css}
  </style>
</helmet>
<div style="width: {w}px; height: {h}px; box-sizing: border-box; padding: 18px 22px; overflow: hidden; display: flex; flex-direction: column; gap: 10px; background: #f6f2ea">
  <div style="display: flex; align-items: baseline; justify-content: space-between; gap: 16px">
    <div style="display: flex; align-items: baseline; gap: 14px; min-width: 0">
      <div class="h1">{title}</div>
      <div class="sub">{subtitle}</div>
    </div>
    <div class="meta" style="text-align: right; flex: 0 1 520px; max-width: 520px">{meta}</div>
  </div>
{body}
</div>
</x-dc>
</body>
</html>
"""

def panel(title, body, style="", right=""):
    r = f'<span>{right}</span>' if right else ''
    return f'<div class="panel" style="{style}"><div class="panel-t"><span>{title}</span>{r}</div>{body}</div>'

def toolbar(items, style=""):
    return '<div class="tb" style="%s">%s</div>' % (style, ''.join(items))

def btn(label, on=False, style=""):
    return f'<div class="btn{" btn-on" if on else ""}" style="{style}">{label}</div>'

def sp(kind, text=None):
    return f'<span class="sp sp-{kind}">{text or kind}</span>'

def tag(t): return f'<span class="tag">{t}</span>'
def grade(g): return f'<span class="grade">{g}</span>'
def lbl(t): return f'<div class="lbl">{t}</div>'
def ph(h, w="100%", text="", style=""):
    return f'<div class="ph" style="height:{h}px; width:{w}; display:flex; align-items:center; justify-content:center; {style}"><span class="lbl">{text}</span></div>'

def box(kind, text, style=""):
    return f'<div class="box box-{kind}" style="{style}">{text}</div>'

def typ(name, fields, meaning="", src=""):
    fs = ''.join(f'<div class="tf">{f}</div>' for f in fields)
    m = f'<div class="tm">{meaning}</div>' if meaning else ''
    s = f'<div class="meta">{src}</div>' if src else ''
    return f'<div class="typ"><div class="tn">{name}</div>{fs}{m}{s}</div>'

def table(headers, rows, style=""):
    th = ''.join(f'<th>{h}</th>' for h in headers)
    trs = ''.join('<tr>' + ''.join(f'<td>{c}</td>' for c in r) + '</tr>' for r in rows)
    return f'<table class="tb2" style="{style}"><thead><tr>{th}</tr></thead><tbody>{trs}</tbody></table>'

def kv(pairs):
    return '<div class="kv">' + ''.join(f'<div class="k">{k}</div><div>{v}</div>' for k, v in pairs) + '</div>'

def code(text, style=""):
    return f'<div class="code" style="{style}">{esc(text)}</div>'

def note(text, style=""):
    return f'<div class="note" style="{style}">{text}</div>'

def row(children, style="", gap=10):
    return f'<div class="row" style="gap:{gap}px; {style}">' + ''.join(children) + '</div>'

def col(children, style="", gap=8):
    return f'<div class="col" style="gap:{gap}px; {style}">' + ''.join(children) + '</div>'

def svg(w, h, inner, style=""):
    return f'<svg width="{w}" height="{h}" viewBox="0 0 {w} {h}" style="display:block; {style}" xmlns="http://www.w3.org/2000/svg">{inner}</svg>'

# --- SVG primitives for wireframe diagrams ---
def s_rect(x, y, w, h, cls="ink", r=3, extra=""):
    return f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{r}" class="{cls}" {extra}/>'
def s_line(x1, y1, x2, y2, cls="ink", extra=""):
    return f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" class="{cls}" {extra}/>'
def s_circ(cx, cy, r, cls="ink", extra=""):
    return f'<circle cx="{cx}" cy="{cy}" r="{r}" class="{cls}" {extra}/>'
def s_text(x, y, t, cls="svgtxt", extra=""):
    return f'<text x="{x}" y="{y}" class="{cls}" {extra}>{esc(t)}</text>'
def s_path(d, cls="ink", extra=""):
    return f'<path d="{d}" class="{cls}" {extra}/>'
def s_arrow_defs(sfx=""):
    return ('<defs><marker id="ah'+sfx+'" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
            '<path d="M 0 0 L 10 5 L 0 10 z" fill="#3c6ea5"/></marker>'
            '<marker id="ahk'+sfx+'" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
            '<path d="M 0 0 L 10 5 L 0 10 z" fill="#292418"/></marker></defs>')
