"""Declared-law schematics accompanying the computed figures (not simulations)."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/papers/source/papers/elementary-holon-generation/figures'
# Recursively place the *new* computed field through a separated four-map IFS.
source=(OUT/'integrated-geometry.svg').read_text()
source=re.sub(r'<metadata>.*?</metadata>','',source,flags=re.S)
inner=source[source.index('>')+1:source.rindex('</svg>')]
parts=['<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" viewBox="0 0 1000 340"><rect width="1000" height="340" fill="white"/>',
       '<metadata>Four separated similarities of ratio 1/3; local face from integrated-geometry.svg; equal mass 4^-depth; this hierarchy is supplied, not learned.</metadata>',
       '<defs><symbol id="field" viewBox="-5 -5 10 10">'+inner+'</symbol></defs>']
for depth in range(3):
    x0=15+depth*330;y0=43;side=290
    parts.append(f'<text x="{x0}" y="22" font-family="serif" font-size="20">Depth {depth} · {4**depth} fields · mass 1/{4**depth}</text>')
    cells=[(x0,y0,side)]
    for _ in range(depth):cells=[(x+s*a/3,y+s*b/3,s/3) for x,y,s in cells for a in (0,2) for b in (0,2)]
    for x,y,s in cells:parts.append(f'<use xlink:href="#field" x="{x}" y="{y}" width="{s}" height="{s}"/>')
    parts.append(f'<rect x="{x0}" y="{y0}" width="{side}" height="{side}" fill="none" stroke="#999" stroke-width=".5"/>')
parts.append('</svg>');(OUT/'recursive-field.svg').write_text(''.join(parts))

out=['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1100 340"><defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="#222"/></marker></defs><rect width="1100" height="340" fill="white"/>']
def line(d,stroke='#222',w=2,dash='',arrow=False):
    out.append(f'<path d="{d}" fill="none" stroke="{stroke}" stroke-width="{w}" stroke-dasharray="{dash}"'+(' marker-end="url(#arrow)"' if arrow else '')+'/>')
def text(x,y,s,size=16):out.append(f'<text x="{x}" y="{y}" font-family="serif" font-size="{size}">{s}</text>')
for offset,label in [(0,'Leader: material and admissible pathways change'),(560,'Return: current in the changed material')]:
    text(offset+10,22,label,19)
    for x,y,rx,ry in [(90,78,60,23),(235,73,74,27),(390,80,66,23),(170,287,110,29),(364,283,76,24)]:
        out.append(f'<ellipse cx="{offset+x}" cy="{y}" rx="{rx}" ry="{ry}" fill="none" stroke="#444" stroke-width="1.1"/>')
        out.append(f'<ellipse cx="{offset+x}" cy="{y}" rx="{rx*.67}" ry="{ry*.60}" fill="none" stroke="#999" stroke-width=".6"/>')
    paths=[f'M{offset+234} 100 C{offset+200} 127 {offset+305} 133 {offset+261} 175 S{offset+195} 218 {offset+199} 260',f'M{offset+258} 166 C{offset+324} 166 {offset+331} 207 {offset+351} 261',f'M{offset+221} 217 C{offset+133} 205 {offset+159} 179 {offset+107} 137',f'M{offset+249} 138 C{offset+147} 149 {offset+161} 103 {offset+97} 99']
    for d in paths:line(d,'#444',2 if offset==0 else 5)
    if offset==0:
        line('M107 137 Q73 165 105 203','#777',1,'4 4')
        line('M351 261 Q392 242 442 226','#777',1,'4 4')
        out.append('<circle cx="107" cy="137" r="22" fill="none" stroke="#777" stroke-dasharray="3 4"/>')
        text(14,179,'ionization front',15);text(18,199,'oriented drift + diffusion',14)
        text(286,230,'conductivity and storage',14);text(286,248,'alter the next current',14)
        line('M190 325 L450 325','#222',1.2,arrow=True);text(55,328,'E, n, σ, C',15)
    else:
        line('M763 253 C751 218 812 204 817 179 S775 136 793 106','#222',1.3,arrow=True)
        text(565,167,'counterpropagating',14);text(565,185,'voltage/current waves',14)
        text(904,217,'RI² + GV²',18);text(904,235,'dissipation',14)
        for x,y in [(817,181),(775,225),(896,236)]:out.append(f'<circle cx="{x}" cy="{y}" r="9" fill="white" stroke="#777" stroke-width="1"/>')
        text(584,325,'same channel geometry · changed material law',15)
text(480,184,'→',38)
out.append('</svg>');(OUT/'leader-and-return.svg').write_text(''.join(out))
