"""Web/SVG face of the same compiled packet consumed by holonic-engraving."""
from fractions import Fraction as Q
from html import escape
import json

def scene_svg(scene,width_mm=Q(80),mode='phase',line_width_pt=Q(1,4)):
    assert mode in ('phase','mono')
    xmin,ymin,xmax,ymax=map(Q,scene['bounds'])
    sx,sy=xmax-xmin,ymax-ymin
    base=line_width_pt*Q(127,5)*sx/(72*width_mm)
    number=lambda q:repr(float(q))
    background='#000000' if mode=='phase' else '#ffffff'
    out=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{number(width_mm)}mm" height="{number(width_mm*sy/sx)}mm" viewBox="{number(xmin)} {number(-ymax)} {number(sx)} {number(sy)}">',
         '<metadata>'+escape(json.dumps({'meta':scene['meta'],'source_packet':scene.get('source_packet')},separators=(',',':')))+'</metadata>',
         f'<rect x="{number(xmin)}" y="{number(-ymax)}" width="{number(sx)}" height="{number(sy)}" fill="{background}"/>',
         '<g transform="scale(1,-1)">']
    for mark in scene['marks']:
        color='#000000' if mode=='mono' else '#'+''.join(f'{int(c*255):02x}' for c in mark['rgb'])
        width=base*Q(mark['width']);points=mark['points']
        source=escape(json.dumps(mark.get('faces',[])),quote=True)
        feature=escape(json.dumps({k:mark.get(k) for k in ('kind','feature','visible_span','source_station_parameter')},separators=(',',':')),quote=True)
        if mark['kind']=='stipple':
            for x,y in points[:1]:
                out.append(f'<circle cx="{number(x)}" cy="{number(y)}" r="{number(width/2)}" fill="{color}" data-faces="{source}" data-receiver-mark="{feature}"/>')
        else:
            coordinates=' '.join(f'{number(x)},{number(y)}' for x,y in points)
            out.append(f'<polyline points="{coordinates}" fill="none" stroke="{color}" stroke-width="{number(width)}" data-faces="{source}" data-receiver-mark="{feature}"/>')
    out+=['</g>','</svg>']
    return '\n'.join(out)+'\n'
