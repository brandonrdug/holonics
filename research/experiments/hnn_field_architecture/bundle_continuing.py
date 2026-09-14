"""Package calculated receiver frames. Black is zero received signal; display gamma is fixed."""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,base64
from io import BytesIO
import numpy as np
from PIL import Image
from continuing_field import CENTERS,AXES,numeric_twist
HERE=Path(__file__).parent
p=argparse.ArgumentParser();p.add_argument('rendered',type=Path);p.add_argument('output',type=Path);args=p.parse_args()
model=json.loads((HERE/'continuing-field.json').read_text());report=json.loads((args.rendered/'frames.json').read_text());states={s['index']:s for s in model['states']}
frames=[];export=[]
cy,sy=15/17,8/17;cx,sx=4/5,3/5
rot=np.array([[cy,sy*sx,sy*cx],[0,cx,-sx],[-sy,cy*sx,cy*cx]])
for f in report['frames']:
    source=states[f['index']]
    rgba=np.asarray(Image.open(args.rendered/f['image']).convert('RGBA'),dtype=float)/255
    # Fixed radiometric display transfer; no framewise normalization or new source dynamics.
    radiance=np.clip(rgba[...,:3]*rgba[...,3:4],0,1)
    gain=float(Q(model['optical_receiver']['display_gain']));gamma=float(Q(model['optical_receiver']['display_gamma']))
    rgb=(1-np.exp(-gain*radiance))**(1/gamma)
    image=Image.fromarray(np.uint8(np.round(rgb*255)),'RGB');export.append(image)
    buffer=BytesIO();image.save(buffer,format='WEBP',quality=91,method=6)
    curves=[]
    for i,(center,axis) in enumerate(zip(CENTERS,AXES)):
        t=np.linspace(0,2*np.pi,641);theta=2*t;phi=3*t
        points=np.tile(np.array(center,float),(len(t),1));points[:,axis]+=np.sin(phi)/3
        points[:,(axis+1)%3]+=(2+np.cos(phi)/3)*np.cos(theta);points[:,(axis+2)%3]+=(2+np.cos(phi)/3)*np.sin(theta)
        for item in source['word']:numeric_twist(points,item['axis'],float(Q(item['parameter'])))
        points=points@rot.T;face=np.stack([24*points[:,0]/(24-points[:,2]),24*points[:,1]/(24-points[:,2])],axis=1)
        ink=np.round(face*1000).astype('<i2');curves.append(base64.b64encode(ink.tobytes()).decode())
    frames.append(dict(index=f['index'],clock=source['clock'],image='data:image/webp;base64,'+base64.b64encode(buffer.getvalue()).decode(),curves=curves))
fragment=(HERE/'continuing.template.html').read_text().replace('@@FRAMES@@',json.dumps(frames,separators=(',',':')))
assert len(fragment.encode())<1_000_000
args.output.write_text(fragment)
export[-1].save(HERE/'continuing-field.png')
export[0].save(HERE/'continuing-field-motion.png',save_all=True,append_images=export[1:],duration=120,loop=1,disposal=0,blend=0)
print(args.output,len(fragment.encode()),'bytes',len(frames),'computed frames')
