"""Lossless playback of computed woven/lobe receiver slices; no tweened states."""
from pathlib import Path
from io import BytesIO
import cairosvg
from PIL import Image
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/papers/rendered/receiver-engraving'
for name,keys in (('woven-motion',('woven_0','woven_6','woven_12')),('conformation-motion',('lobes_0','lobes_2','lobes_4'))):
    frames=[]
    for key in keys:
        raw=cairosvg.svg2png(url=str(OUT/f'{key}.svg'),output_width=1000)
        frames.append(Image.open(BytesIO(raw)).convert('RGB'))
    target=OUT/f'{name}.png'
    frames[0].save(target,save_all=True,append_images=frames[1:],duration=[800,800,1800],loop=0,disposal=0,blend=0)
    with Image.open(target) as check:
        assert check.n_frames==len(frames)
        for i,frame in enumerate(frames):check.seek(i);assert check.convert('RGB').tobytes()==frame.tobytes()
    print(target.name,'three computed frames; lossless decoded comparison passed')
