"""Lossless APNG playback of the five actually computed receiver frames.

No interpolated states; the final pause/loop reset is presentation chronology.
Run with uv run --with cairosvg --with pillow python <this file>.
"""
from pathlib import Path
from io import BytesIO
import cairosvg
from PIL import Image
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'research/papers/rendered/receiver-engraving'
for name in ('trefoil_3_1','figure_eight_4_1','chain'):
    frames=[]
    for k in (0,6,12,18,24):
        png=cairosvg.svg2png(url=str(OUT/f'{name}_{k}.svg'),output_width=900,output_height=900)
        frames.append(Image.open(BytesIO(png)).convert('RGB'))
    target=OUT/f'{name}-motion.png'
    frames[0].save(target,save_all=True,append_images=frames[1:],duration=[600,600,600,600,1800],loop=0,disposal=0,blend=0)
    with Image.open(target) as check:
        assert check.n_frames==5
        for i,original in enumerate(frames):
            check.seek(i);assert check.convert('RGB').tobytes()==original.tobytes()
    print(target.name,'five lossless frames verified')
