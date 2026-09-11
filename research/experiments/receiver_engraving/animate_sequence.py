"""Lossless playback of three actual cuts in the selected legal fold history."""
from pathlib import Path
from io import BytesIO
import cairosvg
from PIL import Image
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'research/papers/rendered/receiver-engraving'
frames=[]
for k in (0,8,16):
    raw=cairosvg.svg2png(url=str(OUT/f'fold_path_{k}.svg'),output_width=1000)
    frames.append(Image.open(BytesIO(raw)).convert('RGB'))
target=OUT/'sequence-fold-history.png'
frames[0].save(target,save_all=True,append_images=frames[1:],duration=[800,800,1800],loop=0,disposal=0,blend=0)
with Image.open(target) as check:
    assert check.n_frames==3
    for i,frame in enumerate(frames):check.seek(i);assert check.convert('RGB').tobytes()==frame.tobytes()
print('Three computed fold-history cuts; lossless frame comparison passed.')
