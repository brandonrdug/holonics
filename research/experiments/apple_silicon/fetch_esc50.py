"""Fetch the curated ESC-50 WAV release without executing a dataset loader.

Labels/folds are cold experimental metadata; this script does not construct native currents.
Run with the isolated Apple Python environment. Data stays under ignored .local/datasets.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import shutil
import wave
import zipfile
from huggingface_hub import HfApi, hf_hub_download

parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, default=Path('.local/datasets/esc50'))
parser.add_argument('--revision', help='Immutable Hugging Face dataset revision; resolves current once if omitted')
args = parser.parse_args()
repo = 'yangwang825/esc50'
revision = args.revision or HfApi().dataset_info(repo).sha
args.output.mkdir(parents=True, exist_ok=True)
archive = Path(hf_hub_download(repo, 'ESC-50-master.zip', repo_type='dataset', revision=revision,
                              cache_dir=args.output.parent / 'huggingface-cache'))
with zipfile.ZipFile(archive) as z:
    for member in z.infolist():
        parts = Path(member.filename).parts
        if not parts or parts[0] != 'ESC-50-master' or '..' in parts or member.is_dir():
            continue
        relative = Path(*parts[1:])
        if not (relative.parts[0] in ('audio', 'meta') or str(relative) in ('LICENSE', 'README.md')):
            continue
        target = args.output / relative
        if target.exists():
            with z.open(member) as source:
                if hashlib.sha256(target.read_bytes()).digest() != hashlib.file_digest(source, 'sha256').digest():
                    raise RuntimeError(f'Existing dataset material differs: {target}')
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        with z.open(member) as source, target.open('xb') as output:
            shutil.copyfileobj(source, output)
rows = list(csv.DictReader((args.output/'meta/esc50.csv').open()))
clips = []
for row in rows:
    path = args.output/'audio'/row['filename']
    with wave.open(str(path)) as w:
        fmt = dict(channels=w.getnchannels(), sample_width=w.getsampwidth(), sample_rate=w.getframerate(), samples=w.getnframes())
        if fmt != dict(channels=1, sample_width=2, sample_rate=44100, samples=220500):
            raise RuntimeError(f'Unexpected WAV chart: {path}: {fmt}')
    clips.append(dict(**row, **fmt, sha256=hashlib.sha256(path.read_bytes()).hexdigest(), octets=path.stat().st_size))
receipt = dict(dataset='ESC-50', upstream='https://github.com/karolpiczak/ESC-50',
    mirror=f'https://huggingface.co/datasets/{repo}', revision=revision,
    archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
    license='CC-BY-NC-3.0; ESC-10 subset CC-BY; individual attribution in LICENSE',
    clip_count=len(clips), audio_octets=sum(c['octets'] for c in clips),
    labels_enter_native_current=False, clips=clips)
(args.output/'acquisition.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='clips'}, indent=2), flush=True)
