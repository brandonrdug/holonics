"""A count ruler, outside the machine (the formal thread, November 25): what a symbol one turn of a ring back tells of a symbol, on
unlike streams read by one program with no branch on the kind of stream. A stream is a list of runs of symbols (a run: one chapter's
transcript, one utterance's samples, one file's octets); a pair never crosses two runs. For a lag n it prints the plug-in mutual
information I(u_t; u_(t-n)) in nats a place less the Miller-Madow bias, over every pair of every run. A boundary hands a stream its
symbols: octets as they are; a 16-bit sample as its rank among 16 levels of equal mass located on the stream itself, and as its sign.
Second read (PAIR): each utterance's duration against its transcript's letters. Usage: ring_lag_ruler.py LIBRISPEECH_DIR PROSE_FILE...
Reads only; ffmpeg decodes each FLAC to its own 16-bit samples at its own 16 kHz (no resampling)."""
import sys, os, json, subprocess
import numpy as np
RINGS = [2, 3, 4, 9, 16, 27, 32, 81, 128, 243, 256, 729, 1024, 2187, 4096, 6561]
LAGS = sorted(set([1, 5, 6, 7, 8, 12, 24, 48, 64, 96, 160, 192, 384, 512, 1536, 3072] + RINGS))
def lag_info(runs, k, n):
    joint = np.zeros(k * k, dtype=np.int64)
    for s in runs:
        if len(s) > n: joint += np.bincount(s[n:].astype(np.int64) * k + s[:-n], minlength=k * k)
    tot = joint.sum()
    if tot == 0: return None, 0
    p = joint.reshape(k, k) / tot; px = p.sum(1); py = p.sum(0); m = p > 0
    i = float((p[m] * np.log(p[m] / np.outer(px, py)[m])).sum())
    return i - (np.count_nonzero(px) - 1) * (np.count_nonzero(py) - 1) / (2 * tot), int(tot)
root = sys.argv[1]; src = root + '/source/LibriSpeech/train-clean-100'
man = [json.loads(l) for l in open(root + '/train-clean-100.manifest.jsonl')]
trans = {}; chapters = {}
for spk in sorted(os.listdir(src)):
    for ch in sorted(os.listdir(f'{src}/{spk}')):
        rows = [l.rstrip('\n').split(' ', 1) for l in open(f'{src}/{spk}/{ch}/{spk}-{ch}.trans.txt')]
        for i, t in rows: trans[i] = t
        chapters[(spk, ch)] = '\n'.join(t for _, t in sorted(rows)) + '\n'
# PAIR: an utterance's duration against its transcript's letters and words
dur = np.array([m['sample_count'] for m in man]) / 16000.0
let = np.array([sum(c.isalpha() for c in trans[m['id']]) for m in man], dtype=float)
wor = np.array([len(trans[m['id']].split()) for m in man], dtype=float)
spk = np.array([m['speaker_id'] for m in man])
for name, y in (('letters', let), ('words', wor)):
    r = float(np.corrcoef(dur, y)[0, 1]); a = float((dur * y).sum() / (dur * dur).sum()); res = y - a * dur
    print(f'PAIR utterances={len(man)} seconds={dur.sum():.0f} {name}={int(y.sum())} r={r:.4f} gaussian_nats_an_utterance={-0.5 * np.log(1 - r * r):.3f} '
          f'{name}_a_second={a:.3f} residual_sd={res.std():.2f} mean_{name}={y.mean():.1f} sd_{name}={y.std():.1f}')
rate = let / dur; sp = sorted(set(spk)); means = np.array([rate[spk == s].mean() for s in sp]); within = np.array([rate[spk == s].std() for s in sp])
print(f'PAIR_RATE letters_a_second all mean={rate.mean():.2f} sd={rate.std():.2f} | speakers={len(sp)} between_sd={means.std():.2f} within_sd_mean={within.mean():.2f} '
      f'| seconds_a_letter={1 / rate.mean():.4f} an_eleven_letter_word_seconds={11 / rate.mean():.3f}')
# the streams
take = [m for s in sp[::16] for m in [x for x in man if x['speaker_id'] == s][:3]]
wave = []
for m in take:
    raw = subprocess.run(['ffmpeg', '-v', 'error', '-i', f"{src}/{m['flac_path']}", '-f', 's16le', '-'], capture_output=True, check=True).stdout
    x = np.frombuffer(raw, dtype='<i2'); assert len(x) == m['sample_count'], (m['id'], len(x)); wave.append(x)
allx = np.concatenate(wave); cuts = np.quantile(allx, np.arange(1, 16) / 16)
rank = [np.searchsorted(cuts, x, side='right').astype(np.int64) for x in wave]; sign = [(x >= 0).astype(np.int64) for x in wave]
print(f'WAVE utterances={len(take)} speakers={len(sp[::16])} samples={len(allx)} seconds={len(allx) / 16000:.1f} cuts={" ".join(str(int(c)) for c in cuts)}')
streams = [('wave_rank16', rank, 16), ('wave_sign', sign, 2),
           ('transcripts', [np.frombuffer(t.encode(), dtype=np.uint8).astype(np.int64) for t in chapters.values()], 256)]
for f in sys.argv[2:]:
    streams.append((os.path.basename(f), [np.frombuffer(open(f, 'rb').read(), dtype=np.uint8).astype(np.int64)], 256))
for name, runs, k in streams:
    h = np.bincount(np.concatenate(runs), minlength=k) / sum(len(r) for r in runs); h = h[h > 0]
    print(f'STREAM {name} runs={len(runs)} places={sum(len(r) for r in runs)} alphabet={k} entropy_nats={float(-(h * np.log(h)).sum()):.4f}')
print('LAG lag ring ' + ' '.join(n for n, _, _ in streams))
for n in LAGS:
    print(f'LAG {n} {"ring" if n in RINGS else "-"} ' + ' '.join('%.4f' % (lag_info(r, k, n)[0] or 0) for _, r, k in streams))
