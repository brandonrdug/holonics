#!/usr/bin/env -S python3 -I
"""An audio ruler: what a sound is, frame by frame, read as an analyst reads it. A ruler's instrument on the host (floats at the
boundary); it measures her sound and the world's and never enters the machine.

Each frame is 25 ms of samples every 10 ms, under a Hann window:
  flatness   the spectrum's geometric mean over its arithmetic mean, 0 to 1: near 1 a frame is static (noise spreads its power
             evenly), near 0 it is tone (its power stands in a few partials)
  harmonic   the autocorrelation's peak r between lags of 50 and 400 Hz, each lag's sum read over the samples it overlaps, and its
             harmonics-to-noise ratio 10 log10(r / (1 - r)) in decibels (r held under 0.999, 30 dB); a frame is voiced where r
             stands over 0.5
  pitch      the voiced frame's frequency at the top of the first peak that stands within a tenth of the highest (so a period's
             multiples never stand for it), and whether it stands within a tenth of the frame
             before it (a pitch that holds or glides)
  formants   the first two resonances of a voiced frame, from linear prediction of order 12 (the roots of its predictor, the
             lowest two over 200 Hz whose bandwidth stands under 400 Hz)
Frames quieter than a fortieth of the file's loudest frame's power are left out of every share (silence is no static).

Usage:
  audio_ruler.py FILE.wav ...                  a line a file: its frames, shares and medians
  audio_ruler.py --picture FILE.wav OUT.png    a spectrogram picture (ffmpeg's showspectrumpic)
"""
import subprocess
import sys
import wave

import numpy as np


def samples_of(path):
    with wave.open(path, "rb") as w:
        if w.getsampwidth() != 2 or w.getnchannels() != 1:
            sys.exit(f"{path}: not one channel of 16-bit samples")
        return np.frombuffer(w.readframes(w.getnframes()), dtype="<i2").astype(np.float64), w.getframerate()


def lpc(frame, order):
    """The predictor of `order` by the autocorrelation method (Levinson's recursion)."""
    r = np.correlate(frame, frame, "full")[len(frame) - 1:len(frame) + order]
    if r[0] <= 0:
        return None
    a, e = np.zeros(order + 1), r[0]
    a[0] = 1.0
    for i in range(1, order + 1):
        k = -(r[i] + a[1:i] @ r[i - 1:0:-1]) / e
        a[1:i] = a[1:i] + k * a[i - 1:0:-1]
        a[i] = k
        e *= 1 - k * k
        if e <= 0:
            return None
    return a


def frames_of(x, rate):
    win, hop = int(0.025 * rate), int(0.010 * rate)
    hann = np.hanning(win)
    lo, hi = int(rate / 400), int(rate / 50)
    out = []
    for s in range(0, len(x) - win + 1, hop):
        f = x[s:s + win] - x[s:s + win].mean()
        power = float((f * f).sum())
        spec = np.abs(np.fft.rfft(f * hann)) ** 2 + 1e-12
        flat = float(np.exp(np.log(spec).mean()) / spec.mean())
        ac = np.correlate(f, f, "full")[win - 1:]
        r = 0.0
        lag = 0
        if ac[0] > 0:
            # the autocorrelation over the overlap alone (a lag of k shares win - k samples), so a held tone reads r near one
            seg = ac[lo:hi] * win / ((win - np.arange(lo, hi)) * ac[0])
            # the shortest lag whose peak stands within a tenth of the highest, so a period's multiples never stand for it
            k = int(np.argmax(seg >= 0.9 * seg.max()))
            while k + 1 < len(seg) and seg[k + 1] >= seg[k]:
                k += 1  # climbed to that peak's top
            lag = lo + k
            r = float(seg[k])
        pitch = rate / lag if r > 0.5 and lag else 0.0
        f1 = f2 = 0.0
        if pitch:
            a = lpc(f * hann, 12)
            if a is not None:
                roots = [z for z in np.roots(a) if z.imag > 0]
                cand = sorted((np.angle(z) * rate / (2 * np.pi), -np.log(abs(z)) * rate / np.pi) for z in roots)
                fs = [fr for fr, bw in cand if fr > 200 and bw < 400]
                if len(fs) >= 2:
                    f1, f2 = fs[0], fs[1]
        out.append((power, flat, r, pitch, f1, f2))
    return out


def read(path):
    x, rate = samples_of(path)
    fr = frames_of(x, rate)
    if not fr:
        return f"AUDIO file={path} frames=0"
    top = max(p for p, *_ in fr)
    loud = [f for f in fr if f[0] > top / 40]
    voiced = [f for f in loud if f[3] > 0]
    held = sum(1 for a, b in zip(voiced, voiced[1:]) if abs(b[3] - a[3]) <= 0.1 * a[3])
    hnr = [10 * np.log10(min(f[2], 0.999) / (1 - min(f[2], 0.999))) for f in loud if f[2] > 0]
    med = lambda v: float(np.median(v)) if len(v) else float("nan")
    return (f"AUDIO file={path.rsplit('/', 1)[-1]} seconds={len(x) / rate:.2f} frames={len(fr)} sounding={len(loud)} "
            f"flatness_median={med([f[1] for f in loud]):.3f} static_share={sum(1 for f in loud if f[1] > 0.3) / max(len(loud), 1):.2f} "
            f"voiced_share={len(voiced) / max(len(loud), 1):.2f} hnr_db_median={med(hnr):.1f} pitch_hz_median={med([f[3] for f in voiced]):.0f} "
            f"pitch_held={held / max(len(voiced) - 1, 1):.2f} f1_median={med([f[4] for f in voiced if f[4]]):.0f} f2_median={med([f[5] for f in voiced if f[5]]):.0f}")


def picture(path, out):
    subprocess.run(["ffmpeg", "-v", "error", "-y", "-i", path, "-lavfi", "showspectrumpic=s=1024x384:legend=1:scale=log:fscale=lin", out], check=True)
    print(f"PICTURE {out}")


def main(argv):
    if len(argv) == 3 and argv[0] == "--picture":
        picture(argv[1], argv[2])
        return
    if not argv:
        sys.exit(__doc__)
    for path in argv:
        print(read(path))


if __name__ == "__main__":
    main(sys.argv[1:])
