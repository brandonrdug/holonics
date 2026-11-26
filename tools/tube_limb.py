#!/usr/bin/env -S python3 -I
"""A voice's limb: a tube of junctions driven by a pulsed source, played at the rate of articulation, its sound charted back as loudness.

The record of November 26 (her writer is a limb): her act is an efference through a body of its own, and its consequence returns through
the chart her senses read. A voice is a tube: a source of pulses at a pitch drives a chain of sections whose cross-sectional areas set
each junction's reflection, `r_k = (A_k - A_(k+1)) / (A_k + A_(k+1))`, each section delaying the wave by one sample each way (the
junction chain of `wave.junction-reflection` and `wave.junction-boost-delay-turn`); the lips reflect most of the arriving wave back and
radiate the rest. The tube is the exterior, a body; it computes no answer. Its controls move once a frame (10 ms at 16 kHz):

  pitch      level 0 is no pulse (the source is breath, a keyed noise), levels 1 to 12 a pulse period of 200 down to 55 samples
             (80 to 290 Hz) in equal steps of the period's logarithm
  loud       the source's amplitude, levels 0 to 12, a sixth of an octave apart from the softest
  areas      the sections' areas, levels 0 to 12 on a logarithmic chart from a closure to a wide opening, one a section

A frame is written as its act's places (pitch, loud, then one place a section) and then the places its sound returns as, a coarse
Doppler spectrogram (Brandon, November 26 21:40 UTC: the winding of parts of wavelengths against each other, Fourier and Doppler
spectrograms): the rendered frame's loudness `v = 16 b + m` (`speech_pairs.py`'s frame value) on the paired slice's chart, then the
power of three bands of the frame's spectrum (under 500 Hz, 500 to 2,000 Hz, over 2,000 Hz) as the same `v`, each on a chart located
on speakers' frames (`bands-chart`), so what she hears of her own act is read on the levels a speaker's sound is read on, and a formant
moving through a band is a ridge across frames. Every place is one of the thirteen free octets (C0, C1, F5 to FF).

`babble` writes a slice of babbled acts: each document a run of frames whose controls walk by keyed steps of at most one level a frame
and are held for a keyed count of frames, rendered and charted back; the acts are the body's, drawn, never hers, so the slice holds the
map from an act to its sound (a forward model's terrain, as an infant's babbling is), and a held part of the same law.

Usage:
  tube_limb.py bands-chart MANIFEST UTTERANCES OUT_TSV             (the bands' charts located on speakers' frames)
  tube_limb.py babble OUT NAME DOCUMENTS FRAMES HELD SEED CHART BANDS   (CHART: a CHART_pairs.tsv; BANDS: a bands-chart's table)
  tube_limb.py render ACTS_HEX OUT.wav [SECTIONS]                 (a document's acts rendered to 16-bit samples at 16 kHz)
"""
import hashlib
import math
import os
import sys
import wave

import numpy as np

FREE_OCTETS = (0xC0, 0xC1) + tuple(range(0xF5, 0x100))
CLOCK, FRAME, SECTIONS, LEVELS = 16000, 160, 4, 13
LIPS = -0.9  # the lips return nine tenths of the arriving wave, inverted (an open end), and radiate the rest
GLIDE = 320  # the body's time constant in samples (20 ms): how fast folds and tongue move toward a command
FOLD = 1 - math.exp(-2 * math.pi * 300 / CLOCK)  # the folds' pulse is smoothed twice at 300 Hz, so the source falls by an octave's square
# above it (the glottal flow's tilt), and the lips' radiation lifts it by one: a voiced spectrum falls as speech's does


def key(*words):
    return int(hashlib.sha256(":".join(map(str, words)).encode()).hexdigest()[:16], 16)


def period_of(level):
    """A pulse period in samples for pitch levels 1 to 12: 200 down to 55 in equal steps of its logarithm."""
    return int(round(200 * (55 / 200) ** ((level - 1) / 11)))


def amplitude_of(level):
    return 400 * 2 ** (level / 6)


def area_of(level):
    """An area for levels 0 to 12, from a near closure (0.05) to a wide opening (8), equal steps of its logarithm."""
    return 0.05 * (8 / 0.05) ** (level / 12)


def render(acts, sections=SECTIONS, seed=0):
    """Samples of a run of frames, each frame's act (pitch, loud, areas) a command the body moves toward: the pitch's period, the
    source's amplitude, its voicing and every area glide toward their commanded values with the body's own time constant (GLIDE
    samples, the inertia of folds and tongue), so a command changes the sound smoothly; the tube's state carries across frames."""
    fwd, bwd = [0.0] * sections, [0.0] * sections
    out, last, clock = [], 0.0, 0.0
    noise = np.random.default_rng(seed).standard_normal(len(acts) * FRAME).tolist()
    g = 1 - math.exp(-1 / GLIDE)
    first = acts[0] if acts else (0, 0) + (0,) * sections
    lp = math.log(period_of(first[0]) if first[0] else period_of(6))
    la = [math.log(area_of(x)) for x in first[2:]] + [math.log(area_of(LEVELS - 1))]
    lamp, voice = math.log(amplitude_of(first[1])), 1.0 if first[0] else 0.0
    s1 = s2 = 0.0
    n = 0
    for pitch, loud, *areas in acts:
        t_lp = math.log(period_of(pitch)) if pitch else lp  # breath keeps the folds' last period
        t_la = [math.log(area_of(x)) for x in areas] + [la[-1]]
        t_amp, t_voice = math.log(amplitude_of(loud)), 1.0 if pitch else 0.0
        for _ in range(FRAME):
            lp += g * (t_lp - lp)
            lamp += g * (t_amp - lamp)
            voice += g * (t_voice - voice)
            for k in range(sections):
                la[k] += g * (t_la[k] - la[k])
            amp = math.exp(lamp)
            clock += 1 / math.exp(lp)
            pulse = 0.0
            if clock >= 1:
                clock -= 1
                pulse = amp
            # The folds' flow: the pulse smoothed twice (its gain restored), beside the breath's noise, which is not smoothed.
            s1 += FOLD * (pulse / (FOLD * FOLD) - s1)
            s2 += FOLD * (s1 - s2)
            src = voice * s2 + (1 - voice) * amp * 0.25 * noise[n]
            n += 1
            a = [math.exp(x) for x in la]
            r = [(a[k] - a[k + 1]) / (a[k] + a[k + 1]) for k in range(sections)]
            # One sample of the chain: the source enters the first section (the glottis returns what arrives, nearly closed), each
            # junction scatters, the lips return their part and radiate the rest.
            f_new = [0.0] * sections
            b_new = [0.0] * sections
            f_new[0] = src + 0.95 * bwd[0]
            for k in range(sections - 1):
                f_new[k + 1] = (1 + r[k]) * fwd[k] - r[k] * bwd[k + 1]
                b_new[k] = r[k] * fwd[k] + (1 - r[k]) * bwd[k + 1]
            b_new[sections - 1] = LIPS * fwd[sections - 1]
            # The radiated sound is the transmitted wave's change (an opening radiates its flow's derivative).
            sent = (1 + LIPS) * fwd[sections - 1]
            out.append(sent - last)
            last = sent
            fwd, bwd = f_new, b_new
    return np.clip(np.round(np.array(out) * 32), -32768, 32767).astype(np.int64)


def loudness(x):
    """Each frame's v = 16 b + m (b the octave of 1 + e, m the four bits under its top), e the frame's summed squares."""
    n = (len(x) + FRAME - 1) // FRAME
    e = np.zeros(n, dtype=np.int64)
    np.add.at(e, np.arange(len(x)) // FRAME, x * x)
    v = []
    for q in (e + 1).tolist():
        b = q.bit_length() - 1
        m = (q >> (b - 4)) - 16 if b >= 4 else (q << (4 - b)) - 16
        v.append(16 * b + m)
    return np.array(v, dtype=np.int64)


BAND_EDGES = (0, 5, 20, 81)  # rfft bins of a frame (100 Hz apart at 160 samples): under 500 Hz, 500 to 2,000 Hz, over 2,000 Hz


def v_of(q):
    """`v = 16 b + m` of a positive integer q: b its octave, m the four bits under its top."""
    b = q.bit_length() - 1
    return 16 * b + ((q >> (b - 4)) - 16 if b >= 4 else (q << (4 - b)) - 16)


def bands(x):
    """Each frame's three bands' power as v, from the frame's spectrum (a Hann window over its 160 samples); host floats at the boundary,
    read to integers before they are charted."""
    n = (len(x) + FRAME - 1) // FRAME
    pad = np.zeros(n * FRAME); pad[:len(x)] = x
    spec = np.abs(np.fft.rfft(pad.reshape(n, FRAME) * np.hanning(FRAME), axis=1)) ** 2
    out = np.zeros((n, 3), dtype=np.int64)
    for k in range(3):
        power = spec[:, BAND_EDGES[k]:BAND_EDGES[k + 1]].sum(axis=1)
        out[:, k] = [v_of(1 + int(p)) for p in power]
    return out


def bands_chart(manifest, utterances, out_tsv):
    """Each band's thirteen levels of equal mass over the frames of the manifest's first UTTERANCES utterances of training speakers."""
    import json, subprocess
    vs = []
    for line in open(manifest, encoding="utf-8"):
        if len(vs) >= utterances:
            break
        d = json.loads(line)
        # A speaker the paired slice holds out (one group in sixteen, `speech_pairs.py`'s rule) is never read for the chart.
        if int(hashlib.sha256(d["speaker_id"].encode("utf-8")).hexdigest()[:8], 16) % 16 == 0:
            continue
        raw = subprocess.run(["ffmpeg", "-v", "error", "-i", os.path.join(d["source_root"], d["flac_path"]), "-f", "s16le", "-ac", "1", "-"], capture_output=True, check=True).stdout
        vs.append(bands(np.frombuffer(raw, dtype="<i2").astype(np.int64)))
    v = np.concatenate(vs)
    with open(out_tsv, "x") as f:
        f.write("band\tlevel\tlow\thigh\tcount\n")
        for b in range(3):
            col = np.sort(v[:, b]); total = len(col)
            cuts = [int(col[min(total - 1, (j * total + LEVELS - 1) // LEVELS)]) for j in range(1, LEVELS)]
            lows, highs = [0] + cuts, cuts + [1 << 12]
            for r in range(LEVELS):
                f.write(f"{b}\t{r}\t{lows[r]}\t{highs[r]}\t{int(((col >= lows[r]) & (col < highs[r])).sum())}\n")
    print(f"BANDS_CHART utterances={len(vs)} frames={len(v)}")


def band_cuts(path):
    rows = [line.split("\t") for line in open(path).read().rstrip("\n").split("\n")[1:]]
    return [np.asarray([int(r[3]) for r in rows if int(r[0]) == b][:-1], dtype=np.int64) for b in range(3)]


def walk(doc, frames, sections):
    """A keyed babble: each control steps by at most one level and holds for a keyed count of frames (2 to 12)."""
    state = [key(doc, "start", c) % LEVELS for c in range(2 + sections)]
    hold = [0] * (2 + sections)
    acts = []
    for t in range(frames):
        for c in range(2 + sections):
            if hold[c] == 0:
                step = key(doc, t, c) % 3 - 1
                state[c] = min(LEVELS - 1, max(0, state[c] + step))
                hold[c] = 2 + key(doc, t, c, "hold") % 11
            hold[c] -= 1
        acts.append(tuple(state))
    return acts


def cuts_of_chart(path):
    lines = open(path).read().rstrip("\n").split("\n")[1:]
    return [int(line.split("\t")[3]) for line in lines[:-1]]


def babble(out, name, documents, frames, held, seed, chart, bands_path):
    os.makedirs(out, exist_ok=True)
    if os.listdir(out):
        sys.exit(f"{out} holds files")
    cuts = np.asarray(cuts_of_chart(chart), dtype=np.int64)
    bcuts = band_cuts(bands_path)
    octets = np.asarray(FREE_OCTETS, dtype=np.uint8)
    roles = {}
    for stem, count, offset in (("DOCS", documents, 0), ("HELD", held, documents)):
        ids_stem = "HELD_IDS" if stem == "HELD" else "IDS"
        sha, total = hashlib.sha256(), 0
        with open(os.path.join(out, f"{stem}_{name}.bin"), "xb") as b, open(os.path.join(out, f"{stem}_{name}.tsv"), "x") as t, open(os.path.join(out, f"{ids_stem}_{name}.txt"), "x") as ids:
            t.write("document\ttitle_octets\ttext_octets\topens\tcloses\n")
            for k in range(count):
                doc = f"{seed}:{offset + k}"
                acts = walk(doc, frames, SECTIONS)
                sound = render(acts, SECTIONS, key(doc, "breath"))
                heard = np.searchsorted(cuts, loudness(sound), side="right")
                spec = bands(sound)
                heard_bands = np.stack([np.searchsorted(bcuts[b], spec[:, b], side="right") for b in range(3)], axis=1)
                body = bytes(int(octets[x]) for act, h, hb in zip(acts, heard, heard_bands) for x in (*act, h, *hb))
                b.write(body)
                sha.update(body)
                t.write(f"{k}\t0\t{len(body)}\t1\t1\n")
                ids.write(doc + "\n")
                total += len(body)
        roles[stem] = (count, total, sha.hexdigest())
    with open(os.path.join(out, f"CHART_{name}.tsv"), "x") as f:
        f.write("level\toctet\tlow\thigh\tcount\n")
        lows = [0] + cuts.tolist()
        highs = cuts.tolist() + [1 << 10]
        for r in range(LEVELS):
            f.write(f"{r}\t{FREE_OCTETS[r]}\t{lows[r]}\t{highs[r]}\t0\n")
    with open(os.path.join(out, f"BOUNDARY_{name}.tsv"), "x") as f:
        f.write(f"clock_hz\t{CLOCK}\nframe_samples\t{FRAME}\nsections\t{SECTIONS}\nlevels\t{LEVELS}\nplaces_a_frame\t{6 + SECTIONS}\nseed\t{seed}\n")
        for stem, label in (("DOCS", "train"), ("HELD", "held")):
            n, total, sha = roles[stem]
            f.write(f"{label}_documents\t{n}\n{label}_octets\t{total}\n{label}_sha256\t{sha}\n")
    print("role\tslice\tshare\tline_floor\tdocuments\tpieces\ttext_octets\tstore_octets\tsha256")
    for role, stem in (("train", "DOCS"), ("prefix", "DOCS"), ("held", "HELD")):
        n, total, sha = roles[stem]
        print(f"{role}\t{name}\t0\t0\t{n}\t{n}\t{total}\t{total}\t{sha}")


def write_wav(path, x):
    with wave.open(path, "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(CLOCK)
        w.writeframes(np.asarray(x, dtype="<i2").tobytes())


def main(argv):
    if len(argv) == 9 and argv[0] == "babble":
        babble(argv[1], argv[2], int(argv[3]), int(argv[4]), int(argv[5]), int(argv[6]), argv[7], argv[8])
        return
    if len(argv) == 4 and argv[0] == "bands-chart":
        bands_chart(argv[1], int(argv[2]), argv[3])
        return
    if len(argv) in (3, 4) and argv[0] == "render":
        body = bytes.fromhex(argv[1][4:] if argv[1].startswith("hex:") else argv[1])
        sections = int(argv[3]) if len(argv) == 4 else SECTIONS
        level = {o: r for r, o in enumerate(FREE_OCTETS)}
        per = 3 + sections
        acts = [tuple(level[o] for o in body[k:k + per - 1]) for k in range(0, len(body) - per + 1, per) if all(o in level for o in body[k:k + per - 1])]
        write_wav(argv[2], render(acts, sections))
        print(f"RENDER frames={len(acts)} seconds={len(acts) * FRAME / CLOCK:.2f}")
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
