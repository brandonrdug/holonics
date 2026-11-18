"""A ruler for the held read with its frontier rows (`athena train complete-language read-cavity`, November 18; guess G-1118-3).

For each named read (NAME=DIR, DIR a `read-cavity` output directory; the first is the control) it prints, in nats a place:
- one place open (`P` rows of `cavity.tsv`) and whole masks (`W` rows), over all places and by slice, each paired place by place with
  the control's, with the paired difference's standard error;
- the frontier (`F` rows of `frontier.tsv`: every place before the place known, the place alone open, the region ending there), over
  all places and by slice, paired the same way;
- the frontier by how many places are known, in octaves (0, 1, 2 to 3, 4 to 7, and so on), with each octave's count of places, so a
  reader sees how far before the place the field's reading still gains;
- where a read holds them, the frontier with each region a known stream (`K` rows: every known place hears only what stands before it)
  and with each stretch read by two streams (`S` rows: one region a stretch, an open place at every place), paired with the control's
  and with the same state's rows under the law.

A cavity's codes are on 2^-20 bits. Outside the machine; codes and counts only.
Usage: python3 -I frontier_ruler.py CONTROL=DIR NAME=DIR [NAME=DIR ...]"""
import sys, os, math
import numpy as np

G = float(1 << 20); LN2 = math.log(2)
reads = [a.split('=', 1) for a in sys.argv[1:]]

def rows(path, kinds, col):
    out = {}
    if not os.path.exists(path): return out
    for line in open(path):
        f = line.rstrip('\n').split('\t')
        if f[0] in kinds:
            out[(f[0], f[1], f[2], f[3])] = int(f[col]) / G * LN2
    return out

def octave(t):
    return 0 if t == 0 else int(math.log2(t)) + 1          # 0 known; 1; 2 to 3; 4 to 7; ...

def span(o):
    return "0" if o == 0 else ("1" if o == 1 else f"{1 << (o - 1)} to {(1 << o) - 1}")

def line(tag, r, base, kind, label):
    keys = [k for k in r if k[0] == kind]
    if not keys: return
    slices = sorted({k[1] for k in keys})
    msg = f"FRONTIER {tag}; {label}: all {np.mean([r[k] for k in keys]):.4f} ({len(keys)} places) | " + " ".join(f"{s} {np.mean([r[k] for k in keys if k[1] == s]):.4f}" for s in slices)
    if base is not None:
        common = [k for k in keys if k in base]
        d = np.array([r[k] - base[k] for k in common])
        msg += f" || less the control's, paired: {d.mean():+.4f} (±{d.std(ddof=1) / math.sqrt(len(d)):.4f}) | " + " ".join(f"{s} {np.mean([r[k] - base[k] for k in common if k[1] == s]):+.4f}" for s in slices)
    print(msg)

control = None
for name, d in reads:
    cav = rows(f"{d}/cavity.tsv", ('P', 'W'), 6)
    fr = rows(f"{d}/frontier.tsv", ('F', 'K', 'S'), 5)
    if not cav and not fr:
        print(f"FRONTIER {name}: no read at {os.path.basename(d)}"); continue
    base_c, base_f = (None, None) if control is None else control
    line(name, cav, base_c, 'P', 'one place open')
    line(name, cav, base_c, 'W', 'whole masks')
    line(name, fr, base_f, 'F', 'the frontier')
    # The frontier read with each region a known stream (rows K) and by two streams (rows S), where the read holds them: paired with the
    # control's own rows of the kind where it holds them and with its F rows otherwise (the control's level under the law), which the
    # line says; then against the same state's rows under the law.
    other = {}
    for kind, label in (('K', 'each region a known stream'), ('S', 'each stretch read by two streams')):
        kr = {k: v for k, v in fr.items() if k[0] == kind}
        if not kr:
            continue
        other.update(kr)
        base_k = None
        if base_f is not None:
            own = {k: v for k, v in base_f.items() if k[0] == kind}
            base_k = own if own else {(kind,) + k[1:]: v for k, v in base_f.items() if k[0] == 'F'}
        line(name, kr, base_k, kind, 'the frontier, ' + label + ('' if base_f is None else (" (against the control's rows of the kind)" if any(k[0] == kind for k in base_f) else " (against the control's rows under the law)")))
        law_rows = {(kind,) + k[1:]: v for k, v in fr.items() if k[0] == 'F'}
        common = [k for k in kr if k in law_rows]
        if common:
            d_ = np.array([kr[k] - law_rows[k] for k in common])
            print(f"FRONTIER {name}; {label}, less the law's reading of the same state, paired: {d_.mean():+.4f} (±{d_.std(ddof=1) / math.sqrt(len(d_)):.4f}) over {len(common)} places")
        by_k = {}
        for k, v in kr.items():
            by_k.setdefault(octave(int(k[3])), []).append((k, v))
        print(f"FRONTIER {name}; {label}, by places known" + ("" if base_k is None else " (less the control's)") + ": " + " | ".join(f"{span(o)}: {np.mean([v for _, v in by_k[o]]):.3f}" + ("" if base_k is None else f" ({np.mean([v - base_k[k] for k, v in by_k[o] if k in base_k]):+.3f})") for o in sorted(by_k)))
        if kind == 'S':
            known_rows = {('S',) + k[1:]: v for k, v in fr.items() if k[0] == 'K'}
            common = [k for k in kr if k in known_rows]
            if common:
                d_ = np.array([kr[k] - known_rows[k] for k in common])
                print(f"FRONTIER {name}; two streams less the known stream's reading of the same state, paired: {d_.mean():+.4f} (±{d_.std(ddof=1) / math.sqrt(len(d_)):.4f}) over {len(common)} places")
    fr = {k: v for k, v in fr.items() if k[0] == 'F'}
    if base_f is not None:
        base_f = {k: v for k, v in base_f.items() if k[0] == 'F'}
    if fr:
        by = {}
        for k, v in fr.items():
            by.setdefault(octave(int(k[3])), []).append((k, v))
        parts = []
        for o in sorted(by):
            own = np.mean([v for _, v in by[o]])
            if base_f is None:
                parts.append(f"{span(o)}: {own:.3f} ({len(by[o])})")
            else:
                d_ = [v - base_f[k] for k, v in by[o] if k in base_f]
                parts.append(f"{span(o)}: {own:.3f} ({np.mean(d_):+.3f})")
        print(f"FRONTIER {name}; the frontier by places known" + ("" if base_f is None else " (less the control's)") + ": " + " | ".join(parts))
    if control is None:
        control = (cav, {**fr, **other})
