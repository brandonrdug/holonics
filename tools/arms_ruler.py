"""A ruler for arms that train the same sections from one state (the cooling laps of November 18, guess G-1118-1).

It reads, for a control arm and each other arm in a directory DIR (files as `cool.sh` leaves them: `arm_N.log`, `arm_N/STATE.k`,
`arm_N/MEAN.k`, `OPEN.N`, `out_mean_N/cavity.tsv`, `out_end_N/cavity.tsv`):
- the sections' own training codes, paired section by section with the control (a section's code a compared place before its
  step, as its line prints it), by thirds of the lap, in nats a compared place, with the paired difference's standard error;
- the held read at each arm's mean and end, one place open and whole masks, by slice, each paired place by place with the control's
  mean, in nats a place;
- each arm's travel: the size of its moves between saves against the state's own size, and the cosine between successive moves;
- each arm's push at its end: the mean of |m| / (sqrt(v) + 1) over the entries with a second moment.

Outside the machine; codes and counts only. Usage: python3 -I arms_ruler.py DIR CONTROL ARM [ARM ...]"""
import sys, os, re, math
import numpy as np

d, control, arms = sys.argv[1], sys.argv[2], sys.argv[3:]
LN2 = math.log(2); G = float(1 << 20)
kv = lambda line: dict(re.findall(r'(\w+)=(\S+)', line))

def sections(n):
    out = {}
    path = f"{d}/arm_{n}.log"
    if not os.path.exists(path): return out
    for line in open(path, errors='replace'):
        if line.startswith('STORE_SECTION '):
            f = kv(line)
            # a section's line prints its codes in millionths of a bit a place (`micro` in the store trainer), where a cavity's rows are on 2^-20 bits
            out[int(f['n'])] = (int(f['before']) / 1e6 * LN2, int(f['domain']), int(f['opening']) / 1e6 * LN2 if f.get('opening', '-') != '-' else float('nan'), int(f.get('opening_places', 0)))
    return out

def paired_sections(a, b, name):
    common = sorted(set(a) & set(b))
    if not common: return
    n = len(common); thirds = [common[: n // 3], common[n // 3: 2 * n // 3], common[2 * n // 3:]]
    parts = []
    for part in thirds + [common]:
        # a section's line gives its code a compared place already; the pairs are unweighed
        da = np.array([a[k][0] for k in part]); db = np.array([b[k][0] for k in part])
        diff = db - da
        parts.append(f"{diff.mean():+.4f} (±{diff.std(ddof=1) / math.sqrt(len(diff)):.4f}; the control {da.mean():.4f})")
    oa = np.array([a[k][2] for k in common]); ob = np.array([b[k][2] for k in common])
    print(f"ARMS sections paired with {control}, arm {name}, {n} sections; the training code a compared place, arm less control, nats, by third then whole: " + " | ".join(parts)
          + f" || the opening's code a place, arm less control, whole: {np.nanmean(ob - oa):+.4f}")

def cavity(path):
    rows = {}
    if not os.path.exists(path): return rows
    for line in open(path):
        f = line.rstrip('\n').split('\t')
        if f[0] in ('P', 'W'):
            rows[(f[0], f[1], f[2], f[3])] = int(f[6]) / G * LN2
    return rows

def read_line(tag, rows, base, kind, label):
    keys = [k for k in rows if k[0] == kind]
    if not keys: return
    slices = sorted({k[1] for k in keys})
    own = " ".join(f"{s} {np.mean([rows[k] for k in keys if k[1] == s]):.4f}" for s in slices)
    msg = f"ARMS held, {label}, {tag}: all {np.mean([rows[k] for k in keys]):.4f} ({len(keys)} places) | {own}"
    if base is not None:
        common = [k for k in keys if k in base]
        diff = np.array([rows[k] - base[k] for k in common])
        by = " ".join(f"{s} {np.mean([rows[k] - base[k] for k in common if k[1] == s]):+.4f}" for s in slices)
        msg += f" || less the control's mean, paired: {diff.mean():+.4f} (±{diff.std(ddof=1) / math.sqrt(len(diff)):.4f}) | {by}"
    print(msg)

def state(path):
    """A learner's text: the field's material, any level's and glue's, and the two moments."""
    if not os.path.exists(path): return None
    L = open(path).read().split('\n')
    theta = [np.array(L[2].split(), dtype=np.float64)]
    i = 3
    if L[i].startswith('level '):
        theta += [np.array(L[i + 2].split(), dtype=np.float64), np.array(L[i + 3].split(), dtype=np.float64)]; i += 4
    m = np.array(L[i].split(), dtype=np.float64); v = np.array([float(x) for x in L[i + 1].split()])
    return np.concatenate(theta), m, v

def travel(n):
    pts = [state(f"{d}/OPEN.{n}")] + [state(f"{d}/arm_{n}/STATE.{k}") for k in (1000, 2000, 3000)]
    if any(p is None for p in pts): return
    th = [p[0] for p in pts]
    moves = [th[i + 1] - th[i] for i in range(3)]
    rms = lambda x: math.sqrt(float((x ** 2).mean()))
    cos = lambda a, b: float(a @ b / (np.linalg.norm(a) * np.linalg.norm(b) + 1e-300))
    m, v = pts[-1][1], pts[-1][2]
    has = v > 0
    push = np.abs(m[has]) / (np.sqrt(v[has]) + 1)
    whole = th[3] - th[0]
    print(f"ARMS travel, arm {n}: a 1,000-section move over the state's size {', '.join(f'{rms(x) / rms(th[0]):.5f}' for x in moves)}; the lap's whole move {rms(whole) / rms(th[0]):.5f}; "
          f"cosines of successive moves {cos(moves[0], moves[1]):+.3f}, {cos(moves[1], moves[2]):+.3f}; the push at its end, mean |m|/(sqrt(v)+1) {push.mean():.3f} over {int(has.sum())} entries")

base_sections = sections(control)
base_mean = cavity(f"{d}/out_mean_{control}/cavity.tsv")
for n in [control] + arms:
    if n != control:
        paired_sections(base_sections, sections(n), n)
    for where in ('mean', 'end'):
        rows = cavity(f"{d}/out_{where}_{n}/cavity.tsv")
        if rows:
            base = None if (n == control and where == 'mean') or not base_mean else base_mean
            read_line(f"arm {n} at its {where}", rows, base, 'P', 'one place open')
            read_line(f"arm {n} at its {where}", rows, base, 'W', 'whole masks')
    travel(n)
