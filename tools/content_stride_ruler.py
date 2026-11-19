#!/usr/bin/env -S python3 -I
"""A ruler: what a carried product reaches when each symbol has a stride of its own, against one with a fixed advance (the lead,
November 18; the record of the two streams §18; atlas `navigator.content-stride-moment`).

A moment on C circles steps by each symbol's own move, `m ← α(u) m + β(u)`, `α(u) = ρ(u) e^(iθ(u))` with `0 < ρ < 1`, and a face
reads it linearly: `log p(y) = b(y) + A_y · (Re m, Im m) − log Z`. With a stride a symbol the moment holds products of every order
of the symbols before a place, in their order; with one advance for every symbol (`fixed`) a linear reading of it holds a sum of
one-place terms. Both readers are fitted here by descent of their code on the first TRAIN octets of a slice's training documents
(Adam; a moment is run over the WINDOW places before a place from rest, so a reach past the window is cut), the strides drawn over
the whole turn and the moduli opened at 4/5, the engine's founding.

Read on the frontier places of a `read-cavity` output, in `frontier_excess_ruler.py`'s bins (the news a count of five places
expects there): each reader's code and the mean mass it gives the arriving symbol (`draw_agrees`), with the mean modulus `ρ` it
came to and the spread of its symbols' strides, beside the named reads' rows of KIND (the fixed advance at the first C alone). The fit prints its held code after every
pass, so a reader sees whether it had stopped falling. With LEXICON and PANEL each reader writes from the panel's prompts and the
share of its written words in the slice's lexicon is printed.

`planted` (in place of the arguments) checks the instrument first: a passage over twelve symbols whose next symbol is the sum of
the three before it modulo twelve, nine times in ten. A sum of one-place rows cannot hold that law and a product of strides can, so
the stride reader's code is printed beside the fixed reader's and the source's own. A reading that finds strides worth nothing is
held to that line.

A host instrument, in floats: nothing here enters a law, and neither reader is a part of the machine. Codes, masses, counts only.

A size `C` may carry a letter: `Cz` opens every stride at zero, and `Cc` opens the strides within 0.06 of a turn at a modulus of
0.39, where the line's own carry circles stand; both ask whether descent reaches the strides from there.

Usage: content_stride_ruler.py STORE CODEC SLICE TRAIN_OCTETS PASSES WINDOW KIND C[z|c][,C...] NAME=DIR [NAME=DIR ...] [-- LEXICON PANEL PLACES DRAWS]
       content_stride_ruler.py planted"""
import os, pickle, random, re, sys
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_excess_ruler import fit, news, G, LN2, EDGES, NAMES

NONE = 256
BATCH = 4096
WORD = re.compile(r"[A-Za-z]{2,}")

def window_of(seq, at, n):
    """The symbols at n .. 1 places before each place of `at`, farthest first (NONE before the passage's first)."""
    cols = []
    for j in range(n, 0, -1):
        src = at - j
        cols.append(np.where(src >= 0, seq[np.maximum(src, 0)], NONE))
    return np.stack(cols, axis=1)

class Reader:
    def __init__(self, circles, strides, unigram, rng, opening="drawn"):
        c = circles
        self.c, self.strides = c, strides
        rows = 257 if strides else 1
        # The opening: strides drawn over the whole turn with ρ = 4/5 (`drawn`); every stride at zero with ρ = 4/5 (`zero`); or
        # strides drawn within 0.06 of a turn with ρ = 0.39 (`closed`: where the line's own circles stand, the record's §17).
        turn = {"drawn": 1.0, "zero": 0.0, "closed": 0.12}[opening]
        rho0 = 0.39 if opening == "closed" else 0.8
        self.p = {
            "theta": (2 * np.pi * turn * (rng.random((rows, c)) - 0.5)).astype(np.float32),
            "r": np.full((rows, c), np.log(rho0 / (1.0 - rho0)), dtype=np.float32),
            "br": (0.5 * rng.standard_normal((257, c))).astype(np.float32),
            "bi": (0.5 * rng.standard_normal((257, c))).astype(np.float32),
            "a": np.zeros((256, 2 * c), dtype=np.float32),
            "b": np.log(unigram).astype(np.float32),
        }
        self.m = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.v = {k: np.zeros_like(v) for k, v in self.p.items()}
        self.t = 0

    def key(self, u):
        return u if self.strides else np.zeros_like(u)

    def forward(self, win):
        p = self.p
        rho = 1.0 / (1.0 + np.exp(-p["r"]))
        alpha = (rho * np.exp(1j * p["theta"])).astype(np.complex64)
        beta = (p["br"] + 1j * p["bi"]).astype(np.complex64)
        m = np.zeros((win.shape[0], self.c), dtype=np.complex64)
        trail = []
        for k in range(win.shape[1]):
            u = win[:, k]
            a_k = alpha[self.key(u)]
            trail.append((u, a_k, m))
            m = a_k * m + beta[u]
        feat = np.concatenate([m.real, m.imag], axis=1)
        return feat @ p["a"].T + p["b"], feat, trail, rho

    def faces(self, win):
        z = self.forward(win)[0]
        z -= z.max(axis=1, keepdims=True)
        np.exp(z, out=z)
        z /= z.sum(axis=1, keepdims=True)
        return z

    def step(self, win, y, rate):
        p, c = self.p, self.c
        z, feat, trail, rho = self.forward(win)
        z -= z.max(axis=1, keepdims=True)
        np.exp(z, out=z)
        z /= z.sum(axis=1, keepdims=True)
        z[np.arange(len(y)), y] -= 1.0
        z /= len(y)
        grads = {"a": z.T @ feat, "b": z.sum(axis=0)}
        back = z @ p["a"]
        gm = (back[:, :c] + 1j * back[:, c:]).astype(np.complex64)
        g_theta, g_r, g_br, g_bi = (np.zeros_like(p[k]) for k in ("theta", "r", "br", "bi"))
        for u, a_k, m_prev in reversed(trail):
            ga = gm * np.conj(m_prev)
            d_theta = (ga * np.conj(1j * a_k)).real
            d_rho = (ga * np.conj(a_k / np.maximum(np.abs(a_k), 1e-12))).real
            key = self.key(u)
            d_r = d_rho * (rho[key] * (1.0 - rho[key]))
            for grad, rows_key, val in ((g_theta, key, d_theta), (g_r, key, d_r), (g_br, u, gm.real), (g_bi, u, gm.imag)):
                o = np.argsort(rows_key, kind="stable")
                ks = rows_key[o]
                starts = np.flatnonzero(np.r_[True, ks[1:] != ks[:-1]])
                grad[ks[starts]] += np.add.reduceat(val[o], starts, axis=0)
            gm = gm * np.conj(a_k)
        grads.update(theta=g_theta, r=g_r, br=g_br, bi=g_bi)
        self.t += 1
        for k, grad in grads.items():
            m, v = self.m[k], self.v[k]
            m *= 0.9; m += 0.1 * grad
            v *= 0.999; v += 0.001 * grad * grad
            p[k] -= rate * (m / (1 - 0.9 ** self.t)) / (np.sqrt(v / (1 - 0.999 ** self.t)) + 1e-8)

    def shape(self):
        """The mean modulus and the spread of the symbols' strides (thousandths of a turn; the circular deviation over symbols)."""
        rho = 1.0 / (1.0 + np.exp(-self.p["r"]))
        if not self.strides:
            return float(rho.mean()), 0.0
        r = np.abs(np.exp(1j * self.p["theta"][:256]).mean(axis=0))
        return float(rho[:256].mean()), float((np.sqrt(-2.0 * np.log(np.maximum(r, 1e-12))) / (2 * np.pi) * 1000.0).mean())

def fit_reader(seq, circles, strides, passes, n, held_win, held_y, rng, rate=0.01, opening="drawn"):
    counts = np.bincount(seq, minlength=256).astype(np.float64) + 1.0
    reader = Reader(circles, strides, counts / counts.sum(), rng, opening)
    trace = []
    for _ in range(passes):
        order = rng.permutation(np.arange(1, len(seq)))
        for s in range(0, len(order), BATCH):
            at = order[s:s + BATCH]
            reader.step(window_of(seq, at, n), seq[at], rate)
        rate /= 2
        trace.append(float(code_of(reader, held_win, held_y).mean()))
    return reader, trace

def code_of(reader, win, y):
    out = np.empty(len(y))
    for s in range(0, len(y), 4 * BATCH):
        f = reader.faces(win[s:s + 4 * BATCH])
        out[s:s + 4 * BATCH] = -np.log(np.maximum(f[np.arange(f.shape[0]), y[s:s + 4 * BATCH]], 1e-30))
    return out

def planted():
    rng = np.random.default_rng(20261118)
    def passage(length):
        s = list(rng.integers(0, 12, 3))
        noise, other = rng.random(length) < 0.1, rng.integers(0, 12, length)
        for t in range(length):
            s.append(int(other[t]) if noise[t] else (s[-1] + s[-2] + s[-3]) % 12)
        return np.array(s, dtype=np.int64)
    train, held = passage(400000), passage(20000)
    at = np.arange(3, len(held))
    source = -(0.9 + 0.1 / 12) * np.log(0.9 + 0.1 / 12) - 11 * (0.1 / 12) * np.log(0.1 / 12)
    for label, strides in (("a stride a symbol", True), ("one advance", False)):
        _, trace = fit_reader(train, 32, strides, 4, 4, window_of(held, at, 4), held[at], rng)
        print(f"STRIDE planted (the sum of three places modulo twelve, nine in ten; the source's code {source:.3f}, a blind reader's {np.log(12):.3f}) "
              f"{label}, 32 circles: held code after each pass " + " ".join(f"{c:.3f}" for c in trace), flush=True)

def main():
    args = sys.argv[1:]
    if args == ["planted"]:
        return planted()
    tail = []
    if "--" in args:
        tail = args[args.index("--") + 1:]
        args = args[:args.index("--")]
    store, codec, name = args[0], args[1], args[2]
    train_n, passes, n, kind = int(args[3]), int(args[4]), int(args[5]), args[6]
    # A size is a count of circles; `z` after it opens the strides at zero and `c` opens them closed (see `Reader`).
    sizes = [(int(w.rstrip("zc")), {"z": "zero", "c": "closed"}.get(w[-1], "drawn")) for w in args[7].split(",")]
    reads = [a.split("=", 1) for a in args[8:]]
    head, used = open(codec).read().split("\n")[:2]
    void = int(head.split(" ")[2])
    used = [int(w) for w in used.split(" ")]
    octet = lambda c: None if c == void else (used[c] if c < void else used[c - 1])
    places = {}
    for line in open(reads[0][1] + "/cavity.tsv"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "P" and f[1] == name:
            places.setdefault(int(f[2]), {})[int(f[3])] = int(f[4])
    codes = []
    for _, d in reads:
        rows = {}
        for line in open(d + "/frontier.tsv"):
            f = line.rstrip("\n").split("\t")
            if f[0] == kind and f[1] == name:
                rows[(int(f[2]), int(f[3]))] = int(f[5]) / G * LN2
        codes.append(rows)
    train = open(f"{store}/DOCS_{name}.bin", "rb").read(train_n)
    model = fit(train, 5)
    held_win, held_y, held_bin, count_code, read_code = [], [], [], [], []
    for stretch, st in sorted(places.items()):
        length = max(st) + 1
        seq = [octet(st.get(t, void)) for t in range(length)]
        raw = bytes(255 if x is None else x for x in seq)
        for t in range(1, length):
            key = (stretch, t)
            if seq[t] is None or any(key not in rows for rows in codes):
                continue
            by_k, expected = news(model, raw, t, 5)
            held_win.append([raw[t - j] if t - j >= 0 else NONE for j in range(n, 0, -1)])
            held_y.append(raw[t])
            held_bin.append(sum(1 for e in EDGES if expected >= e))
            count_code.append(by_k[5])
            read_code.append([rows[key] for rows in codes])
    held_win, held_y, held_bin = np.array(held_win), np.array(held_y), np.array(held_bin)
    count_code, read_code = np.array(count_code), np.array(read_code)
    count = len(held_y)
    sets = [(nm, held_bin == i) for i, nm in enumerate(NAMES)] + [("all", np.ones(count, dtype=bool))]
    row = lambda c: " | ".join(f"{sn!r} code={c[sel].mean():.3f} draw_agrees={np.exp(-c[sel]).mean():.3f}" for sn, sel in sets if sel.any())
    print(f"STRIDE slice={name} kind={kind} places={count} train_octets={len(train)} passes={passes} window={n} shares: "
          + " ".join(f"{nm!r}={sel.mean():.3f}" for nm, sel in sets[:-1]), flush=True)
    print(f"STRIDE slice={name} count_of_5_places: {row(count_code)}", flush=True)
    for r, (nm, _) in enumerate(reads):
        print(f"STRIDE slice={name} read={nm}: {row(read_code[:, r])}", flush=True)
    seq = np.frombuffer(train, dtype=np.uint8).astype(np.int64)
    rng = np.random.default_rng(20261118)
    fitted = []
    for c, opening in sizes:
        # The fixed advance is the control, read at the first size alone (where that size opens drawn).
        for label, strides in (("strides", True), ("fixed", False)) if (c, opening) == sizes[0] and opening == "drawn" else (("strides", True),):
            reader, trace = fit_reader(seq, c, strides, passes, n, held_win, held_y, rng, opening=opening)
            rho, spread = reader.shape()
            tag = f"{label}_{c}_circles" + ("" if opening == "drawn" else f"_opened_{opening}")
            fitted.append((tag, reader))
            print(f"STRIDE slice={name} {tag} the fit's held code after each pass: " + " ".join(f"{v:.4f}" for v in trace)
                  + f" | mean modulus {rho:.3f} | the symbols' strides spread {spread:.0f} thousandths of a turn", flush=True)
            print(f"STRIDE slice={name} {tag}: {row(code_of(reader, held_win, held_y))}", flush=True)
    if tail:
        lexp, panel, n_places, draws = tail[0], tail[1], int(tail[2]), int(tail[3])
        lexicon = pickle.load(open(lexp, "rb"))[name]
        prompts = [l.rstrip("\n").split("\t")[1].replace("\\n", "\n").encode("utf-8", "replace")
                   for l in open(panel, newline="\n", errors="replace") if l.split(":")[0] == name]
        for tag, reader in fitted:
            words = hits = 0
            for p, prompt in enumerate(prompts):
                # Every draw of a prompt is written together, a place at a time.
                seqs = [list(prompt[-n:]) for _ in range(draws)]
                rnds = [random.Random(f"{name}:{p}:{d}:{tag}") for d in range(draws)]
                start = len(seqs[0])
                for _ in range(n_places):
                    win = np.array([[s[-j] if j <= len(s) else NONE for j in range(n, 0, -1)] for s in seqs])
                    f = reader.faces(win)
                    for d in range(draws):
                        seqs[d].append(rnds[d].choices(range(256), weights=f[d].tolist())[0])
                for s in seqs:
                    for m in WORD.finditer(bytes(s[start:]).decode("utf-8", "replace")):
                        words += 1
                        hits += m.group(0).lower() in lexicon
            print(f"STRIDE_WRITER slice={name} prompts={len(prompts)} draws={draws} places={n_places} {tag}: {hits}/{words}({100 * hits // max(words, 1)}%)", flush=True)

if __name__ == "__main__":
    main()
