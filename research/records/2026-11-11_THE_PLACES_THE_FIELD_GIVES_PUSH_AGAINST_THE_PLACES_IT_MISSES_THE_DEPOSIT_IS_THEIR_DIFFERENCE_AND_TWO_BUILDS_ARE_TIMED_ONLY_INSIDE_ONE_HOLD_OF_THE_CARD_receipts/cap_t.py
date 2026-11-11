# Host ruler (never machinery; floats and count tables are the ruler's own): a CHAIN OF COUNT TABLES THAT MARGINALIZES ITS OPEN LETTERS.
#
# The field's held joint (`FIELD_JOINT_NATS`) is the order-averaged joint code of an answer: K of its m sites open, K uniform on 1..m, each
# open site coded beside the written ones, weighed m/K. A model that is one joint law codes every order alike, so its order-averaged code is
# its left-to-right code (less the code of what it is told: the answer's length). This ruler takes the chain of Witten-Bell tables of
# DEPTH left letters (yard.py's LEFT ONLY tables, the same numbers), reads it as one Markov chain on the longest met suffix of its
# history, and codes each open site by the chain's own conditional given every written letter on both sides (forward and backward sums
# over the chain's states, open letters summed out). It prints that code by the quarter of 1..m the count of open sites was drawn from
# (the field's `FIELD_JOINT_STRATA`), the field's two other held states (every fourth site open; every site open), and the left-to-right
# code less the length's that the strata must average to.
#
#   cap_t.py selftest                     controls on a drawn source (no passage is read): the conditionals against enumeration, one
#                                         order's chain-rule sum against the left-to-right code, the strata's mean against it
#   cap_t.py DEPTH [PROCESSES] [given|free] [SEED]   the read on HELD128; `given` (the default) tells the chain the answer's length
#                                         as the field's region does (no void before the last site, the void at it); `free` does
#                                         not. SEED (sixteen hex digits, the last word of the run's key file) draws the field's own
#                                         states (`joint_states`: the same K a stratum, the same open sites), so the two reads pair
#                                         state by state; `open_sites` then prints the field's four counts. Without it, own draws.
#
#   cap_t.py DEPTH left                    the left-to-right code alone (seconds): on every place, and on the places with at least 1, 2,
#                                         3 and 4 of the answer's letters before them, which are the places the grip record's count
#                                         tables were read on (43,214 at two letters, 43,087 at three, 42,960 at four)
#
# numpy alone. A forward sum is held on its support (a written run of DEPTH letters brings it back to one state), so a state of the
# answer costs its open sites times the support times the alphabet; the forward sums are kept every STRIDE sites and walked again a
# stretch at a time, so the memory is a stretch of them.
import numpy as np, sys, time


def contexts(x, seg, d, B, PAD):
    """The code of the d letters before each place (PAD before a segment's start), the nearest letter in the lowest digit (yard.ctx's)."""
    n = len(x)
    c = np.zeros(n, np.int64)
    for k in range(d, 0, -1):
        prev = np.full(n, PAD, np.int64)
        ok = seg[k:] == seg[:-k]
        prev[k:][ok] = x[:-k][ok]
        c = c * B + prev
    return c


def build(x, seg, depth, B, PAD):
    """The chain: states are the met contexts of 0..depth letters; P[s, y] the Witten-Bell share of letter y after s; nxt[s, y] the state
    after it (the longest met suffix of s then y)."""
    E = B - 1
    uni = np.bincount(x, minlength=B).astype(np.float64) + 0.5
    uni /= uni.sum()
    codes = [np.zeros(1, np.int64)]
    tables = [uni[None, :E].copy()]
    for d in range(1, depth + 1):
        c = contexts(x, seg, d, B, PAD)
        uc, inv = np.unique(c, return_inverse=True)
        counts = np.bincount(inv * E + x, minlength=len(uc) * E).reshape(len(uc), E).astype(np.float64)
        n = counts.sum(1)
        lam = np.maximum((counts > 0).sum(1), 1).astype(np.float64)
        suffix = np.searchsorted(codes[d - 1], uc % (B ** (d - 1)))
        assert (codes[d - 1][suffix] == uc % (B ** (d - 1))).all(), "a met context's suffix is met"
        tables.append((counts + lam[:, None] * tables[d - 1][suffix]) / (n + lam)[:, None])
        codes.append(uc)
    off = np.concatenate([[0], np.cumsum([len(c) for c in codes])])
    P = np.concatenate(tables, 0)
    nxt = np.zeros((off[-1], E), np.int32)
    letters = np.arange(E, dtype=np.int64)
    for d in range(depth + 1):
        cand = codes[d][:, None] * B + letters[None, :]
        done = np.zeros(cand.shape, bool)
        for L in range(min(d + 1, depth), -1, -1):
            c = cand % (B ** L) if L > 0 else np.zeros_like(cand)
            i = np.searchsorted(codes[L], c)
            i[i >= len(codes[L])] = 0
            hit = (codes[L][i] == c) & ~done
            nxt[off[d]:off[d + 1]][hit] = (off[L] + i[hit]).astype(np.int32)
            done |= hit
        assert done.all()
    start_code = sum(PAD * B ** j for j in range(depth))
    i = np.searchsorted(codes[depth], start_code)
    assert codes[depth][i] == start_code, "the context of a segment's first place is met"
    return {"P": P, "nxt": nxt, "start": int(off[depth] + i), "E": E, "S": int(off[-1]), "depth": depth, "all": np.arange(int(off[-1]))}


def forward_step(chain, idx, val, ncol, letter):
    """One site's transfer of a forward sum held on its support `idx`: a written letter (`ncol` 0), or an open site summed over its
    first `ncol` letters (the void is the last letter, so `E - 1` leaves it out). Returns the new support, its shares and their sum."""
    P, nxt, S = chain["P"], chain["nxt"], chain["S"]
    if ncol == 0:
        tgt = nxt[idx, letter]
        w = val * P[idx, letter]
    elif len(idx) == S:
        tgt = nxt[:, :ncol].ravel()
        w = (val[:, None] * P[:, :ncol]).ravel()
    else:
        tgt = nxt[idx, :ncol].ravel()
        w = (val[:, None] * P[idx, :ncol]).ravel()
    if len(tgt) * 8 < S:
        nidx, inv = np.unique(tgt, return_inverse=True)
        nval = np.bincount(inv.ravel(), weights=w, minlength=len(nidx))
    else:
        f = np.bincount(tgt, weights=w, minlength=S)
        nidx = np.flatnonzero(f)
        nval = f[nidx]
    if len(nidx) == S:
        nidx = chain["all"]
    z = nval.sum()
    return nidx, nval / z, z


STRIDE = 64


def conditionals(chain, a, is_open, given):
    """The chain's code of each open site given every written letter (and, `given`, the answer's length): forward sums on their
    supports, backward sums read on those supports. Also the code of what is written and told, `-log` of its share."""
    P, nxt, S, E = chain["P"], chain["nxt"], chain["S"], chain["E"]
    m = len(a)
    ncol = np.zeros(m, np.int64)
    ncol[is_open] = E - 1 if given else E
    if given:
        ncol[m - 1] = 0
    marks = []
    idx, val, told = np.array([chain["start"]]), np.ones(1), 0.0
    for t in range(m):
        if t % STRIDE == 0:
            marks.append((idx, val))
        idx, val, z = forward_step(chain, idx, val, int(ncol[t]), int(a[t]))
        told -= np.log(z)
    out = np.zeros(m)
    # The backward sum is read only at the states a forward sum reaches, so one array serves and is written on each support.
    b = np.ones(S)
    for j in range(len(marks) - 1, -1, -1):
        lo, hi = j * STRIDE, min(m, (j + 1) * STRIDE)
        idx, val = marks[j]
        fwd = []
        for t in range(lo, hi):
            fwd.append((idx, val))
            if t + 1 < hi:
                idx, val, _ = forward_step(chain, idx, val, int(ncol[t]), int(a[t]))
        for t in range(hi - 1, lo - 1, -1):
            idx, val = fwd[t - lo]
            n = int(ncol[t])
            if n == 0:
                bn = P[idx, a[t]] * b[nxt[idx, a[t]]]
            else:
                if len(idx) == S:
                    M = P[:, :n] * b[nxt[:, :n]]
                else:
                    M = P[idx, :n] * b[nxt[idx, :n]]
                w = val @ M
                out[t] = -np.log(w[a[t]] / w.sum())
                bn = M.sum(1)
            b[idx] = bn / bn.max()
    return out, told


def left_codes(chain, a):
    """Each place's code read left to right, nothing told."""
    s, out = chain["start"], np.zeros(len(a))
    for t, y in enumerate(a):
        out[t] = -np.log(chain["P"][s, y])
        s = chain["nxt"][s, y]
    return out


def left_to_right(chain, a):
    return left_codes(chain, a).sum()


def strata_of(m):
    return [(1 + s * m // 4, 1 + (s + 1) * m // 4) for s in range(4)]


M64 = (1 << 64) - 1
JOINT_KEY = 9 << 58


def mix(seed, counter):
    """field_train.rs's `mix`: the exterior mask stream."""
    z = (seed + counter * 0x9E3779B97F4A7C15) & M64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
    return z ^ (z >> 31)


def draws(m, key, seed, rng):
    """A problem's rank of sites and its K a stratum: `joint_states`' keyed draws under a seed, the ruler's own without one."""
    strata = [(lo, hi) for lo, hi in strata_of(m)]
    if seed is None:
        rank = rng.permutation(m)
        ks = [int(lo + rng.integers(hi - lo)) if hi > lo else 0 for lo, hi in strata]
    else:
        rank = np.array(sorted(range(m), key=lambda j: (mix(seed, JOINT_KEY ^ key ^ ((j + 1) << 20)), j)))
        ks = [lo + mix(seed, JOINT_KEY ^ key ^ (s + 1)) % (hi - lo) if hi > lo else 0 for s, (lo, hi) in enumerate(strata)]
    return rank, strata, ks


def read_problem(args):
    chain, a, key, seed, given = args
    m = len(a)
    rank, strata, ks = draws(m, key, seed, np.random.default_rng(7000 + key))
    res = np.zeros((4, 3))
    for s, (lo, hi) in enumerate(strata):
        if hi <= lo:
            continue
        k = ks[s]
        is_open = np.zeros(m, bool)
        is_open[rank[:k]] = True
        code, _ = conditionals(chain, a, is_open, given)
        res[s] = ((hi - lo) / k * code[is_open].sum(), hi - lo, k)
    # The field's context read: every fourth site open, each site read once; and every site open, whose told code is the length's.
    ctx = 0.0
    for r in range(4):
        is_open = (np.arange(m) % 4) == r
        if is_open.any():
            ctx += conditionals(chain, a, is_open, given)[0][is_open].sum()
    opening, told = conditionals(chain, a, np.ones(m, bool), given)
    return res, ctx, opening.sum(), left_to_right(chain, a), m, told


GLOBAL = {}


def _work(job):
    i, key = job
    return read_problem((GLOBAL["chain"], GLOBAL["answers"][i], key, GLOBAL["seed"], GLOBAL["given"]))


def selftest():
    # The mixer against SplitMix64's first outputs from a zero state; a keyed draw's shape.
    assert mix(0, 1) == 0xE220A8397B1DCDAF and mix(0, 2) == 0x6E789E6AA1B965F4 and mix(0, 3) == 0x06C45D188009454F
    for m in (1, 2, 3, 7, 40):
        rank, strata, ks = draws(m, 3, 0x0123456789ABCDEF, None)
        assert sorted(rank) == list(range(m)) and sum(hi - lo for lo, hi in strata) == m
        assert all(lo <= k < hi for (lo, hi), k in zip(strata, ks) if hi > lo)
    rng = np.random.default_rng(5)
    E, PAD = 5, 5
    B, VOID = E + 1, E - 1
    # A drawn source of order two with an end letter.
    src = rng.dirichlet(np.ones(E) * 0.4, size=(E + 1, E + 1))

    def draw(nseq):
        xs, seg = [], []
        for k in range(nseq):
            a, b, seq = E, E, []
            while True:
                y = int(rng.choice(E, p=src[a, b]))
                if y == VOID and not seq:
                    continue
                seq.append(y)
                if y == VOID or len(seq) > 40:
                    if y != VOID:
                        seq.append(VOID)
                    break
                a, b = b, y
            xs.append(np.array(seq, np.int64))
            seg.append(np.full(len(seq), k, np.int32))
        return xs, np.concatenate(xs), np.concatenate(seg)

    _, x, seg = draw(4000)
    held, _, _ = draw(300)
    global STRIDE
    for depth, STRIDE in ((1, 64), (2, 3), (3, 5)):
        chain = build(x, seg, depth, B, PAD)
        # 1. Enumeration: a short answer, the conditionals of its open sites against the sum over every completion.
        worst, tried = 0.0, 0
        for a in [h for h in held if 3 <= len(h) <= 7][:12]:
            m = len(a)
            for given in (True, False):
                is_open = rng.random(m) < 0.6
                got, told = conditionals(chain, a, is_open, given)
                sites = np.array([t for t in np.flatnonzero(is_open) if not (given and t == m - 1)], np.int64)
                if len(sites) == 0:
                    continue
                letters = [y for y in range(E) if not (given and y == VOID)]
                mass = {}
                for combo in np.ndindex(*([len(letters)] * len(sites))):
                    b = a.copy()
                    b[sites] = [letters[c] for c in combo]
                    mass[combo] = np.exp(-left_to_right(chain, b))
                total = sum(mass.values())
                worst = max(worst, abs(-np.log(total) - told))
                for j, t in enumerate(sites):
                    here = letters.index(int(a[t]))
                    p = sum(v for c, v in mass.items() if c[j] == here) / total
                    worst = max(worst, abs(-np.log(p) - got[t]))
                    tried += 1
        assert tried > 20 and worst < 1e-9, (tried, worst)
        # 2. One order's chain-rule sum is the left-to-right code less the code of what the chain is told (the chain is one joint law).
        gap = 0.0
        for given in (True, False):
            for a in held[:40]:
                m = len(a)
                order = rng.permutation(m)
                total = 0.0
                for j in range(m):
                    is_open = np.zeros(m, bool)
                    is_open[order[j:]] = True
                    total += conditionals(chain, a, is_open, given)[0][order[j]]
                told = conditionals(chain, a, np.ones(m, bool), given)[1]
                gap = max(gap, abs(total - (left_to_right(chain, a) - told)))
        assert gap < 1e-8, gap
        # 3. The stratified read averages to the same code within its sampling spread.
        line = []
        for given in (True, False):
            GLOBAL.update(chain=chain, answers=held, given=given, seed=None)
            runs = [_work((i, 1000 * r + i)) for r in range(6) for i in range(len(held))]
            GLOBAL.update(seed=0x9E3779B97F4A7C15)
            runs += [_work((i, i)) for i in range(len(held))]
            strat = sum(r[0][:, 0].sum() for r in runs) / 7
            l2r = sum(r[3] - r[5] for r in runs) / 7
            places = sum(r[4] for r in runs) / 7
            assert abs(strat - l2r) / places < 0.02, (strat / places, l2r / places)
            line.append("%s %.4f against %.4f" % ("given" if given else "free", strat / places, l2r / places))
        print("cap_t selftest depth %d, forward sums kept every %d sites: states %d; enumeration of %d sites within %.1e; one order's sum within %.1e of the left-to-right code less the told; strata, nats a place: %s"
              % (depth, STRIDE, chain["S"], tried, worst, gap, "; ".join(line)))
    STRIDE = 64
    print("cap_t: 3 depths, the controls hold")


def main():
    if sys.argv[1] == "selftest":
        return selftest()
    depth = int(sys.argv[1])
    left = len(sys.argv) > 2 and sys.argv[2] == "left"
    procs = 1 if left else int(sys.argv[2]) if len(sys.argv) > 2 else 8
    given = (sys.argv[3] if len(sys.argv) > 3 else "given") == "given"
    seed = int(sys.argv[4], 16) if len(sys.argv) > 4 else None
    t0 = time.time()
    ns = {}
    exec(open("yard.py").read().split("xT,sT=load")[0], ns)
    B, PAD, VOID = ns["B"], ns["PAD"], ns["VOID"]
    assert VOID == B - 2 and PAD == B - 1
    z = np.load("train.npz")
    xT, sT = z["x"].astype(np.int64), z["seg"]
    xH, sH = ns["load"]("HELD128.txt")
    chain = build(xT, sT, depth, B, PAD)
    cuts = np.flatnonzero(np.diff(sH)) + 1
    answers = np.split(xH, cuts)
    assert all(a[-1] == VOID and (a[:-1] != VOID).all() for a in answers)
    print("CHAIN depth=%d states=%d answers=%d places=%d longest=%d length=%s draws=%s processes=%d built_s=%.0f"
          % (depth, chain["S"], len(answers), len(xH), max(len(a) for a in answers), "given" if given else "free",
             "own" if seed is None else "the field's", procs, time.time() - t0), flush=True)
    if left:
        codes = [left_codes(chain, a) for a in answers]
        rows = [(sum(c[g:].sum() for c in codes), sum(max(len(c) - g, 0) for c in codes)) for g in range(5)]
        print("CHAIN_LEFT depth=%d states=%d letters_before_at_least=0/1/2/3/4 nats_a_place=%s places=%s"
              % (depth, chain["S"], "/".join("%.6f" % (t / n) for t, n in rows), "/".join("%d" % n for _, n in rows)))
        return
    GLOBAL.update(chain=chain, answers=answers, given=given, seed=seed)
    # The longest answers first, so the processes end together; a problem's key is its place in the held file, as the field's.
    jobs = sorted(((i, i) for i in range(len(answers))), key=lambda j: -len(answers[j[0]]))
    if procs > 1:
        import multiprocessing as mp
        with mp.get_context("fork").Pool(procs) as pool:
            results = pool.map(_work, jobs, chunksize=1)
    else:
        results = [_work(j) for j in jobs]
    strata = sum(r[0] for r in results)
    places = sum(r[4] for r in results)
    ctx = sum(r[1] for r in results)
    opening = sum(r[2] for r in results)
    l2r = sum(r[3] for r in results)
    told = sum(r[5] for r in results)
    print("CHAIN_STRATA depth=%d open_quarters=1/2/3/4 nats_a_place=%s places=%s open_sites=%s"
          % (depth, "/".join("%.6f" % (strata[s, 0] / strata[s, 1]) for s in range(4)), "/".join("%d" % strata[s, 1] for s in range(4)),
             "/".join("%d" % strata[s, 2] for s in range(4))))
    print("CHAIN_JOINT depth=%d order_averaged_nats_a_place=%.6f left_to_right_nats_a_place=%.6f length_nats_a_place=%.6f every_fourth_open_nats_a_place=%.6f every_site_open_nats_a_place=%.6f places=%d s=%.0f"
          % (depth, strata[:, 0].sum() / places, l2r / places, told / places, ctx / places, opening / places, places, time.time() - t0))


if __name__ == "__main__":
    main()
