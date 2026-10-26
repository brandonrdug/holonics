#!/usr/bin/env python3
"""Exact receipt for the binding bank (record 2026-10-26, "THE BINDING BANK IS A STRAND ...").

Everything is exact: rationals (Fraction) in the cyclotomic field Q(zeta_32), stored as
coefficients on 1, x, ..., x^15 with x^16 = -1 (x = zeta_32 = e^(i pi/16)). A key's turn s is
held in sixteenths of a half turn, s = a/16, so rung n's phase is e^(i pi n s) = zeta_32^(n a).
The bank has 16 rungs (n = 0..15); the character grid is a even (s on 2/16 = 1/8 of a half turn).

Parts
  A  the rung box's kernel K(d) = sum_n zeta^(n d): 16 at d = 0, 0 on the rest of the grid, nonzero off it
  B  exact recall of 16 bindings on the grid; a 17th on a used residue superposes (additive)
     or overwrites (delta)
  C  an off-grid key leaks into a grid read by exactly 2 v / (16 (1 - zeta^d)), d = a_read - a_write
  D  recurrent and chunked forms (delta write, gate, decay) give identical reads on every partition
  E  an antecedent-clocked bank can express in-context copying (keys hand-set here only to show reach)
  F  the MQAR terrain: an exact generator, its first passage, and the SHA-256 of the held-out set
"""
from fractions import Fraction as Q
import hashlib

D = 16                      # degree of Phi_32 = x^16 + 1
RUNGS = 16                  # |N| = 2^4, so the read's 1/|N| is a dyadic shift


# ---------- Q(zeta_32) ----------
def zero():
    return [Q(0)] * D


def const(c):
    z = zero()
    z[0] = Q(c)
    return z


def zpow(k):
    """zeta_32^k."""
    k %= 32
    z = zero()
    if k < 16:
        z[k] = Q(1)
    else:
        z[k - 16] = Q(-1)
    return z


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def scale(a, c):
    return [x * c for x in a]


def mul(a, b):
    out = [Q(0)] * D
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y == 0:
                continue
            k = i + j
            if k < D:
                out[k] += x * y
            else:
                out[k - D] -= x * y
    return out


def conj(a):
    """complex conjugate: zeta^k -> zeta^(-k)."""
    out = zero()
    for k, x in enumerate(a):
        if x == 0:
            continue
        out = add(out, scale(zpow(-k), x))
    return out


def is_rational(a):
    return all(x == 0 for x in a[1:])


def show(a):
    if is_rational(a):
        return str(a[0])
    return " + ".join(f"({x})z^{k}" for k, x in enumerate(a) if x != 0)


def phase(n, a):
    """rung n at key turn a/16 half turns."""
    return zpow(n * a)


# ---------- the bank ----------
class Bank:
    """S[n] is a value vector (length dv) of field elements, one per rung."""

    def __init__(self, dv):
        self.dv = dv
        self.S = [[zero() for _ in range(dv)] for _ in range(RUNGS)]

    def read(self, a):
        """vhat = 2^-4 sum_n e^(i pi n s) S_n."""
        out = [zero() for _ in range(self.dv)]
        for n in range(RUNGS):
            ph = phase(n, a)
            for c in range(self.dv):
                out[c] = add(out[c], mul(ph, self.S[n][c]))
        return [scale(x, Q(1, RUNGS)) for x in out]

    def write(self, a, v, g=Q(1), delta=True, rho=Q(1)):
        """S <- rho (S + g (v - [delta] read(a)) conj(phase))."""
        e = [const(x) if not isinstance(x, list) else x for x in v]
        if delta:
            r = self.read(a)
            e = [sub(x, y) for x, y in zip(e, r)]
        for n in range(RUNGS):
            cph = conj(phase(n, a))
            for c in range(self.dv):
                self.S[n][c] = scale(add(self.S[n][c], scale(mul(cph, e[c]), g)), rho)


def vec_eq(u, w):
    return all(x == y for x, y in zip(u, w))


def part_a():
    print("A  rung-box kernel K(d) = sum_{n<16} zeta_32^(n d)")
    on_grid_zero = 0
    off_grid_nonzero = 0
    for d in range(32):
        k = zero()
        for n in range(RUNGS):
            k = add(k, zpow(n * d))
        if d == 0:
            assert is_rational(k) and k[0] == 16
        elif d % 2 == 0:
            assert k == zero(), d
            on_grid_zero += 1
        else:
            assert k != zero(), d
            # closed form 2 / (1 - zeta^d): check (1 - zeta^d) K = 2
            assert mul(sub(const(1), zpow(d)), k) == const(2), d
            off_grid_nonzero += 1
    print(f"   K(0) = 16; zero at all {on_grid_zero} other grid differences; "
          f"nonzero (= 2/(1 - zeta^d)) at all {off_grid_nonzero} off-grid differences")


def values(i, dv=3):
    """deterministic rational values: no draw, a declared exact routine."""
    return [Q((7 * i + 3 * c + 1) % 23 - 11, 1 + (i + c) % 5) for c in range(dv)]


def part_b():
    print("B  16 bindings on the grid (keys a = 0, 2, ..., 30)")
    for delta in (False, True):
        bank = Bank(3)
        for i in range(16):
            bank.write(2 * i, values(i), delta=delta)
        for i in range(16):
            r = bank.read(2 * i)
            assert all(is_rational(x) for x in r)
            assert [x[0] for x in r] == values(i), (delta, i)
        # a 17th binding on residue 0
        bank.write(0, values(16), delta=delta)
        r0 = [x[0] for x in bank.read(0)]
        if delta:
            assert r0 == values(16)
        else:
            assert r0 == [x + y for x, y in zip(values(0), values(16))]
        for i in range(1, 16):
            assert [x[0] for x in bank.read(2 * i)] == values(i)
        print(f"   {'delta   ' if delta else 'additive'}: every key reads its value exactly; "
              f"rebinding key 0 reads {'the new value (overwrite)' if delta else 'old + new (superposed)'}; "
              f"the other 15 unchanged")


def part_c():
    print("C  an off-grid key leaks into a grid read")
    bank = Bank(1)
    v = [Q(5, 3)]
    bank.write(3, v, delta=False)          # key at a = 3 (odd: off the grid)
    for a in (0, 2, 4, 8):
        d = a - 3
        r = bank.read(a)[0]
        # expected leak 2 v / (16 (1 - zeta^d)) = v K(d)/16  ->  check 16 (1 - zeta^(a-3)) r = 2 v
        assert mul(sub(const(1), zpow(d)), scale(r, Q(16))) == const(2 * v[0]), a
    print("   read at grid key a after writing v at a = 3: 16 (1 - zeta^(a-3)) vhat = 2 v exactly "
          "(a = 0, 2, 4, 8); the leak vanishes only when the turn locks on the grid")


def recurrent(seq, S0=None):
    """seq: list of (a_key, v, g, rho, a_query). Returns reads vhat_t (after the write)."""
    bank = Bank(len(seq[0][1]))
    if S0 is not None:
        bank.S = [[list(x) for x in row] for row in S0]
    reads = []
    for (ak, v, g, rho, aq) in seq:
        bank.write(ak, v, g=g, delta=True, rho=rho)
        reads.append(bank.read(aq))
    return reads, bank.S


def inner(a1, a2):
    """<phi(a1), phi(a2)> = sum_n conj(phi_n(a1)) phi_n(a2) = K(a2 - a1)."""
    k = zero()
    for n in range(RUNGS):
        k = add(k, zpow(n * (a2 - a1)))
    return k


def chunked(seq, S0):
    """the chunk form: (I + L) E = V - P S0 phi, forward substitution (unit lower triangular,
    no division), then the reads from S0 and the news E. S_t = rho_t (S_(t-1) + g_t e_t phi_t^H)."""
    T = len(seq)
    dv = len(seq[0][1])
    # decay products: P[t] = prod_{s<=t} rho_s ; R(t, tau) = prod_{tau < s <= t} rho_s with rho at write
    rho = [x[3] for x in seq]

    def span(lo, hi):           # prod_{lo <= s <= hi} rho_s, empty = 1
        p = Q(1)
        for s in range(lo, hi + 1):
            p *= rho[s]
        return p

    def s0_read(a, decay):
        out = [zero() for _ in range(dv)]
        for n in range(RUNGS):
            ph = phase(n, a)
            for c in range(dv):
                out[c] = add(out[c], mul(ph, S0[n][c]))
        return [scale(x, decay / RUNGS) for x in out]

    E = []
    for t, (ak, v, g, _, _) in enumerate(seq):
        # S_(t-1) = span(0, t-1) S0 + sum_{tau<t} span(tau, t-1) g_tau e_tau phi_tau^H
        base = s0_read(ak, span(0, t - 1))
        acc = [sub(const(x), y) for x, y in zip(v, base)]
        for tau in range(t):
            w = scale(inner(seq[tau][0], ak), span(tau, t - 1) * seq[tau][2] / RUNGS)
            acc = [sub(x, mul(w, y)) for x, y in zip(acc, E[tau])]
        E.append(acc)
    reads = []
    for t, (_, _, _, _, aq) in enumerate(seq):
        out = s0_read(aq, span(0, t))
        for tau in range(t + 1):
            w = scale(inner(seq[tau][0], aq), span(tau, t) * seq[tau][2] / RUNGS)
            out = [add(x, mul(w, y)) for x, y in zip(out, E[tau])]
        reads.append(out)
    return reads


def part_d():
    print("D  recurrent = chunked (delta write, gate g, decay rho), on every partition")
    keys = [3, 0, 7, 2, 3, 12, 5, 0, 9, 3, 14, 1]          # odd ones are off the grid; 3 and 0 repeat
    queries = [0, 3, 2, 7, 12, 3, 1, 5, 0, 9, 3, 14]
    gs = [Q(1, 2), Q(3, 4), Q(1), Q(1, 4), Q(1, 2), Q(7, 8), Q(1, 2), Q(1), Q(3, 8), Q(1, 2), Q(5, 8), Q(1)]
    rhos = [Q(1), Q(4095, 4096), Q(1), Q(255, 256), Q(1), Q(4095, 4096),
            Q(1), Q(1), Q(511, 512), Q(1), Q(4095, 4096), Q(1)]
    seq = [(keys[t], values(t, 2), gs[t], rhos[t], queries[t]) for t in range(12)]
    ref, _ = recurrent(seq)
    for parts in ((12,), (4, 4, 4), (5, 7), (1,) * 12, (3, 9)):
        S = [[zero() for _ in range(2)] for _ in range(RUNGS)]
        got = []
        lo = 0
        for p in parts:
            chunk = seq[lo:lo + p]
            got += chunked(chunk, S)
            _, S = recurrent(chunk, S)          # carry the chunk's closing state to the next
            lo += p
        assert all(vec_eq(x, y) for x, y in zip(ref, got)), parts
    print("   12 cells, keys on and off the grid, two repeated keys, dyadic g and rho: reads identical "
          "for partitions (12), (4,4,4), (5,7), (1 x 12), (3,9)")
    print(f"   e.g. read at cell 5 (query 3): {show(ref[5][0])[:90]}...")


def part_e():
    print("E  antecedent clocking expresses in-context copying (reach only: keys hand-set here)")
    word = [5, 1, 6, 2, 7, 3]                    # six distinct classes
    passage = word + word
    res = {c: 2 * c for c in range(8)}            # class -> grid residue (hand-set for this check)
    onehot = lambda c: [Q(1) if j == c else Q(0) for j in range(8)]
    bank = Bank(8)
    hits = 0
    for t in range(1, len(passage)):
        # write: key = the antecedent (class before the arrival), value = the arrival
        bank.write(res[passage[t - 1]], onehot(passage[t]), delta=True)
        # read: query = the present class; the read names what followed it before
        r = [x[0] for x in bank.read(res[passage[t]])]
        if t >= len(word) and t + 1 < len(passage):
            assert r == onehot(passage[t + 1]), t
            hits += 1
    print(f"   second pass of a six-class word: the read names the next class exactly at all {hits} cells")
    # a class repeated inside the word with two successors: delta keeps the newer, additive both
    word2 = [1, 2, 1, 3]
    for delta in (False, True):
        bank = Bank(8)
        for t in range(1, len(word2)):
            bank.write(res[word2[t - 1]], onehot(word2[t]), delta=delta)
        r = [x[0] for x in bank.read(res[1])]
        if delta:
            assert r == onehot(3)
        else:
            assert r == [a + b for a, b in zip(onehot(2), onehot(3))]
    print("   '1 2 1 3', read at '1': additive names 2 and 3 together (plural); delta names 3 (the newer)")


def _stream(i):
    """SHA-256 in counter mode over the passage index: a declared exact routine, no draw."""
    n = 0
    while True:
        for byte in hashlib.sha256(b"mqar-2026-10-26:" + str(i).encode() + b":" + str(n).encode()).digest():
            yield byte
        n += 1


def _below(stream, m):
    """an integer in [0, m) by rejection on whole bytes (m <= 256), so every residue is equally reached."""
    lim = 256 - 256 % m
    while True:
        b = next(stream)
        if b < lim:
            return b % m


def _shuffle(stream, items):
    items = list(items)
    for j in range(len(items) - 1, 0, -1):
        k = _below(stream, j + 1)
        items[j], items[k] = items[k], items[j]
    return items


def mqar_passage(i):
    """The MQAR terrain, exact and declared. 64 key classes (0..63), 64 value classes (64..127),
    16 pairs, then the 16 keys again in another order, each followed by its value. Passage i
    takes 16 keys and 16 values by a Fisher-Yates shuffle driven by SHA-256 of its index, and
    its query order by a third shuffle. A key's value is fixed only inside its passage: no
    function of the key, and no rule read from a few pairs, names it."""
    st = _stream(i)
    keys = _shuffle(st, range(64))[:16]
    vals = [v + 64 for v in _shuffle(st, range(64))[:16]]
    order = _shuffle(st, range(16))
    cells = []
    for j in range(16):
        cells += [keys[j], vals[j]]
    for j in order:
        cells += [keys[j], vals[j]]
    return cells


def part_f():
    print("F  the MQAR terrain (fixed before any run)")
    p0 = mqar_passage(0)
    print("   passage 0:", " ".join(map(str, p0)))
    h = hashlib.sha256()
    for i in range(1_000_000, 1_001_000):       # held-out: passages 1,000,000 .. 1,000,999
        h.update(bytes(mqar_passage(i)) + b"\x00")
    print("   held-out passages 1,000,000..1,000,999 (64 cells each, answers at the 16 odd cells of the "
          "second half): sha256", h.hexdigest())
    # within a passage a key's value is fixed only by the passage: count how many held-out passages
    # bind key 0 to each value class, so no constitution can name the answer without the passage
    seen = {}
    for i in range(1_000_000, 1_001_000):
        p = mqar_passage(i)
        for j in range(16):
            if p[2 * j] == 0:
                seen[p[2 * j + 1]] = seen.get(p[2 * j + 1], 0) + 1
    print(f"   key 0 is bound to {len(seen)} different value classes across the held-out set "
          f"(the largest share {max(seen.values())} of {sum(seen.values())})")
    # training passages 0..999,999 and the held-out set share no passage index; check the first
    # 1,000 training passages share no whole passage with the held-out set
    held = {bytes(mqar_passage(i)) for i in range(1_000_000, 1_001_000)}
    assert not any(bytes(mqar_passage(i)) in held for i in range(1_000))
    print("   no held-out passage equals any of the first 1,000 training passages")


if __name__ == "__main__":
    import time
    for part in (part_a, part_b, part_c, part_d, part_e, part_f):
        t0 = time.perf_counter_ns()
        part()
        print(f"   [{part.__name__}: {(time.perf_counter_ns() - t0) // 1_000_000} ms]")
    print("all checks hold")
