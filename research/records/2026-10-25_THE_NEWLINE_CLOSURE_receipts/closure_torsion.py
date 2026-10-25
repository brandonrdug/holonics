"""The newline origin's closure system on written sums, read exactly (integers and residues only).

A line is `a+b=c` written in base b. A loop runs from a newline to the arrival of the result's last
digit c0: it meets the pairs (seam, arriving) of every byte after the newline up to, and not
including, the pair into c0. Its row is N_t theta - psi(c0) = 0 (mod n), one column per
(seam, arriving) pair met and one per class of c0 (the tower record, "The machine locates the
carriage key by loop closure"). A key modulo n that no rational key reduces to exists only where the
system has torsion: where its rank modulo a prime falls below its rank over the rationals.

A. Base 10, a, b < 100 (10,000 lines): the rational rank, certified (at least the rank modulo
   P = 2^31 - 1, at most the column count less the integer kernel vectors checked exactly); the gcd
   of several maximal minors' determinants (Bareiss, exact) and the rank modulo each of its primes.
B. The key modulo 11 in closed form, checked on every true line, and on every false line
   a+b=c' with c' = a + b + delta, 0 < |delta| <= 30: it closes exactly when delta = 0 (mod 11).
   It is no rational key: its integer residual is nonzero on some true line.
C. The units key modulo 10 (the tower record's) and the pair of residues: c mod 10 and c mod 11 fix
   c mod 110; the lines whose c mod 110 leaves two candidates in 0..198 (x and x + 110); the
   result's length separates them and is the tens' carry-out a1 + b1 + k0 >= 10 (k0 the units'
   carry); the leading digit alone does not (1 and 111).
D. Split by the result's length (c < 100, c >= 100): neither half has torsion, and on each half the
   exact sum is a key over the integers, psi(d) = d, theta(\\n,y) = theta(+,y) = u y,
   theta(x,y) = v x + w y, theta(x,+) = theta(x,=) = z x, theta(=,y) = u' y, with
   (u, v, w, z, u') = (1, 9, 1, 0, -10) on the short half and (-10, 20, -10, 11, -120) on the long.
   On the union no such key exists: the two halves' sums agree only modulo b(b + 1) = 110.
E. Operands below b^2 in bases 3 to 9 and 12: the minors' gcd is b(b + 1) and the torsion primes
   are those of b(b + 1).
F. Operands below b^3 (all lines in bases 3, 4, 5; 6,000 seeded lines in bases 6, 7, 8, 10): the
   torsion primes are those of 2b.
"""
import math
import random
import sys
import time

P = 2**31 - 1
DIGITS = "0123456789abc"
T0 = time.monotonic()


def word(n, b):
    s = ""
    while True:
        s, n = DIGITS[n % b] + s, n // b
        if n == 0:
            return s


def lines_of(pairs, b):
    return [f"{word(x, b)}+{word(y, b)}={word(x + y, b)}" for x, y in pairs]


def loop_rows(lines, b=10):
    cols, rows = {}, []
    for s in lines:
        seq = "\n" + s
        row = {}
        for i in range(1, len(seq) - 1):
            j = cols.setdefault((seq[i - 1], seq[i]), len(cols))
            row[j] = row.get(j, 0) + 1
        rows.append((row, s[-1]))
    for d in DIGITS[:b]:
        cols.setdefault(("psi", d), len(cols))
    for row, c0 in rows:
        j = cols[("psi", c0)]
        row[j] = row.get(j, 0) - 1
    return [r for r, _ in rows], cols


def echelon_mod(rows, p):
    """Rank modulo p, the indices of the rows kept, and their pivot columns."""
    basis, kept = {}, []
    for t, row in enumerate(rows):
        v = {k: x % p for k, x in row.items() if x % p}
        while v:
            piv = min(v)
            if piv in basis:
                b, f = basis[piv], v[piv]
                for k, x in b.items():
                    y = (v.get(k, 0) - f * x) % p
                    if y:
                        v[k] = y
                    else:
                        v.pop(k, None)
            else:
                inv = pow(v[piv], -1, p)
                basis[piv] = {k: x * inv % p for k, x in v.items()}
                kept.append(t)
                break
    return len(basis), kept, sorted(basis)


def nullspace_mod(rows, ncol, p):
    piv_rows, piv_cols = [], []
    for row in rows:
        v = [0] * ncol
        for k, x in row.items():
            v[k] = x % p
        for pr, pc in zip(piv_rows, piv_cols):
            if v[pc]:
                f = v[pc]
                v = [(a - f * b) % p for a, b in zip(v, pr)]
        nz = next((i for i, a in enumerate(v) if a), None)
        if nz is None:
            continue
        inv = pow(v[nz], -1, p)
        v = [a * inv % p for a in v]
        for i in range(len(piv_rows)):
            if piv_rows[i][nz]:
                f = piv_rows[i][nz]
                piv_rows[i] = [(a - f * b) % p for a, b in zip(piv_rows[i], v)]
        piv_rows.append(v)
        piv_cols.append(nz)
    out = []
    for fc in (c for c in range(ncol) if c not in set(piv_cols)):
        x = [0] * ncol
        x[fc] = 1
        for pr, pc in zip(piv_rows, piv_cols):
            x[pc] = -pr[fc] % p
        out.append([a if a <= p // 2 else a - p for a in x])
    return out


def bareiss_det(m):
    m = [r[:] for r in m]
    n, sign, prev = len(m), 1, 1
    for k in range(n - 1):
        if m[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if m[i][k]), None)
            if sw is None:
                return 0
            m[k], m[sw] = m[sw], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]


def primes_of(n, bound=2**20):
    """The prime factors of |n| below the bound, and the cofactor left (1 when fully read)."""
    n, out, d = abs(n), [], 2
    while d * d <= n and d < bound:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1
    if 1 < n < d * d:
        out.append(n)
        n = 1
    return sorted(set(out)), n


def torsion(rows, ncol, extra=(2, 3, 5, 7, 11, 13), orders=4):
    """Torsion primes: the rank modulo P, certified by the exact integer kernel; the gcd of the
    determinants of maximal minors from several row orders, factored; the rank modulo each candidate:
    a prime is torsion where the rank falls. Every torsion prime divides every maximal minor."""
    rq, kept0, pivs0 = echelon_mod(rows, P)
    kernel = nullspace_mod([rows[t] for t in kept0], ncol, P)  # every row is checked against it below
    exact = all(sum(row.get(k, 0) * x[k] for k in row) == 0 for row in rows for x in kernel)
    g = bareiss_det([[rows[t].get(c, 0) for c in pivs0] for t in kept0])
    for k in range(1, orders):
        order = list(range(len(rows)))
        random.Random(k).shuffle(order)
        _, kept, pivs = echelon_mod([rows[t] for t in order], P)
        g = math.gcd(g, bareiss_det([[rows[order[t]].get(c, 0) for c in pivs] for t in kept]))
    primes, cofactor = primes_of(g)
    cand = sorted(set(primes) | set(extra))
    falls = [p for p in cand if echelon_mod(rows, p)[0] < rq]
    return {"rows": len(rows), "columns": ncol, "rank_mod_P": rq, "integer_kernel": len(kernel),
            "kernel_exact": exact, "rank_certified": exact and rq + len(kernel) == ncol,
            "minor_gcd": g, "minor_gcd_primes": primes, "cofactor_unread": cofactor,
            "tested": cand, "torsion": falls}


def theta11(s, a):
    if s == "\n" and a.isdigit():
        return -(int(a) + 2)
    if s in "+=" and a.isdigit():
        return -int(a)
    if s.isdigit() and a.isdigit():
        return 2 * int(s) - int(a)
    return 0


def residual11(line):
    seq = "\n" + line
    t = sum(theta11(seq[i - 1], seq[i]) for i in range(1, len(seq) - 1))
    return t + (int(line[-1]) + 2)  # minus psi(c0), psi(d) = -(d + 2)


def theta10(s, a):
    return int(s) + 1 if s.isdigit() and a in "+=" else 0


def value_key(s, a, short):
    """The exact sum as a key, in the gauge of each half: short results (c < 100) and long (c >= 100)."""
    u, v, w, z, ue = (1, 9, 1, 0, -10) if short else (-10, 20, -10, 11, -120)
    if a.isdigit() and s in "\n+":
        return u * int(a)
    if s.isdigit() and a.isdigit():
        return v * int(s) + w * int(a)
    if s.isdigit() and a in "+=":
        return z * int(s)
    if s == "=" and a.isdigit():
        return ue * int(a)
    return 0


def say(part, value):
    print(part, f"elapsed_ms={int(1000 * (time.monotonic() - T0))}", value, flush=True)


def main():
    two = [(a, b) for a in range(100) for b in range(100)]
    sums = lines_of(two, 10)
    rows, cols = loop_rows(sums)
    out = {"A": torsion(rows, len(cols))}
    say("A", out["A"])

    true_ok = all(residual11(s) % 11 == 0 for s in sums)
    integer_nonzero = sum(1 for s in sums if residual11(s) != 0)
    closes = {"delta_0_mod_11": [0, 0], "delta_not_0_mod_11": [0, 0]}
    as_function = True
    for a, b in two:
        for delta in range(-30, 31):
            c = a + b + delta
            if delta == 0 or c < 0:
                continue
            r = residual11(f"{a}+{b}={c}") % 11
            as_function &= r == (c - a - b) % 11
            k = "delta_0_mod_11" if delta % 11 == 0 else "delta_not_0_mod_11"
            closes[k][0] += r == 0
            closes[k][1] += 1
    out["B"] = {"true_lines_close": true_ok, "true_lines_with_nonzero_integer_residual": integer_nonzero,
                "false_lines_closing": closes, "residual_is_c_minus_a_minus_b_mod_11": as_function}
    say("B", out["B"])

    def res10(line):
        seq = "\n" + line
        return sum(theta10(seq[i - 1], seq[i]) for i in range(1, len(seq) - 1)) - (int(line[-1]) + 2)
    units_ok = all(res10(s) % 10 == 0 for s in sums)
    pairs, by_length, by_lead, by_carry = 0, True, True, True
    for a, b in two:
        c = a + b
        cand = [x for x in range(199) if x % 110 == c % 110]
        if len(cand) > 1:
            pairs += 1
            by_length &= len({len(str(x)) for x in cand}) == len(cand)
            by_lead &= len({str(x)[0] for x in cand}) == len(cand)
        k0 = (a % 10 + b % 10) >= 10
        by_carry &= (len(str(c)) == 3) == (a // 10 + b // 10 + k0 >= 10)
    out["C"] = {"units_key_closes_every_line": units_ok, "lines_with_two_candidates_mod_110": pairs,
                "length_separates_them": by_length, "leading_digit_separates_them": by_lead,
                "length_is_the_tens_carry_out": by_carry}
    say("C", out["C"])

    out["D"] = {}
    for name, keep in (("c<100", lambda a, b: a + b < 100), ("c>=100", lambda a, b: a + b >= 100)):
        half = lines_of([(a, b) for a, b in two if keep(a, b)], 10)
        r, cl = loop_rows(half)
        out["D"][name] = torsion(r, len(cl))
        x = [0] * len(cl)
        for key, j in cl.items():
            x[j] = int(key[1]) if key[0] == "psi" else value_key(*key, short=name == "c<100")
        out["D"][f"value_key_closes_{name}_exactly"] = all(
            sum(row.get(k, 0) * x[k] for k in row) == 0 for row in r)
    say("D", out["D"])

    out["E"] = {}
    for base in (3, 4, 5, 6, 7, 8, 9, 12):
        r, cl = loop_rows(lines_of([(x, y) for x in range(base * base) for y in range(base * base)], base),
                          base)
        t = torsion(r, len(cl), extra=(2, 3, 5, 7, 11, 13))
        out["E"][base] = {k: t[k] for k in ("rows", "columns", "rank_mod_P", "rank_certified",
                                            "minor_gcd", "cofactor_unread", "torsion")}
        out["E"][base]["predicted"] = primes_of(base * (base + 1))[0]
        say(f"E{base}", out["E"][base])

    out["F"] = {}
    rng = random.Random(20261025)
    for base in (3, 4, 5, 6, 7, 8, 10):
        n = base ** 3
        if n * n <= 20000:
            pairs3 = [(x, y) for x in range(n) for y in range(n)]
        else:
            pairs3 = [(rng.randrange(n), rng.randrange(n)) for _ in range(6000)]
        r, cl = loop_rows(lines_of(pairs3, base), base)
        t = torsion(r, len(cl), extra=(2, 3, 5, 7, 11, 13), orders=3)
        out["F"][base] = {k: t[k] for k in ("rows", "columns", "rank_mod_P", "rank_certified",
                                            "minor_gcd", "cofactor_unread", "torsion")}
        out["F"][base]["predicted"] = primes_of(2 * base)[0]
        say(f"F{base}", out["F"][base])

    fail = []
    if out["A"]["torsion"] != [2, 5, 11] or out["A"]["minor_gcd"] != 110 or not out["A"]["rank_certified"]:
        fail.append("A")
    if not (true_ok and integer_nonzero and as_function and closes["delta_0_mod_11"][0] == closes["delta_0_mod_11"][1]
            and closes["delta_not_0_mod_11"][0] == 0):
        fail.append("B")
    if not (units_ok and by_length and not by_lead and by_carry):
        fail.append("C")
    if any(out["D"][h]["torsion"] or not out["D"][h]["rank_certified"] for h in ("c<100", "c>=100")) \
            or not (out["D"]["value_key_closes_c<100_exactly"] and out["D"]["value_key_closes_c>=100_exactly"]):
        fail.append("D")
    for part in ("E", "F"):
        for base, t in out[part].items():
            if t["torsion"] != t["predicted"] or not t["rank_certified"] or t["cofactor_unread"] != 1:
                fail.append(f"{part}{base}")
    for base, t in out["E"].items():
        if abs(t["minor_gcd"]) != base * (base + 1):
            fail.append(f"E{base}gcd")
    say("fail", fail)
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
