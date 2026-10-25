"""The newline origin's closure system on written differences, read exactly (integers and residues only).

A line is `a-b=c` with b <= a, written in base b; its loop and row are those of closure_torsion.py
(the pair into c0 excluded, one column per (seam, arriving) pair met and one per class of c0), and
this receipt imports that script's exact reading (rank, certified kernel, minors' gcd, rank falls).

G. Base 10, b <= a < 100 (5,050 lines): the torsion, and which results c the closure tells apart in
   each field: c's columns are (=, c1) and psi(c0) only, so a key reads c through
   V(c) = theta(=, c1) - psi(c0), and two results with one V under every kernel vector are not told
   apart.
H. The key modulo 20 in closed form, theta(x, y) = -10x on digit pairs, theta(x, -) = -x,
   theta(x, =) = x, theta(=, y) = 10y, psi(d) = -d, every other move 0: on every true line it closes
   to 0 and on every false line a-b=c' (0 <= c' < 100, c' = c + delta, 0 < |delta| <= 30) to
   delta modulo 20. It has order 20, so the torsion is Z/20.
I. The 4,995 lines whose minuend has two places: no torsion, every result told apart over Q, and
   the exact difference a key over the integers, theta(\\n, y) = -20y, theta(x, y) = 10x,
   theta(x, -) = -x, theta(-, y) = 0, theta(x, =) = x, theta(=, y) = 10y, psi(d) = -d: closure
   c - a + b, 0 on every true line and delta on every false line as in H. It misses the one-place
   minuends.
J. Split by the result's length instead: c < 10 keeps the torsion Z/20, c >= 10 has none.
K. Bases 3 to 9 and 12, b <= a < base^2: the minors' gcd is 2 base.
"""
import importlib.util
import pathlib
import sys
import time

_spec = importlib.util.spec_from_file_location("closure_torsion", pathlib.Path(__file__).with_name("closure_torsion.py"))
ct = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ct)
T0 = time.monotonic()


def say(part, value):
    print(part, f"elapsed_ms={int(1000 * (time.monotonic() - T0))}", value, flush=True)


def diff_lines(pairs, b=10):
    return [f"{ct.word(x, b)}-{ct.word(y, b)}={ct.word(x - y, b)}" for x, y in pairs]


def classes_of_c(lines, p):
    """The results the closure tells apart modulo p: classes of c under V(c) for every kernel vector."""
    rows, cols = ct.loop_rows(lines)
    _, kept, _ = ct.echelon_mod(rows, p)
    kernel = ct.nullspace_mod([rows[t] for t in kept], len(cols), p)
    cls = {}
    for c in sorted({int(s.split("=")[1]) for s in lines}):
        w = str(c)
        v = tuple((-x[cols[("psi", w[-1])]] + (x[cols[("=", w[0])]] if len(w) == 2 else 0)) % p for x in kernel)
        cls.setdefault(v, []).append(c)
    return list(cls.values())


def key20(s, a):
    if s.isdigit() and a.isdigit():
        return -10 * int(s)
    if s.isdigit() and a in "-=":
        return -int(s) if a == "-" else int(s)
    if s == "=" and a.isdigit():
        return 10 * int(a)
    return 0


def key_exact(s, a):
    if s == "\n" and a.isdigit():
        return -20 * int(a)
    return key20(s, a) + (20 * int(s) if s.isdigit() and a.isdigit() else 0)


def close(line, theta):
    seq = "\n" + line
    return sum(theta(seq[i - 1], seq[i]) for i in range(1, len(seq) - 1)) + int(line[-1])


def false_lines(pairs):
    return [(f"{x}-{y}={x - y + d}", d) for x, y in pairs for d in range(-30, 31) if d and 0 <= x - y + d < 100]


def main():
    diffs = [(x, y) for x in range(100) for y in range(x + 1)]
    two = [(x, y) for x, y in diffs if x >= 10]
    lines = diff_lines(diffs)
    rows, cols = ct.loop_rows(lines)
    out = {"G": ct.torsion(rows, len(cols))}
    fields = {}
    for name, p in (("Q", ct.P), ("2", 2), ("5", 5), ("11", 11)):
        cls = classes_of_c(lines, p)
        fields[name] = {"classes": len(cls), "c mod 2": all(len({c % 2 for c in k}) == 1 for k in cls),
                        "c mod 5": all(len({c % 5 for c in k}) == 1 for k in cls)}
    out["G"]["results_told_apart"] = fields
    say("G", out["G"])

    h_true = all(close(s, key20) % 20 == 0 for s in lines)
    h_false = all((close(s, key20) - d) % 20 == 0 for s, d in false_lines(diffs))
    out["H"] = {"true_lines_close_mod_20": h_true, "false_lines_close_to_delta_mod_20": h_false}
    say("H", out["H"])

    two_lines = diff_lines(two)
    r2, c2 = ct.loop_rows(two_lines)
    out["I"] = ct.torsion(r2, len(c2))
    out["I"]["results_told_apart_over_Q"] = len(classes_of_c(two_lines, ct.P))
    out["I"]["exact_key_true_lines_0"] = all(close(s, key_exact) == 0 for s in two_lines)
    out["I"]["exact_key_false_lines_delta"] = all(close(s, key_exact) == d for s, d in false_lines(two))
    out["I"]["one_place_minuend_lines_missed"] = [sum(close(s, key_exact) != 0 for s in diff_lines([(x, y) for x, y in diffs if x < 10])), 55]
    say("I", out["I"])

    out["J"] = {}
    for name, part in (("c<10", [(x, y) for x, y in diffs if x - y < 10]), ("c>=10", [(x, y) for x, y in diffs if x - y >= 10])):
        r, cl = ct.loop_rows(diff_lines(part))
        t = ct.torsion(r, len(cl))
        out["J"][name] = {k: t[k] for k in ("rows", "columns", "rank_mod_P", "rank_certified", "minor_gcd", "torsion")}
    say("J", out["J"])

    out["K"] = {}
    for base in (3, 4, 5, 6, 7, 8, 9, 12):
        r, cl = ct.loop_rows(diff_lines([(x, y) for x in range(base * base) for y in range(x + 1)], base), base)
        t = ct.torsion(r, len(cl), orders=3)
        out["K"][base] = {k: t[k] for k in ("rows", "columns", "rank_mod_P", "rank_certified", "minor_gcd",
                                            "cofactor_unread", "torsion")}
        out["K"][base]["predicted"] = ct.primes_of(2 * base)[0]
        say(f"K{base}", out["K"][base])

    fail = []
    g = out["G"]
    if g["torsion"] != [2, 5] or abs(g["minor_gcd"]) != 20 or not g["rank_certified"] \
            or [fields[f]["classes"] for f in ("Q", "2", "5", "11")] != [1, 2, 5, 1] \
            or not (fields["2"]["c mod 2"] and fields["5"]["c mod 5"]):
        fail.append("G")
    if not (h_true and h_false):
        fail.append("H")
    i = out["I"]
    if i["torsion"] or abs(i["minor_gcd"]) != 1 or not i["rank_certified"] or i["results_told_apart_over_Q"] != 100 \
            or not (i["exact_key_true_lines_0"] and i["exact_key_false_lines_delta"]):
        fail.append("I")
    if out["J"]["c<10"]["torsion"] != [2, 5] or out["J"]["c>=10"]["torsion"] \
            or not all(t["rank_certified"] for t in out["J"].values()):
        fail.append("J")
    for base, t in out["K"].items():
        if abs(t["minor_gcd"]) != 2 * base or t["torsion"] != t["predicted"] or not t["rank_certified"] \
                or t["cofactor_unread"] != 1:
            fail.append(f"K{base}")
    say("fail", fail)
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
