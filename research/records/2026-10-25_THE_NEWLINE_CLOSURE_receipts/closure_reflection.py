"""The newline closure with the hand reversible: each pair counted with the hand in force at its seam.

A reflector byte reverses the hand where it is met as a seam; a restart byte returns it to the line's
starting hand; the end class c0 is read either in the starting hand or in the hand in force. The rows
are those of closure_torsion.py with each pair's count signed by its hand, and this receipt imports
that script's exact reading (rank, certified kernel, minors' gcd, rank falls).

L. Differences b <= a < 100: with no reflector the torsion is Z/20 and over Q no result is told
   apart (section 10); with '-' reflecting, restarted at '=' or not, there is no torsion and all 100
   results are told apart; with '=' reflecting the torsion stays at 2 and 5.
M. Sums a, b < b^2 with '=' reflecting: the minors' gcd is b(b - 1) in bases 3 to 10, so the
   pair closure reaches ring b - 1 (casting out nines) in place of b + 1.
N. Sums and differences in one menu (base 10, 15,050 lines): with no reflector the torsion is 2
   alone; with '-' reflecting and c0 read in the starting hand it is 2 and 5, each field telling c
   mod p in both families; read in the hand in force it is 2 alone; with '-' reflecting and '='
   restarting the hand it is 2, 5 and 11, each field telling c mod p in both families (c mod 110).
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


def hands(seq, reflect="", restart=""):
    """The hand in force at each seam seq[i - 1], i = 1 .. len(seq) - 1 (the last is the end's hand)."""
    out, hand = [], 1
    for i in range(1, len(seq)):
        hand = 1 if seq[i - 1] in restart else -hand if seq[i - 1] in reflect else hand
        out.append(hand)
    return out


def signed_rows(lines, base=10, reflect="", restart="", end_in_force=False):
    cols, rows = {}, []
    for s in lines:
        seq = "\n" + s
        h = hands(seq, reflect, restart)
        row = {}
        for i in range(1, len(seq) - 1):
            j = cols.setdefault((seq[i - 1], seq[i]), len(cols))
            row[j] = row.get(j, 0) + h[i - 1]
        rows.append((row, s[-1], h[-1] if end_in_force else 1))
    for d in ct.DIGITS[:base]:
        cols.setdefault(("psi", d), len(cols))
    out = []
    for row, c0, e in rows:
        j = cols[("psi", c0)]
        row[j] = row.get(j, 0) - e
        out.append({k: x for k, x in row.items() if x})
    return out, cols


def results_told_apart(rows, cols, lines, op, p, reflect="", restart="", end_in_force=False):
    """Classes of the result c under every kernel vector modulo p. V(c) is the result's own share of
    the loop on one line of the family `op` per result: each pair whose seam is '=' or after it, with
    its hand, and -psi(c0) with the end's hand (a pair the operands share is not counted twice)."""
    _, kept, _ = ct.echelon_mod(rows, p)
    kernel = ct.nullspace_mod([rows[t] for t in kept], len(cols), p)
    first = {}
    for s in lines:
        if op in s:
            first.setdefault(int(s.split("=")[1]), s)
    cls = {}
    for c, s in sorted(first.items()):
        seq = "\n" + s
        h = hands(seq, reflect, restart)
        share = {}
        for i in range(seq.index("=") + 1, len(seq) - 1):
            j = cols[(seq[i - 1], seq[i])]
            share[j] = share.get(j, 0) + h[i - 1]
        j = cols[("psi", seq[-1])]
        share[j] = share.get(j, 0) - (h[-1] if end_in_force else 1)
        v = tuple(sum(n * x[j] for j, n in share.items()) % p for x in kernel)
        cls.setdefault(v, []).append(c)
    return {"classes": len(cls), "of": len(first), "each class one c mod p": all(len({c % p for c in k}) == 1 for k in cls.values())}


def reading(rows, cols, orders=2):
    t = ct.torsion(rows, len(cols), orders=orders)
    return {k: t[k] for k in ("rows", "columns", "rank_mod_P", "rank_certified", "minor_gcd", "torsion")}


def main():
    diffs = [f"{a}-{b}={a - b}" for a in range(100) for b in range(a + 1)]
    sums = [f"{a}+{b}={a + b}" for a in range(100) for b in range(100)]
    out = {"L": {}, "M": {}, "N": {}}
    for name, kw in (("no reflector", {}), ("- reflects", {"reflect": "-"}),
                     ("- reflects, = restarts", {"reflect": "-", "restart": "="}), ("= reflects", {"reflect": "="})):
        r, c = signed_rows(diffs, **kw)
        out["L"][name] = reading(r, c)
        out["L"][name]["told_apart_over_Q"] = results_told_apart(r, c, diffs, "-", ct.P, **kw)["classes"]
        say(f"L {name}", out["L"][name])

    for base in (3, 4, 5, 6, 7, 8, 9, 10):
        n = base * base
        lines = [f"{ct.word(a, base)}+{ct.word(b, base)}={ct.word(a + b, base)}" for a in range(n) for b in range(n)]
        r, c = signed_rows(lines, base, reflect="=")
        out["M"][base] = reading(r, c, orders=4)
        out["M"][base]["predicted_gcd"] = base * (base - 1)
        say(f"M{base}", out["M"][base])

    both = sums + diffs
    for name, kw in (("no reflector", {}), ("- reflects, c0 in the starting hand", {"reflect": "-"}),
                     ("- reflects, c0 in the hand in force", {"reflect": "-", "end_in_force": True}),
                     ("- reflects, = restarts", {"reflect": "-", "restart": "="})):
        r, c = signed_rows(both, **kw)
        out["N"][name] = reading(r, c)
        for p in out["N"][name]["torsion"]:
            out["N"][name][f"mod {p}"] = {fam: results_told_apart(r, c, both, op, p, **kw) for fam, op in (("sums", "+"), ("differences", "-"))}
        say(f"N {name}", out["N"][name])

    fail = []
    want_l = {"no reflector": ([2, 5], 1), "- reflects": ([], 100), "- reflects, = restarts": ([], 100), "= reflects": ([2, 5], 1)}
    for name, (tor, apart) in want_l.items():
        t = out["L"][name]
        if t["torsion"] != tor or t["told_apart_over_Q"] != apart or not t["rank_certified"]:
            fail.append(f"L {name}")
    for base, t in out["M"].items():
        if abs(t["minor_gcd"]) != t["predicted_gcd"] or t["torsion"] != ct.primes_of(t["predicted_gcd"])[0] or not t["rank_certified"]:
            fail.append(f"M{base}")
    want_n = {"no reflector": [2], "- reflects, c0 in the starting hand": [2, 5],
              "- reflects, c0 in the hand in force": [2], "- reflects, = restarts": [2, 5, 11]}
    for name, tor in want_n.items():
        t = out["N"][name]
        if t["torsion"] != tor or not t["rank_certified"]:
            fail.append(f"N {name}")
        for p in tor[1:]:
            for fam in ("sums", "differences"):
                k = t[f"mod {p}"][fam]
                if k["classes"] != p or not k["each class one c mod p"]:
                    fail.append(f"N {name} mod {p} {fam}")
    say("fail", fail)
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
