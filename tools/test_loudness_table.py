#!/usr/bin/env -S python3 -I
"""Controls of loudness_table.py on drawn tables (host arithmetic on numbers written here; no private passage is read).

  spearman   the rank correlation is +1 on a rising pair, -1 on a falling one, and averages ties;
  read       a table's last stage is read for each lane, a place's loudness is its lanes' mean log2 power and its code is in nats;
  basin      a drawn region where the loud places carry the cheap codes and the written symbol on top reads a negative correlation,
             a negative temperature and a rank-1 share in its loudest fifth above its quietest;
  flat       a region where loudness is drawn apart from the code reads a correlation near zero;
  pieces     a place's pieces are its written neighbours and its unit, an edge has none, and its color is its lanes' energy entropy;
  count      a letter's occurrence within its word is counted from the places' own units, a word being a run of ASCII letters;
  ceiling    a stretch's broken ceilings are the places above every earlier place, counted against the harmonic number.
"""
import math, os, random, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import loudness_table as lt

passed = 0


def check(cond, what):
    global passed
    if not cond:
        sys.exit(f"FAILED {what}")
    passed += 1


check(abs(lt.spearman([1, 2, 3, 4], [10, 20, 30, 40]) - 1) < 1e-12, "spearman rising")
check(abs(lt.spearman([1, 2, 3, 4], [4, 3, 2, 1]) + 1) < 1e-12, "spearman falling")
check(abs(lt.spearman([1, 1, 2, 3], [1, 1, 2, 3]) - 1) < 1e-12, "spearman ties")


def write(rows, lanes=2, stages=3):
    d = tempfile.mkdtemp()
    with open(os.path.join(d, "loudness.tsv"), "w") as f:
        cols = [f"s{s}_l{l}" for s in range(stages) for l in range(lanes)]
        f.write("row\tslice\tstretch\tt\tclass\tcode\trank\tprev2\tprev\tunit\tnext\t" + "\t".join(cols) + "\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")
    return d


one = 2**20
d = write([["P", "a", 0, 0, 5, one, 1, "73", "74", "79", "-", 1, 1, 1, 1, 2**8, 2**10]])
rows, nl = lt.read(os.path.join(d, "loudness.tsv"))
check(nl == 2 and abs(rows[0]["loud"] - 9.0) < 1e-12, "last stage read and lanes averaged")
check(abs(rows[0]["code"] - math.log(2)) < 1e-12, "a code of one bit is ln 2 nats")
check(rows[0]["piece2"] == "7479" and rows[0]["piece3"] == "737479", "the pieces ending at a place are its written neighbours and its unit")
e1, e2 = 2.0**16, 2.0**20
q = [e1 / (e1 + e2), e2 / (e1 + e2)]
check(abs(rows[0]["color"] + sum(x * math.log(x) for x in q)) < 1e-12, "a place's color is its lanes' energy entropy")
d = write([["P", "a", 0, 0, 5, one, 1, "-", "74", "68", "-", 1, 1, 1, 1, 2**8, 2**8]])
r2 = lt.read(os.path.join(d, "loudness.tsv"))[0][0]
check(r2["piece3"] is None and abs(r2["color"] - math.log(2)) < 1e-12, "an edge has no three-byte piece; equal lanes are the whitest")

rng = random.Random(7)
basin = []
for i in range(2000):
    loud = rng.uniform(4, 12)
    code = int(max(0.05, 12 - loud + rng.gauss(0, 0.5)) * one)
    rank = 1 if loud > 8 else rng.randint(2, 30)
    p = int(2 ** loud)
    basin.append(["P", "b", i, 0, 1, code, rank, "61", "74", "68", "-", 1, 1, 1, 1, p, p])
out = "\n".join(lt.table("b", lt.read(os.path.join(write(basin), "loudness.tsv"))[0], 2))
rho = float(out.split("spearman_loud_code=")[1].split()[0])
temp = float(out.split("a nat): ")[1].split()[0])
loudest = float(out.split("loudest fifth ")[1].split(",")[0])
quietest = float(out.split("quietest fifth ")[1].split()[0])
check(rho < -0.8, f"a basin reads a negative correlation ({rho})")
check(temp < 0, f"a basin reads a negative temperature ({temp})")
check(loudest > quietest, "a basin's loudest fifth holds more rank-1 places")

flat = []
for i in range(2000):
    loud = rng.uniform(4, 12)
    code = int(rng.uniform(0.1, 8) * one)
    p = int(2 ** loud)
    flat.append(["P", "f", i, 0, 1, code, rng.randint(1, 30), "61", "74", "68", "-", 1, 1, 1, 1, p, p])
out = "\n".join(lt.table("f", lt.read(os.path.join(write(flat), "loudness.tsv"))[0], 2))
rho = float(out.split("spearman_loud_code=")[1].split()[0])
check(abs(rho) < 0.1, f"a flat region reads no correlation ({rho})")
# a word "error" then a space then "ab": the r's are the 1st, 2nd and 3rd, the word's length 5
units = ["65", "72", "72", "6f", "72", "20", "61", "62"]
rows = [["P", "m", 0, t, 1, one, 1, "-", "-", u, "-", 1, 1, 1, 1, 2**8, 2**8] for t, u in enumerate(units)]
ps = [r for r in lt.read(os.path.join(write(rows), "loudness.tsv"))[0]]
lt.multiplicity(ps)
check([p.get("j") for p in ps] == [1, 1, 2, 1, 3, None, 1, 1], "a letter's occurrence within its word")
check(ps[0]["wlen"] == 5 and ps[6]["wlen"] == 2 and "j" not in ps[5], "a word's length, and a space in none")
# ceilings: codes 1, 3, 2, 5, 4 in one stretch break the ceiling at 3 and 5 (two), against H_5 - 1
rows = [["P", "c", 0, t, 1, int(c * one), 1, "-", "-", "61", "-", 1, 1, 1, 1, 2**8, 2**8] for t, c in enumerate([1, 3, 2, 5, 4])]
ps = lt.read(os.path.join(write(rows), "loudness.tsv"))[0]
seen, expected, at = lt.records(ps)
check(seen == 2 and abs(expected - (1 + 1/2 + 1/3 + 1/4 + 1/5 - 1)) < 1e-12 and [p["t"] for p in at] == [1, 3], "the ceilings a stretch breaks, against the harmonic number")
print(f"loudness_table controls: {passed} passed")
