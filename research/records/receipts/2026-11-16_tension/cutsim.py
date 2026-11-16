"""A ruler: the cut's stretches over an arithmetic slice's documents, by simulation (uniform octave draws in place of the keyed mixer)."""
import random, sys
def lengths(rng, least=4, octaves=7):
    oq = rng.randrange(octaves); q = (least << oq) + rng.randrange(least << oq)
    oa = rng.randrange(octaves); a = (least << oa) + rng.randrange(least << oa)
    return q, a
def main(d, docs_max, every=8, seed=1):
    rng = random.Random(seed)
    rows = []
    with open(d + "/DOCS_arithmetic.tsv") as f:
        next(f)
        for line in f:
            rows.append(int(line.split("\t")[2]))
            if len(rows) == docs_max: break
    data = open(d + "/DOCS_arithmetic.bin", "rb").read(sum(rows))
    off = 0; places = 0; stretches = 0; sites = 0; pairs = 0; acts = 0; flagged = 0; act_sites = 0
    whole_piece = 0; run1 = 0; useful = 0
    for n in rows:
        cur = 0
        while cur < n:
            rest = n - cur
            q, a = lengths(rng)
            if rest >= q + a + 4: ends = False
            else:
                q = min(q, rest - 1); a = rest - q; ends = True
            s = q + a + (6 if ends else 0)
            b = data[off + cur: off + cur + q + a]
            stretches += 1; places += q + a
            if rng.randrange(every) == 0:
                flagged += 1
                if b.count(b"\n") >= 2:
                    acts += 1; act_sites += 0
                    cur += q + a
                    continue
            sites += s; pairs += s * s
            if a == 1: run1 += 1
            cur += q + a
        off += n
    print(f"CUTSIM docs={len(rows)} places={places} stretches={stretches} per_10k_places: stretches={stretches*1e4/places:.1f} flagged={flagged*1e4/places:.1f} acts={acts*1e4/places:.2f} sites={sites*1e4/places:.0f} pairs={pairs*1e4/places:.0f} run_of_one={run1*1e4/places:.1f}")
main(sys.argv[1], int(sys.argv[2]))
