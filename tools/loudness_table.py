#!/usr/bin/env -S python3 -I
"""loudness_table.py DIR: loudness beside surprise, by region and rank, from `athena train complete-language read-loudness`'s
DIR/loudness.tsv (a ruler on the host; floats are this ruler's, never the machine's).

The reading is the record of November 13 on loudness beside surprise (§4 and its test 1), asked for with every lap by Brandon on
November 15 00:58Z. For each open place of the held read (rows `P`, a place open alone among the written ones) it takes its code
(surprise, on 2^-20 bits, printed here in nats a place), the rank of its written symbol in its face (1: the face's loudest class) and its
lanes' powers after the last tick (the stage the faces read). A place's loudness is the mean over its lanes of log2 of the lane's power,
in octaves; its energy is the sum over lanes of the power squared, read against its slice's mean energy.

Printed for each slice (region), and for all slices together:
  - places, the code in nats a place, the loudness, and the Spearman correlation of loudness against code (negative where the loud
    places are the ones the field codes cheaply, which is what a dense basin is);
  - the loudness and the code in each fifth of the slice's places by surprise (q1 the least surprised);
  - the share of places, the loudness and the code at each rank band of the written symbol (1, 2-3, 4-10, 11 and past);
  - the temperature, energy a nat: the slope of the place's energy (over its slice's mean) against its code in nats, and the share of
    the loudest fifth whose written symbol is its face's loudest (rank 1), beside the same share in the quietest fifth;
  - the color (Brandon, November 15 01:08Z: loudness as scattering, color beside surprise): a place's lanes' spectrum, the entropy in
    nats of its lanes' energy shares (ln L where every lane carries the same energy, 0 where one lane carries it all), with its rank
    correlations against loudness and against the code, and by surprise fifth;
  - the commonest two- and three-byte pieces ending at each place (its written neighbours before it and its own unit: `th`, `ch`,
    `ie` as geometric parts whose stability a place shows), each with its count, code, loudness, color and rank-1 share;
  - a letter's occurrence within its word (its first, second, third or later time in the word, the word a run of ASCII letters read from
    the places' own units: Brandon, November 15 01:17Z, a count felt as magnitude, never iterated), with loudness, code and color, and
    the places by their word's length;
  - the ceilings broken: in each stretch read in place order, the places whose code stands above every earlier place's (Brandon,
    November 15 03:00Z: a surprise past its context's ceiling is a phase transition), counted against the harmonic number an order
    that carries nothing gives, with the loudness, code and color where they land;
  - each lane's loudness, so a lane that stands apart is seen.
Rows `W` (the whole masks' open places) are printed as one line a slice: their code and loudness.
"""
import csv, math, os, re, sys

NAT = math.log(2) / 2**20  # one code unit (2^-20 bits) in nats


def spearman(xs, ys):
    def ranks(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j + 1]] == v[order[i]]:
                j += 1
            for k in range(i, j + 1):
                r[order[k]] = (i + j) / 2
            i = j + 1
        return r
    if len(xs) < 3:
        return float("nan")
    rx, ry = ranks(xs), ranks(ys)
    mx, my = sum(rx) / len(rx), sum(ry) / len(ry)
    sxy = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    sxx = sum((a - mx) ** 2 for a in rx)
    syy = sum((b - my) ** 2 for b in ry)
    return sxy / math.sqrt(sxx * syy) if sxx and syy else float("nan")


def read(path):
    with open(path) as f:
        rd = csv.reader(f, delimiter="\t")
        head = next(rd)
        power = [c for c in head if re.fullmatch(r"s\d+_l\d+", c)]
        stages = sorted({int(c.split("_")[0][1:]) for c in power})
        lanes = sorted({int(c.split("_")[1][1:]) for c in power})
        last = stages[-1]
        cols = [head.index(f"s{last}_l{l}") for l in lanes]
        rows = []
        for r in rd:
            powers = [int(r[c]) for c in cols]
            at = {c: head.index(c) for c in ("prev2", "prev", "unit", "next") if c in head}
            piece = lambda *cs: "".join(r[at[c]] for c in cs) if all(c in at and r[at[c]] != "-" for c in cs) else None
            total = sum(float(p) * float(p) for p in powers)
            shares = [float(p) * float(p) / total for p in powers] if total else []
            rows.append({
                "stretch": int(r[2]), "t": int(r[3]), "unit": r[at["unit"]] if "unit" in at else "-",
                "row": r[0], "slice": r[1], "code": int(r[5]) * NAT, "rank": int(r[6]),
                "piece2": piece("prev", "unit"), "piece3": piece("prev2", "prev", "unit"),
                "color": -sum(q * math.log(q) for q in shares if q > 0) if shares else float("nan"),
                "lanes": [math.log2(p) if p > 0 else float("nan") for p in powers],
                "energy": sum(float(p) * float(p) for p in powers),
            })
    for x in rows:
        good = [v for v in x["lanes"] if not math.isnan(v)]
        x["loud"] = sum(good) / len(good) if good else float("nan")
    return rows, len(lanes)


def show(h):
    """A piece's bytes as text where they are printable, else as hex."""
    b = bytes.fromhex(h)
    t = b.decode("utf-8", "replace")
    return repr(t) if all(32 <= c < 127 for c in b) else h


def mean(v):
    v = [x for x in v if not math.isnan(x)]
    return sum(v) / len(v) if v else float("nan")


def multiplicity(ps):
    """Each P place inside a word (a run of ASCII letters within its stretch, read from the places' own units): the occurrence index of
    its letter (case folded) within the word so far, and the word's length. A ruler's segmentation, on the host."""
    by = {}
    for p in ps:
        by.setdefault((p["slice"], p["stretch"]), []).append(p)
    for seq in by.values():
        seq.sort(key=lambda p: p["t"])
        word = []
        def close():
            seen = {}
            for q in word:
                seen[q["_c"]] = seen.get(q["_c"], 0) + 1
                q["j"], q["wlen"] = seen[q["_c"]], len(word)
            word.clear()
        for p in seq:
            b = bytes.fromhex(p["unit"]) if p["unit"] != "-" else b""
            if len(b) == 1 and (65 <= b[0] <= 90 or 97 <= b[0] <= 122):
                p["_c"] = b[0] | 32
                word.append(p)
            else:
                close()
        close()


def records(ps):
    """The surprises that break their context's ceiling (Brandon, November 15 03:00Z: a surprise past what its context has held is a
    phase transition, not noise): in each stretch, read in place order, a place whose code stands above every earlier place's. For a
    sequence whose order carries nothing (exchangeable), the expected count over n places is the harmonic number H_n, as many in each
    decade of places as the next (ln 10), so the count over its expectation is read beside the places where it lands."""
    by = {}
    for p in ps:
        by.setdefault((p["slice"], p["stretch"]), []).append(p)
    seen, expected, at = 0, 0.0, []
    for seq in by.values():
        seq.sort(key=lambda p: p["t"])
        top = None
        for k, p in enumerate(seq, 1):
            expected += 1.0 / k
            if top is None or p["code"] > top:
                top = p["code"]
                if k > 1:
                    seen += 1
                    at.append(p)
            p["record"] = top == p["code"] and k > 1
        expected -= 1.0  # the first place is a ceiling by definition, counted in neither
    return seen, expected, at


def table(name, ps, nlanes):
    out = []
    codes = [p["code"] for p in ps]
    louds = [p["loud"] for p in ps]
    out.append(f"LOUDNESS region={name} places={len(ps)} nats_a_place={mean(codes):.4f} loudness_octaves={mean(louds):.3f} spearman_loud_code={spearman(louds, codes):+.3f}")
    order = sorted(range(len(ps)), key=lambda i: ps[i]["code"])
    fifths = [order[k * len(order) // 5:(k + 1) * len(order) // 5] for k in range(5)]
    out.append("  by surprise fifth (q1 least surprised): " + "  ".join(f"q{k + 1} nats={mean([ps[i]['code'] for i in f]):.3f} loud={mean([ps[i]['loud'] for i in f]):.3f}" for k, f in enumerate(fifths)))
    bands = [(1, 1), (2, 3), (4, 10), (11, 10**9)]
    parts = []
    for lo, hi in bands:
        sel = [p for p in ps if lo <= p["rank"] <= hi]
        label = f"{lo}" if lo == hi else (f"{lo}-{hi}" if hi < 10**9 else f"{lo}+")
        parts.append(f"rank {label}: share={len(sel) / max(len(ps), 1):.3f} loud={mean([p['loud'] for p in sel]):.3f} nats={mean([p['code'] for p in sel]):.3f}")
    out.append("  by the written symbol's rank: " + "  ".join(parts))
    me = mean([p["energy"] for p in ps])
    es = [p["energy"] / me for p in ps] if me else [float("nan")] * len(ps)
    mc = mean(codes)
    sxy = sum((c - mc) * (e - 1) for c, e in zip(codes, es))
    sxx = sum((c - mc) ** 2 for c in codes)
    loud_order = sorted(range(len(ps)), key=lambda i: ps[i]["loud"])
    quiet, loud = loud_order[:len(ps) // 5], loud_order[-(len(ps) // 5):] if len(ps) >= 5 else []
    top = lambda sel: sum(1 for i in sel if ps[i]["rank"] == 1) / max(len(sel), 1)
    out.append(f"  temperature (energy over the region's mean, a nat): {sxy / sxx if sxx else float('nan'):+.4f}   rank-1 share: loudest fifth {top(loud):.3f}, quietest fifth {top(quiet):.3f}")
    colors = [p["color"] for p in ps]
    out.append(f"  color (the lanes' spectrum, its entropy in nats, ln L the whitest): mean={mean(colors):.4f}  spearman loud~color={spearman(louds, colors):+.3f}  color~code={spearman(colors, codes):+.3f}  by surprise fifth: " + " ".join(f"q{k + 1}={mean([ps[i]['color'] for i in f]):.4f}" for k, f in enumerate(fifths)))
    for key, n in (("piece2", 8), ("piece3", 6)):
        groups = {}
        for p in ps:
            if p[key]:
                groups.setdefault(p[key], []).append(p)
        top = sorted(groups.items(), key=lambda kv: -len(kv[1]))[:n]
        out.append(f"  commonest {key[-1]}-byte pieces ending at the place (piece: count, nats, loud, color, rank-1 share): " + "  ".join(
            f"{show(k)}: {len(v)} {mean([q['code'] for q in v]):.3f} {mean([q['loud'] for q in v]):.2f} {mean([q['color'] for q in v]):.3f} {sum(1 for q in v if q['rank'] == 1) / len(v):.2f}" for k, v in top))
    inw = [p for p in ps if "j" in p]
    if inw:
        parts = []
        for lo, hi, label in ((1, 1, "1st"), (2, 2, "2nd"), (3, 10**9, "3rd+")):
            sel = [p for p in inw if lo <= p["j"] <= hi]
            parts.append(f"{label}: {len(sel)} loud={mean([p['loud'] for p in sel]):.3f} nats={mean([p['code'] for p in sel]):.3f} color={mean([p['color'] for p in sel]):.4f}")
        out.append("  a letter's occurrence within its word (Brandon 01:17Z: a count felt as magnitude): " + "  ".join(parts))
        words = {}
        for p in inw:
            words.setdefault((p["stretch"], p["t"] - 0, p["wlen"]), None)
        parts = []
        for lo, hi in ((1, 3), (4, 6), (7, 9), (10, 10**9)):
            sel = [p for p in inw if lo <= p["wlen"] <= hi]
            label = f"{lo}-{hi}" if hi < 10**9 else f"{lo}+"
            parts.append(f"len {label}: places={len(sel)} loud={mean([p['loud'] for p in sel]):.3f} nats={mean([p['code'] for p in sel]):.3f}")
        out.append("  places by their word's length: " + "  ".join(parts))
    seen, expected, at = records(ps)
    out.append(f"  ceilings broken (a place's code above every earlier place's in its stretch, past the first): {seen} against {expected:.1f} for an order that carries nothing (ratio {seen / expected if expected else float('nan'):.3f}); at them nats={mean([p['code'] for p in at]):.3f} loud={mean([p['loud'] for p in at]):.3f} color={mean([p['color'] for p in at]):.4f} rank-1 share={sum(1 for p in at if p['rank'] == 1) / max(len(at), 1):.2f}")
    out.append("  by lane (octaves): " + "  ".join(f"lane{l}={mean([p['lanes'][l] for p in ps]):.3f}" for l in range(nlanes)))
    return out


def main():
    if len(sys.argv) != 2:
        sys.exit((__doc__ or "loudness_table.py DIR").split("\n")[0])
    rows, nlanes = read(os.path.join(sys.argv[1], "loudness.tsv"))
    ps = [r for r in rows if r["row"] == "P"]
    multiplicity(ps)
    slices = []
    for r in ps:
        if r["slice"] not in slices:
            slices.append(r["slice"])
    for s in slices:
        print("\n".join(table(s, [p for p in ps if p["slice"] == s], nlanes)))
    print("\n".join(table("all", ps, nlanes)))
    for s in slices:
        ws = [r for r in rows if r["row"] == "W" and r["slice"] == s]
        if ws:
            print(f"LOUDNESS_WHOLE region={s} places={len(ws)} nats_a_place={mean([w['code'] for w in ws]):.4f} loudness_octaves={mean([w['loud'] for w in ws]):.3f}")


if __name__ == "__main__":
    main()
