#!/usr/bin/env python3
"""Reads whether the places that pay for a cut are the places where the far past holds the continuation.

    python3 -I repeat_at_dear.py C ROWS OUT_DIR [OUT_DIR ...]

ROWS is the rows file `read-reach` read (a label, the known text and the text after it, tab-separated, a line break written as
backslash n); OUT_DIR holds that read's codes.tsv and settings.tsv with the settings `law` and `cut:C:0`
(a further OUT_DIR is a later read of the same rows, joined by row and place). A place is an octet of a
row, as the codec reads it. A place past the cut is a far repeat at run K when the K octets ending at it stand, whole, before the cut; a far-only repeat when they also stand
nowhere between the cut and the place. Printed:

  REPEAT        for K in 2, 3, 4, 6: the share of far repeats and of far-only repeats among the dearest tenth of places (by the
                price under `cut:C:0`) and among the other nine tenths, their ratio, and the mean price of a far-only repeat and of
                every other place;
  REPEAT_FOUR   for K in 2, 3, 4, by band of places since the cut (1 to 31, 32 on): the count of places and the mean price in the
                four kinds a place can be (its run stands before the cut or not, and since the cut or not), and the share of the
                band's net price each kind holds;
  REPEAT_GROUP  at run 3, from place 32 past the cut on, by the row's group (its label up to the first colon): the places, the net
                price, the share of places that are far-only repeats with their price and their share of the net, and the price
                where the run stands nowhere before;
  REPEAT_SET    at run 3, from place 32 past the cut on, for every setting read: its price at the far-only repeats and where the run
                stands nowhere before, in nats a place, and the share of the region-alone price at the far-only repeats it brings back;
  REPEAT_PLANT  the same read of a planted price that is one at far-only repeats of run 4 and zero elsewhere (the control: its
                dear places are all far-only repeats while those are under a tenth of the places).

A host ruler of counts over octets: it prints shares and sums, never a row's text or a place. It holds no law of the engine.
"""
import collections
import math
import sys

LN2_20 = math.log(2) / (1 << 20)
RUNS = (2, 3, 4, 6)


def flags(text, c, k):
    """far[i], only[i], near[i] for i > c: the k octets ending at i stand before the cut; there and nowhere since; and since the cut.

    A run that ends within k - 1 places of the cut reaches across it and is counted with the runs since the cut."""
    before = set(text[j - k + 1: j + 1] for j in range(k - 1, c))  # runs ending at places 0..c-1
    far, only, near = {}, {}, {}
    since = set()
    for i in range(c + 1, len(text)):
        gram = text[i - k + 1: i + 1]
        far[i] = gram in before
        near[i] = gram in since
        only[i] = far[i] and not near[i]
        since.add(gram)  # runs ending at places c+1..i, all of them past the cut
    return far, only, near


def report(tag, price, far, only, k):
    order = sorted(price, key=lambda key: -price[key])
    n = max(1, len(order) // 10)
    dear, rest = order[:n], order[n:]
    share = lambda keys, f: sum(1 for key in keys if f[key]) / len(keys)
    fd, fr, od, orr = share(dear, far), share(rest, far), share(dear, only), share(rest, only)
    at = [price[key] for key in price if only[key]]
    off = [price[key] for key in price if not only[key]]
    print(f"{tag} run={k} places={len(order)} far_at_dear={fd:.3f} far_at_rest={fr:.3f} far_only_at_dear={od:.3f} far_only_at_rest={orr:.3f} "
          f"ratio_far_only={od / orr if orr else float('inf'):.2f} price_at_far_only={sum(at) / len(at) if at else float('nan'):+.4f} (places {len(at)}) "
          f"price_elsewhere={sum(off) / len(off) if off else float('nan'):+.4f} share_of_net_at_far_only={sum(at) / sum(price.values()):.3f}")


def main():
    c, rows_path, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    every = {}  # setting -> (row, place) -> nats over the law
    for more in sys.argv[3:]:
        names = open(f"{more}/settings.tsv").read().split()
        seen = collections.Counter()
        base = names.index("law") if "law" in names else None
        rowsof = []
        for ln in open(f"{more}/codes.tsv"):
            w = ln.rstrip("\n").split("\t")
            r = int(w[0])
            i = seen[r]
            seen[r] += 1
            rowsof.append((r, i, w[3:]))
        for j, name in enumerate(names):
            if name == "law" or name.startswith("from:") or name.startswith("old:") or name in every:
                continue
            every[name] = {(r, i): int(v[j]) * LN2_20 for r, i, v in rowsof if i > c}
        if base is not None:
            every.setdefault("law", {}).update({(r, i): int(v[base]) * LN2_20 for r, i, v in rowsof if i > c})
    law_code = every.pop("law")
    texts, groups = [], []
    for ln in open(rows_path, "rb"):
        w = ln.rstrip(b"\n").split(b"\t")
        if len(w) >= 3:
            groups.append(w[0].split(b":")[0].decode())
            texts.append(w[1].replace(b"\\n", b"\n") + w[2].replace(b"\\n", b"\n")[:1])
    settings = open(f"{out}/settings.tsv").read().split()
    il, ia = settings.index("law"), settings.index(f"cut:{c}:0")
    price, count = {}, collections.Counter()
    for ln in open(f"{out}/codes.tsv"):
        w = ln.rstrip("\n").split("\t")
        r = int(w[0])
        i = count[r]
        count[r] += 1
        if i > c:
            price[(r, i)] = (int(w[3 + ia]) - int(w[3 + il])) * LN2_20
    bad = [r for r in count if count[r] != len(texts[r])]
    if bad:
        sys.exit(f"{len(bad)} rows hold other counts of places than of octets")
    print(f"REPEAT_HEAD cut={c} rows={len(count)} places_past={len(price)} net={sum(price.values()):.1f}")
    for k in RUNS:
        far, only, since_flag = {}, {}, {}
        for r in count:
            f, o, nr = flags(texts[r], c, k)
            for i in f:
                far[(r, i)], only[(r, i)], since_flag[(r, i)] = f[i], o[i], nr[i]
        report("REPEAT", price, far, only, k)
        if k in (2, 3, 4):
            for band, lo, hi in (("1-31", 1, 31), ("32-on", 32, 10 ** 9)):
                keys = [key for key in price if lo <= key[1] - c <= hi]
                net = sum(price[key] for key in keys)
                cells = []
                for name, want_far, want_since in (("far_only", True, False), ("far_and_since", True, True), ("since_only", False, True), ("neither", False, False)):
                    part = [price[key] for key in keys if far[key] == want_far and (far[key] and not only[key] if want_far else since_flag[key]) == want_since]
                    cells.append(f"{name}:places={len(part)},price={sum(part) / len(part) if part else float('nan'):+.4f},share={sum(part) / net:+.3f}")
                print(f"REPEAT_FOUR run={k} band={band} places={len(keys)} net={net:.1f} " + " ".join(cells))
        if k == 3:
            band = [key for key in price if key[1] - c >= 32]
            fo = [key for key in band if only[key]]
            ne = [key for key in band if not far[key] and not since_flag[key]]
            alone = sum(price[key] for key in fo)
            for name, codes in every.items():
                at = sum(codes[key] - law_code[key] for key in fo)
                off = sum(codes[key] - law_code[key] for key in ne)
                print(f"REPEAT_SET run=3 band=32-on setting={name} far_only_places={len(fo)} far_only_price={at / len(fo):+.4f} back_at_far_only={1 - at / alone:+.3f} neither_places={len(ne)} neither_price={off / len(ne):+.4f}")
            for g in sorted(set(groups)):
                keys = [key for key in price if groups[key[0]] == g and key[1] - c >= 32]
                net = sum(price[key] for key in keys)
                fo = [price[key] for key in keys if only[key]]
                ne = [price[key] for key in keys if not far[key] and not since_flag[key]]
                print(f"REPEAT_GROUP run=3 band=32-on group={g} places={len(keys)} net={net:.1f} a_place={net / len(keys):+.4f} far_only_places={len(fo) / len(keys):.3f} "
                      f"far_only_price={sum(fo) / len(fo):+.4f} far_only_share_of_net={sum(fo) / net:+.3f} neither_places={len(ne) / len(keys):.3f} neither_price={sum(ne) / len(ne):+.4f}")
        if k == 4:
            planted = {key: (1.0 if only[key] else 0.0) for key in price}
            report("REPEAT_PLANT", planted, far, only, k)


main()
