#!/usr/bin/env python3
"""The lanes' parity and speed (Brandon, November 7 19:22): each section line of the lanes run against the card-only run's
same section (the same state, walk and keys), every field equal but the times; and the time a section on each side."""
import sys
def rows(path):
    out = {}
    for l in open(path):
        if l.startswith("FIELD_KERNEL lap="):
            d = dict(kv.split("=", 1) for kv in l.split()[1:])
            out[int(d["n"])] = d
    return out
card, lanes = rows(sys.argv[1]), rows(sys.argv[2])
common = sorted(set(card) & set(lanes))
keys = lambda n: [k for k in card[n] if k in lanes[n] and k not in ("ms", "ms_section")]
same = [n for n in common if all(card[n][k] == lanes[n][k] for k in keys(n))]
c = sum(int(card[n]["ms_section"]) for n in common); l = sum(int(lanes[n]["ms_section"]) for n in common)
print(f"sections {len(common)}: identical but their times {len(same)}; card alone {c} ms, card and host lanes {l} ms ({c / max(l, 1):.3f}x)")
for n in common:
    if n not in same:
        print("differs at", n, {k: (card[n][k], lanes[n].get(k)) for k in card[n] if card[n][k] != lanes[n].get(k) and k not in ("ms", "ms_section")})
        break
# Theory, November 7 19:41: each state's two relaxations' G (faces at the open structure, material at the resolved one).
ag = [lanes[n]["g_agree"] for n in sorted(lanes) if "g_agree" in lanes[n]]
if ag:
    a = sum(int(x.split("/")[0]) for x in ag); b = sum(int(x.split("/")[1]) for x in ag)
    print(f"two relaxations' G agree in bits at {a} of {b} states; largest gap {max(int(lanes[n]['g_gap']) for n in lanes if 'g_gap' in lanes[n])} on 2^-32")
