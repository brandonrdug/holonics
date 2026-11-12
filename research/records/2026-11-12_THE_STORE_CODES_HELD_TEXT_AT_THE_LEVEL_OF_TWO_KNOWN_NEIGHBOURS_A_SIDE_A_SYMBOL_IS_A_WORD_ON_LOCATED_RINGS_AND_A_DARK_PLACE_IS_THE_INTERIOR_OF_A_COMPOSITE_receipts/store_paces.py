#!/usr/bin/env python3 -I
"""store_paces.py CODEC STATE_A STATE_C: R1 of G118 (a), a ruler on the host (no card, no learning): the pace family of the store's states, a row a class.

A paced head's tick rate at a site of class u is `1 + c_h[u]` (Field::paces_with: `k = one + rate`, the pace family's entry on the material's grain 2^-24);
a head is paced where `h % frames >= still`. The family stands after the probe's bias in FieldLayout's order (`tools/pace_rates.py`'s offset, the layout's
families pushed in order), `a + 1` entries a paced head: the alphabet's classes and the open row. A class's byte is the codec's (`field-codec-v3 ANSWER
VOID`: the used units in class order with the void's index skipped); the code line's classes are those of the alphabet before the crossing (the classes
below the first fresh one, the void among them), and the open text's are the classes after them. The layout is checked by the material's length, the
class count by the codec's, and the crossing's fresh classes by their rates (founded at zero, a rate of 1). Rates printed as decimals: a reading.
Numbers only (byte values, no text, no path).
"""
import statistics
import sys


def layout(d):
    a, dw, heads, modes, still, f, frames, carry = d["alphabet"], d["width"], d["heads"], d["modes"], d["still"], d["contacts"], d["frames"], d["carry"]
    m2 = 2 * heads * modes
    paced = [h for h in range(heads) if h % frames >= still]
    tm = len(paced) * modes
    pace = (a + 1) * dw * 3 + (m2 * dw + m2) * 2 + dw * m2 + dw + (f * dw + f) * 2 + dw * f + dw + dw * dw + a + (a + 1) * 2 * tm * 2 + 2 * heads + m2 * dw + m2
    total = pace + len(paced) * (a + 1) + dw * m2 + dw + dw + 2 * carry * dw + 2 * carry + 6 * d["triads"] * dw + 6 * d["triads"] + dw * 2 * d["triads"]
    return paced, pace, total


def read_state(path):
    lines = open(path).read().split("\n")
    head = lines[1].split(" ")
    names = ["alphabet", "width", "heads", "modes", "still", "contacts", "ticks", "frames", "reach", "lanes", "depth", "carry"]
    d = {k: int(w) for k, w in zip(names, head[1:])}
    d["triads"] = int(head[13]) if len(head) > 13 else 0
    theta = [int(x) for x in lines[2].split(" ")]
    return head[0], d, theta


def main():
    codec_path, a_path, c_path = sys.argv[1:4]
    codec = open(codec_path).read().split("\n")
    form, _, void = codec[0].split(" ")
    void = int(void)
    used = [int(x) for x in codec[1].split(" ") if x]
    states = {}
    for name, path in (("A", a_path), ("C", c_path)):
        kind, d, theta = read_state(path)
        paced, pace, total = layout(d)
        states[name] = (d, paced, [[theta[pace + p * (d["alphabet"] + 1) + u] for u in range(d["alphabet"] + 1)] for p in range(len(paced))])
        print(f"CHECK state={name} format={kind} alphabet={d['alphabet']} material={len(theta)} layout_total={total} layout_equal={len(theta) == total} paced_heads={paced} pace_at={pace}")
    d, paced, _ = states["A"]
    a = d["alphabet"]
    print(f"CHECK codec={form} void={void} used={len(used)} classes={len(used) + 1} alphabet={a} equal={len(used) + 1 == a}")
    fresh = next(u for u in range(a) if u > void)  # the code line's alphabet ends at its void; the crossing's classes follow
    added = list(range(fresh, a))

    def byte_of(u):
        if u == a:
            return "open"
        if u == void:
            return "void"
        return str(used[u] if u < void else used[u - 1])

    rate = lambda c: 1 + c / (1 << 24)
    for name in ("A", "C"):
        _, _, rows = states[name]
        at_one = [sum(1 for u in added if rows[p][u] == 0) for p in range(len(paced))]
        print(f"CHECK state={name} added_classes={len(added)} added_at_rate_1={at_one} open_row_rate={[f'{rate(rows[p][a]):.6f}' for p in range(len(paced))]}")
    print("class\tbyte\torigin\t" + "\t".join(f"rate_A_head{h}\trate_C_head{h}" for h in paced))
    for u in range(a + 1):
        origin = "open_row" if u == a else ("open_text" if u >= fresh else "code_line")
        cells = []
        for p in range(len(paced)):
            cells += [f"{rate(states['A'][2][p][u]):.6f}", f"{rate(states['C'][2][p][u]):.6f}"]
        print(f"{u}\t{byte_of(u)}\t{origin}\t" + "\t".join(cells))
    # Summaries a reader of (a) takes from the table (numbers only, no score).
    _, _, rows = states["C"]
    letters = [u for u in range(void) if 65 <= used[u] <= 90 or 97 <= used[u] <= 122]
    newline = [u for u in range(void) if used[u] == 10]
    for p, h in enumerate(paced):
        code = [u for u in range(void)]
        top = max(code, key=lambda u: rows[p][u])
        mean_letters = statistics.mean(rate(rows[p][u]) for u in letters)
        nl = rate(rows[p][newline[0]]) if newline else float("nan")
        med_added = statistics.median(abs(rate(rows[p][u]) - 1) for u in added)
        med_code = statistics.median(abs(rate(rows[p][u]) - 1) for u in code)
        print(f"SUMMARY state=C head={h} newline_rate={nl:.6f} ascii_letters_mean_rate={mean_letters:.6f} newline_over_letters={nl / mean_letters:.4f} "
              f"largest_code_line_class={top} byte={byte_of(top)} rate={rate(rows[p][top]):.6f} median_abs_rate_minus_1_added={med_added:.6f} median_abs_rate_minus_1_code_line={med_code:.6f}")


if __name__ == "__main__":
    main()
