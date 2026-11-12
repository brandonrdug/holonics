#!/usr/bin/env python3
"""A ruler on the host: the arithmetic and the octets one section of the store's trainer needs, against the card.

Usage: python3 engine_count.py RECEIPT [LANE_STEPS_A_SECOND] [OCTETS_A_SECOND] [STEPS_A_PRODUCT]

RECEIPT is a train-store log or receipt: its STORE_DECLARATION line, its STORE_SECTION lines and its FIELD_CARD line.
The ruler reads the declaration by part and a section's census (computed sites, open sites, regions, and the pair-terms
the card counted: a pair for each head and tick), and prints, by family of kernel:

  * products: the multiplications the law's terms need a section, each counted at the width its information needs.
    The unit is one product of two words of at most 32 bits with its 64-bit sum. A term the realization forms on a
    wider word (a 128-bit product, a row's sum on five to twenty limbs of 64 bits) is counted here at the narrow
    products its integers need, never at the words it is run on;
  * octets: what a section must write and read back from the card's memory when a region's rows stand in one
    block's shared memory (a region of some two hundred sites holds 16 words a site and head: 13 KB a head).

Against them: the card's lanes times its clock (lane-steps a second) and its memory's rate. Both defaults are the
card's published figures [from training]: 10,240 lanes at 2.55 GHz and 736 GB a second (RTX 4080 SUPER). They are
ceilings, never measurements: P50 replaces them with a measured narrow-product kernel and a measured sweep.

Every count below is [agent-inferred] from the kernels' source (crates/holonics-cuda/kernels/field.cu and
src/hnn/field.rs at c1c3e5b62) and stands until a profile by entry replaces it. No figure here is a rate of learning.
"""
import re
import sys


def fields(line):
    return {k: v for k, v in re.findall(r"(\w+)=(-?[\w.]+)", line)}


def main():
    path = sys.argv[1]
    lane_steps = float(sys.argv[2]) if len(sys.argv) > 2 else 10240 * 2.55e9
    octets_s = float(sys.argv[3]) if len(sys.argv) > 3 else 736e9
    steps_a_product = float(sys.argv[4]) if len(sys.argv) > 4 else 6.0
    decl, card, sections = None, None, []
    with open(path) as f:
        for line in f:
            if line.startswith("STORE_DECLARATION"):
                decl = fields(line)
            elif line.startswith("FIELD_CARD"):
                card = fields(line)
            elif line.startswith("STORE_SECTION"):
                sections.append(fields(line))
    if decl is None or card is None or not sections:
        sys.exit("engine_count: the receipt lacks STORE_DECLARATION, FIELD_CARD or STORE_SECTION lines")
    n = len(sections)
    mean = lambda k: sum(int(s[k]) for s in sections) / n
    sites, opened, regions, deposit_ms = mean("sites"), mean("open"), mean("regions"), mean("deposit_ms")
    returns = int(card["returns"])
    pair_terms = int(card["pairs"]) / returns

    # The declaration, by part.
    alphabet = int(decl["alphabet"])
    dw = int(decl["lanes"]) * int(decl["lane_width"])        # the face chart's entries a site
    heads, still = int(decl["heads"]), int(decl["still"])
    paced = heads - still
    modes = int(decl["modes"])
    span = 2 * modes                                          # a head's word: its modes' two reals
    m2 = heads * span                                         # the words of every head a site
    f = int(decl["contacts"])
    c2 = 2 * int(decl["carry"])                               # the carry circles' two reals
    ticks = int(decl["ticks"])

    print(f"ENGINE_COUNT receipt_sections={n} sites={sites:.0f} open={opened:.0f} regions={regions:.1f} "
          f"pair_terms={pair_terms:.0f} pair_terms_a_site={pair_terms / sites:.1f} "
          f"pair_terms_a_site_head_tick={pair_terms / sites / heads / ticks:.1f} deposit_ms={deposit_ms:.1f}")
    print(f"ENGINE_PARTS alphabet={alphabet} face_chart={dw} heads={heads} paced={paced} modes={modes} head_word={span} "
          f"words_a_site={m2} contacts={f} carry_reals={c2} ticks={ticks}")

    rows = []  # (family, unit, units a section, products a unit, octets a unit)

    # 1. A site's maps, a site and tick. Forward: the words q, the values v and the probe (m2 by dw each), the
    #    contact's out (dw by m2), the pair contacts' a and b (f by dw each), the carry's gate (c2 by dw), the
    #    contacts' return w (dw by f). Octets: each map reads its input vector and writes its output once.
    fwd = 3 * m2 * dw + dw * m2 + 2 * f * dw + c2 * dw + dw * f
    fwd_octets = (6 * dw * 4 + m2 * 8 + f * 8) + (3 * m2 * 8 + dw * 8 + 2 * f * 8 + c2 * 8 + dw * 8)
    rows.append(("site maps, forward", "site and tick", sites * ticks, fwd, fwd_octets))
    # Their return: an outer product into the covector and a transposed product for each of the eight maps, and
    # the probe read again for the paced heads' frames.
    back = 2 * fwd + m2 * dw
    rows.append(("site maps, return", "site and tick", sites * ticks, back, 2 * fwd_octets))
    # 2. The small site kernels of a tick (the chart and its ratio's return, the frames, the unit words and their
    #    return, the classes, the prefix sums, the carry circles' pair, gate and scan with their returns).
    small = 6 * dw + 12 * m2 + 24 * c2
    rows.append(("site kernels, small", "site and tick", sites * ticks, small, 16 * (dw + m2 + c2)))
    # 3. The paced heads' moments, once a pass and returned once a clock: strands, admission, two prefixes, the
    #    paced moment and its scatter, a moment face (dw by m2) with its return.
    moments = 3 * dw * m2 + 12 * paced * span * 8
    rows.append(("moments", "site", sites, moments, 8 * (2 * dw + 6 * m2)))
    # 4. The face, an open site: the lift (dw by dw), the readout through the encoding (alphabet by dw), the
    #    exponentials (some ten products a class), and the return: the classes' covector, the encoding's two
    #    products (alphabet by dw each), the lift's outer and transposed products.
    face = dw * dw + alphabet * dw + 10 * alphabet + alphabet + 2 * alphabet * dw + 2 * dw * dw
    face_octets = 6 * alphabet * 8 + 6 * dw * 8
    rows.append(("face and its return", "open site", opened, face, face_octets))
    # 5. A blank's clock, an open site and each later tick: its face read again (lift, readout, exponentials), its
    #    rates and paces, and their return.
    blank = dw * dw + alphabet * dw + 10 * alphabet + dw * dw + alphabet * dw + 8 * paced * span
    rows.append(("blank clocks", "open site and later tick", opened * (ticks - 1), blank, face_octets))
    # 6. The contact, a pair-term (a pair for each head and tick).
    #    Forward: the lock, a mode: two products of words, one by the skin, two for the source's power by the
    #    skin's square (the power itself is a site's, formed once); the score and its exponential face, 6; the
    #    share, one product by the row's reciprocal (the division is a row's); the numerators, an entry: one carry
    #    by the skin and one by the share; the skin itself, a mode of a paced head: 4, once a clock.
    lock = modes * 5
    numer = span * 2
    skin = modes * 4 * paced / heads
    pair_fwd = lock + 6 + 1 + numer + skin
    #    Return: the row's (an entry: the share's covector through the carried value, 2; the compare, 3; the
    #    receiver's word through the probe, 3 an entry), the column's (the source's word, 3 an entry; its value, 2
    #    an entry), the skin's (a mode of a paced head: 6).
    pair_back = (span * 2 + 3 + span * 3) + (span * 3 + span * 2) + modes * 6 * paced / heads
    rows.append(("contact, forward", "pair-term", pair_terms, pair_fwd, 8 * 3))
    rows.append(("contact, return", "pair-term", pair_terms, pair_back, 8 * 4))
    # 7. The crowds, a row (a site, head and tick): two an octave of the reach, each a pair-term on summed words.
    octaves = max(1, (int(decl["reach"]) - 1).bit_length())
    crowds = 2 * octaves
    rows.append(("crowds", "site, head and tick", sites * heads * ticks, crowds * (pair_fwd + pair_back), crowds * 8 * 7))

    total_p = total_o = 0.0
    print("family | unit | units a section | products a unit | products a section | octets a section")
    for name, unit, units, products, octets in rows:
        p, o = units * products, units * octets
        total_p += p
        total_o += o
        print(f"{name} | {unit} | {units:.4g} | {products:.0f} | {p:.4g} | {o:.4g}")
    print(f"ENGINE_TOTAL products_a_section={total_p:.4g} products_a_site={total_p / sites:.0f} "
          f"octets_a_section={total_o:.4g} octets_a_site={total_o / sites:.0f}")

    measured_s = deposit_ms / 1e3
    arith_s = total_p * steps_a_product / lane_steps
    octet_s = total_o / octets_s
    print(f"ENGINE_CARD lane_steps_a_second={lane_steps:.4g} octets_a_second={octets_s:.4g} steps_a_product={steps_a_product:g}")
    print(f"ENGINE_MEASURED deposit_ms_a_section={deposit_ms:.1f} us_a_site={measured_s / sites * 1e6:.3f} "
          f"products_a_second={total_p / measured_s:.4g} lane_steps_a_product={lane_steps * measured_s / total_p:.0f} "
          f"octets_a_second={total_o / measured_s:.4g}")
    print(f"ENGINE_FLOOR arithmetic_ms_a_section={arith_s * 1e3:.2f} arithmetic_us_a_site={arith_s / sites * 1e6:.3f} "
          f"octets_ms_a_section={octet_s * 1e3:.2f} octets_us_a_site={octet_s / sites * 1e6:.3f} "
          f"sum_us_a_site={(arith_s + octet_s) / sites * 1e6:.3f}")
    print(f"ENGINE_RATIO measured_over_arithmetic={measured_s / arith_s:.1f} measured_over_octets={measured_s / octet_s:.1f} "
          f"measured_over_sum={measured_s / (arith_s + octet_s):.1f}")
    for bar in (1.0,):
        print(f"ENGINE_BAR us_a_site={bar:g} over_sum_of_floors={bar / ((arith_s + octet_s) / sites * 1e6):.2f} "
              f"ms_a_section={bar * sites / 1e3:.1f} gb_hours={bar * 1e-6 * 1e9 / 3600:.3f}")


if __name__ == "__main__":
    main()
