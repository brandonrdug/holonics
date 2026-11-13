#!/usr/bin/env python3 -I
"""contact_arithmetic.py: P54 item 2, the contact family's arithmetic read from source at main (kernels/field.cu), no run [agent-inferred].

One line a product, quotient or release with its operands, where each is loaded from, the width its declaration proves, the bound those widths
and the releases before it prove on the result, the word it is formed in today (from the shipped PTX: a 128-bit product of two sign-extended
64-bit words is lowered to a full 128 by 128 sequence, three mul.lo.s64 and one mul.hi.u64), the narrowest form its bound proves (32x32>64,
64x64 low, 64x64 high, 64x64>128, 128), and its count a pair (P), a row (R) or a crowd slot (C). A line whose bound is only observed (no
declaration proves its operands' widths) stays wide and names the declaration that would prove it.

Declared widths (proved, not observed):
  D, a skin: <= 2^30 (31 bits unsigned; step 1).          w, a unit word (qf, qf32) or probe (pq, pq32) at unit power: |w| <= sqrt(2n) 2^16 = 2^18
  v, a framed value (vf): fit64, < 2^63.                    (ratio_to_power over the head's 2n reals; field_unit fits it to 32 bits).
  dy, the current's covector (dyh): fit64, < 2^63.          p, a share (e) or a crowd's share (ce): <= 2^63 (a mass fraction on 2^-63).
  ds, a contact covector: |ds| < 2^dsbits = 2^52 (contact_return_bits: 126 - 60 - 2 - reach_bits(3771) = 52; refused past it).
  sb, a lock at unit gain: fit64.  T, a temperature: <= 2^7 on 2^-24, 31 bits.  sw, a prefix of unit words: <= 2^12 x 2^18 = 2^30 (reach < 2^12).
  sv, a prefix of values: < 2^63 x 2^12 = 2^75.  count, a crowd's: < 2^12.  b, a turn rate 2 pi/n on 2^-30: < 2^33.
"""
LINES = [
    # entry, unit, count, product, operands (and loads), result bound bits, today, narrowest, proved
    ("field_contact_rows", "P", 16, "carry_d(D, v): the source value carried by the skin (paced)", "D: skin store; v: vf row", 94, "64x64>128", "64x64>128", True),
    ("field_contact_rows", "P", 16, "dy[x] * v' (pair_dp8's covector, both heads)", "dy: dyh row; v': carried value", 126, "128", "64x64>128", True),
    ("field_contact_rows", "P", 1, "p * dp (the weighted mean's term)", "p: e; dp: the 16-term sum", None, "128", "128", False),
    ("field_contact_rows", "P", 1, "p * (dp - mean) (compare)", "p: e; dp: dpb", None, "128", "128", False),
    ("field_contact_rows", "P", 1, "ln2 * release(., 63) (compare)", "ln2: constant; the release", None, "128", "128", False),
    ("field_contact_rows", "P", 1, "dz * sb (the temperature's covector)", "dz; sb: sb[i][j]", None, "128", "128", False),
    ("field_contact_rows", "P", 1, "T * dz (gained ds)", "T: temper; dz", None, "128", "128", False),
    ("field_contact_rows", "P", 16, "D * w (the probe role, regrouped: (ds D) w = ds (D w))", "D: skin store or 1; w: qf row", 49, "128", "32x32>64", True),
    ("field_contact_rows", "P", 16, "ds * (D w) (the probe role)", "ds: dss (staged); D w", 101, "128", "64x64>128", True),
    ("field_contact_rows", "C", 16, "D * V (a crowd's carried values, paced)", "D: crowd skin; V: sv prefix difference", 106, "128", "128", True),
    ("field_contact_rows", "C", 16, "dy * V' (a crowd's covector)", "dy; V'", None, "128", "128", False),
    ("field_contact_rows", "C", 1, "div_nearest_by(., count) (a crowd's mean)", "the sum; the read divisor", None, "128", "128", False),
    ("field_contact_rows", "C", 1, "ce * dpc", "ce; dpc", None, "128", "128", False),
    ("field_contact_rows", "C", 2, "p * (dp - mean), ln2 * . (a crowd's compare)", "ce; dpc", None, "128", "128", False),
    ("field_contact_rows", "C", 16, "w * W (crowd_base's pairing, a0 b0 + a1 b1)", "w: pq row; W: sw prefix difference", 49, "128", "32x32>64", True),
    ("field_contact_rows", "C", 8, "2 count D (crowd_base)", "count; D: crowd skin", 44, "128", "32x32>64", True),
    ("field_contact_rows", "C", 8, "pairing * (2 count D)", "pairing; 2 count D", 94, "128", "64x64>128", True),
    ("field_contact_rows", "C", 8, "pairing * 2^g (a shift)", "pairing; the grain", 124, "128", "shift", True),
    ("field_contact_rows", "C", 16, "W * W (crowd_base's power)", "W", 62, "128", "32x32>64", True),
    ("field_contact_rows", "C", 8, "D * D (crowd_base)", "D", 60, "128", "32x32>64", True),
    ("field_contact_rows", "C", 8, "power * D^2 (crowd_base)", "power; D^2", 123, "128", "64x64>128", True),
    ("field_contact_rows", "C", 1, "div_nearest(s, count^2 2^bits) (crowd_base)", "s; count", None, "128", "128", False),
    ("field_contact_rows", "C", 2, "dz * cs, T * dz (a crowd's temperature and gain)", "dz; cs; T", None, "128", "128", False),
    ("field_contact_rows", "C", 16, "D * W (a crowd's probe role, regrouped)", "D; W: sw", 61, "128", "32x32>64", True),
    ("field_contact_rows", "C", 16, "ds * (D W) (a crowd's probe role)", "dsk; D W", 113, "128", "64x64>128", True),
    ("field_contact_rows", "C", 16, "div_nearest_by(., count) (a crowd's probe role)", "the product; the read divisor", None, "128", "128", False),
    ("field_contact_rows", "C", 16, "D * w (the key's bracket)", "D; w: pq", 49, "128", "32x32>64", True),
    ("field_contact_rows", "C", 16, "(D w) * count (the key's bracket)", "D w; count", 61, "128", "64x64 low", True),
    ("field_contact_rows", "C", 16, "D * D * W (the key's bracket)", "D; W", 91, "128", "64x64>128", True),
    ("field_contact_rows", "C", 16, "ds * bracket (mul_fits, the key)", "dsk; bracket (<= 2^92)", 144, "128", "128", True),
    ("field_contact_rows", "C", 16, "div_nearest_by(prod, count^2)", "prod; the read divisor", None, "128", "128", False),
    ("field_contact_rows", "C", 16, "carried_ij(D, dy): D * dy", "D; dy", 93, "128", "64x64>128", True),
    ("field_contact_rows", "C", 16, "ce * carried (the values' share)", "ce; carried", 126, "128", "64x64>128", True),
    ("field_contact_rows", "C", 16, "div_nearest_by(., count) (the values' share)", "the product; the read divisor", None, "128", "128", False),
    # field_pace_skin_back, a paced head's pair over its 8 modes.
    ("field_pace_skin_back", "P", 16, "dy * v (inner, two a mode)", "dy: dyh; v: vf row", 126, "128", "64x64>128", True),
    ("field_pace_skin_back", "P", 8, "e * inner (mul_fits)", "p: e; inner (< 2^127)", None, "128", "128", False),
    ("field_pace_skin_back", "P", 16, "w_i * k (the lock's pairing, two a mode)", "w_i: pq row; k: qf row", 36, "128", "32x32>64", True),
    ("field_pace_skin_back", "P", 16, "k * k (the lock's power, two a mode)", "k: qf row", 36, "128", "32x32>64", True),
    ("field_pace_skin_back", "P", 8, "D * |k|^2 (the bracket)", "D: skin store; |k|^2 (< 2^38)", 68, "128", "64x64>128", True),
    ("field_pace_skin_back", "P", 8, "ds * bracket (mul_fits)", "ds: ds[i][j]; bracket (< 2^69)", 121, "128", "128", True),
    ("field_pace_skin_back", "P", 8, "E * D (skin_back_dev)", "E = value + lock; D", None, "128", "128", False),
    ("field_pace_skin_back", "P", 8, "release(E D, 30) * b (skin_back_dev)", "the release; b", None, "128", "128", False),
    ("field_pace_skin_back", "C", 16, "dy * V (a crowd's value, two a mode)", "dy; V: sv", 138, "128", "128", False),
    ("field_pace_skin_back", "C", 8, "ce * (x + y) (mul_fits)", "ce; the sum", None, "128", "128", False),
    ("field_pace_skin_back", "C", 8, "div_nearest(., count)", "the value; count", None, "128", "128", False),
    ("field_pace_skin_back", "C", 16, "w * W (the crowd's pairing)", "w: pq; W: sw", 49, "128", "32x32>64", True),
    ("field_pace_skin_back", "C", 8, "2 count * pairing", "count; pairing", 63, "128", "64x64 low", True),
    ("field_pace_skin_back", "C", 16, "W * W (the crowd's power)", "W", 62, "128", "32x32>64", True),
    ("field_pace_skin_back", "C", 8, "D * |W|^2", "D; |W|^2", 93, "128", "64x64>128", True),
    ("field_pace_skin_back", "C", 8, "div_nearest(., count^2)", "the bracket; count", None, "128", "128", False),
    ("field_pace_skin_back", "C", 8, "cds * bracket (mul_fits)", "cds (< 2^52); bracket", 147, "128", "128", True),
    ("field_pace_skin_back", "C", 16, "skin_back_dev's two products", "E; D; b", None, "128", "128", False),
    # field_contact_l5 and l6, the numerators by limb (every head).
    ("field_contact_l5", "P", 1, "coef_of(face, 2^62): face * multiplier", "face: the exponential's face (<= 2^62); 2^62", 124, "64x64>128", "shift", True),
    ("field_contact_l5", "P", 16, "carry_d(D, v) (paced)", "D: skin store; v: vf", 94, "64x64>128", "64x64>128", True),
    ("field_contact_l5", "P", 32, "(face << b) * |v| (the window's two limbs)", "the staged face (two limbs); |v| (< 2^63)", 127, "64x64>128", "64x64>128", True),
    ("field_contact_l5", "R", 16, "rowdiv_nearest (the row's division, a lane an entry)", "N; the row's divisor", None, "128", "128", False),
    ("field_contact_l5", "R", 16, "frame_of * y (the current's frame)", "U: the frame; y", 94, "128", "64x64>128", True),
    ("field_contact_l5", "P", 1, "rowdiv_nearest (the stored share)", "the share's dividend; the divisor", None, "128", "128", False),
    # field_contact_columns, a source over its receivers.
    ("field_contact_columns", "P", 16, "D * w_i (the key's bracket)", "D: skin store; w_i: pq row", 49, "128", "32x32>64", True),
    ("field_contact_columns", "P", 16, "D * D * w_j (the key's bracket)", "D; w_j: qf row", 79, "128", "64x64>128", True),
    ("field_contact_columns", "P", 16, "ds * bracket (the key)", "ds: ds[i][j]; bracket (< 2^80)", 133, "128", "128", True),
    ("field_contact_columns", "P", 16, "carried_ij(D, dy): D * dy", "D; dy: dyh row", 93, "128", "64x64>128", True),
    ("field_contact_columns", "P", 16, "p * carried (the value's return)", "p: e; carried (< 2^63)", 126, "128", "64x64>128", True),
    # field_exposure, the lock a pair (pair_base8) and the score.
    ("field_exposure", "P", 16, "a * b (the lock's pairing, 32-bit words, two a mode)", "a: pq32; b: qf32 row", 36, "64x64 low", "32x32>64", True),
    ("field_exposure", "P", 16, "b * b (the lock's power)", "b: qf32 row", 36, "64x64 low", "32x32>64", True),
    ("field_exposure", "P", 8, "pairing * 2D", "pairing (< 2^38); D", 69, "128", "64x64>128", True),
    ("field_exposure", "P", 8, "D * D", "D", 60, "64x64 low", "32x32>64", True),
    ("field_exposure", "P", 8, "power * D^2", "power (< 2^38); D^2", 98, "128", "64x64>128", True),
    ("field_exposure", "P", 1, "T * S (scored)", "T: temper (31 bits); S: the lock at unit gain (fit64)", 94, "128", "64x64>128", True),
]


def main():
    print(__doc__.split("\n\n", 1)[1])
    for e, unit, n, what, ops, bits, today, after, proved in LINES:
        b = "-" if bits is None else str(bits)
        print(f"LINE entry={e} unit={unit} count={n} today={today} narrowest={after} bound_bits={b} proved={'yes' if proved else 'observed_only'} product={what!r} operands={ops!r}")
    # Totals a unit by entry: today's forms and the narrowest proved.
    for e in dict.fromkeys(l[0] for l in LINES):
        for unit in ("P", "R", "C"):
            ls = [l for l in LINES if l[0] == e and l[1] == unit]
            if not ls:
                continue
            today, after = {}, {}
            for l in ls:
                today[l[6]] = today.get(l[6], 0) + l[2]
                after[l[7]] = after.get(l[7], 0) + l[2]
            narrowed = sum(l[2] for l in ls if l[6] != l[7])
            total = sum(l[2] for l in ls)
            print(f"TOTAL entry={e} unit={unit} products={total} narrowed_by_proof={narrowed} share={narrowed / total:.3f} today={today} after={after}")

    # Totals a row: the per-pair counts times the pairs a row and the per-slot counts times the crowd slots a row, on step 3's profiled read and
    # the census of its sections (p52_contact_forecast.txt's GEOMETRY: 4,078,042 rows a tick, 4 ticks, 29,269,670 active crowd slots a tick; pairs
    # by head 1,478,325,193, 994,152,016 (still) and 1,001,476,447, 1,092,662,117 (paced)).
    rows = 4078042 * 4
    per_row = {"still": (1478325193 + 994152016) / (2 * rows), "paced": (1001476447 + 1092662117) / (2 * rows)}
    slots = 29269670 / 4078042
    print(f"UNITS pairs_a_row_still={per_row['still']:.1f} pairs_a_row_paced={per_row['paced']:.1f} crowd_slots_a_row={slots:.2f}")
    for e in dict.fromkeys(l[0] for l in LINES):
        for kind in ("still", "paced"):
            if e in ("field_pace_skin_back",) and kind == "still":
                continue
            today, after, narrowed, total = {}, {}, 0.0, 0.0
            for l in LINES:
                if l[0] != e:
                    continue
                if kind == "still" and ("paced" in l[3] or l[3].startswith("carry_d")):
                    continue
                k = l[2] * (per_row[kind] if l[1] == "P" else slots if l[1] == "C" else 1)
                today[l[6]] = today.get(l[6], 0) + k
                after[l[7]] = after.get(l[7], 0) + k
                total += k
                narrowed += k if l[6] != l[7] else 0
            fmt = lambda d: "{" + ", ".join(f"{a}: {b:.0f}" for a, b in sorted(d.items())) + "}"
            print(f"ROW entry={e} head={kind} products_a_row={total:.0f} narrowed_by_proof={narrowed:.0f} share={narrowed / max(total, 1):.3f} today={fmt(today)} after={fmt(after)}")


if __name__ == "__main__":
    main()
