#!/usr/bin/env python3
"""A ruler on the host: the arithmetic and the octets one section of the store's trainer needs, against the card,
with the card's measured time by family beside each floor (the engineering report of November 20, item A2).

Usage: python3 tools/engine_count.py LOG [--pump] [--trace TRACE.sqlite --trace-sections N]
                                     [--products-a-second P] [--octets-a-second B]

LOG is a train-store log: its STORE_DECLARATION line, its STORE_SECTION lines and its FIELD_CARD line. --pump counts the
pumped carry's chart (`Declaration::pump`; the declaration line does not print it). TRACE is an Nsight Systems export
(`nsys export --type sqlite`) of N sections of the same build and declaration; its kernels are summed by family.

The count is the one of November 12 (`research/records/2026-11-12_A_SITES_ARITHMETIC_IS_COUNTED_..._receipts/
engine_count.py`, whose terms it keeps), read at today's parts: the carry circles' scans are their own family (they
were inside "small"), and the pump's chart (2C by D, forward, outer and transposed) joins the site maps. The unit is
one product of two words of at most 32 bits with its 64-bit sum, counted at the width the term's information needs,
never at the word it runs on. The defaults are the card's measured yardsticks (`Resident::yardsticks`, November 12):
5.1914e12 narrow products a second (one thread a 4 by 4 tile of a 64 by 64 map) and 5.7247e11 octets a second read
in order. Both are this card's ceilings for those kernels, never a law's quantity; a family's ratio of its measured
time over its floor names where the realization stands furthest from the law (atlas `tower.field-engine-count`).

Every count is agent-inferred from the kernels' source and stands until a profile by entry replaces it. No figure
here is a rate of learning.
"""
import argparse
import re
import sqlite3


def fields(line):
    return {k: v for k, v in re.findall(r"(\w+)=(-?[\w.]+)", line)}


# The card's kernels by the count's family (by name; agent-inferred from kernels/field.cu).
FAMILIES = [
    ("site maps", ("field_transposed", "field_outer", "field_affine")),
    ("carry scans", ("field_pair_gamma", "field_pair_scan", "field_pair_gate_back")),
    ("contact and crowds", ("field_contact", "field_pace_skin_back", "field_skin", "field_exposure", "field_spread",
                            "field_pair")),
    ("face and blanks", ("field_tied", "field_blank", "field_face", "field_classes", "field_encoding", "field_mark",
                         "field_level", "field_twin", "field_open", "field_exponential")),
    ("moments and clocks", ("field_moment", "field_cavity", "field_clock", "field_pace", "field_paces",
                            "field_pframes")),
    ("site kernels, small", ("field_chart", "field_ratio", "field_unit", "field_frame", "field_unframe", "field_add",
                             "field_sums", "field_current", "field_wide")),
]


def family_of(name):
    for fam, prefixes in FAMILIES:
        if any(name.startswith(p) for p in prefixes):
            return fam
    return "other"


def traced(path, sections):
    db = sqlite3.connect(path)
    by = {}
    for name, ns, n in db.execute("select s.value, sum(k.end-k.start), count(*) from CUPTI_ACTIVITY_KIND_KERNEL k "
                                  "join StringIds s on s.id=k.shortName group by s.value"):
        fam = family_of(name)
        ms, launches = by.get(fam, (0.0, 0))
        by[fam] = (ms + ns / 1e6 / sections, launches + n / sections)
    copies = list(db.execute("select copyKind, sum(bytes), sum(end-start), count(*) from CUPTI_ACTIVITY_KIND_MEMCPY "
                             "group by copyKind"))
    return by, copies


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--pump", action="store_true")
    ap.add_argument("--trace")
    ap.add_argument("--trace-sections", type=int, default=0)
    ap.add_argument("--products-a-second", type=float, default=5.1914e12)
    ap.add_argument("--octets-a-second", type=float, default=5.7247e11)
    a = ap.parse_args()

    decl, card, sections = None, None, []
    with open(a.log) as f:
        for line in f:
            if line.startswith("STORE_DECLARATION"):
                decl = fields(line)
            elif line.startswith("FIELD_CARD "):
                card = fields(line)
            elif line.startswith("STORE_SECTION"):
                sections.append(fields(line))
    if decl is None or card is None or not sections:
        raise SystemExit("engine_count: the log lacks STORE_DECLARATION, FIELD_CARD or STORE_SECTION lines")
    n = len(sections)
    mean = lambda k: sum(int(s[k]) for s in sections) / n
    sites, opened, ms = mean("sites"), mean("open"), mean("ms")
    pair_terms = int(card["pairs"]) / int(card["returns"])
    batches = int(card["batches"]) / n

    alphabet = int(decl["alphabet"])
    dw = int(decl["lanes"]) * int(decl["lane_width"])         # the face width D
    heads, still = int(decl["heads"]), int(decl["still"])
    paced = heads - still
    modes = int(decl["modes"])
    span = 2 * modes
    m2 = heads * span
    f = int(decl["contacts"])
    c2 = 2 * int(decl["carry"])
    ticks = int(decl["ticks"])
    pump = c2 if a.pump else 0                                # the pump's chart: 2C rows of D

    print(f"ENGINE_COUNT log_sections={n} sites={sites:.0f} open={opened:.0f} pair_terms={pair_terms:.4g} "
          f"batches_a_section={batches:.2f} section_ms={ms:.1f}")
    print(f"ENGINE_PARTS alphabet={alphabet} face_width={dw} face_lanes={decl['lanes']} heads={heads} paced={paced} "
          f"modes={modes} words_a_site={m2} contacts={f} carry_reals={c2} pump_rows={pump} ticks={ticks}")

    rows = []  # (family, unit, units a section, products a unit, octets a unit)
    fwd = 3 * m2 * dw + dw * m2 + 2 * f * dw + c2 * dw + pump * dw + dw * f
    fwd_octets = (6 * dw * 4 + m2 * 8 + f * 8) + (3 * m2 * 8 + dw * 8 + 2 * f * 8 + (c2 + pump) * 8 + dw * 8)
    rows.append(("site maps", "site and tick", sites * ticks, fwd + 2 * fwd + m2 * dw, 3 * fwd_octets))
    # The carry circles: the gate's leak and coupling, the scan's complex step (and the pump's conjugate), their
    # returns; a circle's two reals read and written at each step (forward, pre, face, back, gate's back).
    carry = 24 * c2 + (12 * c2 if a.pump else 0)
    rows.append(("carry scans", "site and tick", sites * ticks, carry, 16 * c2 * 5))
    rows.append(("site kernels, small", "site and tick", sites * ticks, 6 * dw + 12 * m2, 16 * (dw + m2)))
    rows.append(("moments and clocks", "site", sites, 3 * dw * m2 + 12 * paced * span * 8, 8 * (2 * dw + 6 * m2)))
    face = dw * dw + alphabet * dw + 10 * alphabet + alphabet + 2 * alphabet * dw + 2 * dw * dw
    face_octets = 6 * alphabet * 8 + 6 * dw * 8
    blank = dw * dw + alphabet * dw + 10 * alphabet + dw * dw + alphabet * dw + 8 * paced * span
    rows.append(("face and blanks", "open site and tick", opened * ticks,
                 (face + blank * (ticks - 1)) / ticks, face_octets))
    lock, numer, skin = modes * 5, span * 2, modes * 4 * paced / heads
    pair_fwd = lock + 6 + 1 + numer + skin
    pair_back = (span * 2 + 3 + span * 3) + (span * 3 + span * 2) + modes * 6 * paced / heads
    octaves = max(1, (int(decl["reach"]) - 1).bit_length())
    crowd_units = sites * heads * ticks * 2 * octaves
    rows.append(("contact and crowds", "pair-term", pair_terms + crowd_units, pair_fwd + pair_back,
                 (8 * 7 * pair_terms + 8 * 7 * crowd_units) / (pair_terms + crowd_units)))

    measured, copies = ({}, [])
    if a.trace:
        if a.trace_sections <= 0:
            raise SystemExit("engine_count: --trace needs --trace-sections")
        measured, copies = traced(a.trace, a.trace_sections)

    total_p = total_o = 0.0
    print("family | unit | units a section | products a unit | products a section | octets a section | "
          "floor ms (products, octets) | card ms a section | over the larger floor")
    for name, unit, units, products, octets in rows:
        p, o = units * products, units * octets
        total_p += p
        total_o += o
        fp, fo = p / a.products_a_second * 1e3, o / a.octets_a_second * 1e3
        got = measured.get(name, (0.0, 0))[0]
        ratio = f"{got / max(fp, fo):.1f}" if got else "-"
        print(f"{name} | {unit} | {units:.4g} | {products:.0f} | {p:.4g} | {o:.4g} | {fp:.2f}, {fo:.2f} | "
              f"{got:.1f} | {ratio}")
    if "other" in measured:
        print(f"other kernels | - | - | - | - | - | - | {measured['other'][0]:.1f} | -")
    fp, fo = total_p / a.products_a_second * 1e3, total_o / a.octets_a_second * 1e3
    print(f"ENGINE_TOTAL products_a_section={total_p:.4g} products_a_site={total_p / sites:.0f} "
          f"octets_a_section={total_o:.4g} floor_products_ms={fp:.1f} floor_octets_ms={fo:.1f} "
          f"floor_sum_ms={fp + fo:.1f}")
    print(f"ENGINE_RATIO section_ms={ms:.1f} over_products={ms / fp:.1f} over_octets={ms / fo:.1f} "
          f"over_sum={ms / (fp + fo):.1f}")
    if measured:
        kernels = sum(v[0] for v in measured.values())
        launches = sum(v[1] for v in measured.values())
        print(f"ENGINE_TRACE kernels_ms_a_section={kernels:.1f} launches_a_section={launches:.0f} "
              f"kernels_over_sum_of_floors={kernels / (fp + fo):.1f}")
        kinds = {1: "host_to_card", 2: "card_to_host", 8: "card_to_card"}
        for kind, nbytes, ns, count in copies:
            print(f"ENGINE_COPIES {kinds.get(kind, kind)} count_a_section={count / a.trace_sections:.0f} "
                  f"mb_a_section={nbytes / 1e6 / a.trace_sections:.2f} ms_a_section={ns / 1e6 / a.trace_sections:.2f}")


if __name__ == "__main__":
    main()
