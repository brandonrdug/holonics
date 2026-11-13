"""P59: G138's parts beside the copies' readings (ratios over the mean of the two controls, as G138 defines them); held or missed, no rule applied.
Part (s): the contact family with each entry at the product of its copies' ratios and the small entries as they stand. Numbers only."""
import re
import sys

Q = sys.argv[1]
FAMILY = r"field_(contact_|exposure|pace_skin_back|spread|sums|classes)"


def entries(path):
    out = {}
    for line in open(path):
        m = re.match(r"FIELD_PROFILE entry=(\w+) launches=(\d+) ms=(\d+) us_a_launch=(\d+)", line)
        if m:
            out[m.group(1)] = int(m.group(4)) * int(m.group(2)) / 1000.0 / 100
    return out


def heads(path, entry):
    out = {}
    for line in open(path):
        m = re.match(r"FIELD_PROFILE_HEAD entry=(\w+) head=(\d+) kind=(\w+) launches=(\d+) us=(\d+)", line)
        if m and m.group(1) == entry:
            out[int(m.group(2))] = (m.group(3), int(m.group(5)) / 1000.0 / 100)
    return out


c1, c2, cp = entries(f"{Q}/hc1.log"), entries(f"{Q}/hc2.log"), entries(f"{Q}/hcopies.log")
ctl = {e: (c1.get(e, 0) + c2.get(e, 0)) / 2 for e in set(c1) | set(c2)}
ratio = lambda copy, entry: cp[copy] / ctl[entry]


def line(part, name, read, guess, lo, hi):
    held = "HELD" if lo <= read <= hi else ("MISSED below" if read < lo else "MISSED above")
    print(f"G138 ({part}) {name} {read:.3f} (guess {guess}, {lo} to {hi}): {held}")


print("# G138, fixed before its reads (the guess file at origin/main), beside P59's copies: a copy's time over its entry's mean of the two controls.")
line("r", "the rows", ratio("field_copy_r_contact_rows", "field_contact_rows"), 0.80, 0.62, 0.93)
line("r", "the skin's return", ratio("field_copy_r_pace_skin_back", "field_pace_skin_back"), 0.72, 0.50, 0.90)
line("r", "the exposure", ratio("field_copy_r_exposure", "field_exposure"), 0.60, 0.35, 0.85)
line("r", "the forward contact at five limbs", ratio("field_copy_r_contact_l5", "field_contact_l5"), 0.92, 0.78, 1.00)
line("r", "the forward contact at six limbs", ratio("field_copy_r_contact_l6", "field_contact_l6"), 0.92, 0.78, 1.00)
line("r", "the columns", ratio("field_copy_r_contact_columns", "field_contact_columns"), 0.85, 0.65, 0.97)
line("w", "the rows", ratio("field_copy_w_contact_rows", "field_contact_rows"), 0.93, 0.82, 0.99)
line("w", "the exposure", ratio("field_copy_w_exposure", "field_exposure"), 0.85, 0.65, 0.97)
line("w", "the forward contact at five limbs", ratio("field_copy_w_contact_l5", "field_contact_l5"), 0.94, 0.82, 1.00)
line("w", "the forward contact at six limbs", ratio("field_copy_w_contact_l6", "field_contact_l6"), 0.94, 0.82, 1.00)
line("w", "the skin's return", ratio("field_copy_w_pace_skin_back", "field_pace_skin_back"), 0.92, 0.80, 0.99)
line("a", "the rows", ratio("field_copy_a_contact_rows", "field_contact_rows"), 0.84, 0.70, 0.94)
line("a", "the skin's return", ratio("field_copy_a_pace_skin_back", "field_pace_skin_back"), 0.78, 0.60, 0.92)
line("c", "the columns", ratio("field_copy_c_contact_columns", "field_contact_columns"), 0.50, 0.30, 0.72)
hc, h1, h2 = heads(f"{Q}/hcopies.log", "field_copy_c_contact_columns"), heads(f"{Q}/hc1.log", "field_contact_columns"), heads(f"{Q}/hc2.log", "field_contact_columns")
for kind, guess, lo, hi in (("paced", 0.42, 0.22, 0.65), ("still", 0.62, 0.40, 0.85)):
    hs = [h for h in hc if hc[h][0] == kind]
    num = sum(hc[h][1] for h in hs)
    den = sum((h1[h][1] + h2[h][1]) / 2 for h in hs)
    line("c", f"the columns on the {kind} heads", num / den, guess, lo, hi)
products = {
    "field_exposure": ratio("field_copy_r_exposure", "field_exposure") * ratio("field_copy_w_exposure", "field_exposure"),
    "field_contact_l5": ratio("field_copy_r_contact_l5", "field_contact_l5") * ratio("field_copy_w_contact_l5", "field_contact_l5"),
    "field_contact_l6": ratio("field_copy_r_contact_l6", "field_contact_l6") * ratio("field_copy_w_contact_l6", "field_contact_l6"),
    "field_contact_rows": ratio("field_copy_r_contact_rows", "field_contact_rows") * ratio("field_copy_w_contact_rows", "field_contact_rows") * ratio("field_copy_a_contact_rows", "field_contact_rows"),
    "field_contact_columns": ratio("field_copy_r_contact_columns", "field_contact_columns") * ratio("field_copy_c_contact_columns", "field_contact_columns"),
    "field_pace_skin_back": ratio("field_copy_r_pace_skin_back", "field_pace_skin_back") * ratio("field_copy_w_pace_skin_back", "field_pace_skin_back") * ratio("field_copy_a_pace_skin_back", "field_pace_skin_back"),
}
family = {e: v for e, v in ctl.items() if re.match(FAMILY, e)}
total = sum(family.values())
at = sum(v * products.get(e, 1.0) for e, v in family.items())
for e, v in sorted(family.items(), key=lambda kv: -kv[1]):
    print(f"G138_FAMILY entry={e} controls_ms={v:.2f} product={products.get(e, 1.0):.3f} at_product_ms={v * products.get(e, 1.0):.2f}")
line("s", f"the family at the products, from {total:.1f} ms a profiled section in this hold's controls (115.6 in p57_schedule)", at, 74, 62, 90)
