"""A ruler (arithmetic only, no machine): the field's entries by block and the card's octets by term at te7's declaration.

The two functions copy the sizing arithmetic of `FieldLayout::new` (`crates/holonics/src/hnn/tower/field.rs`) and of
`read_octets` (`crates/holonics-cuda/src/hnn/field.rs`) as they stand at main 8854c9693, for the state head
`hnn-field-v14e 100 64 4 8 2 128 4 4 3771 2 0 32` (alphabet, width, heads, modes, still, contacts, ticks, frames,
reach, lanes, depth, carry), no triads. It reads no state and no passage.
"""

A, D, H, N, STILL, F, K, FRAMES, REACH, LANES, DEPTH, C, J = 100, 64, 4, 8, 2, 128, 4, 4, 3771, 2, 0, 32, 0
M2 = 2 * H * N                      # the real modes over every head
SPAN = 2 * N
MOMENT_HEADS = sum(1 for h in range(H) if h % FRAMES >= STILL)
TM = MOMENT_HEADS * N               # the modes that carry a moment
PACED = MOMENT_HEADS


def entries(dw):
    blocks = [
        ("letter rows (enc, before, after), (A+1) x D each", 3 * (A + 1) * dw),
        ("moment rows (before, after), (A+1) x 2T each", 2 * (A + 1) * 2 * TM),
        ("heads' charts (q, v, probe, out, moment_face), 2M x D each", 5 * M2 * dw),
        ("readout lift, D x D", dw * dw),
        ("pair contacts (a, b drives, W return), f x D each", 3 * F * dw),
        ("carry charts (turn, leak), C x D each", 2 * C * dw),
        ("biases, temperatures, paces", 3 * M2 + 4 * dw + 2 * F + A + 2 * H + PACED * (A + 1) + 2 * C + 6 * J),
    ]
    return blocks


def octets(dw, f=F):
    slots = sum(1 for level in range(2, 64) if (1 << level) < REACH) * 2
    k = 0
    while 9 ** k < REACH:
        k += 1
    trits = min(N, k)
    probe_site = 4 * H * (1 + 2 * (1 << trits))
    carry_site, triad_site = 48 * C, 80 * J
    tick_site = (triad_site + carry_site + 4 * dw + 16 * LANES + 8 * 2 * M2 + 2 * 8 * H * SPAN + 16 * H + 8 * H + 4 * H + 4 * H
                 + 8 * M2 + 4 * dw + 16 * LANES + 3 * 8 * f + (2 * 16 * SPAN + 8) * H + 8 * H * slots + probe_site
                 + 4 * H * SPAN + 8 * H * SPAN + 4 * H * SPAN + 16 * H)
    face_site = 8 * dw + 4 * dw + 16 * LANES + 8 * A + 8 * A + 16 + 16 + 2 * 8 * dw
    mixture_site = 5 + 2 * 4 * A + 9 + 8 * A + 16
    moment_site = 8 * M2 + 112 * TM + 24 * PACED * N * (K + 1)
    reverse_site = (8 * 8 * J + 16 * C + 8 * M2 + 8 * A + 5 * 8 * dw + 3 * 8 * f + 8 * M2 + 8 * H * SPAN + 2 * 8 * M2 + 16 * M2
                    + 2 * 16 * SPAN + 112 * TM)
    site = K * tick_site + face_site + mixture_site + moment_site + reverse_site + 8 * M2
    pair = K * H * 8 * 2 + 24
    return site, pair


if __name__ == "__main__":
    print("# entries by block, hnn-field-v14e 100 64 4 8 2 128 4 4 3771 2 0 32")
    total = 0
    for name, count in entries(D):
        total += count
        print(f"{count:>7}  {name}")
    print(f"{total:>7}  all (the state's material; the learner header's 175104 is its count of key draws)")
    site, pair = octets(D)
    site0, _ = octets(0)
    site_f0, _ = octets(D, 0)
    print("# the card's octets a training read (a return), by term")
    print(f"octets a pair of sites in one region: {pair}  (K H 8 2 weights and shares, 24 the contact's return and one head's covector)")
    print(f"octets a site: {site}  of which follow the width D: {site - site0}; follow the contacts f: {site - site_f0}")
    for s in (256, 514, 672, 1500, 3771):
        whole = pair * s * s + site * s
        print(f"region of {s:>5} sites: pairs {pair * s:>8} octets a site, carriers {site} a site, pairs' share {pair * s / (pair * s + site):.3f}, width's share {(site - site0) / (pair * s + site):.4f}, region {whole / 1e6:9.1f} MB")
