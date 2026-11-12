#!/usr/bin/env python3
"""A ruler: a lap's training regions, rebuilt from the trainer's own rules and counted by kind of state.

What it measures. `train-field` (crates/holonics/examples/solenoidal_alpha/complete_language/field_train.rs,
read at main 8f9edb018) forms, for every problem of a section, one keyed mask region, one state of the
writer's path (`opening_region`), and under FIELD_PATH_WRITER one writer state. The lap lines' `sites`
count each region's weighed domain (`FieldReceipt.sites`), never the sites the card computes. This ruler
rebuilds every region of a lap from the passage, the held file and the key file, and prints by kind:

  regions, the sites computed (every site of a region is a receiving row on each head and tick),
  the sum of sites squared (the card reserves its weights a pair of a region's sites),
  open and definite sites, and the pairs a head and tick meets:
    an open row meets every definite site of its region (`ClassLists::support`, the open receiver), so
    its pairs are open x definite, a count that does not read the state;
    a definite row meets its near field and its probed classes' definite members, which read the state:
    the ruler prints the near field's count (the least) and definite x (definite - 1) (the most).

The known case it is drawn on first. Every `FIELD_SECTION` line of the lap's own log prints the
section's `sites` (the weighed domains) and `length` (its longest region). The ruler computes both for
every section and counts the lines it reproduces; where any line differs, its counts are not read.

A ruler is an instrument on the host: it reads no state, builds nothing and takes no card. It prints
numbers only (no path, no text of the passage, no key). The switches are read from the environment
under the trainer's own names, so it is run under the exports the lap ran under.

  python3 section_regions_census.py --units U --train T --dev D --keys K --log LAP_LOG
  python3 section_regions_census.py --self-test
"""
import argparse
import os
import re
import sys

M64 = (1 << 64) - 1
NEAR = 6


def mix(seed, counter):
    z = (seed + counter * 0x9E3779B97F4A7C15) & M64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
    return z ^ (z >> 31)


def octave_of(d):
    return d.bit_length() - 1


def popcount(x):
    return bin(x).count("1")


def isqrt(n):
    import math

    return math.isqrt(n)


class Switches:
    """The trainer's declared switches, each set where its variable stands in the environment."""

    NAMES = [
        ("tail_keyed", "FIELD_TAIL_KEYED"),
        ("front_cut", "FIELD_PATH_FRONT_CUT"),
        ("far_keyed", "FIELD_PATH_FAR_KEYED"),
        ("opening", "FIELD_PATH_OPENING"),
        ("writer", "FIELD_PATH_WRITER"),
        ("prefix", "FIELD_PATH_PREFIX"),
        ("room_cut", "FIELD_ROOM_CUT"),
    ]

    def __init__(self, env=None, **given):
        env = os.environ if env is None else env
        for attr, name in self.NAMES:
            setattr(self, attr, given.get(attr, name in env))

    def text(self):
        return " ".join(f"{attr}={int(getattr(self, attr))}" for attr, _ in self.NAMES)


def problems_of(text):
    """`problems_of`: records `question US answer` separated by RS, or blank-line blocks."""
    if b"\x1e" in text:
        out = []
        for record in text.split(b"\x1e"):
            cut = record.find(b"\x1f")
            if cut < 0:
                continue
            q, a = record[:cut], record[cut + 1 :]
            if q and a:
                out.append((q, a))
        return out
    out, block = [], []
    for line in text.split(b"\n") + [b""]:
        if line:
            block.append(line)
            continue
        if len(block) >= 2:
            out.append((block[0], b"\n".join(block[1:])))
        block = []
    return out


def lengths_of(problems):
    """Each problem's classes on a units file of no merges: the question and its line, the answer."""
    return [(len(q) + 1, len(a)) for q, a in problems]


def sections_of(train, section, withheld, seed):
    keyed = sorted(range(len(train)), key=lambda i: (mix(seed, (1 << 61) | i), i))
    w = min(withheld, len(keyed))
    unseen = sorted(keyed[:w])
    order = sorted(keyed[w:], key=lambda i: (train[i][0] + train[i][1], i))
    return [order[c : c + section] for c in range(0, len(order), section)], unseen


def walk(seed, read, sections):
    return sorted(range(sections), key=lambda s: (mix(seed, ((read << 40) ^ s) & M64), s))


def paths_of(seed, read, sections):
    keyed = sorted((i for sec in sections for i in sec), key=lambda i: (mix(seed, (7 << 60) | (read << 40) | i), i))
    out, at = [None] * len(sections), 0
    for s in walk(seed, read, len(sections)):
        out[s] = keyed[at : at + len(sections[s])]
        at += len(sections[s])
    return out


def tail(sw, seed, draw, room):
    room = max(room, 1)
    if not sw.tail_keyed:
        return min(NEAR, room)
    octaves = room.bit_length()
    k = mix(seed, draw | (1 << 63)) % octaves
    low = 1 << k
    high = min((1 << (k + 1)) - 1, room)
    return low + mix(seed, draw | (3 << 62)) % (high - low + 1)


# A region as the ruler keeps it: (kind, sites, resolved bitset, the sites its lap line counts).


def mask_region(sw, seed, answer, ql, al, draw):
    length = ql + al + tail(sw, seed, draw, answer - al)
    head = mix(seed, draw)
    u = ((head >> 1) & 0xFFFF) + 1
    tau = max((u * u) >> 16, 1)
    whole = head & 1 == 1
    frm = 0 if whole else ql
    opened = 0
    for t in range(frm, length):
        if (mix(seed, draw ^ ((t + 1) << 32)) & 0xFFFF) < tau:
            opened |= 1 << t
    if opened == 0:
        opened = 1 << (frm + mix(seed, (draw + 1) & M64) % (length - frm))
    k = popcount(opened)
    m = length if whole else length - ql
    resolved = ((1 << length) - 1) & ~opened
    return ("mask_whole" if whole else "mask_answer", length, resolved, isqrt(4 * m * max(k, 1)))


def first_k(key, ql, extent, k):
    """The first `k` places of the keyed octave order past the question, by distance `d = t + 1 - ql`:
    every distance up to `full`, the `extras` of the octave the count ends in, and the octave of the next
    place in the order (none where every place is taken)."""
    full, c, rem = 0, 0, k
    while rem > 0:
        lo = 1 << c
        hi = min((1 << (c + 1)) - 1, extent)
        size = hi - lo + 1
        if rem >= size:
            full, rem, c = hi, rem - size, c + 1
            continue
        keyed = sorted(range(lo, hi + 1), key=lambda d: (mix(key, ql + d - 1), d))
        return full, sorted(keyed[:rem]), c
    return full, [], (c if full < extent else None)


def bits_of(ql, full, extras):
    r = (1 << (ql + full)) - 1
    for d in extras:
        r |= 1 << (ql + d - 1)
    return r


def opening_region(sw, seed, answer, ql, al, draw):
    if sw.prefix:
        last = min(al, answer - 1)
        k = mix(seed, draw | (5 << 61)) % (last + 1)
        frontier = ql + k
        cut = min(frontier + NEAR, ql + answer)
        return ("prefix", cut, (1 << frontier) - 1, last + 1)
    room = answer
    total = ql + room
    key = mix(seed, draw | (5 << 61))
    o = key % (room.bit_length() + 1)
    if o == 0 or sw.opening:
        k = 0
    else:
        low = 1 << (o - 1)
        high = min((1 << o) - 1, room)
        k = low + mix(seed, draw | (6 << 61)) % (high - low + 1)
    full, extras, front = first_k(key, ql, room, k)
    # The lowest resolved void: the least resolved distance past the answer.
    if full >= al + 1:
        dend = al + 1
    else:
        dend = next((d for d in extras if d >= al + 1), None)
    if dend is not None:
        before = min(full, dend - 1) + sum(1 for d in extras if d < dend)
        opens = (dend - 1) - before
        if opens == 0:
            return None
        tend = ql + dend - 1
        cut = total if sw.tail_keyed else min(tend + NEAR, total)
        resolved = bits_of(ql, min(full, dend - 1), [d for d in extras if d < dend]) | (((1 << cut) - 1) & ~((1 << tend) - 1))
        return ("path_past_void", cut, resolved, opens)
    resolved = bits_of(ql, full, extras)
    front_places = min((1 << (front + 1)) - 1, room)
    if sw.front_cut:
        front_end = min(ql + (1 << (front + 1)) - 1, total)
        cut = min(front_end + NEAR - 1, total)
        return ("path_front_cut", cut, resolved & ((1 << cut) - 1), front_places - k)
    if sw.far_keyed:
        return ("path_room", total, resolved, front_places - k + (octave_of(room) - front))
    return ("path_room", total, resolved, room - k)


def writer_region(sw, seed, answer, ql, al, draw):
    ln = min(al, answer)
    if ln == 0:
        return None
    cut = min(ql + ln + NEAR, ql + answer)
    key = mix(seed, draw | (7 << 61))
    most = ln - 1
    o = key % (most.bit_length() + 1)
    if o == 0:
        k = 0
    else:
        low = 1 << (o - 1)
        high = min((1 << o) - 1, most)
        k = low + mix(seed, draw | (15 << 60)) % (high - low + 1)
    full, extras, _ = first_k(key, ql, ln, k)
    resolved = bits_of(ql, full, extras) | (((1 << cut) - 1) & ~((1 << (ql + ln)) - 1))
    return ("writer", cut, resolved, ln - k)


def section_regions(sw, seed, answer, train, members, paths, draw):
    """`section_regions`: the members' mask regions, then each path problem's state, then its writer state."""
    regions, draws = [], []
    for i in members:
        draw += 1
        draws.append(draw)
        regions.append(mask_region(sw, seed, answer, train[i][0], train[i][1], draw))
    for i, d in zip(paths, draws):
        r = opening_region(sw, seed, answer, train[i][0], train[i][1], d)
        if r is not None:
            regions.append(r)
    if sw.writer:
        for i, d in zip(paths, draws):
            r = writer_region(sw, seed, answer, train[i][0], train[i][1], d)
            if r is not None:
                regions.append(r)
    return regions, draw


def pairs_of(sites, resolved):
    """A region's pairs a head and tick: (open rows', the definite rows' near field's, the definite rows' most)."""
    d = popcount(resolved)
    near = 2 * sum(popcount(resolved & (resolved >> g)) for g in range(1, NEAR))
    return (sites - d) * d, near, d * (d - 1), d


# The literal port, as the trainer writes it with lists: the self-test holds the counting forms above to it.


def opening_literal(sw, seed, answer, ql, al, draw):
    room = answer
    void = [t >= ql + al for t in range(ql + room)]
    unresolved = [t >= ql for t in range(ql + room)]
    key = mix(seed, draw | (5 << 61))
    o = key % (room.bit_length() + 1)
    if o == 0 or sw.opening:
        k = 0
    else:
        low = 1 << (o - 1)
        high = min((1 << o) - 1, room)
        k = low + mix(seed, draw | (6 << 61)) % (high - low + 1)
    order = sorted(range(ql, ql + room), key=lambda t: (octave_of(t + 1 - ql), mix(key, t), t))
    for t in order[:k]:
        unresolved[t] = False
    voided = next((t for t in range(ql, ql + room) if not unresolved[t] and void[t]), None)
    if voided is not None:
        for t in range(voided + 1, ql + room):
            unresolved[t] = False
    if not any(unresolved):
        return None
    stop, heard, kind = None, None, "path_room"
    if voided is not None:
        kind = "path_past_void"
        if not sw.tail_keyed:
            del unresolved[min(voided + NEAR, len(unresolved)) :]
    if voided is None and not sw.front_cut and sw.far_keyed:
        front = octave_of(order[k] + 1 - ql)
        heard = [t >= ql and octave_of(t + 1 - ql) <= front for t in range(len(unresolved))]
        last = front
        for t in order[k:]:
            oc = octave_of(t + 1 - ql)
            if oc > last:
                heard[t] = True
                last = oc
    if voided is None and sw.front_cut:
        kind = "path_front_cut"
        front = octave_of(order[k] + 1 - ql)
        front_end = min(ql + (1 << (front + 1)) - 1, len(unresolved))
        cut = min(front_end + NEAR - 1, len(unresolved))
        del unresolved[cut:]
        stop = front_end if front_end < cut else None
    n = len(unresolved)
    counted = sum(1 for t in range(ql, min(n if stop is None else stop, n)) if unresolved[t] and (heard is None or heard[t]))
    resolved = sum(1 << t for t in range(n) if not unresolved[t])
    return (kind, n, resolved, counted)


def writer_literal(sw, seed, answer, ql, al, draw):
    ln = min(al, answer)
    if ln == 0:
        return None
    cut = min(ql + ln + NEAR, ql + answer)
    unresolved = [ql <= t < ql + ln for t in range(cut)]
    key = mix(seed, draw | (7 << 61))
    most = ln - 1
    o = key % (most.bit_length() + 1)
    if o == 0:
        k = 0
    else:
        low = 1 << (o - 1)
        high = min((1 << o) - 1, most)
        k = low + mix(seed, draw | (15 << 60)) % (high - low + 1)
    order = sorted(range(ql, ql + ln), key=lambda t: (octave_of(t + 1 - ql), mix(key, t), t))
    for t in order[:k]:
        unresolved[t] = False
    return ("writer", cut, sum(1 << t for t in range(cut) if not unresolved[t]), sum(unresolved))


def self_test():
    # The mixer is splitmix64's output at the state `seed + counter * golden`: its published first outputs from zero.
    assert [mix(0, c) for c in (1, 2, 3)] == [0xE220A8397B1DCDAF, 0x6E789E6AA1B965F4, 0x06C45D188009454F]
    assert [octave_of(d) for d in (1, 2, 3, 4, 7, 8)] == [0, 1, 1, 2, 2, 3]
    checked = 0
    for case in range(4000):
        seed = mix(0xC0FFEE, case)
        answer = 2 + mix(seed, 1) % 90
        ql = 1 + mix(seed, 2) % 40
        al = 1 + mix(seed, 3) % (answer - 1)
        draw = 1 + mix(seed, 4) % 100000
        flags = mix(seed, 5)
        sw = Switches(env={}, tail_keyed=bool(flags & 1), front_cut=bool(flags & 2), far_keyed=bool(flags & 4), opening=bool(flags & 8), writer=True, prefix=False, room_cut=False)
        assert opening_region(sw, seed, answer, ql, al, draw) == opening_literal(sw, seed, answer, ql, al, draw), (case, "opening")
        assert writer_region(sw, seed, answer, ql, al, draw) == writer_literal(sw, seed, answer, ql, al, draw), (case, "writer")
        kind, sites, resolved, counted = mask_region(sw, seed, answer, ql, al, draw)
        assert 1 <= sites - popcount(resolved) and resolved < (1 << sites) and counted >= 1
        # A region's open rows meet every definite site once: the support's count, site by site.
        definite = [bool(resolved >> t & 1) for t in range(sites)]
        open_pairs = sum(sum(definite) for t in range(sites) if not definite[t])
        near = sum(1 for t in range(sites) if definite[t] for g in range(1, NEAR) for j in (t - g, t + g) if 0 <= j < sites and definite[j])
        assert pairs_of(sites, resolved)[:2] == (open_pairs, near)
        checked += 1
    print(f"CENSUS_SELF_TEST cases={checked} mixer=1 opening=1 writer=1 pairs=1")


def fields_of(line):
    return dict(re.findall(r"(\w+)=(-?\w+)", line))


def solve(a, b):
    """Least squares by the normal equations (a ruler's floats)."""
    n = len(a[0])
    ata = [[sum(r[i] * r[j] for r in a) for j in range(n)] for i in range(n)]
    atb = [sum(r[i] * y for r, y in zip(a, b)) for i in range(n)]
    for i in range(n):
        p = max(range(i, n), key=lambda r: abs(ata[r][i]))
        ata[i], ata[p], atb[i], atb[p] = ata[p], ata[i], atb[p], atb[i]
        if abs(ata[i][i]) < 1e-12:
            return None
        for r in range(i + 1, n):
            f = ata[r][i] / ata[i][i]
            atb[r] -= f * atb[i]
            for c in range(i, n):
                ata[r][c] -= f * ata[i][c]
    x = [0.0] * n
    for i in reversed(range(n)):
        x[i] = (atb[i] - sum(ata[i][c] * x[c] for c in range(i + 1, n))) / ata[i][i]
    return x


def quantiles(values):
    v = sorted(values)
    at = lambda p: v[min(len(v) - 1, (len(v) * p) // 100)]
    return f"least={v[0]} q10={at(10)} q25={at(25)} q50={at(50)} q75={at(75)} q90={at(90)} q99={at(99)} most={v[-1]} mean={sum(v) // len(v)}"


KINDS = ["mask_whole", "mask_answer", "path_room", "path_past_void", "path_front_cut", "prefix", "writer"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--units")
    ap.add_argument("--train")
    ap.add_argument("--dev")
    ap.add_argument("--keys")
    ap.add_argument("--log")
    ap.add_argument("--pair-octets", type=int, default=280, help="the card's octets a pair of a region's sites (4 heads, 4 kept ticks, returning)")
    ap.add_argument("--site-octets", type=int, default=71486, help="the card's octets a site (te7's declaration, returning)")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return 0
    sw = Switches()
    print(f"CENSUS_SWITCHES {sw.text()}")
    head = open(args.units, "rb").read(64).split(b"\n")[0]
    if head != b"founded-units-v1 0":
        print("CENSUS_REFUSED units_with_merges=1")
        return 1
    train = lengths_of(problems_of(open(args.train, "rb").read()))
    answer = max(al for _, al in train) + 1
    dev = [(ql, al) for ql, al in lengths_of(problems_of(open(args.dev, "rb").read())) if al < answer]
    reach = max(ql + answer for ql, _ in train + dev)
    keys = open(args.keys, "rb").read()
    seed = int.from_bytes(keys[-8:], "big")

    declared, lines, card = None, {}, []
    for line in open(args.log, "r", errors="replace"):
        if "FIELD_DECLARATION " in line and declared is None:
            declared = fields_of(line)
        elif "FIELD_SECTION " in line:
            f = fields_of(line)
            if "length" in f and "n" in f:
                lines[(int(f["lap"]), int(f["n"]))] = f
        elif "FIELD_CARD " in line:
            card.append(fields_of(line))
    if declared is None:
        print("CENSUS_REFUSED log_without_declaration=1")
        return 1
    section = int(declared["section"])
    heads, ticks, read0 = int(declared["heads"]), int(declared["ticks"]), int(declared["laps_read"])
    sections, unseen = sections_of(train, section, len(dev), seed)
    own = dict(answer=answer, train=len(train) - len(unseen), withheld=len(unseen), dev=len(dev), sections=len(sections))
    same = all(int(declared[k]) == v for k, v in own.items())
    print("CENSUS_DECLARATION " + " ".join(f"{k}={v}" for k, v in own.items()) + f" passages_reach={reach} declared_reach={declared['reach']} section={section} heads={heads} ticks={ticks} laps_read={read0} equal={int(same)}")
    print(f"CENSUS_PASSAGE question_classes {quantiles([q for q, _ in train])}")
    print(f"CENSUS_PASSAGE answer_classes {quantiles([a for _, a in train])}")

    laps = sorted({lap for lap, _ in lines})
    for lap in laps:
        read = read0 + lap
        draw = read * len(train)
        paths = paths_of(seed, read, sections)
        order = walk(seed, read, len(sections))
        rank = {s: r for r, s in enumerate(order)}
        tot = {k: [0] * 9 for k in KINDS}  # regions, sites, sites^2, open, definite, open pairs, near pairs, most pairs, the lap line's sites
        longest = {k: 0 for k in KINDS}
        rows, length_equal, sites_equal, first_miss, read_lines = [], 0, 0, None, 0
        for n, s in enumerate(order):
            regions, draw = section_regions(sw, seed, answer, train, sections[s], paths[s], draw)
            sec = {k: [0] * 9 for k in KINDS}
            for kind, sites, resolved, counted_sites in regions:
                po, pn, pm, d = pairs_of(sites, resolved)
                for acc in (tot[kind], sec[kind]):
                    for slot, v in enumerate((1, sites, sites * sites, sites - d, d, po, pn, pm, counted_sites)):
                        acc[slot] += v
                longest[kind] = max(longest[kind], sites)
            counted = sum(r[3] for r in regions)
            length = max(r[1] for r in regions)
            f = lines.get((lap, n))
            if f is not None:
                read_lines += 1
                le, se = int(f["length"]) == length, int(f["sites"]) == counted
                length_equal += le
                sites_equal += se
                if first_miss is None and not (le and se):
                    first_miss = f"n={n} line_sites={f['sites']} ruler_sites={counted} line_length={f['length']} ruler_length={length}"
                rows.append((s, sec, int(f["deposit_ms"]), int(f["regions_ms"])))
        print(f"CENSUS_CHECK lap={lap} sections={len(order)} lines={read_lines} length_equal={length_equal} sites_equal={sites_equal} first_miss={first_miss or '-'}")
        all_sites = sum(t[1] for t in tot.values())
        all_s2 = sum(t[2] for t in tot.values())
        all_open = sum(t[5] for t in tot.values())
        all_least = sum(t[5] + t[6] for t in tot.values())
        for k in KINDS:
            t = tot[k]
            if t[0] == 0:
                continue
            print(
                f"CENSUS_KIND lap={lap} kind={k} regions={t[0]} sites={t[1]} sites_share_ppm={t[1] * 1000000 // all_sites} sites_squared={t[2]} squared_share_ppm={t[2] * 1000000 // all_s2} "
                f"open={t[3]} definite={t[4]} pairs_open_rows={t[5]} open_pairs_share_ppm={t[5] * 1000000 // max(all_open, 1)} pairs_definite_near={t[6]} pairs_definite_most={t[7]} longest={longest[k]} mean_sites={t[1] // t[0]} line_sites={t[8]}"
            )
        print(
            f"CENSUS_LAP lap={lap} sites_computed={all_sites} pair_store_octets={all_s2 * args.pair_octets} site_octets={all_sites * args.site_octets} "
            f"pairs_least_a_head_tick={all_least} pairs_most_a_head_tick={sum(t[5] + t[7] for t in tot.values())} pairs_least_a_lap={all_least * heads * ticks} pairs_most_a_lap={sum(t[5] + t[7] for t in tot.values()) * heads * ticks}"
        )
        for c in card:
            print("CENSUS_CARD_LINE " + " ".join(f"{k}={v}" for k, v in c.items() if k in ("reads", "returns", "pairs", "batches", "peak_store")))
        if not rows:
            continue
        # The lap's sections in ten groups by their place in the length order, with the times the log prints.
        rows.sort(key=lambda r: r[0])
        for g in range(10):
            part = rows[len(rows) * g // 10 : len(rows) * (g + 1) // 10]
            if not part:
                continue
            c = len(part)
            mask = sum(r[1]["mask_whole"][1] + r[1]["mask_answer"][1] for r in part) // c
            room = sum(r[1]["path_room"][1] for r in part) // c
            other = sum(sum(r[1][k][1] for k in ("path_past_void", "path_front_cut", "prefix", "writer")) for r in part) // c
            pairs = sum(sum(v[5] + v[6] for v in r[1].values()) for r in part) * heads * ticks // c
            s2 = sum(sum(v[2] for v in r[1].values()) for r in part) * args.pair_octets // c
            print(f"CENSUS_GROUP lap={lap} group={g} sections={c} mask_sites={mask} room_sites={room} other_sites={other} pairs_least={pairs} pair_store_octets={s2} deposit_ms={sum(r[2] for r in part) // c} regions_ms={sum(r[3] for r in part) // c}")
        # A section's deposit time against its computed sites and its least pairs, and against the pair store beside them.
        y = [float(r[2]) for r in rows]
        x_sites = [float(sum(v[1] for v in r[1].values())) for r in rows]
        x_pairs = [float(sum(v[5] + v[6] for v in r[1].values()) * heads * ticks) for r in rows]
        x_s2 = [float(sum(v[2] for v in r[1].values())) for r in rows]
        mean_y = sum(y) / len(y)
        spread = sum((v - mean_y) ** 2 for v in y)
        for name, cols in (("sites_pairs", (x_sites, x_pairs)), ("sites_pairs_squared", (x_sites, x_pairs, x_s2)), ("pairs", (x_pairs,)), ("sites", (x_sites,))):
            scales = [1.0] + [(sum(col) / len(col)) or 1.0 for col in cols]
            a = [[1.0] + [col[i] / sc for col, sc in zip(cols, scales[1:])] for i in range(len(y))]
            x = solve(a, y)
            if x is None:
                print(f"CENSUS_FIT lap={lap} terms={name} singular=1")
                continue
            rest = sum((yy - sum(c * v for c, v in zip(x, row))) ** 2 for yy, row in zip(y, a))
            shares = " ".join(f"ms{i}={v:.4g}" for i, v in enumerate(x))
            x = [v / sc for v, sc in zip(x, scales)]
            coef = " ".join(f"c{i}={v:.6g}" for i, v in enumerate(x))
            print(f"CENSUS_FIT lap={lap} terms={name} sections={len(y)} ms_fixed_and_per_unit {coef} ms_of_a_mean_section {shares} explained_ppm={int((1 - rest / spread) * 1000000) if spread > 0 else 0}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
