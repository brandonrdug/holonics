"""An independent exact replica of the loop-closure location used by the acoustic-encoding record.

It is NOT a repository owner and runs no repository code. It re-implements, in integers only,
`compression::keys::transport::TransportLocation::locate` (survivors by depth-first loop closure,
the rotation gauge fixed by the read set's first emission, the reflection gauge for the fibre's
classes), `LocatedTransport::keys` and `LocatedTransport::cycle`, and scans the two-ring frame
family of `compression::keys::frames::FrameFamily::pairs`. Its output (`replica_predictions.txt`) is
a PREDICTION that the validation queue's run of `tests/acoustic_encoding.rs` must confirm or refute;
it is not evidence about the Rust. Usage: python3 replica.py > replica_predictions.txt
"""
from math import gcd


def helix(periods):
    big_d = 1
    for d in periods:
        big_d *= d
    cells = periods[-1]
    return big_d, big_d // cells, cells


def locate(periods, classes, passages):
    big_d, grain, cells = helix(periods)
    emissions = [(c, k == 0) for p in passages for k, c in enumerate(p)]
    order = []
    for c, _ in emissions:
        if c not in order:
            order.append(c)
    labels0 = [None] * cells
    labels0[0] = emissions[0][0]
    stack = [(0, tuple([None] * classes), tuple(labels0), tuple(range(grain)))]
    survivors = []
    while stack:
        k, adv, lab, lifts = stack.pop()
        if k + 1 == len(emissions):
            survivors.append((adv, lab))
            continue
        cls, starts = emissions[k + 1]
        prev = None if starts else emissions[k][0]

        def place(advances, moved):
            cell = lab.index(cls) if cls in lab else None

            def keep(cell_x, labels):
                kept = tuple(x for x in moved if x // grain == cell_x)
                if kept:
                    stack.append((k + 1, advances, labels, kept))

            if cell is not None:
                keep(cell, lab)
            else:
                for c2 in range(cells):
                    if lab[c2] is None:
                        new = list(lab)
                        new[c2] = cls
                        keep(c2, tuple(new))

        if prev is None:
            place(adv, tuple(range(big_d)))
        else:
            for a in ([adv[prev]] if adv[prev] is not None else range(big_d)):
                moved = sorted((x + a) % big_d for x in lifts)
                new_adv = list(adv)
                new_adv[prev] = a
                place(tuple(new_adv), moved)
    return dict(periods=periods, classes=classes, order=order, survivors=survivors)


def representative(loc, adv, lab):
    big_d = helix(loc["periods"])[0]
    cells = len(lab)
    order, classes = loc["order"], loc["classes"]

    def ordering(a, l):
        rank = lambda c: order.index(c) if c in order else classes
        unread = lambda x: big_d if x is None else x
        return (
            [unread(a[c]) for c in order] + [unread(a[c]) for c in range(classes) if c not in order],
            [classes if x is None else rank(x) for x in l],
        )

    radv = tuple(None if a is None else (big_d - a) % big_d for a in adv)
    rlab = tuple(lab[(cells - c) % cells] for c in range(cells))
    return (radv, rlab) if ordering(radv, rlab) < ordering(adv, lab) else (adv, lab)


def fibre(loc):
    if not loc["survivors"]:
        return ("empty", None)
    reps = sorted(set(representative(loc, a, l) for a, l in loc["survivors"]), key=repr)
    complete = [r for r in reps if all(x is not None for x in r[0]) and sum(y is not None for y in r[1]) == loc["classes"]]
    if len(reps) == 1 and len(complete) == 1:
        return ("one", complete[0])
    return ("plural", len(reps))


def keys_of(periods, adv, lab, passage):
    big_d, grain, _ = helix(periods)
    out = []
    for key in range(big_d):
        lift, ok = key, True
        for c in passage:
            if lab[lift // grain] != c:
                ok = False
                break
            lift = (lift + adv[c]) % big_d
        if ok:
            out.append(key)
    return out


def cycle(periods, adv, lab, key):
    big_d, grain, _ = helix(periods)
    lift, total = key, 0
    for step in range(1, big_d + 1):
        c = lab[lift // grain]
        if c is None:
            return None
        total += adv[c]
        lift = (lift + adv[c]) % big_d
        if lift == key:
            return (step, total // big_d)
    return None


def classes_of(samples):
    alphabet = []
    for s in samples:
        if s not in alphabet:
            alphabet.append(s)
    return alphabet, [alphabet.index(s) for s in samples]


def family(bound):
    return [(a, b) for a in range(2, bound + 1) for b in range(2, bound + 1) if a != b and gcd(a, b) == 1]


def scan(name, samples, bound):
    alphabet, passage = classes_of(samples)
    k = len(alphabet)
    tally = dict(narrow=0, empty=0, plural=0, open=0, one=0)
    lines = []
    cycles = set()
    for per in family(bound):
        big_d, grain, cells = helix(per)
        if k > cells:
            tally["narrow"] += 1
            continue
        kind, detail = fibre(locate(per, k, [passage]))
        if kind == "empty":
            tally["empty"] += 1
        elif kind == "plural":
            tally["plural"] += 1
            lines.append("  frame %s plural (%d gauge classes)" % (per, detail))
        else:
            adv, lab = detail
            ks = keys_of(per, adv, lab, passage)
            c = cycle(per, adv, lab, ks[0]) if ks else None
            if c is None:
                tally["open"] += 1
                lines.append("  frame %s open" % (per,))
            else:
                tally["one"] += 1
                cycles.add(c[0])
                lines.append("  frame %s one: advances %s labels %s keys %s cycle %d winding %d" % (per, adv, lab, ks, c[0], c[1]))
    print("%s (rings <= %d, %d classes, %d samples): %s; cycles read %s" % (name, bound, k, len(samples), tally, sorted(cycles)))
    for line in lines:
        print(line)


def saw(period, step, count):
    return [256 * ((k % period) // step) - 384 for k in range(count)]


def thue_morse(count):
    return [256 * (bin(k).count("1") % 2) - 384 for k in range(count)]


def table(levels, period, count):
    return [256 * levels[k % period] - 384 for k in range(count)]


if __name__ == "__main__":
    scan("sawtooth period 7", saw(7, 2, 21), 6)
    scan("sawtooth period 12", saw(12, 3, 36), 6)
    scan("Thue-Morse", thue_morse(128), 6)
    scan("sawtooth period 7", saw(7, 2, 21), 9)
    scan("triangle period 7", table([0, 1, 2, 3, 3, 2, 1], 7, 21), 6)
    scan("square period 7", [(-384 if k % 7 < 3 else 384) for k in range(21)], 6)
    scan("sawtooth step 2 period 8", saw(8, 2, 24), 6)
    scan("sawtooth step 3 period 9", saw(9, 3, 27), 6)
    scan("quantized triangle period 12", table([0, 0, 1, 1, 2, 2, 3, 2, 2, 1, 1, 0], 12, 36), 6)
