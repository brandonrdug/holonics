"""A build's reproduction of a line's lap (CLAUDE.md, Method: "A build enters a line by reproducing it").

The build's STORE_SECTION lines are compared with the line's own, timings aside (`regions_ms`, `deposit_ms`, `ms`), and its last STORE_SAVE line
with the line's save at the same `k`, timings and the schedule fields aside. The schedule fields are `batches` and `peak_store`: how the
realization cut the sections into the card's batches (the card's free memory at the open sets the budget), the batch a card computes together,
which is a schedule and never a bit of the state (rulings of P52 and P58, November 13). They are printed beside, never compared. The states'
bytes are compared by the caller (`cmp` of STATE.k and MEAN.k).

Prints `GATE_REPRO` (sections, the line's lines, equal, EQUAL or DIFFERS), the first differing section and its fields where one differs, and
`GATE_SAVE` with the schedule fields of both. Exit 0 when every line is equal, 1 otherwise. Numbers only: the lines carry no text of a passage.

usage: python3 tools/reproduction.py BUILD_LOG LINE_LOG SECTIONS [--no-save]

`--no-save` is for a run of fewer sections than the line's first save (gate 3's, tools/gate_engine.sh). The build's last save then falls
where the line has none, and its state is not the line's to compare, so the save is set aside and printed `GATE_SAVE aside`. The section
lines are compared as always.
"""
import sys

TIMINGS = ("regions_ms", "deposit_ms", "ms")
SCHEDULE = ("batches", "peak_store")


def lines(path, head):
    with open(path) as f:
        return [line.rstrip("\n") for line in f if line.startswith(head)]


def fields(line, aside=()):
    """A line's `key=value` words, the keys in `aside` and the timings left out, in order."""
    return [w for w in line.split()[1:] if "=" in w and w.split("=", 1)[0] not in TIMINGS + aside]


def differing(a, b, aside=()):
    fa, fb = dict(w.split("=", 1) for w in fields(a, aside)), dict(w.split("=", 1) for w in fields(b, aside))
    return [k for k in list(fb) + [k for k in fa if k not in fb] if fa.get(k) != fb.get(k)]


def compare(build_log, line_log, sections, no_save=False):
    a = lines(build_log, "STORE_SECTION ")
    b = lines(line_log, "STORE_SECTION ")[:sections]
    eq = sum(1 for x, y in zip(a, b) if fields(x) == fields(y))
    ok = eq == len(a) == len(b) == sections
    out = [f"GATE_REPRO sections={len(a)} line_lines={len(b)} equal={eq} {'EQUAL' if ok else 'DIFFERS'}"]
    first = next((k for k, (x, y) in enumerate(zip(a, b)) if fields(x) != fields(y)), None)
    if first is not None:
        out.append(f"GATE_REPRO first_differing_section={first} fields={','.join(differing(a[first], b[first]))}")
    saves = lines(build_log, "STORE_SAVE ")
    if saves and no_save:
        out.append("GATE_SAVE aside (a run shorter than the line's first save)")
    elif saves:
        x = saves[-1]
        k = dict(w.split("=", 1) for w in x.split()[1:] if "=" in w).get("k")
        match = [y for y in lines(line_log, "STORE_SAVE ") if f" k={k} " in f" {y} "]
        if not match:
            out.append(f"GATE_SAVE k={k} line_save=absent DIFFERS")
            ok = False
        else:
            y = match[0]
            same = fields(x, SCHEDULE) == fields(y, SCHEDULE)
            kx = dict(w.split("=", 1) for w in x.split()[1:] if "=" in w)
            ky = dict(w.split("=", 1) for w in y.split()[1:] if "=" in w)
            beside = " ".join(f"{s}={kx.get(s)} line_{s}={ky.get(s)}" for s in SCHEDULE)
            out.append(f"GATE_SAVE k={k} {'EQUAL' if same else 'DIFFERS'} timings_and_schedule_aside {beside}")
            if not same:
                out.append(f"GATE_SAVE differing_fields={','.join(differing(x, y, SCHEDULE))}")
            ok = ok and same
    return ok, out


def main(argv):
    if len(argv) not in (4, 5) or (len(argv) == 5 and argv[4] != "--no-save"):
        print("usage: python3 tools/reproduction.py BUILD_LOG LINE_LOG SECTIONS [--no-save]")
        return 2
    ok, out = compare(argv[1], argv[2], int(argv[3]), len(argv) == 5)
    print("\n".join(out))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
