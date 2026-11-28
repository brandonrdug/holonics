"""The parts a saved state carries, read from its head lines, and whether one state carries every part another does.

    python3 tools/state_families.py STATE                 # STATE_PARTS state=... parts=a,b,...
    python3 tools/state_families.py --covers PARITY LINE  # GATE_PARITY_FAMILIES covered|missing ...; exit 0 or 1

A part is a family of the material that a declaration word turns on (`crates/engine/src/declaration.rs`, `Declaration::to_text` and
`Loci::new`): the carry circles, the triads, the opening, the junction, the mark, the loudness, the crossing, the closed characters,
the pump, the lane leak, the friction and its gate, the rings' fades, the classes' fade rates and the rings' second fades, and a depth
ring; a level adds `level`, its words (strand, receipt, inside, lane, bank), the coarse field's parts as `level.<part>`, and the
level's founded units (`units`). Only the head lines are read: the declaration, the level's line and its field's declaration, and the
units' line; each long line of material is streamed past.

Why (November 28, the fade's parity): gate 3's parity ran on LINE_W109's state, whose declaration held no fade, so from November 24
the card's fade covector was compared nowhere while the line trained it, and on W134's state it read about 2.5% under the host's.
`tools/gate_engine.sh` asks this tool whether its parity's state carries every part of the state the line trains, and fails where
it does not. An unknown head line is refused, so a new part is named here in the change that adds its word.
"""
import sys

# Each head's words after `reach lanes depth` (words 9, 10, 11), in order; `hnn-field-v13` has no depth word.
HEADS = {
    "hnn-field-v13": 11,
    "hnn-field-v14": 12,
    "hnn-field-v14e": 13,
    "hnn-field-v14f": 14,
    "hnn-field-v14g": 15,
    "hnn-field-v14j": 16,
    "hnn-field-v14m": 17,
    "hnn-field-v14l": 18,
    "hnn-field-v14x": 19,
    "hnn-field-v14c": 20,
    "hnn-field-v14p": 21,
    "hnn-field-v14q": 22,
    "hnn-field-v14r": 23,
    "hnn-field-v14s": 24,
}
# Word index of each part on every head long enough to write it (a shorter head line writes the part off, except the head's own last
# word, which `Declaration::to_text` writes as one).
WORDS = [(11, "depth"), (12, "carry"), (13, "triads"), (14, "opening"), (15, "junction"), (16, "mark"), (17, "loud"), (18, "crossing"),
         (19, "closed"), (20, "pump"), (21, "lane_leak")]


def declaration_parts(line):
    """The parts one field's head line declares, or ValueError for a line that is no known head."""
    words = line.split()
    if not words or words[0] not in HEADS or len(words) != HEADS[words[0]]:
        raise ValueError(f"not a known field head line: {line[:80]!r}")
    parts = set()
    for at, name in WORDS:
        if at < len(words) and words[at] != "0":
            parts.add(name)
    if len(words) > 22:
        friction = words[22]
        if friction in ("1", "2"):
            parts.add("friction")
        if friction == "2":
            parts.add("friction_gate")
    if len(words) > 23:
        fade = int(words[23])
        for bit, name in ((1, "fade"), (2, "fade_rate"), (4, "twin")):
            if fade & bit:
                parts.add(name)
    return parts


def state_parts(path):
    """Every part a saved state carries: its field's, its level's and the level field's as `level.<part>`, and its units'."""
    parts = set()
    with open(path, "r", encoding="ascii", errors="replace") as f:
        lines = iter(f)
        head = None
        for raw in lines:
            if raw.startswith("hnn-field-v"):
                head = raw
                break
            if raw.startswith("-") or raw[:1].isdigit():
                break
        if head is None:
            raise ValueError(f"{path}: no field head line")
        parts |= declaration_parts(head)
        next(lines, None)  # the field's material
        for raw in lines:
            if raw.startswith("level "):
                words = raw.split()
                parts.add("level")
                for w in words[3:]:
                    if w in ("strand", "receipt", "inside", "lane", "bank"):
                        parts.add(f"level.{w}")
                coarse = next(lines, "")
                parts |= {f"level.{p}" for p in declaration_parts(coarse)}
                next(lines, None)  # the level field's material
            elif raw.startswith("units "):
                parts.add("units")
            elif raw.startswith("hnn-field-v"):
                raise ValueError(f"{path}: a field head line where a level's or units' line was read")
    return parts


def main(argv):
    if len(argv) == 2 and not argv[1].startswith("--"):
        print(f"STATE_PARTS state={argv[1]} parts={','.join(sorted(state_parts(argv[1]))) or '-'}")
        return 0
    if len(argv) == 4 and argv[1] == "--covers":
        parity, line = state_parts(argv[2]), state_parts(argv[3])
        missing = sorted(line - parity)
        print(f"STATE_PARTS parity={','.join(sorted(parity)) or '-'}")
        print(f"STATE_PARTS line={','.join(sorted(line)) or '-'}")
        print(f"GATE_PARITY_FAMILIES {'covered' if not missing else 'missing ' + ','.join(missing)}")
        return 0 if not missing else 1
    print("usage: state_families.py STATE | state_families.py --covers PARITY LINE", file=sys.stderr)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except (OSError, ValueError) as e:
        print(f"GATE_PARITY_FAMILIES refused {e}")
        sys.exit(1)
