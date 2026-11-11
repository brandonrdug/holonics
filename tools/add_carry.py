#!/usr/bin/env python3 -I
"""add_carry.py STATE OUT: the state with the carry across ticks added at zero (theory's ruling R5; holonics::hnn::tower::field::Field::with_carry).

The head line becomes hnn-field-v14k with its carry word, the material gains the third chart `G` (f x D entries, founded at zero after every
family: ruling R5 amended, theory's 00:22) and the learner's two moment lines gain f D zero entries; a trailing `parts` line gains the sixteenth
part's octave (g_chart opens at the old rate: 0). With G at zero every face of the state is unchanged bit for bit. The state read stays untouched (OUT is created new).
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from part_rates import PARTS, load, parts_line  # noqa: E402


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    path, out = sys.argv[1:3]
    lines, d, rate, theta = load(path)
    assert not d.get("carry"), "a state that already carries"
    head = lines[0].split(" ")
    assert head[4] == "-", "a state holding a step (the step line is material-length)"
    f = d["contacts"] * d["width"]
    zeros = " ".join(["0"] * f)
    decl = lines[1].split(" ")
    assert decl[0] == "hnn-field-v14" and len(decl) == 12
    lines[1] = " ".join(["hnn-field-v14k"] + decl[1:] + ["1"])
    lines[2] = lines[2] + " " + zeros
    lines[3] = lines[3] + " " + zeros
    lines[4] = lines[4] + " " + zeros
    kept = [l for l in lines if not l.startswith("parts ")]
    held = parts_line(lines)
    if held is not None:
        kept.append("parts " + " ".join(str(x) for x in [held[0]] + held[1]))
    while kept and kept[-1] == "":
        kept.pop()
    with open(out, "x") as fh:
        fh.write("\n".join(kept) + "\n")
    print(f"ADD_CARRY entries={f} material={len(theta)} -> {len(theta) + f}")


main()
