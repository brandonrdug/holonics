#!/usr/bin/env python3
"""The October 5 states' material identity, recomputed from the current blanked written form.

`Constitution::material_identity` is `text_residue` of the derived `Debug` of the blanked opening
(`hnn/constitution.rs`): the bytes read as one base-256 integer modulo `p = 2^127 - 1`. The form was
written once, on the refusal, by a diagnostic build of 9914bc5a (reverted; never committed):
`continued` wrote `format!("{material:?}")` of the blanked opening to a file before refusing lane B's
founded state. This script reads that form, its residue, and the residue with the four zero scales
that `[Rat; 4]` wrote before #367 put back on each ring that loads no resonator.

usage: identity_residue.py <blanked form>
"""
import sys

P = (1 << 127) - 1


def residue(data: bytes) -> int:
    r = 0
    for byte in data:
        r = (r * 256 + byte) % P
    return r


form = open(sys.argv[1], "rb").read()
zero = b"Ratio { numer: 0, denom: 1 }"
empty = b"resonator_scales: []"
print(f"the current form: {len(form)} bytes, residue {residue(form)}")
print(f"rings writing `resonator_scales: []`: {form.count(empty)}")
before = form.replace(empty, b"resonator_scales: [" + b", ".join([zero] * 4) + b"]")
print(f"with the four zero scales back: {len(before)} bytes, residue {residue(before)}")
