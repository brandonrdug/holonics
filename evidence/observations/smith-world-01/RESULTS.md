# Smith world 01 — the literal impedance boundary stands separately

Date: 2026-07-15

Law: `A2` · quotient face is not construction identity · `FORMULA §§LII–LIII, LVI`

Grade: **EXACT ONE-PORT SMITH-QUOTIENT VALIDATION WORLD BUILT · FIVE ANALYTIC PORT CASES EXACTLY
EVALUATED / MEASURED AT THIS VALIDATION GRAIN · DISCRETE REFERENCE-PLANE PHASE-CONVENTION INVERSE
EXACT · LITERAL TRANSMISSION-LINE WORLD AND PROJECTIVE-PERIPLUS/IMPEDANCE BRIDGE OPEN**

## Construction

`life boundary smith-validate` accepts exact rational complex loads, one positive real reference
impedance, and a signed number of reflection-phase quarter turns. It evaluates

```text
Gamma = (Z - Z0) / (Z + Z0)
Z = Z0 * (1 + Gamma) / (1 - Gamma)
```

without floating point. Positive quarter turn is explicitly the receiver convention
`Gamma -> i*Gamma`; applying the negative turn must restore the port face exactly. Rational
overflow or a zero Möbius denominator is a typed refusal.

This is a separate world instrument. It does not alter Soma, consume a `RegionalForm`, or assert
that the dyadic circuit periplus already carries physical impedance.

## Results

All five analytic faces and all five inverse impedance/reference-plane passages are exact.

| Port | `Gamma` at port | `|Gamma|^2` | Passive-disk face |
|---|---|---:|---|
| matched `Z=1` | `0` | `0` | yes |
| short `Z=0` | `-1` | `1` | yes, boundary |
| double resistance `Z=2` | `1/3` | `1/9` | yes |
| reactive `Z=1+i` | `1/5 + (2/5)i` | `1/5` | yes |
| active negative resistance `Z=-1/2` | `-3` | `9` | no |

The active case is important: the instrument does not force every face into the passive unit disk.
The disk is a property of the declared passive boundary, not a universal clipping rule.

Exact receipt:

```text
results/smith.json
SHA-256 ff00c3f9f037d49470f3b1a564495c61bbfed5b5998c716ead6b844153d6422d
```

## Verdict

The conventional Smith quotient and an exact discrete reference-plane phase convention now have a
separately typed rational Rust witness. No frequency-bearing line or propagation law has yet been
built. The causal atlas remains properly named
`oriented_projective_response`. A future bridge must define what incident/returned quantities in
a concrete circuit or wave world constitute `Z` and `Z0`, then reproduce this receipt before the
projective atlas may be called a Smith atlas.

```text
CURRENT  exact rational port world ⊕ Smith receiver ⊕ one-port/reference-plane grain
HELD     Z ⊕ positive real Z0 ⊕ analytic Möbius map ⊕ complete inverse
MEETING  matched, short, resistive, reactive, and active loads under exact quarter-turn phase
TEST     known Gamma faces ⊕ inverse impedance ⊕ inverse re-reference ⊕ passive boundary
DEED     FOUND — literal impedance was absent from the existing dyadic periplus
CARRY    a separate exact Smith-world receipt; no reclassification of the projective atlas
GRADE    BUILT / MEASURED; literal transmission-line world and periplus-to-impedance bridge OPEN
```

Command:

```text
cargo test -p life smith::tests
cargo run -p life -- boundary smith-validate observations/smith-world-01/plan.json
```
