# Smith line world 01 — the quotient crosses a literal line

Date: 2026-07-15

Law: `A2` · quotient face is not construction identity · `FORMULA §LVI`

Grade: **EXACT ONE-PORT TRANSMISSION-LINE WORLD BUILT · FREQUENCY/LENGTH/VELOCITY PROPAGATION
MEASURED AT DISCRETE ELECTRICAL LENGTH · INCIDENT/RETURNED WAVE RATIOS AND BOTH IMPEDANCE
INVERSES EXACT · REVOLVED PORT ORBITS BUILT · GENERAL PHASE / MULTIPORT / PROJECTIVE-PERIPLUS
BRIDGE OPEN**

## Construction

`life boundary smith-line-validate` receives exact rational load and reference impedances,
frequency, line length, phase velocity, one-way voltage attenuation, and a nonzero complex incident
wave. With the declared `exp(+i*w*t)` convention, the one-way phase in quarter turns is

```text
n = -4*f*l/v.
```

This first exact species accepts only integral `n`; a nonintegral electrical length is a typed
refusal, not a floating approximation. Its one-way factor is

```text
P = attenuation * i^n.
```

The world carries the actual wave faces

```text
A_load = P * A_reference
B_load = Gamma_load * A_load
B_reference = P * B_load
Gamma_reference = B_reference / A_reference = P^2 * Gamma_load.
```

It then recovers `Gamma_load`, the original load impedance, and the reference-plane input
impedance through the exact Smith inverse. Frequency, propagation, and incident/returned waves are
therefore construction data rather than labels attached to a quotient.

## Measured lines

All six lines preserve both wave ratios and all load/input inverses exactly. Every expected
analytic face is exact.

| Line | one-way turns | `Gamma_load` | `Gamma_reference` | `Z_input` | passive at load/reference |
|---|---:|---|---|---|---|
| matched, zero length | 0 | `0` | `0` | `1` | yes / yes |
| quarter-wave `Z_L=2` | -1 | `1/3` | `-1/3` | `1/2` | yes / yes |
| quarter-wave `Z_L=1+i` | -1 | `1/5 + 2i/5` | `-1/5 - 2i/5` | `1/2 - i/2` | yes / yes |
| attenuated quarter-wave `Z_L=2`, `a=1/2` | -1 | `1/3` | `-1/12` | `11/13` | yes / yes |
| short, zero length | 0 | `-1` | `-1` | `0` | yes / yes |
| active `Z_L=-1/2`, zero length | 0 | `-3` | `-3` | `-1/2` | no / no |

The attenuated line verifies that the reference-plane reflection is changed by the square of the
one-way propagation factor. The active case remains outside the passive disk; the apparatus does
not clip it into the receiver's passive boundary.

## Revolution

For each load and reference-plane quotient `Gamma=x+iy`, the receipt revolves the port about the
incident-current real axis as the exact orbit

```text
(x, y, 0) -> (x, 0, y) -> (x, -y, 0) -> (x, 0, -y).
```

It retains `x` and `y^2` exactly. Revolving the complete passive disk gives the receiver domain
`x^2+y^2+z^2 <= 1`; no mesh, morphology, metric, or body template enters Soma. The reactive line
has exact orbit radius squared `4/25` at both planes while the quarter-wave passage reverses its
oriented quotient.

## Honest boundary

This closes the literal one-port line missing from the earlier quotient-only validation at this
discrete electrical-length grain. General phase needs a separately declared exact/controlled
representation of trigonometric or exponential propagation; it is not approximated here. Open
circuit infinity, multiport scattering, dispersion, nonlinear media, time-domain wave packets,
and coupling from `RegionalForm`/periplus transport to physical `Z`, `Z0`, and waves remain open
world constructions.

Exact receipt:

```text
results/line.json
  38,908 octets
  SHA-256 cb231898001afd6c34fb95f97bf8bdb3809e9eddea8df2657d225f62db1926c6
```

```text
CURRENT  exact one-port line ⊕ transmission-line receiver ⊕ discrete electrical-length grain
HELD     Z_L ⊕ Z0 ⊕ f ⊕ l ⊕ v ⊕ attenuation ⊕ nonzero incident voltage wave
MEETING  incident and returned waves cross the line and re-form Gamma at the reference plane
TEST     analytic loads ⊕ exact wave ratios ⊕ Smith inverses ⊕ attenuation ⊕ passive/active foil
DEED     FOUND — the prior quotient had no physical line or wave propagation
CARRY    exact line receipt ⊕ revolved port orbits; generalized projective bridge remains separate
GRADE    BUILT / MEASURED; general phase, multiport, and periplus-to-impedance bridge OPEN
```

Command:

```text
cargo test -p life smith::tests
cargo run -p life -- boundary smith-line-validate observations/smith-line-world-01/plan.json
```
