# FT0: the zeros are Foster tanks, and the paired Landau form carries the remainder

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT0 under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md),
directed by Brandon on 2026-09-03: *"I am directing that campaign."*  
**Owner:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/FosterTanks.lean`, registered in the
root umbrella after `HeatFlowStackedSeam`.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] The tank data. `capacitance = ½`; `inductance ρ′ = −2/ρ′²`; the tank of `ρ′` at the
centred point `w` is the impedance `2w/(w² − ρ′²)`.

[proved-derived; formal-checked] The tank algebra, unconditional:

- `pair_eq_tank`: for `z` distinct from `ρ` and from `1 − ρ`,
  `1/(z − ρ) + 1/(z − (1 − ρ)) = 2(z − ½)/((z − ½)² − (ρ − ½)²)`. The two members of a reflection
  pair sum to one tank.
- `tank_eq_parallel_LC`: for `ρ′ ≠ 0`, the tank is `wL/(w²LC + 1)` with the seam's capacitance and
  the zero's inductance, the impedance of a parallel LC circuit.
- `inductance_pos_real_iff`: the inductance is a positive real iff `ρ′` is purely imaginary and
  nonzero. **Positivity iff on the seam.**
- `seam_tank_resonance`: for `ρ′ = iγ`, `γ > 0`, the inductance is `2/γ²` and `1/√(LC) = γ`. The
  resonance of a seam tank is the height of its zero, the `(LC)^{−1/2}` form.

[proved-derived; formal-checked] `flux_eq_tankSum`: on a finite comb closed under `ρ ↦ 1 − ρ` with
matched multiplicities, the Coulomb flux `Σ m_ρ/(z − ρ)` equals the tank sum
`Σ m_ρ (z − ½)/((z − ½)² − (ρ − ½)²)`, one tank per pair counted from both members.

[proved-derived; formal-checked] `SymmetricZeroFactorization r`: a zero factorization of `ξ` on
the disc of radius `r` about `½` whose comb is closed under the reflection with matched
multiplicities. `exists_symmetricZeroFactorization_count` constructs it as
`ZeroFactorizationExists` does, at the seam's centre, where `one_sub_mem_ball_half_iff` and
`divisor_riemannXi_one_sub_ball` (the open-disc form of `ZeroComb`'s symmetry) make the reflection
preserve the disc and the divisor; its count is the divisor mass of the closed half disc.

[proved-derived; formal-checked] **`exists_paired_foster_form`.** On the disc of radius `r` about
`½`, for every `z` in the `r/8` disc with `ξ z ≠ 0`,

```text
‖ ξ′/ξ(z) − Σ_ρ m_ρ (z − ½)/((z − ½)² − (ρ − ½)²) ‖ ≤ 16 (M + N log 2) / r,
```

with `M = xiBudget C ½ r` from the order-one envelope and `N` bounded by Jensen's count
`log(jensenCeiling / ‖ξ(½)‖) / log(3/2)`, exactly the Landau owners' bound transported to the
tank sum by the paired flux identity. The sum runs over the symmetric comb of the half disc.

`#print axioms` on every theorem returns `propext`, `Classical.choice`, `Quot.sound`. The owner
builds alone (8,729 jobs) and inside the root umbrella.

## The carried hypothesis

[definition] The existence theorems carry `riemannXi (½) ≠ 0` explicitly. It is the value at the
centre, `ξ(½) ≈ 0.4971`, positive; the standing Landau owners normalize at a nonvanishing centre,
Mathlib carries no value of `ζ` at `½`, and the disc must be centred at `½` for the reflection to
preserve it. `RH/OffLineJensen.lean` already carries the same hypothesis under the same name.
Nothing in this owner assumes anything about any zero. Its discharge by an enclosure of the theta
tail is the first item of FT1. Measured 2026-09-03 by
`grep -rn "riemannXi (1 / 2)" ElementaryHolonics/RH/*.lean | grep "≠ 0"`: three occurrences, all
hypotheses, none a theorem.

## Pass FT0

The contract's pass conditions: the theorem builds on `exists_zeroFactorization_riemannXi_jensen`'s
ingredients (`finsum_divisor_le`, `norm_riemannXi_le_of_growth`, `xiBudget`, `norm_logDeriv_sub_flux_le`)
without a new axiom; the pairing uses `ZeroComb`'s reflection symmetry of the divisor through
`meromorphicOrderAt_riemannXi_one_sub`; the equivalence is proved. **FT0 passes** at its declared
scope, with the carried hypothesis named above. Falsifier unchanged: a disc and a point on which
the paired sum plus the remainder bound fails against the directly computed `ξ′/ξ`.

## Boundaries

- No claim of movement on the Riemann Hypothesis. The form is finite, on one disc, with a
  remainder.
- The count `N` is bounded by Jensen; FT1 owes the `R log R` count and the exponent of
  convergence, and the centre value.
- The impedance reading is exact at the algebra of the tank; no physical transport is claimed.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.FosterTanks
timeout 180s lake build ElementaryHolonics
```
