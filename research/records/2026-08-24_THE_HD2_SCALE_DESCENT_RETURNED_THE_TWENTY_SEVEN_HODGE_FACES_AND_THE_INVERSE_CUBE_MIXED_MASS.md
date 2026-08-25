# HD2 returned the twenty-seven Hodge faces and the inverse-cube mixed mass

**Date:** 2026-08-24  
**Scope:** HD2 exterior Lean theorem station; this record schedules no Rust/GPU deed and does not
move `CONSTRUCTION_STATE.md`.  
**Truth status:** each material claim is graded locally under `canon/EPISTEMIC_GRADES.md`.

## 1. Development card

[definition] The source owners are the HD0 ordered higher-difference/product ledger, the HD1
proof-bearing quadratic annihilator, the local reciprocal identity for `q(k)=|k|^2`, the genuine
three-axis successor stencil, and the existing dyadic annular lower/bound aperture. The port types
are an addressed generator word, a successor frequency, a strict predecessor order, numerator and
reciprocal sections, a receiver norm, and the retained local lower-scale aperture.

[definition] The event is one active denominator-difference occurrence in the pruned recurrence.
Its predecessor identity is its exact lower-order reciprocal word and shifted successor point. Its
local constitutive law is the shifted Leibniz recurrence for `q * q^-1 = 1`, with the inverse required
only on the returned successor window. The receiver asks for the norm of the actual Hodge
multiplier's `(2,2,2)` mixed difference and then for its dyadic radial scale.

[definition] The first falsifier is any retained face whose reciprocal order is not strictly lower
than the parent recurrence. The second is any nonzero numerator allocation of total order at least
three. The third is dyadic scaling slower than `R^-6` after all numerator weights are restored. The
return below closes all three in the declared aperture.

## 2. The well-founded scale owner

[proved-derived; formal-checked] `Foundation/HigherDifferenceScaleDescent.lean` defines
`StrictOrderFace`. Each face retains its `Fin order` predecessor, shifted successor, occurrence
multiplicity, coefficient, and lower-order section. `StrictOrderFace.predecessor_lt` proves the
address is strictly smaller than the parent order. `norm_strictOrderReturn_le_envelope` derives the
complete weighted norm envelope from the same addressed population; it does not replace the
population by an untyped scalar.

[proved-derived; formal-checked] `difference_shift_of_interchange` proves the comparison square
which transports a difference through a shifted receiver under the existing exact interchange
receipt. Thus the lower-order section is evaluated at the actual successor chart rather than at an
unshifted proxy.

## 3. The reciprocal chain closes

[proved-derived; formal-checked]
`NavierStokesThreeAxisHodgeScaleDescent.lean` constructs the grouped active returns and controlled
successor apertures for the strict chain

```text
11 -> 111 -> 112 -> 122 -> 222.
```

The exact envelopes are

```text
E111 = 3 A E11 / L
E112 = (2 A E111 + 2 A E12 + 2 E11) / L
E122 = (A E22 + 4 A E112 + 4 E12) / L
E222 = (6 A E122 + 6 E22) / L,
```

where `A = 2 * bound + 1` and `L = lower`. Every recursive theorem derives its shifted lower-order
faces from `ThreeAxisStencilControlled`; no order-`112`, `122`, or `222` facewise norm is supplied as
an independent premise.

[proved-derived; formal-checked] The `222` theorem groups the nine HD1 active occurrences into six
first-denominator faces of reciprocal type `122` and three same-axis-second faces of reciprocal type
`22`, with their exact multiplicities. The local denominator lower bound divides the grouped return
and closes the top recurrence.

## 4. The twenty-seven product faces collapse to ten

[proved-derived; formal-checked]
`NavierStokesThreeAxisHodgeProductMass.lean` applies the second-order shifted Leibniz law successively
on three commuting coordinate axes. `threeAxisMixedForwardDifference_two_two_two_mul_eq_allocationReturn`
identifies the result with the twenty-seven allocation addresses `(a,b,c) in {0,1,2}^3`, retaining
the binomial occurrence weight on every face. `threeAxisHodgeAllocation_face_card` proves the face
count is exactly twenty-seven.

[proved-derived; formal-checked]
`hodgeJacobianRatioNumerator_threeDifferences_eq_zero` proves that every three addressed differences
annihilate the quadratic Hodge numerator. The general allocation theorem therefore kills every face
with `a+b+c >= 3`. The three staged slices retain exactly six, three, and one nonzero numerator
allocations. Their derived envelopes are

```text
c = 0:  3 B^2 E222 + 4 A E122 + 4 E22 + 8 E112
c = 1:                2 A E122           + 16 E112
c = 2:                              2 E22,
```

with `B = bound`. Summing them gives the exact full mixed envelope

```text
3 B^2 E222 + 6 A E122 + 6 E22 + 24 E112.
```

[proved-derived; formal-checked]
`norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_two_two_two_le` applies that
envelope to the actual Hodge Jacobian multiplier entry. Its only analytic aperture premise is one
`3 x 3 x 3` `ThreeAxisStencilControlled` population. The theorem assumes no individual bound for
any of the ten surviving faces.

## 5. Inverse cube is a checked scale statement

[proved-derived; formal-checked]
`NavierStokesThreeAxisHodgeDyadicMass.lean` evaluates the recursive envelopes on the existing dyadic
annular aperture for every scale `s >= 3`. It proves the explicit bounds

```text
E111 <=       3,000,000 / R^5
E112 <=     600,000,000 / R^6
E122 <= 150,000,000,000 / R^7
E222 <=  50,000,000,000,000 / R^8,
```

where `R = 2^s`.

[proved-derived; formal-checked]
`hodgeJacobianEntryThreeAxisFullMixedEnvelope_dyadic_inverseCube_le` combines those four returns with
`B^2 <= 25 R^2`, `A <= 11 R`, and the existing `E22 <= 420,000,000 / R^6` theorem to prove

```text
fullMixedHodgeEnvelope(s) <= 4,000,000,000,000,000 / R^6.
```

Because the denominator coordinate is `q=|k|^2`, the radial power `R^-6` is the inverse-cube
scale `q^-3`. This is a theorem about the complete mixed allocation mass, not an asymptotic label or
a separately assumed face estimate.

## 6. Validation and exact residual

[established-bounded; formal-checked] Direct elaboration of
`NavierStokesThreeAxisHodgeProductMass.lean` returned in 4.990 seconds. Direct elaboration of
`NavierStokesThreeAxisHodgeDyadicMass.lean` returned in 6.227 seconds. The focused dyadic-mass build
returned 3,273 jobs in 6.936 seconds. The aggregate `lake build ElementaryHolonics` receiver returned
4,142 jobs in 5.150 seconds. Printed axiom receipts for every promoted HD2 theorem contain no
`sorryAx`.

[open] The remaining Navier--Stokes kernel receiver is not another reciprocal face estimate. It is
the all-eight-subset physical receiver: empty set, three single axes, three axis pairs, and all three
axes, joined to a one-circle near/far Haar partition around each character singularity. The top
mixed difference cannot be divided globally by the product of the three character denominators.
The next theorem must retain the lower-dimensional boundary faces and return one uniform physical
Hodge-kernel bound for every dyadic scale at least three.

[interpretation] The generic strict-order owner can now receive other degree filtrations: exterior
nilpotence for Hodge, covariant commutator order for Yang--Mills, prime-local reciprocal ledgers for
RH, and valuation/local-height order for BSD. Those lines are not promoted by the fluid instance.
Their first theorem is to construct the corresponding typed annihilator and positive receiver; a
nondecreasing retained face or a nontrivial null fibre is a falsifier.
