# A simple zero of H_t persists as a unique simple zero

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/SimpleZeroPersists.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow at the entire face: a simple zero has analytic order one through the difference quotient, so the winding around a small square is 2πi; by local constancy of the count the winding of H_t is 2πi for t near t₀, and a winding of 2πi is exactly one zero of multiplicity one, read off the corpus factorization. Assistant derivation for the proofs.
**Band:** F z₀ = 0 ∧ F′ z₀ ≠ 0 ⟺ analyticOrderAt F z₀ = 1 / u ∈ Z.zeros ⟺ F u = 0 IN THE HALF-BALL / ∮ F′/F = 2πi Σ_{Z.zeros ∩ openRect} mult / UNIQUE SIMPLE INTERIOR ZERO ⇒ WINDING 2πi / WINDING 2πi ⇒ ∃! ZERO IN openRect, SIMPLE / H_{t₀} SIMPLE ZERO AT z₀ ⇒ ∃ η > 0, ∀ᶠ t, ∃! ZERO OF H_t IN THE η-SQUARE, SIMPLE / SAME FOR Ξ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.SimpleZeroPersists` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/SimpleZeroPersists.lean`, importing
`RH.RectangleCountStable` and Mathlib's difference quotient. Receiver: the zero set of `H_t`
inside a small square about a simple zero of `H_{t₀}`.

## Theorems

[proved-derived] `analyticOrderAt_eq_one`, `deriv_ne_zero_of_analyticOrderAt_eq_one`: a zero is
simple iff its analytic order is one, via `dslope`.

[proved-derived] `mem_zeros_iff`: in the half-ball of a corpus factorization, its zero set is
exactly the zero set of `F`.

[proved-derived] `exists_factorization_winding`: the winding of an entire `F` nonvanishing on the
boundary is `2πi Σ_{ρ ∈ Z.zeros ∩ openRect} mult ρ` for the factorization about the corner.

[proved-derived] `winding_eq_of_unique`: if the only zero of `F` in the closed rectangle is a
simple interior zero, the winding is `2πi`.

[proved-derived] `unique_zero_of_winding`: a winding of `2πi` gives exactly one zero in the open
rectangle, and it is simple; a sum of positive naturals equal to one has one term.

[proved-derived] `simple_zero_persists`, `simple_zero_persists_riemannXi`: for a simple zero `z₀`
of `H_{t₀}` there is `η > 0` such that for all `t` near `t₀`, `H_t` has exactly one zero in the
open square of half-side `η` about `z₀`, and that zero is simple.

## Position on the route

[established-bounded] This is the existence-and-uniqueness half of the implicit function theorem
for the zero curve through a simple pair, obtained from the argument principle instead of joint
differentiability. Together with `zero_curve_velocity` it says: a simple pair of `H_t` is followed
by a well-defined nearby simple zero for nearby `t`, and if that selection is `C¹` its velocity
is `H″/H′`. The continuity and differentiability of the selection are the next owner.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the selected zero as a function of `t`, its continuity by the same
count argument on smaller squares, and its differentiability with velocity `H″/H′`.
