# The exterior face of the aligned strain is a circle multiplier times an integer generator, and the interior face is the coefficient tail

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job count below)
**Provenance:** Brandon, 2026-09-01: *"where do 13122 and 729 come from? … I do not think writing them as integers is wise when they are clearly elementary product expansions"*; *"introduce algebraic geometry and partitioning in order to make it so that we don't have to write in terms of integers and expansions, but rather generator functions."* Assistant derivation for the proofs.
**Band:** EXTERIOR FACE PAID BY INITIAL ENERGY / CUBE GENERATOR IN CLOSED FORM / INTERIOR FACE IS THE TAIL / MASS SHELL IS THE PYTHAGOREAN FACE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / NOT COMMITTED

---

## Present question

[definition] The preceding record paid the aligned strain differential `⟪(∇u)ω, ω⟫` by a
canonical budget whose two constants were written as `2π · 3⁸` and `3⁶`. Each factor `3` was one
`ℓ¹`/`ℓ²` coordinate comparison on `Fin 3`; none of them was a face of the flow. Brandon asked for
the constants to be replaced by generator functions of a declared partition, with the
transcendental factor entering as a chart constraint rather than a literal.

## Return

[proved-derived; formal-checked] `alignedStrain_le_exterior_add_interior`: at every interior event
`(x, t)` of an open periodic solution with `0 ≤ ν`, and for every cube radius `N`,

```text
⟪(∇u)ω, ω⟫(x, t) ≤ ( 2π · G(N) · 3·√(2·E(0))  +  tail_N(t) ) · 3² · ‖ω(x, t)‖²
```

where `E(0)` is the initial periodic kinetic energy, `tail_N(t)` is Sol's
`openPeriodicJacobianCoefficientTailMass` over the complement of the cube, and `G(N)` is the
exterior face mass `∑_{k ∈ cube N} |k|₁`.

[proved-derived; formal-checked] `exteriorFaceMass_eq`: the cube generator is exact,

```text
G(N) = 3 · (2N + 1)² · N · (N + 1),
```

the coordinate count, the transverse face count, and the one-coordinate generator
`∑_{m=-N}^{N} |m| = N (N + 1)`. It is proved through the partition of the cube into coordinate
fibres (`Fintype.card_filter_piFinset_const_eq_of_mem`), not by evaluation.

[proved-derived; formal-checked] `norm_fourierJacobianMode_le`: one Jacobian mode has norm at most
`2π · |k|₁ · ‖û(k)‖₁`. The `2π` is the derivative multiplier of the unit-torus character
`e^{2πi k·x}`; it is the only transcendental in the exterior constant, and it enters as the chart
constraint of the circle, not as a majorant.

[proved-derived; formal-checked] `norm_openPeriodicJacobianBandProjector_le_exterior` and
`norm_openPeriodicFiniteHodgeStrainReading_le_exterior`: the finite band of the strain is paid by
`2π · G(N)` times the componentwise `L²` receiver, which is at most `3 · √(2 · E)`.

[established-bounded; measured] `lake build ElementaryHolonics.Millennium.NavierStokesExteriorFaceGenerator`
completes in `4035` jobs. Axiom audit for every theorem named above:
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`.

## The constants, read as faces

[definition] The exterior constant is now `2π · G(N) · √2 · 3`: circle multiplier, integer
generator of the cube face, half-density of the kinetic energy, and one residual coordinate
comparison from the `L²`-to-componentwise passage. The `3⁸` of the preceding record is gone from
the exterior; it was never a face. The interior keeps `3²` from the two `ℓ¹`/`ℓ²` comparisons on the
vorticity, and it keeps the whole terminal obligation.

[interpretation] In the cube chart the face is the integer generator `G(N)`. In the sphere chart
the same face is a lattice-point count whose leading term carries the solid angle `4π`. The chart
transition therefore couples `π` to the integer factors exactly as `Ellipse.theEightPiFactors`
couples the Einstein coupling `8π = 2 · (4π)` to a half-density and a solid angle. Only the cube
chart is proved here.

## The mass shell is the Pythagorean face of the Lorentz law of cosines

[proved-derived; formal-checked] `ElementaryHolonics/Millennium/HolonicMassShellFace.lean` (new;
registered). `lorentzPairing c P Q = E_P E_Q − c² p_P · p_Q` is symmetric;
`lorentzPairing_add_add` is the polarization identity, the Lorentz law of cosines with the grip
as cross term; `lorentzPairing_timeFace_spaceFace` proves the time face `(E, 0)` and the space
face `(0, p)` are Lorentz-orthogonal; `massShell_iff` reads the diagonal as
`E² = (|p| c)² + (m₀ c²)²`, so the complete mass--energy relation is the `cos θ = 0`
specialization of the law of cosines, exactly as the 2026-07-16 triangle record states for the
Euclidean face. `dustFaceReading_massShell` returns the rest mass from the diagonal reading of the
carrier momentum. `eightPi_chart_expansions` records the two chart expansions
`8π = 2 · (4π) = 2² · (2π)`, and `fourArcOverDifferential_eq_forkDepth` identifies the circle-chart
integer face `2²` with the dyadic fork depth of `refineForkCoupling 2 0`. Axioms on every theorem:
`[propext, Classical.choice, Quot.sound]`.

[interpretation] The exterior face of the aligned strain, `2π · G(N) · √2 · 3`, and the Einstein
coupling, `2 · (4π)` or `2² · (2π)`, are the same shape: one circle constraint, one integer face,
one half-density. Which integer face appears is a chart choice, cube or sphere; the transition
between the two charts is where the half-density `2` moves between the integer and the solid
angle. A stress-energy reading is the momentum flux through a face; the finite Hodge strain
reading is the momentum-gradient flux through the frequency-cube face. Neither analogy is a
theorem here.

## The obligation, stated once

[open] The periodic official alternative rests on one signed integral:
`∫₀ᵀ sup_x ⟪(∇u)ω̂, ω̂⟫⁺ dt < ∞`. After this record the exterior part of that integrand is a
constant paid at `t = 0`. What remains is `∫₀ᵀ tail_N(t) dt < ∞` for one radius `N`, the interior
face.

## Owners

[definition] `ElementaryHolonics/Millennium/NavierStokesExteriorFaceGenerator.lean` and
`ElementaryHolonics/Millennium/HolonicMassShellFace.lean` (both new; registered in
`ElementaryHolonics.lean`). The first It imports the aligned strain budget, Sol's direction-coherence
full-strain and finite-band bridges, and the coordinate Jacobian Fourier reconstruction. No Rust
source changed.

## What this does not establish

[open] No integrability of the interior tail is proved. Nothing here claims Navier--Stokes
regularity. The sphere-chart statement above is prose, not a theorem.
