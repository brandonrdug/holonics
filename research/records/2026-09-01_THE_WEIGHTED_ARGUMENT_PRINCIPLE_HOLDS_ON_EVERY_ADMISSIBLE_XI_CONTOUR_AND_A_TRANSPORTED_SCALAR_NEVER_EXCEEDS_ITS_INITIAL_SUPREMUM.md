# The weighted argument principle holds on every admissible xi contour, and a transported scalar never exceeds its initial supremum

**Date:** 2026-09-01
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, printed axiom audits below); `measured` (`lake` job counts below); `source-inspected` (Claude Code session logs and Codex rollouts for the Scratch recovery)
**Provenance:** Brandon, 2026-09-01: *"Your two recommended 'bounded deeds' that relate to Weil and NS respectively are what I would like you to act on in addition to the request to fetch more context that I supplied above."* Assistant derivation for the proofs.
**Band:** RH ARGUMENT PRINCIPLE PROVED / NS MAXIMUM PRINCIPLE PROVED / ONE CERTIFICATE FIELD REMOVED / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / NOT COMMITTED

---

## Present question

[definition] The 2026-08-29 finish-line audit named, for each Millennium receiver, the fields of
an executable certificate whose construction would count as progress and whose renaming would
count as churn. This record returns one field on the Riemann line and the analytic core of the
two-dimensional calibration on the Navier--Stokes line. It also recovers the context Brandon asked
for: where the Riemann positivity object lives and what happened to the Lean `Scratch` directory.

## Return: the weighted argument principle

[proved-derived; formal-checked] `ElementaryHolonics/RH/WeightedArgumentPrinciple.lean` proves
`hasWeightedArgumentPrinciple`: for every Weil test `T` and every positively oriented circle
`C(c, R)` with `0 < R` meeting no zero of the entire Riemann xi function,

```text
(2πi)⁻¹ ∮_{C(c,R)} Φ(z) ξ'(z)/ξ(z) dz = Σ_{ξ(ρ)=0, |ρ-c| ≤ R} m_ρ Φ(ρ),
```

with the right-hand side literally `ExplicitFormulaReceiver.truncatedZeroReceiver T c R`, the
divisor of xi on the closed disc retained with multiplicity. The returned structure is exactly the
first port `HasWeightedArgumentPrinciple T c R` named by `RH.ExplicitFormulaReceiver` on
2026-08-28, and `argumentPrincipleDefect_eq_zero` records the vanishing defect.

[proved-derived; formal-checked] The mechanism retains every antecedent. Mathlib's
`MeromorphicOn.extract_zeros_poles` writes `ξ = P · g` on a codiscrete subset of the disc, where `P`
is the factorized rational function of the divisor and `g` is analytic and nonvanishing on the
disc; `meromorphicOrderAt_riemannXi_ne_top` supplies the nowhere-locally-zero premise from
`ξ(0) = 1/2`. The identity theorem on the connected component of the open set where `g` is
analytic and nonvanishing upgrades the codiscrete equality to equality near every point of the
closed disc. On the contour the logarithmic derivative therefore splits into
`Σ m_ρ (z - ρ)⁻¹ + g'/g`; each simple pole returns `Φ(ρ)` by Cauchy's integral formula, and the
analytic remainder returns zero by Cauchy--Goursat. No zero-counting estimate, growth bound, or
finite census enters.

[proved-derived; formal-checked] `RH/GlobalWeilFinishLine.lean` no longer stores the argument
principle as a field of `GlobalExplicitFormulaWitness`; the admissibility retained in
`CofinalXiContours` already supplies it, and `GlobalExplicitFormulaWitness.truncatedFormula` now
consumes the proved theorem. The certificate's remaining fields are the archimedean residual
identity on every member, the three convergence laws, the vanishing boundary return, and the limit
passage.

[established-bounded; measured] `lake env lean ElementaryHolonics/RH/WeightedArgumentPrinciple.lean`
returned zero errors and zero warnings under Lean `v4.33.0`; its printed axiom audit for
`meromorphicOrderAt_riemannXi_ne_top`, `hasWeightedArgumentPrinciple`, and
`argumentPrincipleDefect_eq_zero` is exactly `[propext, Classical.choice, Quot.sound]`.
`lake build ElementaryHolonics.Millennium.OfficialFinishLines` then returned
`Build completed successfully (4516 jobs)` with the reduced certificate.

## Return: the transported-scalar maximum principle

[proved-derived; formal-checked]
`ElementaryHolonics/Millennium/NavierStokesTransportedScalarMaximumPrinciple.lean` proves
`transportedScalar_le_of_initial_le`: a scalar `theta` on the periodic space that is `C²` on the
open slab, one-periodic at every admitted time, and obeys the transported heat law

```text
derivWithin (theta x) (Ico 0 T) t + fderiv ℝ (theta · t) x (u x t) = nu * Δ (theta · t) x
```

with `0 ≤ nu`, never exceeds its initial supremum on `Ico 0 T`. The two-sided corollary
`abs_transportedScalar_le_of_abs_initial_le` bounds `|theta x t|` by the initial absolute bound.
No incompressibility, no bound on the carrying field `u`, and no positivity of `T` is assumed. The
law is spelled exactly as the momentum law of `OpenSmoothSolutionOn`, so a vorticity component
that obeys it can consume the theorem without a rebase.

[proved-derived; formal-checked] The mechanism is the classical `ε`-argument with every step
retained: `unitBox` is compact and every point has a periodic representative in it
(`boxRepresentative`, coordinatewise `Int.fract`, descended through
`isOnePeriodic_eq_of_euclideanToSpatialTorus_eq`); the penalised scalar `theta - ε t` attains its
maximum on `unitBox ×ˢ Icc 0 t₁`; a maximum at positive time is a global spatial maximum, so the
gradient vanishes and the Laplacian is nonpositive (`laplacian_nonpos_of_isLocalMax`, a
second-derivative test proved here through `laplacian_eq_iteratedFDeriv_orthonormalBasis` and a
one-variable `strictMonoOn_of_deriv_pos` argument); the one-sided time derivative at that maximum
is at least `ε` by `IsLocalMaxOn.hasFDerivWithinAt_nonpos` in the direction `-1`; the law forbids
this, so the maximum sits on the initial face.

[interpretation] This is the exact statement of Brandon's spinning-top reading on the two-dimensional
Navier--Stokes line: when the stretching channel is closed, vorticity is only transported and
diffused, and the maximum principle says the top can only lose winding to friction. The
three-dimensional problem is the case where the stretching channel `ω · S · ω` is open; its sign is
receiver-relative, given by the alignment of the vorticity with the extensional or compressional
strain axis, which is why no maximum principle applies and why `CriticalVorticityTerminalControl`
remains the single open Prop of the periodic finish line.

[established-bounded; measured] `lake build
ElementaryHolonics.Millennium.NavierStokesTransportedScalarMaximumPrinciple` returned success with
zero errors and zero warnings; the printed axiom audit for `deriv_deriv_nonpos_of_isLocalMax`,
`laplacian_nonpos_of_isLocalMax`, `transportedScalar_le_of_initial_le`, and
`abs_transportedScalar_le_of_abs_initial_le` is exactly `[propext, Classical.choice, Quot.sound]`.
The owner was registered in `ElementaryHolonics.lean`.

## Context recovered: the positivity object and the Scratch directory

[historical; source-inspected] Brandon recalled a Riemann positivity object phrased as
"`2^{-1} + ε` where `ε` is like the complex part" in a `Scratch` directory. The Claude Code session
logs of 2026-08-27 and 2026-08-28 show the phrasing entered from Brandon's own message
*"what does that mean about the critical line, real part 2^{-1}, how does the complex part relate to
curl"*, was adopted as "`σ = 2^{-1}` is the swing anchor, an off-line vortex at `½ + δ` has a mirror
twin at `½ − δ`", and became formal on 2026-08-28 as `RH/WeilPositivity.lean`: the spectral kernel
of a Weil square satisfies `ĥ(½ + iγ) = |G(½ + iγ)|²` on the critical line, and under RH the
truncated zero receiver of every square on every disc is a nonnegative real
(`truncatedZeroReceiver_nonneg_of_RH`), with Weil's converse retained as the named port
`HasWeilCriterion`.

[historical; source-inspected] That file and ten companions (`RH/ArchimedeanReceiver`,
`Millennium/PrimeSimplex`, `PrimeSimplexPeeling`, `PrimeSimplexCrossing`, `MestreHeightLattice`,
`RealizedMillenniumForms`, `HelicityAsLinking`, `RealizerJoints`, `PositivityIsRealization`,
`RealizationCorollaries`) were written in `Scratch/` on 2026-08-28 and copied into the library the
same day; they entered Git in commit `c9054045` on 2026-08-31. The `Scratch` directory itself was
never tracked and was removed by Sol on 2026-08-30 at 21:52 UTC under the CONS4 disposition after
measuring eleven byte-identical copies of live modules, six divergent shadows, and 133 probes. The
four unpromoted solver files written on 2026-08-30 (`HolonicSolver`, `HolonicActionSolver`,
`HolonicShellNumbering`, `HolonicBandLaw`) were lost with it; no promoted file was affected.

## Repository-health counterexample

[counterexample; measured] Four Millennium modules do not compile under the pinned station on
2026-09-01: `FamilyFiveDescent` (line 209, an implicit-argument drift; it blocks seventeen modules
including `UniversalBSD`, `UniversalBSDLedger`, `MillenniumInstance`, `FamilyPairing`, and
`FamilyOddDescent`), `FamilyCentralRatio` (line 51, a simp normal-form drift; it blocks
eighty-eight modules including every `FamilyTunnell*` owner), `GeneralSupport` (line 106, the
removed `Nat.factorization_eq_zero_of_non_prime`; it blocks sixteen modules), and
`HolonicStateAddressedQuadratic` (instance synthesis; it blocks none). The blockers named on
2026-08-29 (`FiveHalving`, `FamilySupport`, `FamilyImage`, `HeckeEuler`) now build. The live
release umbrella reaches 111 of 854 Millennium modules and none of the 23 RH modules, so these
failures are invisible to `tools/lean_check.sh`. The failures are API drift, not mathematical
defects; the proofs are unchanged since 2026-08-22 and 2026-08-23.

## Owners

[definition] `ElementaryHolonics/RH/WeightedArgumentPrinciple.lean` (new) owns the argument
principle; `ElementaryHolonics/RH/GlobalWeilFinishLine.lean` consumes it and lost one field;
`ElementaryHolonics/Millennium/NavierStokesTransportedScalarMaximumPrinciple.lean` (new) owns the
maximum principle; `ElementaryHolonics.lean` registers both. No Rust, CUDA, canon, blueprint, or
construction-state file changed. The Codex session's concurrent SCF2 edits under `crates/` were
neither read nor touched.

## What this does not establish

[open] The second explicit-formula port, `HasArchimedeanResidualIdentity`, which deforms the same
contour onto the prime, polar, and archimedean receivers with a vanishing boundary return, is
untouched. The Riemann finish line still owes it, the three convergence laws, arithmetic positivity,
and the off-line separator.

[open] The two-dimensional Navier--Stokes regression still owes the derivation of the vorticity
transport equation from the momentum law of an `OpenPeriodicSolutionOn`, the z-independence of the
solution for z-independent data through the uniqueness receipt, the vanishing of the third velocity
component, and the identification of the bounded scalar with `criticalVorticityRate`. The
three-dimensional Prop `CriticalVorticityTerminalControl` is not approached.

[definition] Nothing here claims or approaches the Riemann hypothesis or Navier--Stokes regularity.
The construction state and roadmap are unchanged; the live frontier remains SCF2.
