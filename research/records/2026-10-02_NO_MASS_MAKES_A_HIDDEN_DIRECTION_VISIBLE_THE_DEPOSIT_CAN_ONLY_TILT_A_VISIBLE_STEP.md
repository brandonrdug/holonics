# No mass makes a hidden direction visible; the deposit can only tilt a visible step

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [proved-derived;
formal-checked] for §1 to §3 (`HNN/ExecutedComparison` §11); [agent-inferred] where marked. No run.
Follows [a metric keeps the move native exactly when it acts through the readings](2026-10-02_A_METRIC_KEEPS_THE_MOVE_NATIVE_EXACTLY_WHEN_IT_ACTS_THROUGH_THE_READINGS.md).

This is the other branch of the hidden-share read. If `rms`'s gain comes through the part of its
steps no reading sees, a metric that keeps the move native cannot carry it. The question is whether a
change of the port's mass, made through the existing owners, can.

Notation as in the predecessor: `A` the readings' Jacobian (surjective), `M = I ⊗ H′ ≻ 0` the port's
mass, `H′` the source law's feature Gram with the passage deposited. A move `v` is native when
`M v = Aᵀμ` for some reading weights `μ`.

## 1. Visibility belongs to the readings alone

- **A direction no reading sees is never native, under any positive mass** (`hidden_never_native`).
  If `A δ = 0` and `M δ = Aᵀμ`, then `⟨δ, M δ⟩ = ⟨A δ, μ⟩ = 0`, so `δ = 0`.
- **Some positive mass makes `δ` native exactly when a reading sees it**
  (`native_under_some_mass_iff`): `δ = 0` or `A δ ≠ 0`.

So no mass change makes a hidden direction visible. What a mass change can do is choose which lift
of a visible reading change the native step deposits. It can tilt that lift so that it carries
hidden components along with a reading change the comparison asks for.

## 2. The smallest change that tilts a step onto a target

For a target `δ` with `A δ ≠ 0`:
- **Unstructured, rank one** (`deposit_makes_native`). With `z = Aᵀμ − M δ` and
  `⟨δ, z⟩ = ⟨A δ, μ⟩ − ⟨δ, M δ⟩ > 0`, the addition `K = z zᵀ/⟨δ, z⟩ ⪰ 0` keeps the mass positive
  definite and gives `(M + K) δ = Aᵀμ`. A deposit only adds, and one rank-one addition is the least
  it can make.
- **Through the feature Gram** (`feature_deposit_makes_native`). The mass acts on `E`'s rows
  through one Gram, `V ↦ V H`, and the deposit changes only `H`. For a target `Δ` in `E`'s shape and
  a momentum `X` built from the readings' covectors, put `Z = X − Δ H`. If `Z Δᵀ` is positive
  definite, the feature deposit `k = Zᵀ (Z Δᵀ)⁻¹ Z ⪰ 0`, of rank at most the number of rows, gives
  `Δ (H + k) = X`.
- **And the condition is needed** (`feature_deposit_native_needs`): any feature deposit `k ⪰ 0`
  with `Δ (H + k) = X` makes `(X − Δ H) Δᵀ = Δ k Δᵀ` positive semidefinite. Its entry `(i, j)`
  pairs row `i`'s needed change `Z_i` with row `j`'s target `Δ_j`: one Gram serves every row, so the
  condition binds every pair of rows. A target fails it wherever a row's needed change opposes its
  own target, `⟨Z_i, Δ_i⟩ < 0`.

## 3. The cost in the Fisher form

- **At first order, nothing.** A native step's reading change is the same under every mass
  (`KineticFace.horizontal_reads`), so its first-order decrease `⟨c, D c⟩` and its Fisher-form
  certificate on the readings (`reading_scale_descends`) are unchanged.
- **The step's kinetic energy never falls.** After a deposit `K ⪰ 0`, the least energy of a reading
  change `w`, `½⟨w, (A M⁻¹ Aᵀ)⁻¹ w⟩`, is at most its value under `M + K`
  (`deposit_raises_native_energy`).
- **At second order, only through the readings' curvature.** [derived] For a hidden part `h`
  (`A h = 0`), the second-order change of `L` is `½ hᵀ (AᵀFA + Σ_k c_k ∇²r_k) h = ½ Σ_k c_k hᵀ∇²r_k h`,
  since the Gauss–Newton term `AᵀFA` vanishes on `h`. The same tensor `∇²r_k` is how `h` changes the
  readings' Jacobian at the next state. So a tilted step's hidden part pays off, or costs, only
  through the term the Gauss–Newton law omits.

## 4. Whether the existing owners carry it

**They do not.**
- The only law that changes `M` is the normal law's Gram deposit,
  `ΔH = Σ_t w_t f_t f_tᵀ` (`hnn::constitution::NormalLaw`, Lean `HNN/Normal`). It adds only
  features that reached the port, with the returns' own weights.
- A tilt toward a target needs `k = Zᵀ (Z Δᵀ)⁻¹ Z`. That is a choice of features and weights made
  for the target, not the returns' weights, so it would be a new law choosing the constitution's
  change. The deposition law admits only covectors that actually reached the locus.
- `Physics/Information/PortWork` is the thermal port's level-shift law. It does not act on `E`'s
  mass.

## 5. The release guard and the read-order results

- [agent-inferred] **The release guard stays intact.** It certifies each trial whole
  (`OwnNotBelow`). A mass change changes the proposed step, not the guard, so the guard still
  certifies and may still refuse.
- [agent-inferred] **The read-order results stay intact.** They are #179 and #189,
  `Compression/Landmark/Context/BaseMeasure`, any past-only base with mass at least `1/4`. They
  live on the landmark tree's base measure, a different locus with its own owner, and `E`'s feature
  Gram does not enter them.

## 6. What follows if the gain is hidden

[agent-inferred] If the hidden-share read finds that `rms`'s gain lies in its hidden part, the
counterpart is the curvature term `Σ_k c_k ∇²r_k` on hidden directions (§3), not a mass change.
- No owner computes it today. `hnn::executed`'s curvatures are Gauss–Newton squares of first
  derivatives (the storage curvature `Σ_c |∂z_c/∂ρ|²`, the witness's `AᵀFA`).
- It would complete the kinetic solve's own law, the Newton term its Gauss–Newton model drops, not
  add a parallel mechanism. The solve already stops where `pᵀAᵀFAp ≤ 0` (`KineticStop::Kernel`),
  on directions its Gauss–Newton form does not read. Every hidden direction is one of them, and
  there only that term reads.
