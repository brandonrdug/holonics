# The readings' curvature is the only native source of hidden motion

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [proved-derived;
formal-checked] for the statements cited to `HNN/ExecutedComparison` §12; [derived] and
[agent-inferred] where marked. No run. Not built in Rust.
Follows [no mass makes a hidden direction visible](2026-10-02_NO_MASS_MAKES_A_HIDDEN_DIRECTION_VISIBLE_THE_DEPOSIT_CAN_ONLY_TILT_A_VISIBLE_STEP.md).

That record named the term through which a hidden direction acts: the readings' curvature, which
the Gauss–Newton law drops. This record states its native law in the kinetic solve's owner
(`hnn::executed::KineticSolve`), when it is well defined, and what it costs. It waits on the main
line's hidden-share read: parked if the share is small, carried to the U6 counterpart if it is large.

## 1. The term

[derived] With `L(E) = ℓ(r(E))`, readings `r`, their Jacobian `A`, the comparison's covector
`c = ∇ℓ` and the witness's Fisher form `F = ∇²ℓ`, the chain rule gives
`∇²L = AᵀFA + C`, `C = Σ_k c_k ∇²r_k`. The kinetic solve keeps `AᵀFA` and drops `C`.

**On a hidden direction only `C` and the mass act** (`hidden_curvature`): if `A h = 0`, the
Gauss–Newton form and the first-order term `⟨Aᵀc, h⟩` both vanish on `h`.

## 2. When the step is well defined

`C` has either sign: `c_t = θ_t − 1 < 0` at the target, `c_k = θ_k > 0` at its rivals, and each
`∇²r_k` is indefinite in general. Where `C` curves down on the hidden directions, the undamped
model `⟨Aᵀc, v⟩ + ½⟨v, (AᵀFA + C) v⟩` is unbounded below and has no step.
- **The damped form** `Q_s = AᵀFA + C + s M` uses the port's own mass as the damping.
- **It is positive definite once the damping clears the curvature** (`newtonForm_posDef`): if
  `C + s₀ M ⪰ 0` and `s > s₀`, then `Q_s ≻ 0`. Here `s₀` is the most negative curvature of `C`
  measured against `M`.
- [agent-inferred] **Choosing `s` exactly.** `Q_s ≻ 0` is decided over the rationals by an exact
  `LDLᵀ` with every pivot positive, so `s` can be the least step of the existing dyadic ladder that
  passes, read at each state. No eigenvalue is computed.

## 3. The step

- **It descends and keeps `L`'s fixed points** (`newton_step`). At `Q_s ≻ 0` the step
  `v = −Q_s⁻¹Aᵀc` solves the damped model, `⟨Aᵀc, v⟩ < 0`, and as the metric step of
  `P = Q_s⁻¹ ≻ 0` it rests exactly where `∇L = 0` (`metric_step_zero_iff`).
- **The curvature is the only source of its hidden motion** (`newton_step_hidden_iff`): `v` is
  native exactly when `C v` is a combination of the readings' covectors. Without `C`, the damped
  Gauss–Newton step is always native (`gaussNewton_regularized_native`). With #199, this closes the
  question: a native law moves the hidden directions only through `C`.

## 4. Its place in the kinetic solve

[agent-inferred] The solve already runs conjugate gradients on `AᵀFA v = −Aᵀc`, preconditioned by
`M⁻¹`. The Newton law changes the operator to `Q_s`:
- **One added product per iteration**, `C p`, the directional derivative of `Aᵀc` along `p`: the
  derivative of `reading_gradients` along the search direction, with `c` held. The log-readings'
  gradients are rational in the state, so this derivative is exact.
- **The stop is the same signal.** Its `Kernel` stop (`pᵀAᵀFAp ≤ 0`) becomes `pᵀQ_s p ≤ 0`, which
  now means the damping is below `s₀`. The step then takes the next rung of the ladder.
- **The iterates are no longer depositions of the returns.** With `C`, `M v_k` is not a
  combination of the readings' covectors, so the move is not a normal-law deposit at reading
  weights. It is a direct change of `E`, as the kinetic move's adopted trial already is.

## 5. Its energy cost

- **Split** (`KineticFace.energy_split`): `½⟨M v, v⟩ = ½⟨A v, S⁻¹ A v⟩ + ½⟨M h, h⟩`, with
  `S = AM⁻¹Aᵀ` and `h = hidden(v)`. The second term is the cost over the native lift of the same
  reading change. It is zero exactly when the step is native.
- [derived] **Bound.** From `Q_s ⪰ (s − s₀) M` and `⟨v, Q_s v⟩ = −⟨Aᵀc, v⟩`:
  `(s − s₀)⟨M v, v⟩ ≤ ⟨Aᵀc, Q_s⁻¹Aᵀc⟩ ≤ ⟨c, S c⟩/(s − s₀)`, so
  `⟨M v, v⟩ ≤ ⟨c, S c⟩/(s − s₀)²`. The damping above the curvature's negative part sets the
  largest energy a step can carry.

## 6. The release guard and the read-order results

- [agent-inferred] **The release guard still certifies every trial.** It evaluates each trial whole
  (`OwnNotBelow`, the fixed mask), independent of the model that proposed it. The certified step's
  first-order check (`a ≥ 0`) holds, since `−⟨Aᵀc, v⟩ > 0`.
- [agent-inferred] **The read-order results are untouched.** #179 and #189 sit on the landmark
  tree's base measure; the step changes only `E`.

## 7. Status

The law is stated and proved in Lean. The Rust product `C p` and the damped operator are not built.
If the main line's hidden share of `rms`'s steps is small, this stays parked as the stated
counterpart. If it is large, this is the U6 counterpart, and the next step is the Rust change in
§4 with its tests against the kinetic solve's own.
