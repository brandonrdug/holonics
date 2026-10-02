# A metric keeps the move native exactly when it acts through the readings

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1). **Grade.** [proved-derived;
formal-checked] for §1 to §3 (`HNN/ExecutedComparison` §10); [agent-inferred] where marked. No run.
Follows [the native move at `E` alone](2026-10-02_THE_NATIVE_MOVE_AT_E_ALONE_ITS_FIXED_POINTS_AND_ONE_STEPS_REACH.md).

The main line's first seed ranks the exterior refit's optimizers `rms` ahead of `adam`, `sgd` and
momentum, so a per-coordinate scale leads as the ingredient. This record states which metrics a
native move can carry, and gives the per-reading scale as the candidate native counterpart of
`rms`'s, with its step, fixed points, reach and certificate.

Notation: `E`'s move `v`, the readings' Jacobian `A` (surjective), the port's mass `M = I ⊗ H′ ≻ 0`,
the comparison's covector on the readings `c`, so `∇_E L = Aᵀc`. The cometric `S = AM⁻¹Aᵀ`, the
least-energy lift `H = M⁻¹AᵀS⁻¹` (`H w = KineticFace.horizontal w`, `A H = 1`).

## 1. Which metrics keep the move native

The native span is the horizontal space: `v` has no hidden part exactly when `M v = Aᵀμ` for some
reading weights `μ` (`hidden_eq_zero_iff`).

**A metric `P` keeps every step `P ∇L` in that span exactly when each step is the least-energy
lift of the reading change `(A P Aᵀ) c`** (`keeps_span_iff`). So a span-keeping metric acts on the
comparison only through its form on the readings, `D = A P Aᵀ`. The rest of `P` never moves `E`.

Conversely every positive definite reading form `D` is such a metric:
`P_D = H D Hᵀ + (1 − HA) M⁻¹ (1 − HA)ᵀ` is positive definite (`readingMetric_posDef`), has
`A P_D Aᵀ = D` (`readingMetric_reads`) and steps from `Aᵀc` to `H D c`
(`readingMetric_step`). Its second term is the port's own cometric on the hidden directions,
where no comparison covector lies.

The members already in the machine:
- **the normal law** is `D = S`, the readings' Gram in the port's cometric: `H S c = M⁻¹Aᵀc`
  (`readingStep_normal`);
- [agent-inferred] **the kinetic solve** is `D = F⁻¹` where the witness's Fisher form `F` is
  invertible on the readings, by its Rust owner's statement (`hnn::executed::KineticSolve`).

## 2. The per-reading scale is a member

A per-reading scale `D = diag(d)`, `d > 0`, one entry per reading coordinate (each lock
candidate's log-reading and each order piece's log-gap, 320 at the opening), is a reading form, so
its step `v = −η H (d ⊙ c)` is native:
- **its reading change is exactly `−η (d ⊙ c)`** (`KineticFace.horizontal_reads`);
- **its energy is the least of every move with that reading change**,
  `½ η² ⟨d ⊙ c, S⁻¹ (d ⊙ c)⟩` (`KineticFace.unique_minimum_energy`);
- **it is a deposition of the returns** at reading weights `−η S⁻¹(d ⊙ c)`, the same form the
  normal law and every kinetic iterate take.

## 3. Its fixed points, reach and certificate

- **Fixed points.** The step rests exactly where `∇L = Aᵀc = 0` (`readingStep_zero_iff`). No
  reading form changes where the move can rest; it changes the path.
- **Slope.** The first-order change of `L` is `−η Σ_k d_k c_k²` (`readingStep_slope`).
- **One step's reach.** The steps `−H diag(d) c`, `d > 0`, are exactly the horizontal moves whose
  reading change is zero where `c_k = 0` and opposite in sign to `c_k` elsewhere
  (`reading_diagonal_reach`). A full reading form reaches every horizontal move whose reading change
  descends (`reading_posDef_reach`).
- **Certificate in the Fisher form.** On one sheet with face `p` and target `t`, `c = p − e_t`: if
  the change's spread is at most `ω` and `η · ln 2 · 2^ω · Var_p(d ⊙ c) ≤ Σ_k d_k c_k²`, the code
  falls by at least `η Σ_k d_k c_k²/2` bits (`reading_scale_descends`, from
  `HNN/Ratio/Certificate.codeLength_step_descends`). `Var_p(d ⊙ c) = (d ⊙ c)ᵀ J_p (d ⊙ c)` is the
  receiver's Fisher form. Sheets sum (`Certificate.window_code_add_le`). The certificate reads the
  readings' first-order change; where the readings are not linear in `E`, the move's guards certify
  each trial whole, as they do now.

## 4. A per-entry scale is not a member

The exterior `rms` scales each of `E`'s 600 entries, not each reading. That generally leaves the
native span. The smallest case: two entries, one reading, `A = [1 1]`, `M = I`. The horizontal
space is the line through `(1, 1)`, and `∇L = (c, c)`. The step `−diag(p₁, p₂)(c, c)` is horizontal
exactly when `p₁ = p₂`.

[agent-inferred] So the per-reading scale reproduces `rms`'s ingredient only if `rms`'s gain comes
through the horizontal part of its steps. The read that settles it on the main line's own
constitutions is §4's first read of the baseline record, taken on `rms`'s steps instead of the
chord: the hidden energy `½⟨M h, h⟩` of each step, `h = hidden(v_rms)`, against its whole
`½⟨M v_rms, v_rms⟩`.
- If the hidden share is small, the counterpart is the per-reading scale above.
- If it carries the gain, no span-keeping metric reproduces it (§1). The native counterpart is then
  a change of the port's mass `M` itself, which changes what is horizontal.

## 5. What `rms`'s scale estimates in the readings

[agent-inferred] Under the witness's own face `θ`, the second moment of a reading's covector is the
Fisher form's diagonal: `E_t[(θ_k − [t = k])²] = θ_k(1 − θ_k) = F_kk`. Taken per reading, `rms`
divides by the square root of a running estimate of that second moment, so it sits between the
plain step in the readings (`d_k = 1`) and the Jacobi step `d_k = 1/F_kk`, the diagonal of the
kinetic member `F⁻¹`. Over the data, the running second moment equals `F_kk` only where the face is
calibrated. An exact native rule would hold `d_k` dyadic, `d_k = 2^(−⌊½ log₂ F̂_kk⌋)` with `F̂` the
accumulated per-reading second moment, as `hnn::constitution::receiving_class_metric` steps at
`2^⌊log₂(1/λ̄)⌋`. It is not built: the main line's remaining seeds and the hidden-share read above
decide whether it is the ingredient's counterpart.
