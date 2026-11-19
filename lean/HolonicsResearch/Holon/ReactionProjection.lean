import Holonics.Holon.Reaction
import Holonics.Holon.Deposition
import Holonics.Holon.Cayley

/-!
# Holon.ReactionProjection: the complex passive projection, its grain, and the scalar shift

[definition] A learned complex relation `W` (a reaction slice's linear self-relation) is read on its
realification `L = realify W` over `n ⊕ n` (`Holon/Reaction.realify`), where multiplication by `i`
is the complex structure `J = realify (i·1)`. Its power at an effort `e` is the quadratic form
`⟨e, L e⟩`, and the relation is passive when `⟨e, L e⟩ ≤ 0` for every `e` (the form in which
`Holon/Deposition.projectPassiveCongruence_passive` states it). A passive projection removes a
positive semidefinite part `R` with `L − R` passive; the retired Rust `holon::reaction` held two of
them at a dyadic grain `u = 2^(−g)`, the averaged congruence clip and the minimal scalar shift.

[proved-derived; formal-checked] What is proved, over `ℝ`, on a finite index `m` (`n ⊕ n` where a
statement reads the realification). The forms used throughout: `⟨e, (W − c·1)e⟩ = ⟨e, W e⟩ − c|e|²`
(`quad_sub_smul_one`), `|e|² ≥ 0` (`dot_self_nonneg`), and a symmetric matrix is its own symmetric
part (`symPartK_transpose`, `symPartK_of_transpose_eq`).

1. **The averaging argument.** For a complex structure `J` (`Jᵀ J = 1`, `J J = −1`; then
   `Jᵀ = −J`, `complexStructure_transpose`, and `J Jᵀ = 1`, `complexStructure_mul_transpose`) the average
   `R̄ = ½(R + JᵀRJ)` (`average`) has `⟨e, R̄ e⟩ = ½⟨e, R e⟩ + ½⟨Je, R Je⟩` (`quad_average`), so it is
   positive semidefinite with `R` (`average_psd`) and commutes with `J` (`average_commute`: it is
   complex-linear). If `Jᵀ (sym L) J = sym L` then `⟨Je, L Je⟩ = ⟨e, L e⟩` (`quad_conj_invariant`)
   and `⟨e, (L − R̄)e⟩ = ½⟨e, (L − R)e⟩ + ½⟨Je, (L − R)Je⟩` (`averaging_identity`), so `L − R̄` is
   passive whenever `L − R` is (`average_passive`); neither step reads `J` beyond that invariance.
   `J = realify (i·1)` is a complex structure (`realifyI`, `realifyI_eq`, `realifyI_transpose_mul`,
   `realifyI_mul_self`), the realification of every complex matrix commutes with it
   (`realify_commute`), and a matrix commuting with an orthogonal `J` keeps its symmetric part under
   `J` (`symPartK_conj_of_commute`, `realify_symPartK_invariant`). The congruence clip's removed part
   `P⁻ᵀ diag(d₊) P⁻¹` (`clipRemoved`) is positive semidefinite (`clipRemoved_psd`), so the averaged
   clip of a complex relation is passive (`averaged_clip_passive`), and on a passive relation the clip
   removes nothing and its average is `0` (`average_zero`, `averaged_clip_of_passive`).
2. **The grain correction.** [proved-standard; formal-checked] `|E_ij| ≤ ε` on an index of size `m`
   gives `|⟨e, E e⟩| ≤ m ε |e|²` (`quad_abs_le_of_entry`, by `(Σ|e_i|)² ≤ m Σ e_i²`). Hence if
   `L − R̄` is passive and `R̃` is within `u/2` of `R̄` in every entry, `L − (R̃ + (m u/2)·1)` is
   passive (`grain_passive`), and `R̃ + (m u/2)·1` stays positive semidefinite when `R̄` is
   (`grain_removed_psd`). Entrywise rounding to the grain, `roundGrain u x = u·round(x/u)` with
   `round x = ⌊x + ½⌋` (Mathlib's `round_eq`) as the Rust's `round_nearest`, is within `u/2`
   (`abs_roundGrain_sub`,
   `grainRound`, `abs_grainRound_sub`) and sends `0` to `0` (`roundGrain_zero`, `grainRound_zero`).
   On the realification `m = 2n`, and the shift is `n` grain units: removing `round(R̄) + n u·1`
   from `realify W`, with `R̄` the averaged congruence clip, leaves a passive relation
   (`passive_complex_at_grain`) and removes a positive semidefinite part
   (`passive_complex_at_grain_removed_psd`); on a passive relation the removed part is the shift
   `n u·1` alone (`grain_removed_of_passive`).
3. **The scalar shift.** Gershgorin ([proved-standard; formal-checked]): for symmetric `S` with
   every row sum `Σ_j |S_ij| ≤ G`, `⟨e, S e⟩ ≤ G|e|²` (`gershgorin_quad`, with
   `gershgorin S = max_i Σ_j |S_ij|`, `le_gershgorin`). The naturals `τ` with `W − τ·1` passive,
   those with `⟨e, W e⟩ ≤ τ|e|²` (`shiftSet`, `mem_shiftSet`), contain `⌈c⌉₊` for every such bound
   `c` (`ceil_mem_shiftSet`) and so are nonempty (`shiftSet_nonempty`, Gershgorin on `sym W`). Their
   least element `τ*` (`leastShift`, `leastShift_le`) gives a passive `W − τ*·1`
   (`leastShift_passive`) that keeps the skew part (`shift_keeps_skew`; on a complex relation
   `skewPart (W − τ·1) = skewPart W`, `skewPart_shift`). `τ*` reads only the symmetric part
   (`leastShift_symPartK`, `shift_passive_of_symPart`); `τ* = 0` exactly when `W` is passive
   (`leastShift_eq_zero_iff`); `τ* ≤ ⌈c⌉₊` for every `c` with `⟨e, W e⟩ ≤ c|e|²`
   (`leastShift_le_ceil`), in particular `τ* ≤ ⌈gershgorin⌉₊` for symmetric `W`
   (`leastShift_le_gershgorin`); and `τ* ≥ 1` leaves a witness `e` with `⟨e, W e⟩ > (τ* − 1)|e|²`
   (`leastShift_active`). Joined to `Holon/Cayley.shift_passive_iff`, `τ* = ⌈λ_max(sym W)⌉₊`
   (`leastShift_eq_ceil_lamMax`) and `τ* < λ_max(sym W)₊ + 1` (`leastShift_lt`). At a grain `u > 0`
   the least `τ` with `W − τu·1` passive is `τ*(u⁻¹ W)` (`grainShift`, `mem_shiftSet_grain`,
   `grainShift_passive`, `grainShift_le`), equal to `⌈λ_max(sym W)/u⌉₊` (`grainShift_eq_ceil`).
4. **The comparison with the congruence clip** ([counterexample; formal-checked]). For
   `S = [[0, 1], [1, 0]]` (`clipS`; eigenvalues `±1`, its top eigenvalue in `(0, 1]` by
   `lamMax_clipS`) the congruences `P_t = [[t, t], [t⁻¹, −t⁻¹]]`, `P_t⁻¹ = ½[[t⁻¹, t], [t⁻¹, −t]]`
   (`clipP`, `clipPinv`, `clipP_mul_clipPinv`) give `P_tᵀ S P_t = diag(2, −2)` for every `t ≠ 0`
   (`clipD`, `clipP_congruence`): the same diagonal for every `t`. The clip removes
   `½[[t⁻², 1], [1, t²]]` (`clipRemoved_clipPinv`), of trace `(t² + t⁻²)/2` (`trace_clipRemoved`),
   which exceeds every bound along `t = k + 1` (`clip_removed_unbounded`), while the scalar shift is
   `τ* = 1` (`leastShift_clipS`) and removes `1·1`, of trace `2` (`clip_vs_shift_witness`).

Sources: the box of #410, "The complex-passivity averaging argument, grain correction and
scalar-shift comparison of Rust `holon::reaction` (no Lean statement)"; the retired Rust
`crates/holonics/src/holon/reaction.rs` at `2d34b819` (the same file as `d8dd2455e^`: its module
header, `passive_complex_at_grain` and its comment, `passive_shift_at_grain`), retired at
`d8dd2455e`, whose laws `docs/HNN_FORMULA.md` keeps in its reaction section ("Retired September 28",
the three laws it marks as not in Lean); the
Holon's open paragraph in `docs/ELEMENTARY_OBJECTS.md` §"The Holon as one object" (passivity is a
proved property, never assumed: learned relations enter with their actual power term); the precision
law of `CLAUDE.md` (a value is read at a declared width, and rounding is a section that commutes
when it stands once; here it stands once, after the average, and its remainder is accounted by the
diagonal shift). The owners read: `Holon/Reaction` (`realify`, `realify_skew`, `skewPart`,
`skewPart_of_skew`, `herm`, `re_herm_skew`), `Holon/Deposition` (`symPartK`, `quad_symPartK`,
`quad_congr`, `congruenceClip_nonpos`, `projectPassiveCongruence`,
`projectPassiveCongruence_passive`, `projectPassiveCongruence_of_passive`, and the witness
`congruence_vs_eigen_witness`, where the clip differs from the eigen-clip; item 4 adds that its
removed part is unbounded across congruences) and
`Holon/Cayley` (`lamMax`, `rayleigh_le`, `shift_passive_iff`, `shifted_committed_energy_bound`, which
carries any passive shift into the committed-energy bound). Atlas rows served:
`holon.minimal-certified-shift`, `holon.skew-part-projection`, `holon.committed-energy-bound`,
`holon.modulated-skew-reaction`.

What is not claimed. The skew-Hermitian rounding at the grain (`skew_hermitian_at_grain`: the strict
upper triangle rounded and completed by `A_ji = −conj(A_ij)`); the inertia bisection's algorithm
and its rational inertia certificates (the Rust re-certified each projection by inertia; here
passivity is proved for the formula and nothing is re-certified); the Rust's `BigInt` arithmetic
and its interleaved `(re, im)` coordinates (the realification here is `Holon/Reaction`'s block form,
the same up to the coordinate order); that the Rust's rounding of complex entries is the entrywise
`roundGrain` of the realification (at a tie `round(−x) ≠ −round(x)`; both are within `u/2` of each
entry, which is the hypothesis `grain_passive` reads); that `R̄` is the nearest complex-linear
passive correction, or that either projection is optimal in any norm; and the measured statement
that on learned native reaction blocks the clip removed far more than the block (item 4 is a family
on which the removed part is unbounded, not a measurement).

The computational object is the helical pair interaction read on a reaction slice: `J` is the
quarter-turn `i = e^{iπ/2}` of the helix's phase, and averaging over `{1, J}` (the orbit of the
quarter-turn on the form, since `J²` acts on it as `1`) makes the removed resistive part commute with
the turn; that removed part is the pair contact's dissipative material, whose power `⟨e, R̄ e⟩ ≥ 0`
the projection moves out of the learned relation; and the grain is a face read at a declared width
whose rounding remainder is placed on the diagonal. Of the winding guide's six general objects this
touches the helix (the quarter-turn and its orbit), the pair (the contact's resistive material) and
faces and placement (the grain and its placed remainder); cell holonomy, the tube and the tower
thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Holon.ReactionProjection

open Matrix
open Holonics.HolonCore

/-! ## 0. Quadratic forms -/

section Quad

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- [proved-standard; formal-checked] Shifting by `c·1` lowers the form by `c|e|²`. -/
theorem quad_sub_smul_one (W : Matrix m m ℝ) (c : ℝ) (e : m → ℝ) :
    e ⬝ᵥ ((W - c • (1 : Matrix m m ℝ)) *ᵥ e) = e ⬝ᵥ (W *ᵥ e) - c * (e ⬝ᵥ e) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

omit [DecidableEq m] in
/-- [proved-standard; formal-checked] `|e|² ≥ 0`. -/
theorem dot_self_nonneg (e : m → ℝ) : 0 ≤ e ⬝ᵥ e := by
  simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (e i)

omit [Fintype m] [DecidableEq m] in
/-- [proved-standard; formal-checked] The symmetric part is symmetric. -/
theorem symPartK_transpose (W : Matrix m m ℝ) : (symPartK W)ᵀ = symPartK W := by
  rw [symPartK, transpose_smul, transpose_add, transpose_transpose, add_comm]

omit [Fintype m] [DecidableEq m] in
/-- [proved-standard; formal-checked] A symmetric matrix is its own symmetric part. -/
theorem symPartK_of_transpose_eq {S : Matrix m m ℝ} (hS : Sᵀ = S) : symPartK S = S := by
  rw [symPartK, hS, ← two_smul ℝ S, smul_smul]; norm_num

end Quad

/-! ## 1. The averaging argument -/

section Averaging

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- [proved-standard; formal-checked] A complex structure with `Jᵀ J = 1` is skew: `Jᵀ = −J`. -/
theorem complexStructure_transpose {J : Matrix m m ℝ} (hJo : Jᵀ * J = 1) (hJJ : J * J = -1) : Jᵀ = -J := by
  calc Jᵀ = Jᵀ * (-(J * J)) := by rw [hJJ, neg_neg, Matrix.mul_one]
    _ = -((Jᵀ * J) * J) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
    _ = -J := by rw [hJo, Matrix.one_mul]

/-- [proved-standard; formal-checked] A complex structure with `Jᵀ J = 1` also has `J Jᵀ = 1`. -/
theorem complexStructure_mul_transpose {J : Matrix m m ℝ} (hJo : Jᵀ * J = 1) (hJJ : J * J = -1) :
    J * Jᵀ = 1 := by
  rw [complexStructure_transpose hJo hJJ, Matrix.mul_neg, hJJ, neg_neg]

/-- [definition] **The average over the complex structure**: `R̄ = ½(R + JᵀRJ)`. -/
def average (J R : Matrix m m ℝ) : Matrix m m ℝ := (1 / 2 : ℝ) • (R + Jᵀ * R * J)

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] `⟨e, R̄ e⟩ = ½⟨e, R e⟩ + ½⟨Je, R Je⟩`. -/
theorem quad_average (J R : Matrix m m ℝ) (e : m → ℝ) :
    e ⬝ᵥ (average J R *ᵥ e) =
      (1 / 2) * (e ⬝ᵥ (R *ᵥ e)) + (1 / 2) * ((J *ᵥ e) ⬝ᵥ (R *ᵥ (J *ᵥ e))) := by
  rw [average, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, quad_congr, smul_eq_mul,
    mul_add]

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] The average of a positive semidefinite `R` is positive
semidefinite. -/
theorem average_psd (J : Matrix m m ℝ) {R : Matrix m m ℝ} (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e))
    (e : m → ℝ) : 0 ≤ e ⬝ᵥ (average J R *ᵥ e) := by
  rw [quad_average]
  have h1 := hR e
  have h2 := hR (J *ᵥ e)
  linarith

/-- [proved-derived; formal-checked] **The average is complex-linear**: `J R̄ = R̄ J`. -/
theorem average_commute {J : Matrix m m ℝ} (hJo : Jᵀ * J = 1) (hJJ : J * J = -1)
    (R : Matrix m m ℝ) : J * average J R = average J R * J := by
  have h1 : J * (Jᵀ * R * J) = R * J := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, complexStructure_mul_transpose hJo hJJ, Matrix.one_mul]
  have h2 : Jᵀ * R * J * J = J * R := by
    rw [Matrix.mul_assoc, hJJ, Matrix.mul_neg, Matrix.mul_one, complexStructure_transpose hJo hJJ,
      Matrix.neg_mul, neg_neg]
  rw [average, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h1, h2, add_comm]

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] If `J` keeps the symmetric part of `L`, it keeps its form:
`⟨Je, L Je⟩ = ⟨e, L e⟩`. -/
theorem quad_conj_invariant {J L : Matrix m m ℝ} (hL : Jᵀ * symPartK L * J = symPartK L)
    (e : m → ℝ) : (J *ᵥ e) ⬝ᵥ (L *ᵥ (J *ᵥ e)) = e ⬝ᵥ (L *ᵥ e) := by
  rw [← quad_symPartK L (J *ᵥ e), ← quad_congr, hL, quad_symPartK]

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] **The averaging identity**:
`⟨e, (L − R̄)e⟩ = ½⟨e, (L − R)e⟩ + ½⟨Je, (L − R)Je⟩`. -/
theorem averaging_identity {J L : Matrix m m ℝ} (hL : Jᵀ * symPartK L * J = symPartK L)
    (R : Matrix m m ℝ) (e : m → ℝ) :
    e ⬝ᵥ ((L - average J R) *ᵥ e) =
      (1 / 2) * (e ⬝ᵥ ((L - R) *ᵥ e)) + (1 / 2) * ((J *ᵥ e) ⬝ᵥ ((L - R) *ᵥ (J *ᵥ e))) := by
  rw [sub_mulVec, dotProduct_sub, quad_average, sub_mulVec, dotProduct_sub, sub_mulVec,
    dotProduct_sub, quad_conj_invariant hL]
  ring

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] **The averaging keeps passivity**: if `L − R` is passive and
`J` keeps `sym L`, then `L − R̄` is passive. -/
theorem average_passive {J L R : Matrix m m ℝ} (hL : Jᵀ * symPartK L * J = symPartK L)
    (hpass : ∀ e, e ⬝ᵥ ((L - R) *ᵥ e) ≤ 0) (e : m → ℝ) :
    e ⬝ᵥ ((L - average J R) *ᵥ e) ≤ 0 := by
  rw [averaging_identity hL]
  have h1 := hpass e
  have h2 := hpass (J *ᵥ e)
  linarith

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] The average of `0` is `0`. -/
theorem average_zero (J : Matrix m m ℝ) : average J 0 = 0 := by
  simp [average]

/-- [proved-standard; formal-checked] If `J` is orthogonal and commutes with `L`, it keeps the
symmetric part: `Jᵀ (sym L) J = sym L`. -/
theorem symPartK_conj_of_commute {J L : Matrix m m ℝ} (hJo : Jᵀ * J = 1) (hc : L * J = J * L) :
    Jᵀ * symPartK L * J = symPartK L := by
  have h1 : Jᵀ * L * J = L := by
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hJo, Matrix.one_mul]
  have h2 : Jᵀ * Lᵀ * J = Lᵀ := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
  rw [symPartK, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h1, h2]

/-- [definition] **The congruence clip's removed part** `P⁻ᵀ diag(d₊) P⁻¹`. -/
def clipRemoved (Pinv : Matrix m m ℝ) (d : m → ℝ) : Matrix m m ℝ :=
  Pinvᵀ * Matrix.diagonal (fun i => max (d i) 0) * Pinv

/-- [proved-derived; formal-checked] The congruence clip removes a positive semidefinite part. -/
theorem clipRemoved_psd (Pinv : Matrix m m ℝ) (d : m → ℝ) (e : m → ℝ) :
    0 ≤ e ⬝ᵥ (clipRemoved Pinv d *ᵥ e) := by
  rw [clipRemoved, quad_congr]
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_nonneg
  intro i _
  have := le_max_right (d i) 0
  nlinarith [mul_self_nonneg ((Pinv *ᵥ e) i)]

/-- [proved-derived; formal-checked] On a passive relation the averaged clip is `0`: the clip
removes nothing and its average is the average of `0`. -/
theorem averaged_clip_of_passive (J : Matrix m m ℝ) {L P Pinv : Matrix m m ℝ} {d : m → ℝ}
    (hD : Pᵀ * symPartK L * P = Matrix.diagonal d) (hL : ∀ e, e ⬝ᵥ (L *ᵥ e) ≤ 0) :
    average J (clipRemoved Pinv d) = 0 := by
  have h := projectPassiveCongruence_of_passive (Pinv := Pinv) hD hL
  rw [projectPassiveCongruence, sub_eq_self] at h
  rw [clipRemoved, h, average_zero]

end Averaging

/-! ### The realified complex structure -/

section Realify

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] The complex structure of the realification: `J = realify (i·1)`. -/
def realifyI : Matrix (n ⊕ n) (n ⊕ n) ℝ := realify (Complex.I • (1 : Matrix n n ℂ))

omit [Fintype n] in
/-- [proved-standard; formal-checked] `realify (i·1) = [[0, −1], [1, 0]]` in blocks. -/
theorem realifyI_eq : (realifyI : Matrix (n ⊕ n) (n ⊕ n) ℝ) = fromBlocks 0 (-1) 1 0 := by
  rw [realifyI, realify]
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- [proved-standard; formal-checked] `Jᵀ J = 1` for the realified `i`. -/
theorem realifyI_transpose_mul :
    (realifyI : Matrix (n ⊕ n) (n ⊕ n) ℝ)ᵀ * realifyI = 1 := by
  rw [realifyI_eq, fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one]
  simp

/-- [proved-standard; formal-checked] `J J = −1` for the realified `i`. -/
theorem realifyI_mul_self : (realifyI : Matrix (n ⊕ n) (n ⊕ n) ℝ) * realifyI = -1 := by
  rw [realifyI_eq, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

/-- [proved-standard; formal-checked] **The realification is complex-linear**: `realify W`
commutes with the realified `i`. -/
theorem realify_commute (W : Matrix n n ℂ) : realify W * realifyI = realifyI * realify W := by
  rw [realifyI_eq, realify, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- [proved-derived; formal-checked] The realified `i` keeps the symmetric part of every
realification. -/
theorem realify_symPartK_invariant (W : Matrix n n ℂ) :
    realifyIᵀ * symPartK (realify W) * realifyI = symPartK (realify W) :=
  symPartK_conj_of_commute realifyI_transpose_mul (realify_commute W)

/-- [proved-derived; formal-checked] **The averaged clip of a complex relation is passive**: with a
certified congruence `Pᵀ (sym realify W) P = diag d`, `P P⁻¹ = 1`, removing the average over the
realified `i` of `P⁻ᵀ diag(d₊) P⁻¹` leaves a passive relation. -/
theorem averaged_clip_passive (W : Matrix n n ℂ) {P Pinv : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    {d : n ⊕ n → ℝ} (hP : P * Pinv = 1) (hD : Pᵀ * symPartK (realify W) * P = Matrix.diagonal d)
    (e : n ⊕ n → ℝ) :
    e ⬝ᵥ ((realify W - average realifyI (clipRemoved Pinv d)) *ᵥ e) ≤ 0 :=
  average_passive (realify_symPartK_invariant W)
    (fun e => projectPassiveCongruence_passive hP hD e) e

end Realify

/-! ## 2. The grain correction -/

section Grain

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- [proved-standard; formal-checked] **Entrywise bound on a form**: `|E_ij| ≤ ε` gives
`|⟨e, E e⟩| ≤ m ε |e|²`, by `(Σ|e_i|)² ≤ m Σ e_i²`. -/
theorem quad_abs_le_of_entry {E : Matrix m m ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ∀ i j, |E i j| ≤ ε) (e : m → ℝ) :
    |e ⬝ᵥ (E *ᵥ e)| ≤ Fintype.card m * ε * (e ⬝ᵥ e) := by
  have hq : e ⬝ᵥ (E *ᵥ e) = ∑ i, ∑ j, e i * E i j * e j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have h1 : |∑ i, ∑ j, e i * E i j * e j| ≤ ∑ i, ∑ j, |e i| * ε * |e j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    gcongr
    exact hE i j
  have h2 : ∑ i, ∑ j, |e i| * ε * |e j| = ε * (∑ i, |e i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : (∑ i, |e i|) ^ 2 ≤ Fintype.card m * (e ⬝ᵥ e) := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |e i|)
    have hd : e ⬝ᵥ e = ∑ i, |e i| ^ 2 := by simp [dotProduct, sq]
    rw [hd]
    simpa using this
  rw [hq]
  calc |∑ i, ∑ j, e i * E i j * e j| ≤ ε * (∑ i, |e i|) ^ 2 := h1.trans h2.le
    _ ≤ ε * (Fintype.card m * (e ⬝ᵥ e)) := mul_le_mul_of_nonneg_left h3 hε
    _ = Fintype.card m * ε * (e ⬝ᵥ e) := by ring

/-- [proved-derived; formal-checked] **The grain correction keeps passivity**: if `L − R̄` is
passive and `R̃` is within `u/2` of `R̄` in every entry, `L − (R̃ + (m u/2)·1)` is passive. -/
theorem grain_passive {L Rbar Rt : Matrix m m ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hpass : ∀ e, e ⬝ᵥ ((L - Rbar) *ᵥ e) ≤ 0) (hE : ∀ i j, |Rt i j - Rbar i j| ≤ u / 2)
    (e : m → ℝ) :
    e ⬝ᵥ ((L - (Rt + (Fintype.card m * u / 2) • (1 : Matrix m m ℝ))) *ᵥ e) ≤ 0 := by
  have hdec : L - (Rt + (Fintype.card m * u / 2) • (1 : Matrix m m ℝ)) =
      (L - Rbar) - (Rt - Rbar) - (Fintype.card m * u / 2) • (1 : Matrix m m ℝ) := by abel
  have hb := quad_abs_le_of_entry (E := Rt - Rbar) (ε := u / 2) (by linarith) (fun i j => by
    simpa using hE i j) e
  rw [hdec, quad_sub_smul_one, sub_mulVec, dotProduct_sub]
  have h1 := hpass e
  have h2 := neg_abs_le (e ⬝ᵥ ((Rt - Rbar) *ᵥ e))
  nlinarith

/-- [proved-derived; formal-checked] **The removed part stays positive semidefinite**: if `R̄ ⪰ 0`
and `R̃` is within `u/2` of `R̄` in every entry, `R̃ + (m u/2)·1 ⪰ 0`. -/
theorem grain_removed_psd {Rbar Rt : Matrix m m ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hR : ∀ e, 0 ≤ e ⬝ᵥ (Rbar *ᵥ e)) (hE : ∀ i j, |Rt i j - Rbar i j| ≤ u / 2) (e : m → ℝ) :
    0 ≤ e ⬝ᵥ ((Rt + (Fintype.card m * u / 2) • (1 : Matrix m m ℝ)) *ᵥ e) := by
  have hdec : Rt + (Fintype.card m * u / 2) • (1 : Matrix m m ℝ) =
      Rbar + (Rt - Rbar) + (Fintype.card m * u / 2) • (1 : Matrix m m ℝ) := by abel
  have hb := quad_abs_le_of_entry (E := Rt - Rbar) (ε := u / 2) (by linarith) (fun i j => by
    simpa using hE i j) e
  rw [hdec, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    add_mulVec, dotProduct_add]
  have h1 := hR e
  have h2 := neg_abs_le (e ⬝ᵥ ((Rt - Rbar) *ᵥ e))
  nlinarith

/-- [definition] **Rounding to the grain** `u`: `u·round(x/u)`, the nearest grain point. -/
def roundGrain (u x : ℝ) : ℝ := u * round (x / u)

/-- [proved-standard; formal-checked] Rounding to a grain `u > 0` moves a value by at most `u/2`. -/
theorem abs_roundGrain_sub {u : ℝ} (hu : 0 < u) (x : ℝ) : |roundGrain u x - x| ≤ u / 2 := by
  have hy : roundGrain u x - x = u * ((round (x / u) : ℝ) - x / u) := by
    rw [roundGrain, mul_sub, mul_div_cancel₀ x hu.ne']
  rw [hy, abs_mul, abs_of_pos hu, abs_sub_comm]
  have := abs_sub_round (x / u)
  nlinarith

/-- [proved-standard; formal-checked] Rounding `0` to the grain gives `0`. -/
theorem roundGrain_zero (u : ℝ) : roundGrain u 0 = 0 := by
  simp [roundGrain]

/-- [definition] A matrix rounded entrywise to the grain `u`. -/
def grainRound (u : ℝ) (M : Matrix m m ℝ) : Matrix m m ℝ := M.map (roundGrain u)

omit [Fintype m] [DecidableEq m] in
/-- [proved-standard; formal-checked] Entrywise rounding is within `u/2` in every entry. -/
theorem abs_grainRound_sub {u : ℝ} (hu : 0 < u) (M : Matrix m m ℝ) (i j : m) :
    |grainRound u M i j - M i j| ≤ u / 2 := by
  simpa [grainRound] using abs_roundGrain_sub hu (M i j)

omit [Fintype m] [DecidableEq m] in
/-- [proved-standard; formal-checked] Rounding the zero matrix gives the zero matrix. -/
theorem grainRound_zero (u : ℝ) : grainRound u (0 : Matrix m m ℝ) = 0 := by
  ext i j; simp [grainRound, roundGrain_zero]

end Grain

section ComplexGrain

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] **The passive projection of a complex relation at a grain**:
with a certified congruence of `sym (realify W)`, removing `round(R̄) + n u·1`, `R̄` the averaged
clip rounded entrywise to the grain `u > 0` and `n = card n`, leaves a passive relation. -/
theorem passive_complex_at_grain (W : Matrix n n ℂ) {P Pinv : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    {d : n ⊕ n → ℝ} (hP : P * Pinv = 1) (hD : Pᵀ * symPartK (realify W) * P = Matrix.diagonal d)
    {u : ℝ} (hu : 0 < u) (e : n ⊕ n → ℝ) :
    e ⬝ᵥ ((realify W - (grainRound u (average realifyI (clipRemoved Pinv d)) +
      (Fintype.card n * u) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))) *ᵥ e) ≤ 0 := by
  have hcard : (Fintype.card n * u : ℝ) = Fintype.card (n ⊕ n) * u / 2 := by
    rw [Fintype.card_sum]; push_cast; ring
  rw [hcard]
  exact grain_passive hu.le (averaged_clip_passive W hP hD)
    (abs_grainRound_sub hu _) e

/-- [proved-derived; formal-checked] **The removed part at the grain is positive semidefinite.** -/
theorem passive_complex_at_grain_removed_psd {Pinv : Matrix (n ⊕ n) (n ⊕ n) ℝ} {d : n ⊕ n → ℝ}
    {u : ℝ} (hu : 0 < u) (e : n ⊕ n → ℝ) :
    0 ≤ e ⬝ᵥ ((grainRound u (average realifyI (clipRemoved Pinv d)) +
      (Fintype.card n * u) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) *ᵥ e) := by
  have hcard : (Fintype.card n * u : ℝ) = Fintype.card (n ⊕ n) * u / 2 := by
    rw [Fintype.card_sum]; push_cast; ring
  rw [hcard]
  exact grain_removed_psd hu.le (average_psd _ (clipRemoved_psd Pinv d))
    (abs_grainRound_sub hu _) e

/-- [proved-derived; formal-checked] **On a passive relation the grain step removes the shift
alone**: the averaged clip is `0`, rounds to `0`, and the removed part is `n u·1`. -/
theorem grain_removed_of_passive (W : Matrix n n ℂ) {P Pinv : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    {d : n ⊕ n → ℝ} (hD : Pᵀ * symPartK (realify W) * P = Matrix.diagonal d)
    (hW : ∀ e, e ⬝ᵥ (realify W *ᵥ e) ≤ 0) (u : ℝ) :
    grainRound u (average realifyI (clipRemoved Pinv d)) +
      (Fintype.card n * u) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (Fintype.card n * u) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  rw [averaged_clip_of_passive realifyI hD hW, grainRound_zero, zero_add]

end ComplexGrain

/-! ## 3. The scalar shift -/

section Shift

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- [proved-standard; formal-checked] **Gershgorin on the form**: for symmetric `S` with every row
sum `Σ_j |S_ij| ≤ G`, `⟨e, S e⟩ ≤ G|e|²`. -/
theorem gershgorin_quad {S : Matrix m m ℝ} (hS : Sᵀ = S) {G : ℝ} (hG : ∀ i, ∑ j, |S i j| ≤ G)
    (e : m → ℝ) : e ⬝ᵥ (S *ᵥ e) ≤ G * (e ⬝ᵥ e) := by
  have hq : e ⬝ᵥ (S *ᵥ e) = ∑ i, ∑ j, e i * S i j * e j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hpt : ∀ i j, e i * S i j * e j ≤ (|S i j| * e i ^ 2 + |S i j| * e j ^ 2) / 2 := by
    intro i j
    have h2 : e i * S i j * e j ≤ |S i j| * (|e i| * |e j|) := by
      have := le_abs_self (e i * S i j * e j)
      rw [abs_mul, abs_mul] at this
      linarith
    have h3 : |e i| * |e j| ≤ (e i ^ 2 + e j ^ 2) / 2 := by
      nlinarith [sq_nonneg (|e i| - |e j|), sq_abs (e i), sq_abs (e j)]
    nlinarith [abs_nonneg (S i j)]
  have hB : ∑ i, ∑ j, |S i j| * e j ^ 2 = ∑ i, ∑ j, |S i j| * e i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := congrFun (congrFun hS i) j
    rw [transpose_apply] at h
    rw [h]
  have hA : ∑ i, ∑ j, |S i j| * e i ^ 2 ≤ G * (e ⬝ᵥ e) := by
    calc ∑ i, ∑ j, |S i j| * e i ^ 2 = ∑ i, (∑ j, |S i j|) * e i ^ 2 := by
          simp [Finset.sum_mul]
      _ ≤ ∑ i, G * e i ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hG i) (sq_nonneg _)
      _ = G * (e ⬝ᵥ e) := by simp [dotProduct, Finset.mul_sum, sq]
  have hsplit : ∑ i, ∑ j, (|S i j| * e i ^ 2 + |S i j| * e j ^ 2) / 2 =
      ((∑ i, ∑ j, |S i j| * e i ^ 2) + ∑ i, ∑ j, |S i j| * e j ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  calc e ⬝ᵥ (S *ᵥ e) = ∑ i, ∑ j, e i * S i j * e j := hq
    _ ≤ ∑ i, ∑ j, (|S i j| * e i ^ 2 + |S i j| * e j ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = ((∑ i, ∑ j, |S i j| * e i ^ 2) + ∑ i, ∑ j, |S i j| * e j ^ 2) / 2 := hsplit
    _ ≤ G * (e ⬝ᵥ e) := by rw [hB]; linarith

/-- [definition] The Gershgorin bound `max_i Σ_j |S_ij|`. -/
def gershgorin [Nonempty m] (S : Matrix m m ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, |S i j|

omit [DecidableEq m] in
/-- [proved-standard; formal-checked] Every row sum is at most the Gershgorin bound. -/
theorem le_gershgorin [Nonempty m] (S : Matrix m m ℝ) (i : m) : ∑ j, |S i j| ≤ gershgorin S :=
  Finset.le_sup' (fun i => ∑ j, |S i j|) (Finset.mem_univ i)

/-- [definition] **The shifts that make `W` passive**: the naturals `τ` with `W − τ·1` passive. -/
def shiftSet (W : Matrix m m ℝ) : Set ℕ :=
  {τ | ∀ e, e ⬝ᵥ ((W - (τ : ℝ) • (1 : Matrix m m ℝ)) *ᵥ e) ≤ 0}

/-- [proved-derived; formal-checked] `τ` is a passive shift exactly when `⟨e, W e⟩ ≤ τ|e|²`. -/
theorem mem_shiftSet {W : Matrix m m ℝ} {τ : ℕ} :
    τ ∈ shiftSet W ↔ ∀ e, e ⬝ᵥ (W *ᵥ e) ≤ τ * (e ⬝ᵥ e) := by
  simp only [shiftSet, Set.mem_ofPred_eq, quad_sub_smul_one, sub_nonpos]

/-- [proved-derived; formal-checked] A bound `⟨e, W e⟩ ≤ c|e|²` makes `⌈c⌉₊` a passive shift. -/
theorem ceil_mem_shiftSet {W : Matrix m m ℝ} {c : ℝ} (hc : ∀ e, e ⬝ᵥ (W *ᵥ e) ≤ c * (e ⬝ᵥ e)) :
    ⌈c⌉₊ ∈ shiftSet W := by
  rw [mem_shiftSet]
  intro e
  have h1 := hc e
  have h2 := Nat.le_ceil c
  have h3 := dot_self_nonneg e
  nlinarith

/-- [proved-derived; formal-checked] Some natural shift makes `W` passive (Gershgorin on `sym W`). -/
theorem shiftSet_nonempty (W : Matrix m m ℝ) : (shiftSet W).Nonempty := by
  refine ⟨_, ceil_mem_shiftSet (c := ∑ i, ∑ j, |symPartK W i j|) fun e => ?_⟩
  rw [← quad_symPartK W e]
  refine gershgorin_quad (symPartK_transpose W) (fun i => ?_) e
  exact Finset.single_le_sum (f := fun i => ∑ j, |symPartK W i j|)
    (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- [definition] **The minimal scalar shift** `τ*`: the least natural `τ` with `W − τ·1` passive. -/
def leastShift (W : Matrix m m ℝ) : ℕ := sInf (shiftSet W)

/-- [proved-derived; formal-checked] **The scalar shift is passive**: `W − τ*·1` is passive. -/
theorem leastShift_passive (W : Matrix m m ℝ) (e : m → ℝ) :
    e ⬝ᵥ ((W - (leastShift W : ℝ) • (1 : Matrix m m ℝ)) *ᵥ e) ≤ 0 :=
  Nat.sInf_mem (shiftSet_nonempty W) e

/-- [proved-derived; formal-checked] `τ*` is the least passive shift. -/
theorem leastShift_le {W : Matrix m m ℝ} {τ : ℕ} (hτ : τ ∈ shiftSet W) : leastShift W ≤ τ :=
  Nat.sInf_le hτ

omit [Fintype m] in
/-- [proved-standard; formal-checked] **The shift keeps the skew part**:
`(W − τ·1) − (W − τ·1)ᵀ = W − Wᵀ`. -/
theorem shift_keeps_skew (W : Matrix m m ℝ) (τ : ℝ) :
    (W - τ • (1 : Matrix m m ℝ)) - (W - τ • (1 : Matrix m m ℝ))ᵀ = W - Wᵀ := by
  rw [transpose_sub, transpose_smul, transpose_one]; abel

omit [Fintype m] in
/-- [proved-standard; formal-checked] On a complex relation the real shift keeps the skew-Hermitian
part: `skewPart (W − τ·1) = skewPart W` (`Holon/Reaction.skewPart`). -/
theorem skewPart_shift (W : Matrix m m ℂ) (τ : ℝ) :
    skewPart (W - (τ : ℂ) • (1 : Matrix m m ℂ)) = skewPart W := by
  rw [skewPart, skewPart, conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
  simp only [Complex.star_def, Complex.conj_ofReal]
  congr 1; abel

/-- [proved-derived; formal-checked] `τ*` reads only the symmetric part. -/
theorem leastShift_symPartK (W : Matrix m m ℝ) : leastShift (symPartK W) = leastShift W := by
  have : shiftSet (symPartK W) = shiftSet W := by
    ext τ; simp only [mem_shiftSet, quad_symPartK]
  rw [leastShift, leastShift, this]

/-- [proved-derived; formal-checked] `W − τ*(S)·1` is passive whenever `sym W = S`. -/
theorem shift_passive_of_symPart {W S : Matrix m m ℝ} (hW : symPartK W = S) (e : m → ℝ) :
    e ⬝ᵥ ((W - (leastShift S : ℝ) • (1 : Matrix m m ℝ)) *ᵥ e) ≤ 0 := by
  rw [← hW, leastShift_symPartK]; exact leastShift_passive W e

/-- [proved-derived; formal-checked] **The shift fixes a passive relation**: `τ* = 0` exactly when
`W` is passive. -/
theorem leastShift_eq_zero_iff (W : Matrix m m ℝ) :
    leastShift W = 0 ↔ ∀ e, e ⬝ᵥ (W *ᵥ e) ≤ 0 := by
  constructor
  · intro h e
    have := leastShift_passive W e
    rwa [h, Nat.cast_zero, zero_smul, sub_zero] at this
  · intro h
    have h0 : (0 : ℕ) ∈ shiftSet W := fun e => by
      rw [Nat.cast_zero, zero_smul, sub_zero]; exact h e
    exact Nat.le_zero.mp (leastShift_le h0)

/-- [proved-derived; formal-checked] **The removed part is bounded by the active part**: every `c`
with `⟨e, W e⟩ ≤ c|e|²` has `τ* ≤ ⌈c⌉₊`. -/
theorem leastShift_le_ceil {W : Matrix m m ℝ} {c : ℝ}
    (hc : ∀ e, e ⬝ᵥ (W *ᵥ e) ≤ c * (e ⬝ᵥ e)) : leastShift W ≤ ⌈c⌉₊ :=
  leastShift_le (ceil_mem_shiftSet hc)

/-- [proved-derived; formal-checked] For symmetric `S`, `τ* ≤ ⌈max_i Σ_j |S_ij|⌉₊`. -/
theorem leastShift_le_gershgorin [Nonempty m] {S : Matrix m m ℝ} (hS : Sᵀ = S) :
    leastShift S ≤ ⌈gershgorin S⌉₊ :=
  leastShift_le_ceil (gershgorin_quad hS (le_gershgorin S))

/-- [proved-derived; formal-checked] **`τ*` is reached by the active part**: if `τ* ≥ 1`, some `e`
has `⟨e, W e⟩ > (τ* − 1)|e|²`. -/
theorem leastShift_active {W : Matrix m m ℝ} (h : 1 ≤ leastShift W) :
    ∃ e, ((leastShift W : ℝ) - 1) * (e ⬝ᵥ e) < e ⬝ᵥ (W *ᵥ e) := by
  have hnot : leastShift W - 1 ∉ shiftSet W := Nat.notMem_of_lt_sInf (by unfold leastShift at h ⊢; omega)
  rw [mem_shiftSet] at hnot
  push Not at hnot
  obtain ⟨e, he⟩ := hnot
  refine ⟨e, ?_⟩
  rwa [Nat.cast_sub h, Nat.cast_one] at he

/-- [proved-derived; formal-checked] **Joined to `Holon/Cayley`**: `τ* = ⌈λ_max(sym W)⌉₊`. -/
theorem leastShift_eq_ceil_lamMax [Nonempty m] (W : Matrix m m ℝ) :
    leastShift W = ⌈lamMax W⌉₊ := by
  have hset : ∀ τ : ℕ, τ ∈ shiftSet W ↔ lamMax W ≤ τ := fun τ => shift_passive_iff W τ
  apply le_antisymm
  · exact leastShift_le ((hset _).mpr (Nat.le_ceil _))
  · exact Nat.ceil_le.mpr ((hset _).mp (Nat.sInf_mem (shiftSet_nonempty W)))

/-- [proved-derived; formal-checked] `τ* < λ_max(sym W)₊ + 1`: the shift removes less than one unit
above the active part. -/
theorem leastShift_lt [Nonempty m] (W : Matrix m m ℝ) :
    (leastShift W : ℝ) < max (lamMax W) 0 + 1 := by
  rw [leastShift_eq_ceil_lamMax]
  calc (⌈lamMax W⌉₊ : ℝ) ≤ ⌈max (lamMax W) 0⌉₊ := by
        exact_mod_cast Nat.ceil_mono (le_max_left _ _)
    _ < max (lamMax W) 0 + 1 := Nat.ceil_lt_add_one (le_max_right _ _)

/-- [definition] **The scalar shift at a grain** `u`, counted in grain units: `τ*(u⁻¹ W)`. -/
def grainShift (u : ℝ) (W : Matrix m m ℝ) : ℕ := leastShift (u⁻¹ • W)

/-- [proved-derived; formal-checked] At a grain `u > 0`, `τ` is a passive shift of `u⁻¹ W` exactly
when `W − τu·1` is passive. -/
theorem mem_shiftSet_grain {u : ℝ} (hu : 0 < u) (W : Matrix m m ℝ) (τ : ℕ) :
    τ ∈ shiftSet (u⁻¹ • W) ↔ ∀ e, e ⬝ᵥ ((W - ((τ : ℝ) * u) • (1 : Matrix m m ℝ)) *ᵥ e) ≤ 0 := by
  rw [mem_shiftSet]
  refine forall_congr' fun e => ?_
  rw [quad_sub_smul_one, smul_mulVec, dotProduct_smul, smul_eq_mul, sub_nonpos]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hu.le
    rw [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul] at this
    linarith
  · intro h
    rw [inv_mul_le_iff₀ hu]
    linarith

/-- [proved-derived; formal-checked] **The grain shift is passive**: `W − τ*(u) u·1` is passive. -/
theorem grainShift_passive {u : ℝ} (hu : 0 < u) (W : Matrix m m ℝ) (e : m → ℝ) :
    e ⬝ᵥ ((W - ((grainShift u W : ℝ) * u) • (1 : Matrix m m ℝ)) *ᵥ e) ≤ 0 :=
  (mem_shiftSet_grain hu W _).mp (Nat.sInf_mem (shiftSet_nonempty _)) e

/-- [proved-derived; formal-checked] The grain shift is the least `τ` with `W − τu·1` passive. -/
theorem grainShift_le {u : ℝ} (hu : 0 < u) {W : Matrix m m ℝ} {τ : ℕ}
    (hτ : ∀ e, e ⬝ᵥ ((W - ((τ : ℝ) * u) • (1 : Matrix m m ℝ)) *ᵥ e) ≤ 0) : grainShift u W ≤ τ :=
  leastShift_le ((mem_shiftSet_grain hu W τ).mpr hτ)

/-- [proved-derived; formal-checked] The grain shift is `⌈λ_max(sym W)/u⌉₊` grain units. -/
theorem grainShift_eq_ceil [Nonempty m] {u : ℝ} (hu : 0 < u) (W : Matrix m m ℝ) :
    grainShift u W = ⌈lamMax W / u⌉₊ := by
  have hset : ∀ τ : ℕ, τ ∈ shiftSet (u⁻¹ • W) ↔ lamMax W / u ≤ τ := fun τ => by
    rw [mem_shiftSet_grain hu, shift_passive_iff, div_le_iff₀ hu]
  apply le_antisymm
  · exact leastShift_le ((hset _).mpr (Nat.le_ceil _))
  · exact Nat.ceil_le.mpr ((hset _).mp (Nat.sInf_mem (shiftSet_nonempty _)))

end Shift

/-! ## 4. The comparison with the congruence clip -/

/-- [definition] `S = [[0, 1], [1, 0]]`, eigenvalues `±1`. -/
def clipS : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- [definition] The congruence `P_t = [[t, t], [t⁻¹, −t⁻¹]]`. -/
def clipP (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t, t; t⁻¹, -t⁻¹]

/-- [definition] Its inverse `P_t⁻¹ = ½[[t⁻¹, t], [t⁻¹, −t]]`. -/
def clipPinv (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![t⁻¹ / 2, t / 2; t⁻¹ / 2, -t / 2]

/-- [definition] The congruence's diagonal `d = (2, −2)`. -/
def clipD : Fin 2 → ℝ := ![2, -2]

/-- [proved-derived; formal-checked] `P_t P_t⁻¹ = 1` for `t ≠ 0`. -/
theorem clipP_mul_clipPinv {t : ℝ} (ht : t ≠ 0) : clipP t * clipPinv t = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clipP, clipPinv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] `P_tᵀ (sym S) P_t = diag(2, −2)` for every `t ≠ 0`. -/
theorem clipP_congruence {t : ℝ} (ht : t ≠ 0) :
    (clipP t)ᵀ * symPartK clipS * clipP t = Matrix.diagonal clipD := by
  have hS : clipSᵀ = clipS := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [clipS]
  rw [symPartK_of_transpose_eq hS]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clipP, clipS, clipD, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] The clip removes `½[[t⁻², 1], [1, t²]]`. -/
theorem clipRemoved_clipPinv {t : ℝ} (ht : t ≠ 0) :
    clipRemoved (clipPinv t) clipD = !![t⁻¹ ^ 2 / 2, 1 / 2; 1 / 2, t ^ 2 / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [clipRemoved, clipPinv, clipD, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- [proved-derived; formal-checked] The clip's removed part has trace `(t² + t⁻²)/2`. -/
theorem trace_clipRemoved {t : ℝ} (ht : t ≠ 0) :
    trace (clipRemoved (clipPinv t) clipD) = (t ^ 2 + t⁻¹ ^ 2) / 2 := by
  rw [clipRemoved_clipPinv ht, trace_fin_two]
  simp; ring

/-- [counterexample; formal-checked] **The clip's removed part is unbounded** along the family:
for every bound `B` some `k` has `trace(P_(k+1)⁻ᵀ diag(d₊) P_(k+1)⁻¹) > B`. -/
theorem clip_removed_unbounded (B : ℝ) :
    ∃ k : ℕ, B < trace (clipRemoved (clipPinv ((k : ℝ) + 1)) clipD) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * B)
  refine ⟨k, ?_⟩
  have ht : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [trace_clipRemoved ht]
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg (((k : ℝ) + 1)⁻¹)]

/-- [proved-derived; formal-checked] The scalar shift of `S = [[0, 1], [1, 0]]` is `τ* = 1`. -/
theorem leastShift_clipS : leastShift clipS = 1 := by
  have h1 : (1 : ℕ) ∈ shiftSet clipS := by
    rw [mem_shiftSet]
    intro e
    simp [clipS, dotProduct, mulVec, Fin.sum_univ_two]
    nlinarith [sq_nonneg (e 0 - e 1)]
  have hne : leastShift clipS ≠ 0 := by
    rw [Ne, leastShift_eq_zero_iff]
    intro h
    have := h ![1, 1]
    simp [clipS, dotProduct, mulVec, Fin.sum_univ_two] at this
    norm_num at this
  have := leastShift_le h1
  omega

/-- [proved-derived; formal-checked] The top eigenvalue of `S = [[0, 1], [1, 0]]` lies in `(0, 1]`
(`Holon/Cayley.lamMax`): one positive eigenvalue, at most `1`. -/
theorem lamMax_clipS : 0 < lamMax clipS ∧ lamMax clipS ≤ 1 := by
  have h := leastShift_eq_ceil_lamMax clipS
  rw [leastShift_clipS] at h
  have h1 := Nat.ceil_le.mp h.symm.le
  have h0 : ¬ ⌈lamMax clipS⌉₊ ≤ 0 := by omega
  rw [Nat.ceil_le, Nat.cast_zero, not_le] at h0
  exact ⟨h0, by exact_mod_cast h1⟩

/-- [counterexample; formal-checked] **The scalar shift against the congruence clip.** On
`S = [[0, 1], [1, 0]]` every `P_t`, `t ≠ 0`, is a certified congruence with the same `d = (2, −2)`;
the clip's removed part has trace `(t² + t⁻²)/2`, above every bound along `t = k + 1`, while the
scalar shift is `τ* = 1` and removes `1·1`, of trace `2`. -/
theorem clip_vs_shift_witness :
    (∀ t : ℝ, t ≠ 0 → clipP t * clipPinv t = 1 ∧
      (clipP t)ᵀ * symPartK clipS * clipP t = Matrix.diagonal clipD ∧
      trace (clipRemoved (clipPinv t) clipD) = (t ^ 2 + t⁻¹ ^ 2) / 2) ∧
    (∀ B : ℝ, ∃ k : ℕ, B < trace (clipRemoved (clipPinv ((k : ℝ) + 1)) clipD)) ∧
    leastShift clipS = 1 ∧
    trace ((leastShift clipS : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 2 := by
  refine ⟨fun t ht => ⟨clipP_mul_clipPinv ht, clipP_congruence ht, trace_clipRemoved ht⟩,
    clip_removed_unbounded, leastShift_clipS, ?_⟩
  rw [leastShift_clipS, trace_fin_two]
  simp; norm_num

end Holonics.Holon.ReactionProjection
