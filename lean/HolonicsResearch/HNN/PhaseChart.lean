import Mathlib
import HolonicsResearch.Compression.Landmark.SiteIsolation
import HolonicsResearch.HNN.FoundingAtZero

/-!
# The level's phase chart, its founding at zero and its clock

The design record of November 13 (`research/records/2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_…`,
§4.5 and §4.9; atlas `tower.field-scale-packets`) charts an epoch's places at their phases in sections of news,
`φ_t = (S_t − S_(a_j))/σ`, by the six real harmonics `1, cos 2πφ, sin 2πφ, cos 4πφ, sin 4πφ, cos 6πφ`, returns the
level's values to the places through the same harmonics (the prolongation), founds the level with the prolongation
at zero, and ticks the level on its own clock `τ¹_j = (S_(a_j) − S_(a_0))/σ`. #410 owes three statements, and this
file states them.

What is proved.

1. **The phases at equal news** (`arrival_const`, `phase_at_equal_news`): where every place carries the same news
   and a section is six places of it, the place `k` after an anchor stands at phase `k/6`.
2. **The chart at those phases** (`cos_sixth`, `sin_sixth`, `harmonic_sixth`, `chart_eq_chartOf`): the six harmonics
   read at the phases `k/6` are the six-by-six table `chartOf (√3/2)`. `sixth_sine_vanishes` is why the sixth
   harmonic is a cosine alone: `sin 6πφ` reads nothing at these phases.
3. **The chart is an invertible change of basis** (`chartOf_mul_transpose`, `chart_mul_transpose`, `chartInv_apply`,
   `chart_mul_chartInv`, `chartInv_mul_chart`, `isUnit_chart_det`): the harmonics are orthogonal over the six places
   with squares `6, 3, 3, 3, 3, 6`, so the chart's inverse is its transpose after the weights
   `1/6, 1/3, 1/3, 1/3, 1/3, 1/6`. On the six places' rows in any real module (`moments`, `rows`, `prolong`,
   `rows_moments`, `moments_rows`, `chartEquiv`, `prolong_weighted_moments`): the six moments and the six rows
   determine each other, and the prolongation of the weighted moments returns the rows.
4. **The founding at zero** (`levelTick`, `levelTick_zero`, `founded_level_keeps_every_face`, `prolong_zero`,
   `founded_chart_level_keeps_every_face`): a field whose step reads its own state with the level's prolongation
   added, the prolongation at zero, is the tick of `HNN/FoundingAtZero`, so every face of the field it is founded on
   is kept at every tick, for every start and every law of the level. Its covectors (`covector_split`,
   `covector_to_level_state_zero`, `covector_to_prolongation`, `founded_face_moves_by_outer_pairing`): a covector `g`
   at the prolonged read reaches the level's state as `g ᵥ* B`, which is zero at the founding, and reaches the
   prolongation as the outer pairing of `g` with the level's state, whatever `B` is. So at the founding the
   prolongation's own entries are the first to receive a covector.
5. **The level's clock** (`clock`, `stride`, `clock_zero`, `stride_eq`, `arrival_sub_eq_sum`, `clock_mul_section`,
   `one_le_stride_of_apart`, `one_le_stride_of_sites`, `one_le_stride_of_claim`, `clock_strictMono`, `index_le_clock`,
   `sum_stride`, `sum_stride_mul_section`): the clock at an anchor is the news since the first anchor in sections,
   a sum of the places' news between them; between two sites of the first round, or of the claim, it advances by one
   or more (the separation of `Compression/Landmark/SiteIsolation`), so it is strictly increasing and stands at or
   past the count of anchors; the strides sum to the clock, and in news to the news between the first anchor and the
   last.

Limits. The chart is proved at the six phases `k/6` alone: the chart of `n` places at phases `k/n` for a general `n`
is not here, and neither is the chart of an epoch whose phases are not equally spaced or whose interior winds (the
record's §4.5 owes that chart). The founding is the block form of `HNN/FoundingAtZero` with the level's write added
to the field's state before its step; widths, releases and the restriction's glue `A` are not modelled, and the
covector statements are for a prolongation linear in the level's state, stated as the two adjoint identities of the
pairing (no derivative of a nonlinear readout). The clock is over `ℝ`; its anchors are any strictly increasing
places that are sites, and nothing here says which places a level takes as its anchors. The Rust
`holonics_engine::field::Scale` and the host's tests are not tied to these statements.

The computational object is the helical pair interaction: a place's phase is its position on the helix of the news
between two anchors, the harmonics are that helix's first windings read as a face, and the level's clock is the
count of whole sections a strand has passed. Of the winding guide's six general objects this touches the helix (the
phase and its harmonics), the faces and placement (the chart as a change of basis of the places' rows) and the tower
thread (the level, its founding and its clock); the pair, cell holonomy and tube stay attached.

Consumers: the atlas rows `tower.field-scale-packets` and `code.site-isolation-landmark` (the stride `κ_j ≥ 1` and
`Σ_j κ_j σ`); #410's box for the level's phase chart and founding.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.PhaseChart

open Real Finset Matrix
open Holonics.Compression.Landmark.SiteIsolation

/-! ## The six harmonics at the phases of equal news -/

/-- [definition] **The level's six real harmonics** at a phase `φ` in sections of news:
`1, cos 2πφ, sin 2πφ, cos 4πφ, sin 4πφ, cos 6πφ`. -/
noncomputable def harmonic (h : Fin 6) (φ : ℝ) : ℝ :=
  ![1, cos (2 * π * φ), sin (2 * π * φ), cos (4 * π * φ), sin (4 * π * φ), cos (6 * π * φ)] h

/-- [proved-standard] Where every place carries the news `c̄`, a place arrives at its count of places times `c̄`. -/
theorem arrival_const (cbar : ℝ) (t : ℕ) : arrival (fun _ => cbar) t = (t + 1) * cbar := by
  simp [arrival]

/-- [proved-derived] **The phases at equal news:** with a section of six places' news, the place `k` after an anchor
`a` stands at phase `k/6`. -/
theorem phase_at_equal_news {cbar : ℝ} (h : cbar ≠ 0) (a k : ℕ) :
    (arrival (fun _ => cbar) (a + k) - arrival (fun _ => cbar) a) / (6 * cbar) = k / 6 := by
  rw [arrival_const, arrival_const]
  push_cast
  field_simp
  ring

/-- [proved-standard] The cosines of the six multiples of a sixth of a turn. -/
theorem cos_sixth (k : Fin 6) :
    cos (((k : ℕ) : ℝ) * (π / 3)) = ![1, 1 / 2, -(1 / 2), -1, -(1 / 2), 1 / 2] k := by
  fin_cases k
  · show cos (((0 : ℕ) : ℝ) * (π / 3)) = 1
    rw [Nat.cast_zero, zero_mul, cos_zero]
  · show cos (((1 : ℕ) : ℝ) * (π / 3)) = 1 / 2
    rw [Nat.cast_one, one_mul, cos_pi_div_three]
  · show cos (((2 : ℕ) : ℝ) * (π / 3)) = -(1 / 2)
    rw [Nat.cast_ofNat, cos_two_mul, cos_pi_div_three]
    norm_num
  · show cos (((3 : ℕ) : ℝ) * (π / 3)) = -1
    rw [Nat.cast_ofNat, show (3 : ℝ) * (π / 3) = π by ring, cos_pi]
  · show cos (((4 : ℕ) : ℝ) * (π / 3)) = -(1 / 2)
    rw [Nat.cast_ofNat, show (4 : ℝ) * (π / 3) = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]
  · show cos (((5 : ℕ) : ℝ) * (π / 3)) = 1 / 2
    rw [Nat.cast_ofNat, show (5 : ℝ) * (π / 3) = 2 * (π / 3) + π by ring, cos_add_pi, cos_two_mul,
      cos_pi_div_three]
    norm_num

/-- [proved-standard] The sines of the six multiples of a sixth of a turn. -/
theorem sin_sixth (k : Fin 6) :
    sin (((k : ℕ) : ℝ) * (π / 3)) = ![0, √3 / 2, √3 / 2, 0, -(√3 / 2), -(√3 / 2)] k := by
  fin_cases k
  · show sin (((0 : ℕ) : ℝ) * (π / 3)) = 0
    rw [Nat.cast_zero, zero_mul, sin_zero]
  · show sin (((1 : ℕ) : ℝ) * (π / 3)) = √3 / 2
    rw [Nat.cast_one, one_mul, sin_pi_div_three]
  · show sin (((2 : ℕ) : ℝ) * (π / 3)) = √3 / 2
    rw [Nat.cast_ofNat, sin_two_mul, sin_pi_div_three, cos_pi_div_three]
    ring
  · show sin (((3 : ℕ) : ℝ) * (π / 3)) = 0
    rw [Nat.cast_ofNat, show (3 : ℝ) * (π / 3) = π by ring, sin_pi]
  · show sin (((4 : ℕ) : ℝ) * (π / 3)) = -(√3 / 2)
    rw [Nat.cast_ofNat, show (4 : ℝ) * (π / 3) = π / 3 + π by ring, sin_add_pi, sin_pi_div_three]
  · show sin (((5 : ℕ) : ℝ) * (π / 3)) = -(√3 / 2)
    rw [Nat.cast_ofNat, show (5 : ℝ) * (π / 3) = 2 * (π / 3) + π by ring, sin_add_pi, sin_two_mul,
      sin_pi_div_three, cos_pi_div_three]
    ring

/-- [proved-standard] The six harmonics at the phase `k/6`, through the cosine and the sine of `k` sixths of a turn
(the second and third windings by the double and triple angle). -/
theorem harmonic_sixth (k : ℝ) (h : Fin 6) :
    harmonic h (k / 6) =
      ![1, cos (k * (π / 3)), sin (k * (π / 3)), 2 * cos (k * (π / 3)) ^ 2 - 1,
        2 * sin (k * (π / 3)) * cos (k * (π / 3)), 4 * cos (k * (π / 3)) ^ 3 - 3 * cos (k * (π / 3))] h := by
  unfold harmonic
  rw [show 2 * π * (k / 6) = k * (π / 3) by ring, show 4 * π * (k / 6) = 2 * (k * (π / 3)) by ring,
    show 6 * π * (k / 6) = 3 * (k * (π / 3)) by ring, cos_two_mul, sin_two_mul, cos_three_mul]

/-- [proved-standard] **The sixth sine reads nothing on the plain clock:** `sin 6πφ` vanishes at every phase `k/6`,
which is why the sixth harmonic is a cosine alone. -/
theorem sixth_sine_vanishes (k : ℕ) : sin (6 * π * ((k : ℝ) / 6)) = 0 := by
  rw [show 6 * π * ((k : ℝ) / 6) = k * π by ring]
  exact sin_nat_mul_pi k

/-- [definition] **The chart at equal news:** the harmonic `h` read at the place `k` of a section of six places,
at its phase `k/6`. -/
noncomputable def chart : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun h k => harmonic h (((k : ℕ) : ℝ) / 6)

/-- [proved-standard] The chart's entry. -/
theorem chart_apply (h k : Fin 6) : chart h k = harmonic h (((k : ℕ) : ℝ) / 6) := rfl

/-- [definition] The chart's table with `s` in the place of `√3/2`: harmonics down, places across. -/
noncomputable def chartOf (s : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1 / 2, -(1 / 2), -1, -(1 / 2), 1 / 2;
     0, s, s, 0, -s, -s;
     1, -(1 / 2), -(1 / 2), 1, -(1 / 2), -(1 / 2);
     0, s, -s, 0, s, -s;
     1, -1, 1, -1, 1, -1]

/-- [proved-derived] **The chart at equal news is its table** with `s = √3/2`. -/
theorem chart_eq_chartOf : chart = chartOf (√3 / 2) := by
  ext h k
  rw [chart_apply, harmonic_sixth, cos_sixth, sin_sixth]
  fin_cases k <;> fin_cases h <;> norm_num [chartOf] <;> ring

/-- [proved-derived] **The harmonics are orthogonal over the six places**, with squares `6, 3, 3, 3, 3, 6`, for any
`s` with `s² = 3/4`. -/
theorem chartOf_mul_transpose (s : ℝ) (hs : s * s = 3 / 4) :
    chartOf s * (chartOf s)ᵀ = Matrix.diagonal ![6, 3, 3, 3, 3, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chartOf, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;> linarith

/-- [proved-derived] **The chart's rows are orthogonal:** `chart · chartᵀ = diag(6, 3, 3, 3, 3, 6)`. -/
theorem chart_mul_transpose : chart * chartᵀ = Matrix.diagonal ![6, 3, 3, 3, 3, 6] := by
  rw [chart_eq_chartOf]
  refine chartOf_mul_transpose _ ?_
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- [definition] **The chart's inverse:** its transpose after the harmonics' weights `1/6, 1/3, 1/3, 1/3, 1/3, 1/6`. -/
noncomputable def chartInv : Matrix (Fin 6) (Fin 6) ℝ :=
  chartᵀ * Matrix.diagonal ![1 / 6, 1 / 3, 1 / 3, 1 / 3, 1 / 3, 1 / 6]

/-- [proved-standard] The inverse's entry: the harmonic `h` at the place `k`, times that harmonic's weight. -/
theorem chartInv_apply (k h : Fin 6) :
    chartInv k h = chart h k * (![1 / 6, 1 / 3, 1 / 3, 1 / 3, 1 / 3, 1 / 6] : Fin 6 → ℝ) h := by
  rw [chartInv, Matrix.mul_diagonal, Matrix.transpose_apply]

/-- [proved-derived] **The chart is invertible** (from the right). -/
theorem chart_mul_chartInv : chart * chartInv = 1 := by
  rw [chartInv, ← Matrix.mul_assoc, chart_mul_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- [proved-derived] **The chart is invertible** (from the left). -/
theorem chartInv_mul_chart : chartInv * chart = 1 :=
  mul_eq_one_comm.mp chart_mul_chartInv

/-- [proved-derived] The chart's determinant is a unit. -/
theorem isUnit_chart_det : IsUnit chart.det :=
  Matrix.isUnit_det_of_right_inverse chart_mul_chartInv

/-! ## The six places' rows and their six moments -/

section Rows

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- [definition] **An epoch's moments** at equal news: the harmonic `h` summed over the six places' rows. -/
noncomputable def moments (x : Fin 6 → E) : Fin 6 → E := fun h => ∑ k, chart h k • x k

/-- [definition] The rows that hold given moments. -/
noncomputable def rows (m : Fin 6 → E) : Fin 6 → E := fun k => ∑ h, chartInv k h • m h

/-- [definition] **The prolongation** through the same chart: the place `k` receives `Σ_h h_h(φ_k) v_h`. -/
noncomputable def prolong (v : Fin 6 → E) : Fin 6 → E := fun k => ∑ h, chart h k • v h

/-- [proved-standard] Two tables whose product is one undo each other on rows in any module. -/
theorem sum_smul_sum_of_mul_eq_one {A B : Matrix (Fin 6) (Fin 6) ℝ} (h : A * B = 1) (x : Fin 6 → E) (k : Fin 6) :
    ∑ i, A k i • ∑ j, B i j • x j = x k := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

/-- [proved-derived] **The rows are read back from their moments.** -/
theorem rows_moments (x : Fin 6 → E) : rows (moments x) = x :=
  funext fun k => sum_smul_sum_of_mul_eq_one chartInv_mul_chart x k

/-- [proved-derived] **The moments are read back from their rows.** -/
theorem moments_rows (m : Fin 6 → E) : moments (rows m) = m :=
  funext fun h => sum_smul_sum_of_mul_eq_one chart_mul_chartInv m h

/-- [proved-derived] **The chart is an invertible change of basis of the six places' rows:** the linear equivalence
between six rows and their six moments. -/
noncomputable def chartEquiv : (Fin 6 → E) ≃ₗ[ℝ] (Fin 6 → E) where
  toFun := moments
  invFun := rows
  map_add' x y := by
    funext h
    simp [moments, smul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext h
    simp only [moments, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  left_inv := rows_moments
  right_inv := moments_rows

/-- [proved-derived] **The prolongation of the weighted moments returns the rows:** the return through the same
chart inverts the restriction once each harmonic is weighed by `1/6, 1/3, 1/3, 1/3, 1/3, 1/6`. -/
theorem prolong_weighted_moments (x : Fin 6 → E) :
    prolong (fun h => (![1 / 6, 1 / 3, 1 / 3, 1 / 3, 1 / 3, 1 / 6] : Fin 6 → ℝ) h • moments x h) = x := by
  have h := rows_moments x
  rw [← h]
  funext k
  simp only [prolong, rows, chartInv_apply, mul_smul, h]

/-- [proved-standard] The prolongation of nothing is nothing. -/
theorem prolong_zero : prolong (0 : Fin 6 → E) = 0 := by
  funext k
  simp [prolong]

end Rows

/-! ## The founding at zero -/

section Founding

variable {U V F : Type*}

/-- [definition] **A tick of a field with a level:** the field steps from its own state with the level's
prolongation added, and the level steps from both. -/
def levelTick [Add U] (f : U → U) (g : U → V → V) (P : V → U) (p : U × V) : U × V :=
  (f (p.1 + P p.2), g p.1 p.2)

/-- [proved-derived] With the prolongation at zero the tick is the founding tick of `HNN/FoundingAtZero`. -/
theorem levelTick_zero [AddZeroClass U] (f : U → U) (g : U → V → V) :
    levelTick f g (0 : V → U) = FoundingAtZero.tick f g := by
  funext p
  simp [levelTick, FoundingAtZero.tick]

/-- [proved-derived] **A level founded with its prolongation at zero reads every face of the field it is founded
on:** after any count of ticks, from any start of the level and under any law of the level, a readout of the field's
state is the old field's. -/
theorem founded_level_keeps_every_face [AddZeroClass U] (f : U → U) (g : U → V → V) (read : U → F) (u : U) (v : V)
    (n : ℕ) : read ((levelTick f g (0 : V → U))^[n] (u, v)).1 = read (f^[n] u) := by
  rw [levelTick_zero]
  exact FoundingAtZero.faces_kept f g read u v n

/-- [proved-derived] The same for the level's own chart: the prolongation `prolong (B r̂(y) + b)` founded with
`B = 0` and `b = 0` keeps every face of the six places' rows. -/
theorem founded_chart_level_keeps_every_face {E R : Type*} [AddCommGroup E] [Module ℝ E]
    (f : (Fin 6 → E) → (Fin 6 → E)) (g : (Fin 6 → E) → V → V) (rhat : V → R) (read : (Fin 6 → E) → F)
    (u : Fin 6 → E) (v : V) (n : ℕ) :
    read ((levelTick f g (fun y => prolong ((0 : R → Fin 6 → E) (rhat y) + 0)))^[n] (u, v)).1 = read (f^[n] u) := by
  have h : (fun y : V => prolong ((0 : R → Fin 6 → E) (rhat y) + 0)) = 0 := by
    funext y
    simp [prolong_zero]
  rw [h]
  exact founded_level_keeps_every_face f g read u v n

end Founding

section Covector

variable {m n : Type*} [Fintype m] [Fintype n]

/-- [proved-standard] **A covector at the prolonged read splits** into its pairing with the field's state and the
pairing of `g ᵥ* B` with the level's state. -/
theorem covector_split (g x : m → ℝ) (B : Matrix m n ℝ) (y : n → ℝ) :
    g ⬝ᵥ (x + B *ᵥ y) = g ⬝ᵥ x + (g ᵥ* B) ⬝ᵥ y := by
  rw [dotProduct_add, Matrix.dotProduct_mulVec]

omit [Fintype n] in
/-- [proved-standard] **At the founding no covector reaches the level's state:** `g ᵥ* 0 = 0`. -/
theorem covector_to_level_state_zero (g : m → ℝ) : g ᵥ* (0 : Matrix m n ℝ) = 0 :=
  Matrix.vecMul_zero g

/-- [proved-standard] **The covector that reaches the prolongation is the outer pairing** of the covector at the
read with the level's state, whatever the prolongation holds. -/
theorem covector_to_prolongation (g : m → ℝ) (B : Matrix m n ℝ) (y : n → ℝ) :
    g ⬝ᵥ (B *ᵥ y) = ∑ i, ∑ j, Matrix.vecMulVec g y i j * B i j := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived] So from the founding a change `δB` of the prolongation moves the pairing at the read by its
pairing with the outer product, for every state of the level. -/
theorem founded_face_moves_by_outer_pairing (g x : m → ℝ) (δB : Matrix m n ℝ) (y : n → ℝ) :
    g ⬝ᵥ (x + ((0 : Matrix m n ℝ) + δB) *ᵥ y) - g ⬝ᵥ (x + (0 : Matrix m n ℝ) *ᵥ y) =
      ∑ i, ∑ j, Matrix.vecMulVec g y i j * δB i j := by
  rw [zero_add, Matrix.zero_mulVec, add_zero, dotProduct_add, add_sub_cancel_left, covector_to_prolongation]

end Covector

/-! ## The level's clock -/

section Clock

variable {c : ℕ → ℝ} {σ : ℝ} {a : ℕ → ℕ}

/-- [definition] **The level's clock** at its anchor `a_j`: the news since the first anchor, in sections,
`τ_j = (S_(a_j) − S_(a_0))/σ`. -/
noncomputable def clock (c : ℕ → ℝ) (σ : ℝ) (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  (arrival c (a j) - arrival c (a 0)) / σ

/-- [definition] The level's stride between two anchors, `κ_j = τ_(j+1) − τ_j`. -/
noncomputable def stride (c : ℕ → ℝ) (σ : ℝ) (a : ℕ → ℕ) (j : ℕ) : ℝ := clock c σ a (j + 1) - clock c σ a j

/-- [proved-standard] The clock starts at zero. -/
theorem clock_zero : clock c σ a 0 = 0 := by
  simp [clock]

/-- [proved-standard] A stride is the news between its two anchors in sections. -/
theorem stride_eq (j : ℕ) : stride c σ a j = (arrival c (a (j + 1)) - arrival c (a j)) / σ := by
  unfold stride clock
  ring

/-- [proved-standard] **The news between two places** is the sum of the news of the places after the first up to
the second. -/
theorem arrival_sub_eq_sum (c : ℕ → ℝ) {s t : ℕ} (h : s ≤ t) :
    arrival c t - arrival c s = ∑ v ∈ Finset.Ioc s t, c v := by
  induction t, h using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rw [Finset.sum_Ioc_succ_top hst, ← ih, arrival_succ]
    ring

/-- [proved-standard] **The clock is the news between anchors in sections.** -/
theorem clock_mul_section (hσ : σ ≠ 0) (j : ℕ) : clock c σ a j * σ = arrival c (a j) - arrival c (a 0) := by
  unfold clock
  field_simp

/-- [proved-derived] A stride between two anchors a section or more apart is one or more. -/
theorem one_le_stride_of_apart (hσ : 0 < σ) {j : ℕ} (h : σ ≤ arrival c (a (j + 1)) - arrival c (a j)) :
    1 ≤ stride c σ a j := by
  rw [stride_eq, le_div_iff₀ hσ, one_mul]
  exact h

/-- [proved-derived] **The level's rates are at least one between sites:** anchors that are sites of the first
round advance the clock by one or more. -/
theorem one_le_stride_of_sites (hc : ∀ v, 0 ≤ c v) (hσ : 0 < σ) (ha : StrictMono a) {N : ℕ}
    (hs : ∀ j, Site c N σ (a j)) (j : ℕ) : 1 ≤ stride c σ a j :=
  one_le_stride_of_apart hσ (sites_apart_ordered hc (hs j) (hs (j + 1)) (ha (Nat.lt_succ_self j)))

/-- [proved-derived] The same for anchors that are sites of the claim. -/
theorem one_le_stride_of_claim (hc : ∀ v, 0 ≤ c v) (hσ : 0 < σ) (ha : StrictMono a) {N : ℕ} {G : ℕ → Prop}
    (hG : IsClaim c N σ G) (hs : ∀ j, G (a j)) (j : ℕ) : 1 ≤ stride c σ a j := by
  have hlt : a j < a (j + 1) := ha (Nat.lt_succ_self j)
  have h := claim_sites_apart hG (hs j) (hs (j + 1)) hlt.ne
  rw [dist_of_le hc hlt.le] at h
  exact one_le_stride_of_apart hσ h

/-- [proved-derived] **The clock is strictly increasing** where its strides are one or more. -/
theorem clock_strictMono (h : ∀ j, 1 ≤ stride c σ a j) : StrictMono (clock c σ a) :=
  strictMono_nat_of_lt_succ fun j => by
    have hj := h j
    unfold stride at hj
    linarith

/-- [proved-derived] **The clock stands at or past the count of anchors:** `j ≤ τ_j`. -/
theorem index_le_clock (h : ∀ j, 1 ≤ stride c σ a j) (j : ℕ) : (j : ℝ) ≤ clock c σ a j := by
  induction j with
  | zero => simp [clock_zero]
  | succ j ih =>
    have hj := h j
    unfold stride at hj
    push_cast
    linarith

/-- [proved-standard] **The strides sum to the clock.** -/
theorem sum_stride (c : ℕ → ℝ) (σ : ℝ) (a : ℕ → ℕ) (J : ℕ) : ∑ j ∈ range J, stride c σ a j = clock c σ a J := by
  unfold stride
  rw [Finset.sum_range_sub, clock_zero, sub_zero]

/-- [proved-standard] **The strides in news sum to the news between the first anchor and the last**,
`Σ_j κ_j σ = S_(a_J) − S_(a_0)`. -/
theorem sum_stride_mul_section (hσ : σ ≠ 0) (J : ℕ) :
    (∑ j ∈ range J, stride c σ a j) * σ = arrival c (a J) - arrival c (a 0) := by
  rw [sum_stride, clock_mul_section hσ]

end Clock

end Holonics.HNN.PhaseChart
