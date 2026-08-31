import ElementaryHolonics.Millennium.PositivityIsRealization
import ElementaryHolonics.Millennium.RealizerJoints
import ElementaryHolonics.Millennium.LocalFrame
import ElementaryHolonics.Millennium.HilbertReceiverForm
import ElementaryHolonics.Millennium.HodgeIndex
import ElementaryHolonics.Millennium.MassGap

/-!
# The corollaries of positivity-is-realization, on every form the library owns

`PositivityIsRealization` proved that on a finite-dimensional carrier a receiver form is positive
exactly when it is a pullback of the anchor, definite exactly when the realizer is an injection,
gapped exactly when the realizer is bounded below.  This file runs every receiver form in the
library through it.

**General** (no finite dimension needed where a realizer is given):
* `nullCone_iff_realizer_kernel` — the null cone of a realized form *is* the realizer's kernel;
* `collapse_iff_realizer_kernel` — hence the collapsed population (`Ш`, the blind population of
  `Separation`) is the kernel of the realizer;
* `vacuum_is_realizer_kernel` — a vacuum is a kernel vector, and `theVacuumIsInvisible` follows;
* `not_coercive_of_realizer_kernel` — a nonzero kernel vector refuses the gap;
* `realizer_norm_unique` — any two realizers of one form agree in norm.

**Rows:**
* Hodge: `hodgeForm_not_realized` — the signature-`(1, n−1)` form admits no realizer;
* P vs NP / BSD frame: `frameForm_realized_by_readings` — the joint reading map *is* the realizer
  of the frame operator, and `frameForm_realized_injective_iff_separating`;
* Hilbert transport chain: the Laplacian receiver is realized, realized injectively exactly when
  the harmonic population is trivial, and the nonharmonic receiver is realized bounded below;
* Yang–Mills: `transferForm_realized_iff` — the transfer coupling is realized exactly for
  `|u| ≤ 1`; at `u = 1` it is realized but by no injection; `transferForm_gap_le` bounds every gap
  by `1 − u`; `transferFamily_no_uniform_bound` — the family `u = 1 − 1/(n+1)` is realized at every
  scale and no bounded-below constant survives uniformly (`YangMillsLimit` in realizer form);
* Navier–Stokes: `stokesForm_realized` for every mode family, realized injectively iff every mode is
  nonzero; the Borromean helicity form is realized by the zero map — blindness is realization by
  nothing;
* Riemann: `gramForm_realized_injective_iff_linearIndependent`;
* BSD: `mestreForm_realized_boundedBelow`;
* the anchor itself: `euclidean_realized_by_id`.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.RealizationCorollaries

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.RealizedMillenniumForms
open Soma.Holonics.Millennium.PositivityIsRealization
open Soma.Holonics.Millennium.RealizerJoints
open Soma.Holonics.Millennium.Pivots
open Soma.Holonics.Millennium.HodgeIndex
open Soma.Holonics.Millennium.LocalFrame
open Soma.Holonics.Millennium.HelicityAsLinking
open Soma.Holonics.Millennium.Crossings
open Finset

/-! ## General corollaries -/

section General
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- [proved-derived; formal-checked] **The null cone is the realizer's kernel.** -/
theorem nullCone_iff_realizer_kernel (G : ReceiverForm V) (f : V →L[ℝ] W)
    (hf : ∀ x y, inner ℝ (f x) (f y) = G.B x y) (v : V) :
    G.B v v = 0 ↔ f v = 0 := by
  rw [← hf v v, real_inner_self_eq_norm_sq]
  constructor
  · intro h
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  · intro h
    rw [h]
    simp

/-- [proved-derived; formal-checked] **The collapsed population is the realizer's kernel**: no
reading of the form tells `v` from `0` exactly when the realizer kills `v` — `Ш` as a kernel. -/
theorem collapse_iff_realizer_kernel (G : ReceiverForm V) (f : V →L[ℝ] W)
    (hf : ∀ x y, inner ℝ (f x) (f y) = G.B x y) (v : V) :
    Soma.Holonics.Millennium.Separation.collapseOf G.readings v 0 ↔ f v = 0 := by
  have hpos : G.IsPositive := theRealizedFormIsPositive G f hf
  rw [← G.theNullConeIsTheCollapsedPopulation hpos v]
  exact nullCone_iff_realizer_kernel G f hf v

/-- [proved-derived; formal-checked] A vacuum is a kernel vector of every realizer, and adding it
changes no reading. -/
theorem vacuum_is_realizer_kernel (G : ReceiverForm V) (f : V →L[ℝ] W)
    (hf : ∀ x y, inner ℝ (f x) (f y) = G.B x y) {e : V} (he : G.B e e = 0) :
    f e = 0 ∧ ∀ (v : V) (c : ℝ), G.B (v + c • e) (v + c • e) = G.B v v :=
  ⟨(nullCone_iff_realizer_kernel G f hf e).mp he,
    fun v c => Soma.Holonics.Millennium.MassGap.theVacuumIsInvisible
      (theRealizedFormIsPositive G f hf) he v c⟩

/-- [proved-derived; formal-checked] A nonzero kernel vector of a realizer refuses the gap. -/
theorem not_coercive_of_realizer_kernel (G : ReceiverForm V) (f : V →L[ℝ] W)
    (hf : ∀ x y, inner ℝ (f x) (f y) = G.B x y) {e : V} (hne : e ≠ 0) (he : f e = 0) :
    ¬ G.IsCoercive :=
  Soma.Holonics.Millennium.MassGap.theVacuumRefusesAGlobalGap hne
    ((nullCone_iff_realizer_kernel G f hf e).mpr he)

/-- [proved-derived; formal-checked] Any two realizers of one form agree in norm. -/
theorem realizer_norm_unique {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
    (G : ReceiverForm V) (f : V →L[ℝ] W) (g : V →L[ℝ] W')
    (hf : ∀ x y, inner ℝ (f x) (f y) = G.B x y) (hg : ∀ x y, inner ℝ (g x) (g y) = G.B x y)
    (v : V) : ‖f v‖ = ‖g v‖ := by
  have h : ‖f v‖ ^ 2 = ‖g v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hf, hg]
  have := Real.sqrt_le_sqrt (le_of_eq h)
  have := Real.sqrt_le_sqrt (le_of_eq h.symm)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at *
  linarith

end General

/-! ## Hodge -/

section Hodge
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- [proved-derived; formal-checked] The Hodge-index form admits no realizer once a unit direction
orthogonal to the ample one exists: the signature `(1, n−1)` is not a magnitude. -/
theorem hodgeForm_not_realized {e w : V} (he : ‖e‖ = 1) (hw : ‖w‖ = 1)
    (hew : (inner ℝ e w : ℝ) = 0) :
    ¬ ∃ f : V →L[ℝ] V, ∀ x y, inner ℝ (f x) (f y) = (hodgeForm e).B x y := by
  rw [← positive_iff_realized]
  exact theHodgeFormIsNotPositive he hw hew

end Hodge

/-! ## The frame operator: the joint reading map is its realizer -/

section Frame
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

/-- The joint reading map `v ↦ (⟪rᵢ, v⟫)ᵢ`. -/
def readingsMap (r : ι → V) : V →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun v := WithLp.toLp 2 (fun i => inner ℝ (r i) v)
  map_add' := by
    intro x y
    ext i
    simp [inner_add_right]
  map_smul' := by
    intro c x
    ext i
    simp [inner_smul_right]

/-- [proved-derived; formal-checked] **The joint reading map realizes the frame operator.** -/
theorem frameForm_realized_by_readings [FiniteDimensional ℝ V] (r : ι → V) (x y : V) :
    inner ℝ (LinearMap.toContinuousLinearMap (readingsMap r) x)
        (LinearMap.toContinuousLinearMap (readingsMap r) y) = (frameForm r).B x y := by
  rw [theFrameReading, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [readingsMap]
  ring

/-- [proved-derived; formal-checked] Realized by an injection exactly when the readings
separate. -/
theorem frameForm_realized_injective_iff_separating [FiniteDimensional ℝ V] (r : ι → V) :
    (∃ f : V →L[ℝ] V, (∀ x y, inner ℝ (f x) (f y) = (frameForm r).B x y) ∧
        ∀ x, f x = 0 → x = 0) ↔
      ∀ v : V, (∀ i, (inner ℝ (r i) v : ℝ) = 0) → v = 0 := by
  rw [← positiveDefinite_iff_realized_injective, theFrameFormIsDefiniteIffSeparating]
  exact ⟨fun h => h.2, fun h => ⟨theFrameFormIsPositive r, h⟩⟩

end Frame

/-! ## The Hilbert transport chain -/

section Hilbert
open Soma.Holonics.Millennium.Coupling.HilbertTransportChain
universe u
variable {A B C : Type u}
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable (T : Soma.Holonics.Millennium.Coupling.HilbertTransportChain A B C)

/-- The Laplacian receiver is realized. -/
theorem laplacian_realized :
    ∃ f : B →L[ℝ] B, ∀ x y, inner ℝ (f x) (f y) = T.laplacianReceiverForm.B x y :=
  (positive_iff_realized _).mp T.laplacianReceiverForm_isPositive

/-- Realized by an injection exactly when the harmonic population is trivial. -/
theorem laplacian_realized_injective_iff :
    (∃ f : B →L[ℝ] B, (∀ x y, inner ℝ (f x) (f y) = T.laplacianReceiverForm.B x y) ∧
        ∀ x, f x = 0 → x = 0) ↔ T.harmonic = ⊥ := by
  rw [← positiveDefinite_iff_realized_injective, T.laplacianReceiverForm_isDefinite_iff]
  exact ⟨fun h => h.2, fun h => ⟨T.laplacianReceiverForm_isPositive, h⟩⟩

/-- The nonharmonic receiver is realized bounded below: the gap is a realizer's lower bound. -/
theorem nonharmonic_realized_boundedBelow :
    ∃ (f : T.nonharmonic →L[ℝ] T.nonharmonic) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ≤ ‖f x‖) ∧
      ∀ x y, inner ℝ (f x) (f y) = T.nonharmonicReceiverForm.B x y :=
  (coercive_iff_realized_boundedBelow _).mp T.nonharmonicReceiverForm_isCoercive

end Hilbert

/-! ## Yang–Mills: the transfer coupling -/

/-- The transfer form is positive for `|u| ≤ 1`. -/
theorem transferForm_positive_of_abs_le_one (u : ℝ) (hu : |u| ≤ 1) :
    (transferForm u).IsPositive := by
  intro v
  rw [transferForm_reading]
  have hab : |v.ofLp 0 * v.ofLp 1| ≤ (v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|v.ofLp 0| - |v.ofLp 1|), sq_abs (v.ofLp 0), sq_abs (v.ofLp 1),
      abs_nonneg (v.ofLp 0), abs_nonneg (v.ofLp 1)]
  have hle := neg_abs_le (u * (v.ofLp 0 * v.ofLp 1))
  have habs := abs_mul u (v.ofLp 0 * v.ofLp 1)
  have hprod : |u| * |v.ofLp 0 * v.ofLp 1| ≤ 1 * ((v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2) / 2) :=
    mul_le_mul hu hab (abs_nonneg _) (by norm_num)
  nlinarith [hle, habs, hprod, sq_nonneg (v.ofLp 0), sq_nonneg (v.ofLp 1)]

/-- The transfer form is not positive for `|u| > 1`: the direction `(1, −sign u)` reads
`2 − 2|u| < 0`. -/
theorem transferForm_not_positive_of_one_lt_abs (u : ℝ) (hu : 1 < |u|) :
    ¬ (transferForm u).IsPositive := by
  intro hpos
  rcases le_or_gt 0 u with h0 | h0
  · have := hpos antiDiagonal
    rw [transferForm_reading] at this
    simp [antiDiagonal] at this
    rw [abs_of_nonneg h0] at hu
    linarith
  · have := hpos (WithLp.toLp 2 ![1, 1])
    rw [transferForm_reading] at this
    simp at this
    rw [abs_of_neg h0] at hu
    linarith

/-- [proved-derived; formal-checked] **The transfer coupling is realized exactly for `|u| ≤ 1`.** -/
theorem transferForm_realized_iff (u : ℝ) :
    (∃ f : Carrier 2 →L[ℝ] Carrier 2, ∀ x y, inner ℝ (f x) (f y) = (transferForm u).B x y) ↔
      |u| ≤ 1 := by
  rw [← positive_iff_realized]
  constructor
  · intro hpos
    by_contra h
    exact transferForm_not_positive_of_one_lt_abs u (lt_of_not_ge h) hpos
  · exact transferForm_positive_of_abs_le_one u

/-- [proved-derived; formal-checked] At `u = 1` the coupling is realized, but by no injection: the
balanced direction is in every realizer's kernel. -/
theorem transferForm_one_realized_not_injective :
    (∃ f : Carrier 2 →L[ℝ] Carrier 2, ∀ x y, inner ℝ (f x) (f y) = (transferForm 1).B x y) ∧
    ¬ ∃ f : Carrier 2 →L[ℝ] Carrier 2, (∀ x y, inner ℝ (f x) (f y) = (transferForm 1).B x y) ∧
        ∀ x, f x = 0 → x = 0 := by
  constructor
  · exact (transferForm_realized_iff 1).mpr (by norm_num)
  · rw [← positiveDefinite_iff_realized_injective]
    rintro ⟨_, hdef⟩
    have hnull : (transferForm 1).B antiDiagonal antiDiagonal = 0 := by
      rw [transferForm_reading]
      simp [antiDiagonal]
      norm_num
    exact antiDiagonal_ne_zero (hdef antiDiagonal hnull)

/-- The balanced direction reads `2(1 − u)`. -/
theorem transferForm_antiDiagonal (u : ℝ) :
    (transferForm u).B antiDiagonal antiDiagonal = 2 * (1 - u) := by
  rw [transferForm_reading]
  simp [antiDiagonal]
  ring

theorem antiDiagonal_norm_sq : ‖antiDiagonal‖ ^ 2 = 2 := by
  rw [norm_sq_carrier, Fin.sum_univ_two]
  simp [antiDiagonal]
  norm_num

/-- [proved-derived; formal-checked] Every gap of the transfer coupling is at most `1 − u`: the
balanced direction reads `2(1 − u)` at norm² `2`. -/
theorem transferForm_gap_le (u : ℝ) {Δ : ℝ}
    (hΔ : ∀ v, Δ * ‖v‖ ^ 2 ≤ (transferForm u).B v v) : Δ ≤ 1 - u := by
  have h := hΔ antiDiagonal
  rw [transferForm_antiDiagonal, antiDiagonal_norm_sq] at h
  linarith

/-- [proved-derived; formal-checked] **No uniform bound survives the family `u = 1 − 1/(n+1)`.**
Every member is realized; for every `c > 0` some member admits no realizer bounded below by `c`.
`YangMillsLimit` in realizer form: pointwise realization is not uniform realization. -/
theorem transferFamily_no_uniform_bound :
    (∀ n : ℕ, ∃ f : Carrier 2 →L[ℝ] Carrier 2,
      ∀ x y, inner ℝ (f x) (f y) = (transferForm (1 - 1 / ((n : ℝ) + 1))).B x y) ∧
    ∀ c : ℝ, 0 < c → ∃ n : ℕ, ¬ ∃ f : Carrier 2 →L[ℝ] Carrier 2,
      (∀ x, c * ‖x‖ ≤ ‖f x‖) ∧
        ∀ x y, inner ℝ (f x) (f y) = (transferForm (1 - 1 / ((n : ℝ) + 1))).B x y := by
  constructor
  · intro n
    apply (transferForm_realized_iff _).mpr
    have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [abs_le]
    constructor <;> linarith
  · intro c hc
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / c ^ 2)
    refine ⟨n, ?_⟩
    rintro ⟨f, hbelow, hf⟩
    have hw := hbelow antiDiagonal
    have hfw : ‖f antiDiagonal‖ ^ 2 = 2 * (1 - (1 - 1 / ((n : ℝ) + 1))) := by
      rw [← real_inner_self_eq_norm_sq, hf, transferForm_antiDiagonal]
    have hw2 : (c * ‖antiDiagonal‖) ^ 2 ≤ ‖f antiDiagonal‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hw 2
    rw [mul_pow, antiDiagonal_norm_sq, hfw] at hw2
    have hlt : 1 / ((n : ℝ) + 1) < c ^ 2 := by
      have hn' : (1 : ℝ) / c ^ 2 < n := hn
      have hc2 : 0 < c ^ 2 := by positivity
      rw [div_lt_iff₀ hc2] at hn'
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hn', hc2]
    linarith

/-! ## Navier–Stokes -/

theorem stokesForm_positive {n : ℕ} (k : Fin n → ℝ) : (stokesForm k).IsPositive := by
  intro v
  rw [stokesForm_reading]
  positivity

/-- Every Stokes form is realized. -/
theorem stokesForm_realized_all {n : ℕ} (k : Fin n → ℝ) :
    ∃ f : Carrier n →L[ℝ] Carrier n, ∀ x y, inner ℝ (f x) (f y) = (stokesForm k).B x y :=
  (positive_iff_realized _).mp (stokesForm_positive k)

theorem stokesForm_definite_iff {n : ℕ} (k : Fin n → ℝ) :
    (stokesForm k).IsDefinite ↔ ∀ i, k i ≠ 0 := by
  constructor
  · intro hdef i hi
    have hnull : (stokesForm k).B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0 := by
      rw [stokesForm_reading]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hji : j = i
      · subst hji
        rw [hi]
        ring
      · simp [EuclideanSpace.single_apply, hji]
    have := hdef _ hnull
    have h1 := congrArg (fun x : Carrier n => x.ofLp i) this
    simp at h1
  · intro hk v hv
    rw [stokesForm_reading] at hv
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin n)), k i ^ 2 * v.ofLp i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hv
    ext i
    have := hterms i (Finset.mem_univ i)
    have hki : k i ^ 2 ≠ 0 := pow_ne_zero 2 (hk i)
    have : v.ofLp i ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hki
      · exact h
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- [proved-derived; formal-checked] The Stokes form is realized by an injection exactly when every
mode is nonzero. -/
theorem stokesForm_realized_injective_iff {n : ℕ} (k : Fin n → ℝ) :
    (∃ f : Carrier n →L[ℝ] Carrier n, (∀ x y, inner ℝ (f x) (f y) = (stokesForm k).B x y) ∧
        ∀ x, f x = 0 → x = 0) ↔ ∀ i, k i ≠ 0 := by
  rw [← positiveDefinite_iff_realized_injective, stokesForm_definite_iff]
  exact ⟨fun h => h.2, fun h => ⟨stokesForm_positive k, h⟩⟩

/-- [proved-derived; formal-checked] **Blindness is realization by nothing**: the Borromean helicity
form is realized by the zero map. -/
theorem helicityForm_borromean_realized_by_zero :
    ∀ x y : Carrier 3, inner ℝ ((0 : Carrier 3 →L[ℝ] Carrier 3) x)
      ((0 : Carrier 3 →L[ℝ] Carrier 3) y) = (helicityForm borromeanTable).B x y := by
  intro x y
  simp only [ContinuousLinearMap.zero_apply, inner_zero_left]
  rw [ReceiverForm.B]
  simp only [helicityForm, matrixForm, LinearMap.coe_toContinuousLinearMap']
  rw [PiLp.inner_apply]
  simp [matrixMap_apply, linkingArray, theLinkingReadingsVanishWhileSixCrossingsStand.1]

/-! ## Riemann, BSD, and the anchor -/

/-- [proved-derived; formal-checked] A Gram of readings is realized by an injection exactly when
the readings are linearly independent. -/
theorem gramForm_realized_injective_iff_linearIndependent {n m : ℕ} (w : Fin n → Carrier m) :
    (∃ f : Carrier n →L[ℝ] Carrier n, (∀ x y, inner ℝ (f x) (f y) = (gramForm w).B x y) ∧
        ∀ x, f x = 0 → x = 0) ↔ LinearIndependent ℝ w := by
  rw [← positiveDefinite_iff_realized_injective, gramForm_definite_iff_linearIndependent]
  exact ⟨fun h => h.2, fun h => ⟨gramForm_positive w, h⟩⟩

/-- The rank-12 height form is realized bounded below: the regulator's gap is a realizer's lower
bound. -/
theorem mestreForm_realized_boundedBelow :
    ∃ (f : Carrier 12 →L[ℝ] Carrier 12) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ≤ ‖f x‖) ∧
      ∀ x y, inner ℝ (f x) (f y) = mestreForm.B x y :=
  (coercive_iff_realized_boundedBelow _).mp mestreForm_coercive

/-- The anchor is realized by the identity, bounded below by one. -/
theorem euclidean_realized_by_id {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    (∀ x, 1 * ‖x‖ ≤ ‖(ContinuousLinearMap.id ℝ V) x‖) ∧
      ∀ x y : V, inner ℝ ((ContinuousLinearMap.id ℝ V) x) ((ContinuousLinearMap.id ℝ V) y) =
        (euclidean V).B x y :=
  ⟨fun x => by simp, fun x y => rfl⟩

section Audit

#print axioms collapse_iff_realizer_kernel
#print axioms hodgeForm_not_realized
#print axioms frameForm_realized_by_readings
#print axioms laplacian_realized_injective_iff
#print axioms transferForm_realized_iff
#print axioms transferFamily_no_uniform_bound
#print axioms stokesForm_realized_injective_iff
#print axioms helicityForm_borromean_realized_by_zero
#print axioms gramForm_realized_injective_iff_linearIndependent

end Audit

end Soma.Holonics.Millennium.RealizationCorollaries
