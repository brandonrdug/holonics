import ElementaryHolonics.Mathematics.PowerSeriesExactDilation
import ElementaryHolonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver
import ElementaryHolonics.Millennium.FamilyTunnellJacobiEulerCube

/-!
# Exact dilation of the Tunnell theta charts

The scale change `x ↦ 2x`, `x² ↦ 4x²` is retained as a bijection of finite
root populations.  Consequently substitution `X ↦ X⁴` transports the two
Jacobi unit specializations to the even quarter-residue faces `A+C` and
`A-C`.  No analytic theta transformation or packaged modular-form theorem is
assumed.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellThetaDilation

open Finset
open PowerSeries
open Soma.Holonics.Mathematics.PowerSeriesExactDilation
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver
open Soma.Holonics.Millennium.FamilyTunnellJacobiProductReceiver
open Soma.Holonics.Millennium.FamilyTunnellJacobiEulerCube
open Soma.Holonics.Mathematics.JacobiEulerCubeStabilization

/-- The exact fourth-power exponent chart. -/
def fourDilate : PowerSeries ℤ →+* PowerSeries ℤ :=
  exactDilateHom 4 (by decide)

@[simp] theorem coeff_fourDilate (F : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (fourDilate F) =
      if 4 ∣ n then PowerSeries.coeff (n / 4) F else 0 := by
  exact coeff_exactDilate 4 (by decide) F n

/-- Exact dilation is continuous in the coefficient topology because every
target coordinate is either one source coordinate or the zero coordinate. -/
theorem fourDilate_continuous :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Continuous fourDilate := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [continuous_pi_iff]
  intro i
  change Continuous (fun F : PowerSeries ℤ => fourDilate F i)
  have heval : (fun F : PowerSeries ℤ => fourDilate F i) =
      (fun F => PowerSeries.coeff (i ()) (fourDilate F)) := by
    funext F
    change fourDilate F i = fourDilate F (Finsupp.single () (i ()))
    have hi : i = Finsupp.single () (i ()) := by
      ext
      simp
    rw [hi]
    simp
  rw [heval]
  by_cases h : 4 ∣ i ()
  · have hc :=
      PowerSeries.WithPiTopology.continuous_coeff ℤ ((i ()) / 4)
    convert hc using 1
    funext F
    rw [coeff_fourDilate, if_pos h]
  · have hz : (fun F : PowerSeries ℤ =>
        PowerSeries.coeff (i ()) (fourDilate F)) = fun _ => 0 := by
      funext F
      rw [coeff_fourDilate, if_neg h]
    rw [hz]
    fun_prop

/-- Dilation commutes with every admitted complete Pochhammer product.  The
proof maps the whole factor population through the continuous ring receiver;
it does not assume a symbolic substitution rule for infinite products. -/
theorem fourDilate_qPochhammerInf (A Q : PowerSeries ℤ)
    (hm : letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
      Multipliable (fun n => 1 - A * Q ^ n)) :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    fourDilate (qPochhammerInf A Q) =
      qPochhammerInf (fourDilate A) (fourDilate Q) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  letI : T2Space (PowerSeries ℤ) :=
    PowerSeries.WithPiTopology.instT2Space ℤ
  have hcont : Continuous fourDilate := fourDilate_continuous
  have hterm (n : ℕ) :
      fourDilate (1 - A * Q ^ n) =
        1 - fourDilate A * fourDilate Q ^ n := by
    simp
  have hmTarget : Multipliable (fun n =>
      1 - fourDilate A * fourDilate Q ^ n) := by
    exact (hm.map fourDilate hcont).congr (fun n => hterm n)
  rw [integer_qPochhammerInf_eq_tprod A Q hm,
    integer_qPochhammerInf_eq_tprod _ _ hmTarget]
  calc
    fourDilate (∏' n, (1 - A * Q ^ n)) =
        ∏' n, fourDilate (1 - A * Q ^ n) :=
      hm.map_tprod fourDilate hcont
    _ = ∏' n, (1 - fourDilate A * fourDilate Q ^ n) := by
      congr 1
      funext n
      exact hterm n

@[simp] theorem fourDilate_X :
    fourDilate (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X ^ 4 := by
  unfold fourDilate
  exact PowerSeries.substAlgHom_X
    (PowerSeries.HasSubst.X_pow (by decide : 4 ≠ 0))

private theorem integerEvenEulerFactors_multipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (PowerSeries.X : PowerSeries ℤ) ^ 2 *
        ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ n) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hm : Multipliable (fun n => 1 - q ^ 2 * (q ^ 2) ^ n) :=
    multipliable_factors
  have hmap := hm.map (jacobiUnitReceiver (1 : ℤˣ))
    (jacobiUnitReceiver_continuous (1 : ℤˣ))
  convert hmap using 1
  funext n
  simp

private theorem integerPositiveUnitFactors_multipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (-(PowerSeries.X : PowerSeries ℤ)) *
        ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ n) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hm : Multipliable (fun n =>
      1 - (-q * a) * (q ^ 2) ^ n) :=
    (factors_multipliable a).congr (fun n => by ring)
  have hmap := hm.map (jacobiUnitReceiver (1 : ℤˣ))
    (jacobiUnitReceiver_continuous (1 : ℤˣ))
  convert hmap using 1
  funext n
  simp

private theorem integerNegativeUnitFactors_multipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (PowerSeries.X : PowerSeries ℤ) *
        ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ n) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hm : Multipliable (fun n =>
      1 - (-q * a) * (q ^ 2) ^ n) :=
    (factors_multipliable a).congr (fun n => by ring)
  have hmap := hm.map (jacobiUnitReceiver (-1 : ℤˣ))
    (jacobiUnitReceiver_continuous (-1 : ℤˣ))
  convert hmap using 1
  funext n
  norm_num
  ring

/-- The two even modulo-four sheets, before their cardinal receiver. -/
def evenQuarterSquarePopulation (n : ℕ) : Finset ℤ :=
  quarterSquarePopulation 0 n ∪ quarterSquarePopulation 2 n

private theorem squareRoot_box_of_square {n : ℕ} {x : ℤ}
    (hroot : (n : ℤ) = x ^ 2) :
    x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  rw [Finset.mem_Icc]
  constructor
  · by_cases hx : 0 ≤ x
    · omega
    · have hx' : x ≤ -1 := by omega
      have hprod : 0 ≤ (-x) * (-x - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  · by_cases hx : x ≤ 0
    · omega
    · have hx' : 1 ≤ x := by omega
      have hprod : 0 ≤ x * (x - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith

private theorem double_mem_evenQuarter {m : ℕ} {x : ℤ}
    (hx : x ∈ squareRootPopulation m) :
    2 * x ∈ evenQuarterSquarePopulation (4 * m) := by
  rcases Finset.mem_filter.mp hx with ⟨hxBox, hxRoot⟩
  have hxSquare : (m : ℤ) = x ^ 2 := by
    rw [hxRoot]
    simp
  have hbox : 2 * x ∈ Finset.Icc (-((4 * m : ℕ) : ℤ)) ((4 * m : ℕ) : ℤ) := by
    rw [Finset.mem_Icc] at hxBox ⊢
    push_cast
    omega
  have hsquare : (2 * x) ^ 2 = ((4 * m : ℕ) : ℤ) := by
    push_cast
    nlinarith
  have hresidue : ((2 * x : ℤ) : ZMod 4) = 0 ∨
      ((2 * x : ℤ) : ZMod 4) = 2 := by
    have hreturn := quarterResidueAddress_returns x
    generalize hr : quarterResidueAddress x = r at hreturn
    fin_cases r
    all_goals norm_num at hreturn
    all_goals simp [Int.cast_mul, hreturn]
    all_goals decide
  rcases hresidue with hzero | htwo
  · rw [evenQuarterSquarePopulation, Finset.mem_union]
    left
    rw [quarterSquarePopulation, Finset.mem_filter]
    exact ⟨hbox, hsquare, hzero⟩
  · rw [evenQuarterSquarePopulation, Finset.mem_union]
    right
    rw [quarterSquarePopulation, Finset.mem_filter]
    exact ⟨hbox, hsquare, htwo⟩

private theorem evenQuarter_is_double {m : ℕ} {y : ℤ}
    (hy : y ∈ evenQuarterSquarePopulation (4 * m)) :
    ∃ x ∈ squareRootPopulation m, 2 * x = y := by
  rw [evenQuarterSquarePopulation, Finset.mem_union] at hy
  have hyEven : (2 : ℤ) ∣ y := by
    rcases hy with hy0 | hy2
    · have hres := (Finset.mem_filter.mp hy0).2.2
      have hdiv : (4 : ℤ) ∣ (0 : ℤ) - y :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub y 0 4).mp (by simpa using hres)
      rcases hdiv with ⟨k, hk⟩
      refine ⟨-2 * k, ?_⟩
      omega
    · have hres := (Finset.mem_filter.mp hy2).2.2
      have hdiv : (4 : ℤ) ∣ (2 : ℤ) - y :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub y 2 4).mp (by simpa using hres)
      rcases hdiv with ⟨k, hk⟩
      refine ⟨1 - 2 * k, ?_⟩
      omega
  let x : ℤ := y / 2
  have hreturn : 2 * x = y := by
    dsimp [x]
    rw [mul_comm, Int.ediv_mul_cancel hyEven]
  have hySquare : y ^ 2 = ((4 * m : ℕ) : ℤ) := by
    rcases hy with hy0 | hy2
    · exact (Finset.mem_filter.mp hy0).2.1
    · exact (Finset.mem_filter.mp hy2).2.1
  have hxSquare : (m : ℤ) = x ^ 2 := by
    push_cast at hySquare
    rw [← hreturn] at hySquare
    nlinarith
  refine ⟨x, ?_, hreturn⟩
  rw [squareRootPopulation, Finset.mem_filter]
  refine ⟨squareRoot_box_of_square hxSquare, ?_⟩
  have : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by simp
  exact_mod_cast hxSquare.trans this.symm

/-- Doubling is an exact bijection from the source root population to the
two even residue sheets at four times the square address. -/
theorem image_double_squareRootPopulation (m : ℕ) :
    (squareRootPopulation m).image (fun x : ℤ => 2 * x) =
      evenQuarterSquarePopulation (4 * m) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact double_mem_evenQuarter hx
  · intro hy
    rcases evenQuarter_is_double hy with ⟨x, hx, hxy⟩
    exact Finset.mem_image.mpr ⟨x, hx, hxy⟩

theorem card_evenQuarter_four_mul (m : ℕ) :
    (evenQuarterSquarePopulation (4 * m)).card =
      (squareRootPopulation m).card := by
  rw [← image_double_squareRootPopulation]
  exact Finset.card_image_of_injective _ (by
    intro a b h
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h)

private theorem evenQuarter_disjoint (n : ℕ) :
    Disjoint (quarterSquarePopulation 0 n) (quarterSquarePopulation 2 n) := by
  rw [Finset.disjoint_left]
  intro x hx0 hx2
  have h0 := (Finset.mem_filter.mp hx0).2.2
  have h2 := (Finset.mem_filter.mp hx2).2.2
  have : (0 : ZMod 4) = 2 := h0.symm.trans h2
  exact (by decide : (0 : ZMod 4) ≠ 2) this

theorem card_evenQuarter_eq_sum (n : ℕ) :
    (evenQuarterSquarePopulation n).card =
      (quarterSquarePopulation 0 n).card +
        (quarterSquarePopulation 2 n).card := by
  exact Finset.card_union_of_disjoint (evenQuarter_disjoint n)

private theorem evenQuarter_empty_of_not_four_dvd {n : ℕ}
    (h4 : ¬4 ∣ n) : evenQuarterSquarePopulation n = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  rcases hnonempty with ⟨x, hx⟩
  rw [evenQuarterSquarePopulation, Finset.mem_union] at hx
  have hsquare : x ^ 2 = (n : ℤ) := by
    rcases hx with hx0 | hx2
    · exact (Finset.mem_filter.mp hx0).2.1
    · exact (Finset.mem_filter.mp hx2).2.1
  have heven : (2 : ℤ) ∣ x := by
    rcases hx with hx0 | hx2
    · have hres := (Finset.mem_filter.mp hx0).2.2
      have hdiv : (4 : ℤ) ∣ (0 : ℤ) - x :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub x 0 4).mp (by simpa using hres)
      rcases hdiv with ⟨k, hk⟩
      refine ⟨-2 * k, by omega⟩
    · have hres := (Finset.mem_filter.mp hx2).2.2
      have hdiv : (4 : ℤ) ∣ (2 : ℤ) - x :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub x 2 4).mp (by simpa using hres)
      rcases hdiv with ⟨k, hk⟩
      refine ⟨1 - 2 * k, by omega⟩
  rcases heven with ⟨k, rfl⟩
  apply h4
  refine ⟨k.natAbs ^ 2, ?_⟩
  have hsquare' := hsquare
  simp at hsquare'
  have hcast : (((4 * k.natAbs ^ 2 : ℕ) : ℤ)) = (2 * k) ^ 2 := by
    push_cast
    simp
    ring
  exact_mod_cast hsquare'.symm.trans hcast.symm

/-- The positive square theta under `X ↦ X⁴` is exactly the sum of the two
even quarter-residue square streams. -/
theorem fourDilate_unitSquareTheta_one :
    fourDilate (unitSquareTheta (1 : ℤˣ)) =
      quarterSquareTheta 0 + quarterSquareTheta 2 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_fourDilate]
  by_cases h4 : 4 ∣ n
  · rw [if_pos h4]
    obtain ⟨m, rfl⟩ := h4
    rw [Nat.mul_div_cancel_left m (by decide : 0 < 4),
      coeff_unitSquareTheta_one, map_add, coeff_quarterSquareTheta,
      coeff_quarterSquareTheta]
    have hcard : (squareRootPopulation m).card =
        (quarterSquarePopulation 0 (4 * m)).card +
          (quarterSquarePopulation 2 (4 * m)).card :=
      (card_evenQuarter_four_mul m).symm.trans
        (card_evenQuarter_eq_sum (4 * m))
    exact_mod_cast hcard
  · rw [if_neg h4, map_add, coeff_quarterSquareTheta,
      coeff_quarterSquareTheta]
    have hempty := congrArg Finset.card
      (evenQuarter_empty_of_not_four_dvd h4)
    have hsum := card_evenQuarter_eq_sum n
    rw [hempty] at hsum
    simp only [Finset.card_empty] at hsum
    exact_mod_cast hsum

/-! ## The orientation sign survives the scale change -/

/-- The target sign is not assigned independently: it is read from which of
the two even residue sheets receives the doubled occurrence. -/
def evenQuarterWeight (y : ℤ) : ℤ :=
  if (y : ZMod 4) = 0 then 1 else -1

private theorem negOnePow_eq_doubleWeight (x : ℤ) :
    (((-1 : ℤˣ) ^ x).val : ℤ) = evenQuarterWeight (2 * x) := by
  rcases Int.even_or_odd x with hx | hx
  · rcases hx with ⟨k, rfl⟩
    have hres : ((2 * (k + k) : ℤ) : ZMod 4) = 0 := by
      push_cast
      ring_nf
      rw [show (4 : ZMod 4) = 0 by decide]
      simp
    change (k + k).negOnePow.val = evenQuarterWeight (2 * (k + k))
    rw [Int.negOnePow_even (k + k) ⟨k, by ring⟩]
    simp [evenQuarterWeight, hres]
  · rcases hx with ⟨k, rfl⟩
    have hres : ((2 * (2 * k + 1) : ℤ) : ZMod 4) = 2 := by
      push_cast
      ring_nf
      rw [show (4 : ZMod 4) = 0 by decide]
      simp
    change (2 * k + 1).negOnePow.val =
      evenQuarterWeight (2 * (2 * k + 1))
    rw [Int.negOnePow_odd (2 * k + 1) ⟨k, by ring⟩]
    simp [evenQuarterWeight, hres, show (2 : ZMod 4) ≠ 0 by decide]

private theorem sum_doubleWeight_eq_evenDifference (n : ℕ) :
    (∑ y ∈ evenQuarterSquarePopulation n, evenQuarterWeight y) =
      ((quarterSquarePopulation 0 n).card : ℤ) -
        ((quarterSquarePopulation 2 n).card : ℤ) := by
  rw [evenQuarterSquarePopulation,
    Finset.sum_union (evenQuarter_disjoint n)]
  congr 1
  · calc
      (∑ y ∈ quarterSquarePopulation 0 n, evenQuarterWeight y) =
          ∑ _y ∈ quarterSquarePopulation 0 n, (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro y hy
            have hres := (Finset.mem_filter.mp hy).2.2
            simp [evenQuarterWeight, hres]
      _ = ((quarterSquarePopulation 0 n).card : ℤ) := by simp
  · calc
      (∑ y ∈ quarterSquarePopulation 2 n, evenQuarterWeight y) =
          ∑ _y ∈ quarterSquarePopulation 2 n, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro y hy
            have hres := (Finset.mem_filter.mp hy).2.2
            have hne : (y : ZMod 4) ≠ 0 := by
              rw [hres]
              decide
            rw [evenQuarterWeight, if_neg hne]
      _ = -((quarterSquarePopulation 2 n).card : ℤ) := by simp

private theorem squareRootNegCurrent_eq_evenDifference (m : ℕ) :
    (∑ x ∈ squareRootPopulation m,
        (((-1 : ℤˣ) ^ x).val : ℤ)) =
      ((quarterSquarePopulation 0 (4 * m)).card : ℤ) -
        ((quarterSquarePopulation 2 (4 * m)).card : ℤ) := by
  calc
    (∑ x ∈ squareRootPopulation m,
        (((-1 : ℤˣ) ^ x).val : ℤ)) =
        ∑ x ∈ squareRootPopulation m, evenQuarterWeight (2 * x) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact negOnePow_eq_doubleWeight x
    _ = ∑ y ∈ (squareRootPopulation m).image (fun x : ℤ => 2 * x),
          evenQuarterWeight y := by
          rw [Finset.sum_image]
          intro a _ha b _hb hab
          exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hab
    _ = ∑ y ∈ evenQuarterSquarePopulation (4 * m),
          evenQuarterWeight y := by
          rw [image_double_squareRootPopulation]
    _ = _ := sum_doubleWeight_eq_evenDifference (4 * m)

/-- The negative Jacobi unit under `X ↦ X⁴` is the polarized even-sheet
difference.  Source parity and target orientation are the same retained
occurrence in two charts. -/
theorem fourDilate_unitSquareTheta_neg_one :
    fourDilate (unitSquareTheta (-1 : ℤˣ)) =
      quarterSquareTheta 0 - quarterSquareTheta 2 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_fourDilate]
  by_cases h4 : 4 ∣ n
  · rw [if_pos h4]
    obtain ⟨m, rfl⟩ := h4
    rw [Nat.mul_div_cancel_left m (by decide : 0 < 4),
      coeff_unitSquareTheta_eq_squareRootCurrent, map_sub,
      coeff_quarterSquareTheta, coeff_quarterSquareTheta]
    exact squareRootNegCurrent_eq_evenDifference m
  · rw [if_neg h4, map_sub, coeff_quarterSquareTheta,
      coeff_quarterSquareTheta]
    have hempty := congrArg Finset.card
      (evenQuarter_empty_of_not_four_dvd h4)
    have hsum := card_evenQuarter_eq_sum n
    rw [hempty] at hsum
    simp only [Finset.card_empty] at hsum
    have hzero0 : (quarterSquarePopulation 0 n).card = 0 := by omega
    have hzero2 : (quarterSquarePopulation 2 n).card = 0 := by omega
    simp [hzero0, hzero2]

/-! ## The two even theta faces as exact scale-eight Euler products -/

/-- The positive even face is the scale-four transport of the positive unit
Jacobi product. -/
theorem evenSum_eq_scaleEightJacobiProduct :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf
          ((PowerSeries.X : PowerSeries ℤ) ^ 8) (PowerSeries.X ^ 8) *
        qPochhammerInf (-PowerSeries.X ^ 4) (PowerSeries.X ^ 8) ^ 2 =
      quarterSquareTheta 0 + quarterSquareTheta 2 := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have h := congrArg fourDilate
    (jacobi_unit_product_eq_unitSquareTheta (1 : ℤˣ))
  simp only [map_mul] at h
  norm_num at h
  rw [fourDilate_qPochhammerInf _ _
      integerEvenEulerFactors_multipliable,
    fourDilate_qPochhammerInf _ _
      integerPositiveUnitFactors_multipliable,
    fourDilate_unitSquareTheta_one] at h
  simp only [map_pow, map_neg, fourDilate_X] at h
  have hpow :
      ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ 2 =
        PowerSeries.X ^ 8 := by ring
  rw [hpow] at h
  simpa [pow_two, mul_assoc] using h

/-- The polarized even face is the scale-four transport of the negative unit
Jacobi product. -/
theorem evenDifference_eq_scaleEightJacobiProduct :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf
          ((PowerSeries.X : PowerSeries ℤ) ^ 8) (PowerSeries.X ^ 8) *
        qPochhammerInf (PowerSeries.X ^ 4) (PowerSeries.X ^ 8) ^ 2 =
      quarterSquareTheta 0 - quarterSquareTheta 2 := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have h := congrArg fourDilate
    (jacobi_unit_product_eq_unitSquareTheta (-1 : ℤˣ))
  simp only [map_mul] at h
  norm_num at h
  rw [fourDilate_qPochhammerInf _ _
      integerEvenEulerFactors_multipliable,
    fourDilate_qPochhammerInf _ _
      integerNegativeUnitFactors_multipliable,
    fourDilate_unitSquareTheta_neg_one] at h
  simp only [map_pow, fourDilate_X] at h
  have hpow :
      ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ 2 =
        PowerSeries.X ^ 8 := by ring
  rw [hpow] at h
  simpa [pow_two, mul_assoc] using h

/-- The completed even Euler product itself transports to its literal
scale-eight factor population. -/
theorem fourDilate_infiniteEvenEulerProduct_eq_scaleEight :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    fourDilate infiniteEvenEulerProduct =
      qPochhammerInf ((PowerSeries.X : PowerSeries ℤ) ^ 8)
        (PowerSeries.X ^ 8) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  unfold infiniteEvenEulerProduct
  rw [fourDilate_qPochhammerInf _ _
    integerEvenEulerFactors_multipliable]
  simp only [map_pow, fourDilate_X]
  have hpow : ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ 2 =
      PowerSeries.X ^ 8 := by ring
  rw [hpow]

/-! ## The affine receiver is multiplication after exact dilation -/

/-- The pre-existing affine coefficient receiver is not an opaque reindexing:
it is exactly `F(X) ↦ X · F(X⁴)`. -/
theorem affineFourRegrade_eq_X_mul_fourDilate (F : PowerSeries ℤ) :
    affineFourRegrade F = PowerSeries.X * fourDilate F := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_affineFourRegrade]
  | succ n =>
      rw [coeff_affineFourRegrade,
        PowerSeries.coeff_succ_X_mul, coeff_fourDilate]
      by_cases hdiv : 4 ∣ n
      · have hmod : (n + 1) % 4 = 1 := by
          have hnmod : n % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
          omega
        rw [if_pos hmod, if_pos hdiv]
        congr 2
      · have hmod : (n + 1) % 4 ≠ 1 := by
          intro h
          apply hdiv
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        rw [if_neg hmod, if_neg hdiv]

/-- The oriented quarter-square current is the completed even Euler cube
after the exact scale-four chart and one retained leading occurrence. -/
theorem weightedQuarterSquareTheta_eq_X_mul_dilatedEulerCube :
    weightedQuarterSquareTheta 1 =
      PowerSeries.X * fourDilate infiniteEvenEulerCube := by
  rw [← affineFourRegrade_infiniteEvenEulerCube_eq_weightedQuarterSquareTheta,
    affineFourRegrade_eq_X_mul_fourDilate]

/-- The scale chart distributes through the three Euler populations. -/
theorem weightedQuarterSquareTheta_eq_X_mul_dilatedEulerProduct_cube :
    weightedQuarterSquareTheta 1 =
      PowerSeries.X *
        (fourDilate infiniteEvenEulerProduct ^ 2 *
          fourDilate infiniteEvenEulerProduct) := by
  rw [weightedQuarterSquareTheta_eq_X_mul_dilatedEulerCube]
  unfold infiniteEvenEulerCube
  simp only [map_mul, map_pow]

/-- Thus the weighted orientation current is already the scale-eight Euler
cube with its leading addressed occurrence retained. -/
theorem weightedQuarterSquareTheta_eq_scaleEightEulerCube :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    weightedQuarterSquareTheta 1 =
      PowerSeries.X *
        (qPochhammerInf ((PowerSeries.X : PowerSeries ℤ) ^ 8)
            (PowerSeries.X ^ 8) ^ 2 *
          qPochhammerInf (PowerSeries.X ^ 8) (PowerSeries.X ^ 8)) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [weightedQuarterSquareTheta_eq_X_mul_dilatedEulerProduct_cube,
    fourDilate_infiniteEvenEulerProduct_eq_scaleEight]

#print axioms image_double_squareRootPopulation
#print axioms fourDilate_unitSquareTheta_one
#print axioms fourDilate_unitSquareTheta_neg_one
#print axioms evenSum_eq_scaleEightJacobiProduct
#print axioms evenDifference_eq_scaleEightJacobiProduct
#print axioms weightedQuarterSquareTheta_eq_scaleEightEulerCube
#print axioms affineFourRegrade_eq_X_mul_fourDilate
#print axioms weightedQuarterSquareTheta_eq_X_mul_dilatedEulerProduct_cube

end Soma.Holonics.Millennium.FamilyTunnellThetaDilation
