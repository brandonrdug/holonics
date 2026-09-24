import ElementaryHolonics.Millennium.FamilyTunnellThetaDilation
import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalBridge

/-!
# The positive Jacobi diagonal returns the missing Gauss factor

The differentiated diagonal `a = -q` returns the weighted Jacobi current.
The companion undifferentiated diagonal `a = q` has two reflected source
occurrences over every triangular address.  On the product side the inverse
orientation factor has a literal first factor `2`.  Cancelling this common
two-sheet population gives Gauss's triangular product without division in
the coefficient ring.  Exact affine regrading then supplies the missing
quarter-square factor.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiGaussFactor

open Finset
open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalProduct
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalCone
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalBridge
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalReceiver
open Soma.Holonics.Mathematics.JacobiEulerCubeStabilization
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Mathematics.PowerSeriesExactDilation
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellJacobiOrientation
open Soma.Holonics.Millennium.FamilyTunnellJacobiRegrading
open Soma.Holonics.Millennium.FamilyTunnellJacobiProductReceiver
open Soma.Holonics.Millennium.FamilyTunnellThetaDilation

open scoped PowerSeries.WithPiTopology

abbrev LaurentBody := LaurentPolynomial ℤ
abbrev PolynomialBody := Polynomial LaurentBody

/-- Laurent bodies act as coefficient functions, as they did before `AddMonoidAlgebra` became a
structure. -/
instance : CoeFun LaurentBody (fun _ => ℤ → ℤ) := ⟨fun f => AddMonoidAlgebra.coeff f⟩
abbrev BivariateSeries := PowerSeries LaurentBody

/-! ## The positive finite diagonal -/

/-- Simultaneously send the outer polynomial variable and the retained
Laurent orientation to the same Laurent generator. -/
def positiveFiniteDiagonalHom : PolynomialBody →+* LaurentBody :=
  Polynomial.eval₂RingHom (RingHom.id LaurentBody) (LaurentPolynomial.T 1)

@[simp] theorem positiveFiniteDiagonalHom_q :
    positiveFiniteDiagonalHom polynomialQ = LaurentPolynomial.T 1 := by
  simp [positiveFiniteDiagonalHom, polynomialQ]

@[simp] theorem positiveFiniteDiagonalHom_a :
    positiveFiniteDiagonalHom polynomialA = LaurentPolynomial.T 1 := by
  simp [positiveFiniteDiagonalHom, polynomialA]

@[simp] theorem positiveFiniteDiagonalHom_aInv :
    positiveFiniteDiagonalHom polynomialAInv = LaurentPolynomial.T (-1) := by
  simp [positiveFiniteDiagonalHom, polynomialAInv]

/-- The finite coefficient face of the formal positive diagonal `a = q`.
The window is forced by the same square cone as the differentiated receiver. -/
def positiveFiniteDiagonalReceiver (d : ℕ) (F : BivariateSeries) : ℤ :=
  ∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
    if 0 ≤ (d : ℤ) - m then
      (PowerSeries.coeff (((d : ℤ) - m).toNat) F) m
    else 0

/-- The unsigned address change underlying the positive diagonal. -/
theorem positiveDiagonalWindow_sum_reindex (c : ℕ → ℤ → ℤ) (d : ℕ) :
    (∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
      if 0 ≤ (d : ℤ) - m then c (((d : ℤ) - m).toNat) m else 0) =
    ∑ n ∈ Finset.range (2 * d + 2), c n ((d : ℤ) - (n : ℤ)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm => ((d : ℤ) - m).toNat)
  · intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_range]
    have hbox := (Finset.mem_Icc.mp hm.1).1
    have hcast : (((d : ℤ) - m).toNat : ℤ) = (d : ℤ) - m :=
      Int.toNat_of_nonneg hm.2
    omega
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    have hca : (((d : ℤ) - a).toNat : ℤ) = (d : ℤ) - a :=
      Int.toNat_of_nonneg ha.2
    have hcb : (((d : ℤ) - b).toNat : ℤ) = (d : ℤ) - b :=
      Int.toNat_of_nonneg hb.2
    omega
  · intro n hn
    rw [Finset.mem_range] at hn
    let m : ℤ := (d : ℤ) - (n : ℤ)
    have hnonneg : 0 ≤ (d : ℤ) - m := by dsimp [m]; omega
    have hmem : m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1) := by
      rw [Finset.mem_Icc]
      dsimp [m]
      omega
    refine ⟨m, Finset.mem_filter.mpr ⟨hmem, hnonneg⟩, ?_⟩
    dsimp [m]
    have heq : (d : ℤ) - ((d : ℤ) - (n : ℤ)) = (n : ℤ) := by ring
    rw [heq]
    simp
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hcast : (((d : ℤ) - m).toNat : ℤ) = (d : ℤ) - m :=
      Int.toNat_of_nonneg hm.2
    have hadd : (d : ℤ) - (((d : ℤ) - m).toNat : ℤ) = m := by omega
    rw [hadd]

/-- Coefficient formula for the positive polynomial diagonal. -/
theorem positiveFiniteDiagonalHom_apply (p : PolynomialBody) (d : ℤ) :
    positiveFiniteDiagonalHom p d =
      ∑ n ∈ p.support, p.coeff n (d - (n : ℤ)) := by
  change (Polynomial.eval₂ (RingHom.id LaurentBody)
      (LaurentPolynomial.T 1) p) d = _
  rw [Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum
  change AddMonoidAlgebra.coeff
      (∑ n ∈ p.support, p.coeff n * LaurentPolynomial.T 1 ^ n) d = _
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [LaurentPolynomial.T_pow]
  have hshift :
      ((p.coeff n * LaurentPolynomial.T (n : ℤ) : LaurentBody)) d =
        p.coeff n (d - (n : ℤ)) := by
    have hT : (LaurentPolynomial.T (n : ℤ) : LaurentBody) =
        AddMonoidAlgebra.single (n : ℤ) 1 := by
      simpa using
        (LaurentPolynomial.single_eq_C_mul_T (R := ℤ) 1 (n : ℤ)).symm
    rw [mul_comm, hT,
      AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (d - (n : ℤ)) (fun m' _ => by omega)]
    simp
  simpa using hshift

private def polynomialDiagonalSupport (p : PolynomialBody) (d : ℕ) : Finset ℕ :=
  p.support.filter fun n => p.coeff n ((d : ℤ) - (n : ℤ)) ≠ 0

private theorem polynomialDiagonalSupport_subset_range
    (p : PolynomialBody) (d : ℕ)
    (hcone : SquareCone (polynomialPowerSeriesHom p)) :
    polynomialDiagonalSupport p d ⊆ Finset.range (2 * d + 2) := by
  intro n hn
  rw [polynomialDiagonalSupport, Finset.mem_filter] at hn
  rw [Finset.mem_range]
  have hcoeff :
      PowerSeries.coeff n (polynomialPowerSeriesHom p)
          ((d : ℤ) - (n : ℤ)) ≠ 0 := by
    simpa using hn.2
  have hdiag : (n : ℤ) + ((d : ℤ) - (n : ℤ)) = (d : ℤ) := by ring
  have := SquareCone.diagonal_outer_le hcone hcoeff hdiag
  omega

private theorem polynomial_support_sum_eq_diagonalSupport
    (p : PolynomialBody) (d : ℕ) :
    (∑ n ∈ p.support, p.coeff n ((d : ℤ) - (n : ℤ))) =
      ∑ n ∈ polynomialDiagonalSupport p d,
        p.coeff n ((d : ℤ) - (n : ℤ)) := by
  rw [polynomialDiagonalSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs with h
  · rfl
  · simp [Classical.not_not.mp h]

private theorem polynomial_range_sum_eq_diagonalSupport
    (p : PolynomialBody) (d : ℕ)
    (hcone : SquareCone (polynomialPowerSeriesHom p)) :
    (∑ n ∈ Finset.range (2 * d + 2),
      p.coeff n ((d : ℤ) - (n : ℤ))) =
      ∑ n ∈ polynomialDiagonalSupport p d,
        p.coeff n ((d : ℤ) - (n : ℤ)) := by
  symm
  apply Finset.sum_subset (polynomialDiagonalSupport_subset_range p d hcone)
  intro n _hnrange hnnot
  by_cases hsupp : n ∈ p.support
  · have hzero : p.coeff n ((d : ℤ) - (n : ℤ)) = 0 := by
      by_contra hne
      exact hnnot (Finset.mem_filter.mpr ⟨hsupp, hne⟩)
    simp [hzero]
  · have hpzero : p.coeff n = 0 := by
      by_contra hne
      exact hsupp (Polynomial.mem_support_iff.mpr hne)
    simp [hpzero]

/-- The positive finite receiver is the coefficient of the positive
polynomial diagonal whenever the exact square cone is present. -/
theorem positiveFiniteDiagonalReceiver_polynomial_eq
    (p : PolynomialBody) (d : ℕ)
    (hcone : SquareCone (polynomialPowerSeriesHom p)) :
    positiveFiniteDiagonalReceiver d (polynomialPowerSeriesHom p) =
      positiveFiniteDiagonalHom p (d : ℤ) := by
  rw [positiveFiniteDiagonalReceiver]
  simp only [coeff_polynomialPowerSeriesHom]
  calc
    (∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
        if 0 ≤ (d : ℤ) - m then
          p.coeff (((d : ℤ) - m).toNat) m else 0) =
        ∑ n ∈ Finset.range (2 * d + 2),
          p.coeff n ((d : ℤ) - (n : ℤ)) :=
      positiveDiagonalWindow_sum_reindex (fun n m => p.coeff n m) d
    _ = ∑ n ∈ polynomialDiagonalSupport p d,
          p.coeff n ((d : ℤ) - (n : ℤ)) :=
      polynomial_range_sum_eq_diagonalSupport p d hcone
    _ = ∑ n ∈ p.support,
          p.coeff n ((d : ℤ) - (n : ℤ)) :=
      (polynomial_support_sum_eq_diagonalSupport p d).symm
    _ = positiveFiniteDiagonalHom p (d : ℤ) :=
      (positiveFiniteDiagonalHom_apply p (d : ℤ)).symm

/-! ## The exact finite product return -/

/-- The positive even Euler factors presented in the positive diagonal. -/
def finitePositiveEvenEulerProduct (n : ℕ) : LaurentBody :=
  qPoch (-LaurentPolynomial.T 2) (LaurentPolynomial.T 2) n

@[simp] theorem positiveFiniteDiagonalHom_P0 (n : ℕ) :
    positiveFiniteDiagonalHom (finitePolynomialP0 n) = finiteEulerProduct n := by
  rw [finitePolynomialP0, map_qPoch]
  simp [finiteEulerProduct, positiveFiniteDiagonalHom, polynomialQ]

@[simp] theorem positiveFiniteDiagonalHom_P1 (n : ℕ) :
    positiveFiniteDiagonalHom (finitePolynomialP1 n) =
      finitePositiveEvenEulerProduct n := by
  rw [finitePolynomialP1, map_qPoch]
  have hT : LaurentPolynomial.T (1 : ℤ) ^ 2 =
      (LaurentPolynomial.T 2 : LaurentBody) := by
    rw [pow_two, ← LaurentPolynomial.T_add]
    norm_num
  simp only [map_neg, map_mul, map_pow, positiveFiniteDiagonalHom_q,
    positiveFiniteDiagonalHom_a, finitePositiveEvenEulerProduct]
  rw [hT]
  congr 1
  simpa [pow_two] using congrArg Neg.neg hT

@[simp] theorem positiveFiniteDiagonalHom_P3_succ (n : ℕ) :
    positiveFiniteDiagonalHom (finitePolynomialP3 (n + 1)) =
      2 * finitePositiveEvenEulerProduct n := by
  rw [finitePolynomialP3, map_qPoch]
  have hT : LaurentPolynomial.T (1 : ℤ) ^ 2 =
      (LaurentPolynomial.T 2 : LaurentBody) := by
    rw [pow_two, ← LaurentPolynomial.T_add]
    norm_num
  simp only [map_neg, map_mul, map_pow, positiveFiniteDiagonalHom_q,
    positiveFiniteDiagonalHom_aInv]
  rw [hT]
  have hA : -(LaurentPolynomial.T 1) * LaurentPolynomial.T (-1) =
      (-1 : LaurentBody) := by
    rw [neg_mul, ← LaurentPolynomial.T_add]
    norm_num
  rw [hA]
  unfold qPoch finitePositiveEvenEulerProduct
  have htail :
      (∏ k ∈ Finset.range n,
          (1 - (-1 : LaurentBody) * LaurentPolynomial.T 2 ^ (k + 1))) =
        ∏ k ∈ Finset.range n,
          (1 - (-LaurentPolynomial.T 2) * LaurentPolynomial.T 2 ^ k) := by
    apply Finset.prod_congr rfl
    intro k _hk
    rw [pow_succ]
    ring
  rw [Finset.prod_range_succ', htail]
  rw [pow_zero]
  have heq :
      (∏ k ∈ Finset.range n,
          ((1 : LaurentBody) - (-(LaurentPolynomial.T 2 : LaurentBody)) *
            (LaurentPolynomial.T 2 : LaurentBody) ^ k)) =
        qPoch (-(LaurentPolynomial.T 2 : LaurentBody))
          (LaurentPolynomial.T 2 : LaurentBody) n := rfl
  rw [heq]
  ring

/-- The positive diagonal of the finite Jacobi body retains its literal
two-sheet factor and the three neighboring Euler populations. -/
theorem positiveFiniteDiagonalHom_tripleProduct (n : ℕ) :
    positiveFiniteDiagonalHom (finitePolynomialTripleProduct (n + 1)) =
      2 * (finiteEulerProduct (n + 1) *
        finitePositiveEvenEulerProduct (n + 1) *
        finitePositiveEvenEulerProduct n) := by
  rw [finitePolynomialTripleProduct, map_mul, map_mul,
    positiveFiniteDiagonalHom_P0, positiveFiniteDiagonalHom_P1,
    positiveFiniteDiagonalHom_P3_succ]
  ring

/-! ## Coefficientwise completion of the positive factors -/

def infinitePositiveEvenEulerProduct : PowerSeries ℤ :=
  qPochhammerInf (-(PowerSeries.X ^ 2)) (PowerSeries.X ^ 2)

def finitePositiveEvenEulerSeries (N : ℕ) : PowerSeries ℤ :=
  qPoch (-(PowerSeries.X ^ 2)) (PowerSeries.X ^ 2) N

private theorem integerPositiveEvenFactors_multipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (-(PowerSeries.X : PowerSeries ℤ) ^ 2) *
        ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ n) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hm : Multipliable (fun n =>
      1 - (-q * q) * (q ^ 2) ^ n) := factors_multipliable q
  have hmap := hm.map (jacobiUnitReceiver (1 : ℤˣ))
    (jacobiUnitReceiver_continuous (1 : ℤˣ))
  convert hmap using 1
  funext n
  simp
  ring

/-- Every coefficient below the first omitted positive factor has already
returned its complete value. -/
theorem coeff_infinitePositiveEvenEulerProduct_eq_finite
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d infinitePositiveEvenEulerProduct =
      PowerSeries.coeff d (finitePositiveEvenEulerSeries N) := by
  letI : TopologicalSpace BivariateSeries := piTop
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hm : Multipliable (fun n =>
      1 - (-q * q) * (q ^ 2) ^ n) := factors_multipliable q
  have hmapInf := jacobiUnitReceiver_qPochhammerInf (1 : ℤˣ)
    (-q * q) (q ^ 2) hm
  have hstable :
      PowerSeries.coeff d
          (qPochhammerInf (-q * q) (q ^ 2) : BivariateSeries) =
        PowerSeries.coeff d (qPoch (-q * q) (q ^ 2) N : BivariateSeries) := by
    exact lhs_coeff_stable q d N h
  have hfiniteMap :
      jacobiUnitReceiver (1 : ℤˣ) (qPoch (-q * q) (q ^ 2) N) =
        finitePositiveEvenEulerSeries N := by
    rw [map_qPoch]
    simp [finitePositiveEvenEulerSeries]
    ring
  calc
    PowerSeries.coeff d infinitePositiveEvenEulerProduct =
        PowerSeries.coeff d
          (jacobiUnitReceiver (1 : ℤˣ)
            (qPochhammerInf (-q * q) (q ^ 2))) := by
              rw [hmapInf]
              simp [infinitePositiveEvenEulerProduct]
              ring
    _ = laurentUnitReceiver (1 : ℤˣ)
          (PowerSeries.coeff d
            (qPochhammerInf (-q * q) (q ^ 2))) := by simp
    _ = laurentUnitReceiver (1 : ℤˣ)
          (PowerSeries.coeff d (qPoch (-q * q) (q ^ 2) N)) := by
            rw [hstable]
    _ = PowerSeries.coeff d
          (jacobiUnitReceiver (1 : ℤˣ)
            (qPoch (-q * q) (q ^ 2) N)) := by simp
    _ = PowerSeries.coeff d (finitePositiveEvenEulerSeries N) := by
      rw [hfiniteMap]

/-- The completed product returned after cancelling the source's common
two-sheet multiplicity. -/
def gaussTriangularProduct : PowerSeries ℤ :=
  infiniteEvenEulerProduct * infinitePositiveEvenEulerProduct ^ 2

/-- The finite positive-diagonal return in the same association. -/
def finiteGaussNeighborReturn (N : ℕ) : PowerSeries ℤ :=
  finiteEvenEulerSeries (N + 1) *
    finitePositiveEvenEulerSeries (N + 1) *
    finitePositiveEvenEulerSeries N

theorem coeff_gaussTriangularProduct_eq_finiteNeighbor
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d gaussTriangularProduct =
      PowerSeries.coeff d (finiteGaussNeighborReturn N) := by
  have hE : ∀ j ≤ d,
      PowerSeries.coeff j infiniteEvenEulerProduct =
        PowerSeries.coeff j (finiteEvenEulerSeries (N + 1)) := by
    intro j hj
    exact coeff_infiniteEvenEulerProduct_eq_finite j (N + 1) (by omega)
  have hP1 : ∀ j ≤ d,
      PowerSeries.coeff j infinitePositiveEvenEulerProduct =
        PowerSeries.coeff j (finitePositiveEvenEulerSeries (N + 1)) := by
    intro j hj
    exact coeff_infinitePositiveEvenEulerProduct_eq_finite j (N + 1) (by omega)
  have hP : ∀ j ≤ d,
      PowerSeries.coeff j infinitePositiveEvenEulerProduct =
        PowerSeries.coeff j (finitePositiveEvenEulerSeries N) := by
    intro j hj
    exact coeff_infinitePositiveEvenEulerProduct_eq_finite j N (by omega)
  have hEP : ∀ j ≤ d,
      PowerSeries.coeff j
          (infiniteEvenEulerProduct * infinitePositiveEvenEulerProduct) =
        PowerSeries.coeff j
          (finiteEvenEulerSeries (N + 1) *
            finitePositiveEvenEulerSeries (N + 1)) := by
    intro j hj
    exact coeff_mul_eq_of_coeff_le _ _ _ _ j
      (fun k hk => hE k (le_trans hk hj))
      (fun k hk => hP1 k (le_trans hk hj))
  unfold gaussTriangularProduct finiteGaussNeighborReturn
  rw [pow_two]
  rw [show infiniteEvenEulerProduct *
      (infinitePositiveEvenEulerProduct * infinitePositiveEvenEulerProduct) =
      (infiniteEvenEulerProduct * infinitePositiveEvenEulerProduct) *
        infinitePositiveEvenEulerProduct by ring]
  exact coeff_mul_eq_of_coeff_le _ _ _ _ d hEP hP

/-! ## The complete positive Jacobi return -/

def positiveEvenEulerPolynomial (N : ℕ) : Polynomial ℤ :=
  qPoch (-(Polynomial.X ^ 2)) (Polynomial.X ^ 2) N

theorem toLaurent_positiveEvenEulerPolynomial (N : ℕ) :
    Polynomial.toLaurent (positiveEvenEulerPolynomial N) =
      finitePositiveEvenEulerProduct N := by
  rw [positiveEvenEulerPolynomial, map_qPoch]
  simp [finitePositiveEvenEulerProduct]

theorem toPowerSeries_positiveEvenEulerPolynomial (N : ℕ) :
    polynomialPowerSeriesHom (positiveEvenEulerPolynomial N) =
      finitePositiveEvenEulerSeries N := by
  have hX : polynomialPowerSeriesHom (Polynomial.X : Polynomial ℤ) =
      (PowerSeries.X : PowerSeries ℤ) := by
    apply PowerSeries.ext
    intro d
    by_cases hd : d = 1 <;> simp [Polynomial.coeff_X, PowerSeries.coeff_X,
      hd, eq_comm]
  rw [positiveEvenEulerPolynomial, map_qPoch]
  unfold finitePositiveEvenEulerSeries
  rw [map_neg polynomialPowerSeriesHom,
    map_pow polynomialPowerSeriesHom, hX]

/-- The common finite polynomial body proves that the Laurent positive
return and the ordinary finite power-series return have identical
coefficients. -/
theorem coeff_finitePositiveDiagonalProduct_eq_series (d N : ℕ) :
    (2 * (finiteEulerProduct (N + 1) *
      finitePositiveEvenEulerProduct (N + 1) *
      finitePositiveEvenEulerProduct N)) (d : ℤ) =
      PowerSeries.coeff d (2 * finiteGaussNeighborReturn N) := by
  let p : Polynomial ℤ :=
    2 * (evenEulerPolynomial (N + 1) *
      positiveEvenEulerPolynomial (N + 1) *
      positiveEvenEulerPolynomial N)
  have hpLaurent : Polynomial.toLaurent p =
      2 * (finiteEulerProduct (N + 1) *
        finitePositiveEvenEulerProduct (N + 1) *
        finitePositiveEvenEulerProduct N) := by
    dsimp [p]
    rw [map_mul, map_mul, map_mul, map_ofNat,
      toLaurent_evenEulerPolynomial,
      toLaurent_positiveEvenEulerPolynomial,
      toLaurent_positiveEvenEulerPolynomial]
  have hpSeries : polynomialPowerSeriesHom p =
      2 * finiteGaussNeighborReturn N := by
    dsimp [p]
    rw [map_mul, map_mul, map_mul, map_ofNat,
      toPowerSeries_evenEulerPolynomial,
      toPowerSeries_positiveEvenEulerPolynomial,
      toPowerSeries_positiveEvenEulerPolynomial]
    unfold finiteGaussNeighborReturn
    rfl
  rw [← hpLaurent, coeff_toLaurent,
    ← hpSeries, coeff_polynomialPowerSeriesHom]

theorem positiveFiniteDiagonalReceiver_eq_of_coeff_lt
    (F G : BivariateSeries) (d : ℕ)
    (hcoeff : ∀ n < 2 * d + 2,
      PowerSeries.coeff n F = PowerSeries.coeff n G) :
    positiveFiniteDiagonalReceiver d F =
      positiveFiniteDiagonalReceiver d G := by
  unfold positiveFiniteDiagonalReceiver
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hnonneg : 0 ≤ (d : ℤ) - m
  · rw [if_pos hnonneg, if_pos hnonneg]
    have hbox := (Finset.mem_Icc.mp hm).1
    have hlt : ((d : ℤ) - m).toNat < 2 * d + 2 := by
      have hcast : (((d : ℤ) - m).toNat : ℤ) = (d : ℤ) - m :=
        Int.toNat_of_nonneg hnonneg
      omega
    rw [hcoeff _ hlt]
  · rw [if_neg hnonneg, if_neg hnonneg]

theorem positiveFiniteDiagonalReceiver_lhs_eq_finiteTriple (d : ℕ) :
    positiveFiniteDiagonalReceiver d lhs =
      positiveFiniteDiagonalReceiver d
        (finiteBivariateTripleProduct (2 * d + 2)) := by
  apply positiveFiniteDiagonalReceiver_eq_of_coeff_lt
  intro n hn
  exact coeff_lhs_eq_finiteBivariateTripleProduct n (2 * d + 2) hn

/-- The complete product-side positive Jacobi receiver is twice the exact
Gauss product coefficient. -/
theorem positiveFiniteDiagonalReceiver_lhs_eq_two_gauss (d : ℕ) :
    positiveFiniteDiagonalReceiver d lhs =
      PowerSeries.coeff d (2 * gaussTriangularProduct) := by
  let N : ℕ := 2 * d + 1
  have hN : N + 1 = 2 * d + 2 := by dsimp [N]
  have hcone : SquareCone
      (polynomialPowerSeriesHom
        (finitePolynomialTripleProduct (N + 1))) := by
    rw [polynomialPowerSeriesHom_finiteTriple]
    exact finiteBivariateTripleProduct_squareCone (N + 1)
  have hstable := coeff_gaussTriangularProduct_eq_finiteNeighbor d N (by
    dsimp [N]
    omega)
  calc
    positiveFiniteDiagonalReceiver d lhs =
        positiveFiniteDiagonalReceiver d
          (finiteBivariateTripleProduct (2 * d + 2)) :=
      positiveFiniteDiagonalReceiver_lhs_eq_finiteTriple d
    _ = positiveFiniteDiagonalReceiver d
          (polynomialPowerSeriesHom
            (finitePolynomialTripleProduct (N + 1))) := by
      rw [polynomialPowerSeriesHom_finiteTriple, hN]
    _ = positiveFiniteDiagonalHom
          (finitePolynomialTripleProduct (N + 1)) (d : ℤ) :=
      positiveFiniteDiagonalReceiver_polynomial_eq _ _ hcone
    _ = (2 * (finiteEulerProduct (N + 1) *
          finitePositiveEvenEulerProduct (N + 1) *
          finitePositiveEvenEulerProduct N)) (d : ℤ) := by
      rw [positiveFiniteDiagonalHom_tripleProduct]
    _ = PowerSeries.coeff d (2 * finiteGaussNeighborReturn N) :=
      coeff_finitePositiveDiagonalProduct_eq_series d N
    _ = PowerSeries.coeff d (2 * gaussTriangularProduct) := by
      change PowerSeries.coeff d
          (PowerSeries.C (2 : ℤ) * finiteGaussNeighborReturn N) =
        PowerSeries.coeff d
          (PowerSeries.C (2 : ℤ) * gaussTriangularProduct)
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hstable.symm]

/-! ## The two reflected roots and Gauss's triangular series -/

theorem positiveFiniteDiagonalReceiver_rhs (d : ℕ) :
    positiveFiniteDiagonalReceiver d rhs =
      ((diagonalRootPopulation d).card : ℤ) := by
  calc
    positiveFiniteDiagonalReceiver d rhs =
        ∑ m ∈ diagonalRootPopulation d, (1 : ℤ) := by
      rw [positiveFiniteDiagonalReceiver, diagonalRootPopulation,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      rw [coeff_coeff_rhs]
      by_cases hnonneg : 0 ≤ (d : ℤ) - m
      · rw [if_pos hnonneg]
        by_cases hroot : m ^ 2 + m = (d : ℤ)
        · rw [if_pos hroot,
            if_pos ((diagonal_outer_eq_square_iff d m hnonneg).mpr hroot)]
        · rw [if_neg hroot,
            if_neg (not_congr (diagonal_outer_eq_square_iff d m hnonneg) |>.mpr hroot)]
      · rw [if_neg hnonneg]
        have hnotroot : m ^ 2 + m ≠ (d : ℤ) := by
          intro hroot
          apply hnonneg
          nlinarith [sq_nonneg m]
        rw [if_neg hnotroot]
    _ = ((diagonalRootPopulation d).card : ℤ) := by simp

theorem exists_pronic_of_integer_root {d : ℕ} {m : ℤ}
    (hroot : m ^ 2 + m = (d : ℤ)) :
    ∃ k : ℕ, k ^ 2 + k = d := by
  by_cases hm : 0 ≤ m
  · refine ⟨m.toNat, ?_⟩
    have hmcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    exact_mod_cast (show ((m.toNat : ℤ) ^ 2 + (m.toNat : ℤ)) =
      (d : ℤ) by rw [hmcast]; exact hroot)
  · let k : ℕ := (-m - 1).toNat
    have hnonneg : 0 ≤ -m - 1 := by omega
    have hkcast : ((k : ℕ) : ℤ) = -m - 1 := Int.toNat_of_nonneg hnonneg
    refine ⟨k, ?_⟩
    exact_mod_cast (show ((k : ℤ) ^ 2 + (k : ℤ)) = (d : ℤ) by
      rw [hkcast]
      nlinarith)

theorem diagonalRootPopulation_eq_empty_of_no_pronic (d : ℕ)
    (hnone : ¬ ∃ k : ℕ, k ^ 2 + k = d) :
    diagonalRootPopulation d = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  apply hnone
  exact exists_pronic_of_integer_root (Finset.mem_filter.mp hm).2

/-- The natural triangular address population after the reflected integer
pair has been condensed but before affine regrading. -/
local instance pronicAddressDecidable (d : ℕ) :
    Decidable (∃ k : ℕ, k ^ 2 + k = d) := Classical.propDecidable _

def gaussTriangularTheta : PowerSeries ℤ := by
  classical
  exact PowerSeries.mk fun d => if ∃ k : ℕ, k ^ 2 + k = d then 1 else 0

@[simp] theorem coeff_gaussTriangularTheta (d : ℕ) :
    PowerSeries.coeff d gaussTriangularTheta =
      if ∃ k : ℕ, k ^ 2 + k = d then 1 else 0 := by
  classical
  simp [gaussTriangularTheta]

theorem positiveFiniteDiagonalReceiver_rhs_eq_two_gaussTheta (d : ℕ) :
    positiveFiniteDiagonalReceiver d rhs =
      PowerSeries.coeff d (2 * gaussTriangularTheta) := by
  rw [positiveFiniteDiagonalReceiver_rhs]
  by_cases hpronic : ∃ k : ℕ, k ^ 2 + k = d
  · obtain ⟨k, hk⟩ := hpronic
    subst d
    rw [diagonalRootPopulation_triangular]
    have hdistinct : (k : ℤ) ≠ -(k : ℤ) - 1 := by omega
    change (({(k : ℤ), -(k : ℤ) - 1} : Finset ℤ).card : ℤ) = _
    rw [Finset.card_insert_of_notMem (by
      simpa only [Finset.mem_singleton] using hdistinct), Finset.card_singleton]
    change (2 : ℤ) = PowerSeries.coeff (k ^ 2 + k)
      (PowerSeries.C 2 * gaussTriangularTheta)
    rw [PowerSeries.coeff_C_mul, coeff_gaussTriangularTheta]
    simp
  · rw [diagonalRootPopulation_eq_empty_of_no_pronic d hpronic]
    change (0 : ℤ) = PowerSeries.coeff d
      (PowerSeries.C 2 * gaussTriangularTheta)
    rw [PowerSeries.coeff_C_mul, coeff_gaussTriangularTheta, if_neg hpronic]
    ring

/-- **GAUSS TRIANGULAR PRODUCT FROM THE POSITIVE JACOBI DIAGONAL.**
Both sides first occur with the literal reflected-sheet multiplicity `2`;
the final cancellation is therefore exact in `ℤ`, not division by a scalar. -/
theorem gaussTriangularProduct_eq_theta :
    gaussTriangularProduct = gaussTriangularTheta := by
  apply PowerSeries.ext
  intro d
  have hsource : positiveFiniteDiagonalReceiver d lhs =
      positiveFiniteDiagonalReceiver d rhs :=
    congrArg (positiveFiniteDiagonalReceiver d) jacobi_triple_product
  rw [positiveFiniteDiagonalReceiver_lhs_eq_two_gauss,
    positiveFiniteDiagonalReceiver_rhs_eq_two_gaussTheta] at hsource
  rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 by rfl,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hsource
  omega

/-! ## Exact affine return to the residue-one square sheet -/

theorem card_quarterSquareOne_eq_shiftedTriangular (n : ℕ) :
    (quarterSquarePopulation 1 n).card =
      (shiftedTriangularPopulation n).card := by
  let e := (quarterSquareOneEquivJacobiOrientation n).trans
    (jacobiOrientationEquivShiftedTriangular n)
  simpa only [Fintype.card_coe] using Fintype.card_congr e

private theorem shiftedTriangularPopulation_affine_eq_singleton
    {d k : ℕ} (hk : k ^ 2 + k = d) :
    shiftedTriangularPopulation (1 + 4 * d) = {k} := by
  ext j
  simp only [shiftedTriangularPopulation, Finset.mem_filter,
    Finset.mem_range, Finset.mem_singleton]
  constructor
  · intro hj
    have hjIndex := two_mul_triangularIndex j
    have hdegree := hj.2
    have hjpronic : j ^ 2 + j = d := by nlinarith
    have hfactor : (j : ℤ) ^ 2 + j = (k : ℤ) ^ 2 + k := by
      exact_mod_cast hjpronic.trans hk.symm
    have hzero : ((j : ℤ) - k) * ((j : ℤ) + k + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hzero with h | h
    · exact_mod_cast (sub_eq_zero.mp h)
    · have hpos : 0 < (j : ℤ) + k + 1 := by positivity
      exact (hpos.ne' h).elim
  · intro hj
    subst j
    constructor
    · nlinarith
    · have htri := two_mul_triangularIndex k
      nlinarith

private theorem shiftedTriangularPopulation_affine_eq_empty (d : ℕ)
    (hnone : ¬ ∃ k : ℕ, k ^ 2 + k = d) :
    shiftedTriangularPopulation (1 + 4 * d) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  apply hnone
  have hkIndex := two_mul_triangularIndex k
  have hdegree := (Finset.mem_filter.mp hk).2
  refine ⟨k, ?_⟩
  nlinarith

private theorem quarterSquarePopulation_one_empty_of_mod_ne_one
    {n : ℕ} (hn : n % 4 ≠ 1) :
    quarterSquarePopulation 1 n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  let e := (quarterSquareOneEquivJacobiOrientation n).trans
    (jacobiOrientationEquivShiftedTriangular n)
  let k := e ⟨x, hx⟩
  have hk := k.2
  have hdegree := (Finset.mem_filter.mp hk).2
  apply hn
  omega

/-- The residue-one square sheet is exactly the affine regrade
`F(X) ↦ X F(X⁴)` of the positive Jacobi diagonal. -/
theorem affineFourRegrade_gaussTriangularTheta_eq_quarterSquareTheta_one :
    affineFourRegrade gaussTriangularTheta = quarterSquareTheta 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_affineFourRegrade, coeff_quarterSquareTheta]
  by_cases hn : n % 4 = 1
  · rw [if_pos hn]
    have hnpos : 0 < n := by omega
    let d : ℕ := (n - 1) / 4
    have hdecompose : n = 1 + 4 * d := by
      dsimp [d]
      omega
    rw [hdecompose, Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left d (by decide : 0 < 4),
      coeff_gaussTriangularTheta,
      card_quarterSquareOne_eq_shiftedTriangular]
    by_cases hpronic : ∃ k : ℕ, k ^ 2 + k = d
    · rw [if_pos hpronic]
      obtain ⟨k, hk⟩ := hpronic
      rw [shiftedTriangularPopulation_affine_eq_singleton hk]
      simp
    · rw [if_neg hpronic,
        shiftedTriangularPopulation_affine_eq_empty d hpronic]
      simp
  · rw [if_neg hn, quarterSquarePopulation_one_empty_of_mod_ne_one hn]
    simp

theorem quarterSquareTheta_one_eq_X_mul_fourDilate_gaussProduct :
    quarterSquareTheta 1 =
      PowerSeries.X * fourDilate gaussTriangularProduct := by
  rw [← affineFourRegrade_gaussTriangularTheta_eq_quarterSquareTheta_one,
    ← gaussTriangularProduct_eq_theta,
    affineFourRegrade_eq_X_mul_fourDilate]

/-! ## Euler's exact distinct/odd cancellation -/

/-- The finite cancellation body: distinct positive parts through `2N`
paired with odd negative parts through `2N-1`. -/
def finiteDistinctOddCancellation (N : ℕ) : PowerSeries ℤ :=
  qPoch (-PowerSeries.X) PowerSeries.X (2 * N) *
    qPoch PowerSeries.X (PowerSeries.X ^ 2) N

/-- Pairing each odd factor with its opposite leaves precisely the same body
after the exact scale-two chart.  This finite recurrence is the source-level
Euler distinct/odd partition bijection. -/
theorem finiteDistinctOddCancellation_scaleTwo (N : ℕ) :
    finiteDistinctOddCancellation N =
      qPoch (-(PowerSeries.X ^ 2)) (PowerSeries.X ^ 2) N *
        qPoch (PowerSeries.X ^ 2) (PowerSeries.X ^ 4) N := by
  induction N with
  | zero => simp [finiteDistinctOddCancellation, qPoch]
  | succ N ih =>
      unfold finiteDistinctOddCancellation at ih ⊢
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        qPoch_succ', show 2 * N + 1 = 2 * N + 1 by rfl, qPoch_succ',
        qPoch_succ' PowerSeries.X (PowerSeries.X ^ 2) N,
        qPoch_succ' (-(PowerSeries.X ^ 2)) (PowerSeries.X ^ 2) N,
        qPoch_succ' (PowerSeries.X ^ 2) (PowerSeries.X ^ 4) N]
      have hodd :
          (-PowerSeries.X : PowerSeries ℤ) * PowerSeries.X ^ (2 * N) =
            -(PowerSeries.X ^ (2 * N + 1)) := by
        rw [show PowerSeries.X ^ (2 * N + 1) =
          PowerSeries.X ^ (2 * N) * PowerSeries.X by rw [pow_succ]]
        ring
      have heven :
          (-PowerSeries.X : PowerSeries ℤ) * PowerSeries.X ^ (2 * N + 1) =
            -(PowerSeries.X ^ (2 * N + 2)) := by
        rw [show PowerSeries.X ^ (2 * N + 2) =
          PowerSeries.X ^ (2 * N + 1) * PowerSeries.X by rw [pow_succ]]
        ring
      have hoddSquare :
          (PowerSeries.X : PowerSeries ℤ) *
              (PowerSeries.X ^ 2) ^ N =
            PowerSeries.X ^ (2 * N + 1) := by
        rw [← pow_mul, show 2 * N + 1 = 1 + 2 * N by omega, pow_add]
        ring
      have hevenSquare :
          (-(PowerSeries.X ^ 2) : PowerSeries ℤ) *
              (PowerSeries.X ^ 2) ^ N =
            -(PowerSeries.X ^ (2 * N + 2)) := by
        rw [← pow_mul, show 2 * N + 2 = 2 + 2 * N by omega, pow_add]
        ring
      have hoddFourth :
          (PowerSeries.X ^ 2 : PowerSeries ℤ) *
              (PowerSeries.X ^ 4) ^ N =
            PowerSeries.X ^ (4 * N + 2) := by
        rw [← pow_mul, show 4 * N + 2 = 2 + 4 * N by omega, pow_add]
      have hpair :
          (1 + (PowerSeries.X : PowerSeries ℤ) ^ (2 * N + 1)) *
              (1 - (PowerSeries.X : PowerSeries ℤ) ^ (2 * N + 1)) =
            1 - (PowerSeries.X : PowerSeries ℤ) ^ (4 * N + 2) := by
        rw [show 4 * N + 2 = 2 * (2 * N + 1) by omega, pow_mul]
        ring
      have hfactor :
          (1 - (-PowerSeries.X : PowerSeries ℤ) * PowerSeries.X ^ (2 * N)) *
                (1 - (-PowerSeries.X : PowerSeries ℤ) *
                  PowerSeries.X ^ (2 * N + 1)) *
                (1 - (PowerSeries.X : PowerSeries ℤ) *
                  (PowerSeries.X ^ 2) ^ N) =
            (1 - (-(PowerSeries.X ^ 2) : PowerSeries ℤ) *
                (PowerSeries.X ^ 2) ^ N) *
              (1 - (PowerSeries.X ^ 2 : PowerSeries ℤ) *
                (PowerSeries.X ^ 4) ^ N) := by
        rw [hodd, heven, hoddSquare, hevenSquare, hoddFourth, ← hpair]
        ring
      calc
        qPoch (-(PowerSeries.X : PowerSeries ℤ))
              (PowerSeries.X : PowerSeries ℤ) (2 * N) *
              (1 - (-(PowerSeries.X : PowerSeries ℤ)) *
                (PowerSeries.X : PowerSeries ℤ) ^ (2 * N)) *
              (1 - (-(PowerSeries.X : PowerSeries ℤ)) *
                (PowerSeries.X : PowerSeries ℤ) ^ (2 * N + 1)) *
              (qPoch (PowerSeries.X : PowerSeries ℤ)
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) N *
                (1 - (PowerSeries.X : PowerSeries ℤ) *
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ N)) =
            (qPoch (-(PowerSeries.X : PowerSeries ℤ))
                  (PowerSeries.X : PowerSeries ℤ) (2 * N) *
                qPoch (PowerSeries.X : PowerSeries ℤ)
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) N) *
              ((1 - (-(PowerSeries.X : PowerSeries ℤ)) *
                  (PowerSeries.X : PowerSeries ℤ) ^ (2 * N)) *
                (1 - (-(PowerSeries.X : PowerSeries ℤ)) *
                  (PowerSeries.X : PowerSeries ℤ) ^ (2 * N + 1)) *
                (1 - (PowerSeries.X : PowerSeries ℤ) *
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ N)) := by ring
        _ = (qPoch (-((PowerSeries.X : PowerSeries ℤ) ^ 2))
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) N *
                qPoch ((PowerSeries.X : PowerSeries ℤ) ^ 2)
                  ((PowerSeries.X : PowerSeries ℤ) ^ 4) N) *
              ((1 - (-(PowerSeries.X : PowerSeries ℤ)) *
                  (PowerSeries.X : PowerSeries ℤ) ^ (2 * N)) *
                (1 - (-(PowerSeries.X : PowerSeries ℤ)) *
                  (PowerSeries.X : PowerSeries ℤ) ^ (2 * N + 1)) *
                (1 - (PowerSeries.X : PowerSeries ℤ) *
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ N)) := by rw [ih]
        _ = (qPoch (-((PowerSeries.X : PowerSeries ℤ) ^ 2))
                  ((PowerSeries.X : PowerSeries ℤ) ^ 2) N *
                qPoch ((PowerSeries.X : PowerSeries ℤ) ^ 2)
                  ((PowerSeries.X : PowerSeries ℤ) ^ 4) N) *
              ((1 - (-((PowerSeries.X : PowerSeries ℤ) ^ 2)) *
                    ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ N) *
                (1 - (PowerSeries.X : PowerSeries ℤ) ^ 2 *
                  ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ N)) := by
              rw [hfactor]
        _ = qPoch (-((PowerSeries.X : PowerSeries ℤ) ^ 2))
                ((PowerSeries.X : PowerSeries ℤ) ^ 2) N *
              (1 - (-((PowerSeries.X : PowerSeries ℤ) ^ 2)) *
                ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ N) *
              (qPoch ((PowerSeries.X : PowerSeries ℤ) ^ 2)
                  ((PowerSeries.X : PowerSeries ℤ) ^ 4) N *
                (1 - (PowerSeries.X : PowerSeries ℤ) ^ 2 *
                  ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ N)) := by ring

private theorem integerQpochSplit (A Q : PowerSeries ℤ) (n k : ℕ) :
    qPoch A Q (n + k) = qPoch A Q n * qPoch (A * Q ^ n) Q k := by
  rw [qPoch, qPoch, qPoch, Finset.prod_range_add]
  simp [pow_add, mul_assoc]

private theorem integerAntidiagSumEq
    (f g : PowerSeries ℤ) (m : ℕ)
    (hg : ∀ j ≤ m, PowerSeries.coeff j g = if j = 0 then 1 else 0) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g =
      PowerSeries.coeff m f := by
  rw [Finset.sum_eq_single_of_mem (m, 0)
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero m))
    (fun b hb hne => ?_)]
  · simp [hg 0 (Nat.zero_le m)]
  · have hbSum := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    rw [hg b.2 (by omega), if_neg (fun h => hne (by ext <;> simp_all)), mul_zero]

private theorem integerCoeffMulOfTruncOne
    (f g : PowerSeries ℤ) (m : ℕ)
    (hg : ∀ j ≤ m, PowerSeries.coeff j g = if j = 0 then 1 else 0) :
    PowerSeries.coeff m (f * g) = PowerSeries.coeff m f := by
  rw [PowerSeries.coeff_mul]
  exact integerAntidiagSumEq f g m hg

private theorem integerProdCoeffDelta
    (m : ℕ) (f : ℕ → PowerSeries ℤ) (k : ℕ)
    (hf : ∀ i < k, ∀ j ≤ m,
      PowerSeries.coeff j (f i) = if j = 0 then 1 else 0)
    (j : ℕ) (hj : j ≤ m) :
    PowerSeries.coeff j (∏ i ∈ Finset.range k, f i) =
      if j = 0 then 1 else 0 := by
  induction k with
  | zero => simp [PowerSeries.coeff_one]
  | succ k ih =>
      rw [Finset.prod_range_succ,
        integerCoeffMulOfTruncOne _ _ j
          (fun j' hj' => hf k (Nat.lt_succ_self k) j' (le_trans hj' hj))]
      exact ih (fun i hi j' hj' => hf i (Nat.lt_succ_of_lt hi) j' hj')

private theorem distinctTailFactorDelta
    (m n i j : ℕ) (hmn : m < n) (hj : j ≤ m) :
    PowerSeries.coeff j
        (1 - ((-(PowerSeries.X : PowerSeries ℤ)) * PowerSeries.X ^ n) *
          PowerSeries.X ^ i) =
      if j = 0 then 1 else 0 := by
  have hpow :
      ((-(PowerSeries.X : PowerSeries ℤ)) * PowerSeries.X ^ n) *
          PowerSeries.X ^ i =
        -(PowerSeries.X ^ (n + i + 1)) := by
    rw [show PowerSeries.X ^ (n + i + 1) =
      (PowerSeries.X : PowerSeries ℤ) * PowerSeries.X ^ n *
        PowerSeries.X ^ i by
          rw [show n + i + 1 = 1 + n + i by omega, pow_add, pow_add,
            pow_one]]
    ring
  rw [hpow]
  simp only [sub_neg_eq_add, map_add, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow]
  split_ifs <;> omega

private theorem oddTailFactorDelta
    (m n i j : ℕ) (hmn : m < n) (hj : j ≤ m) :
    PowerSeries.coeff j
        (1 - ((PowerSeries.X : PowerSeries ℤ) *
            (PowerSeries.X ^ 2) ^ n) *
          (PowerSeries.X ^ 2) ^ i) =
      if j = 0 then 1 else 0 := by
  have hpow :
      ((PowerSeries.X : PowerSeries ℤ) *
          (PowerSeries.X ^ 2) ^ n) * (PowerSeries.X ^ 2) ^ i =
        PowerSeries.X ^ (2 * (n + i) + 1) := by
    rw [← pow_mul, ← pow_mul,
      show 2 * (n + i) + 1 = 1 + 2 * n + 2 * i by omega, pow_add, pow_add]
    simp
  rw [hpow]
  simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  split_ifs <;> omega

private theorem distinctTailCoeffDelta
    (m n k j : ℕ) (hmn : m < n) (hj : j ≤ m) :
    PowerSeries.coeff j
        (qPoch ((-(PowerSeries.X : PowerSeries ℤ)) *
          PowerSeries.X ^ n) PowerSeries.X k) =
      if j = 0 then 1 else 0 := by
  unfold qPoch
  exact integerProdCoeffDelta m
    (fun i => 1 - ((-(PowerSeries.X : PowerSeries ℤ)) *
      PowerSeries.X ^ n) * PowerSeries.X ^ i) k
    (fun i _hi j hj => distinctTailFactorDelta m n i j hmn hj) j hj

private theorem oddTailCoeffDelta
    (m n k j : ℕ) (hmn : m < n) (hj : j ≤ m) :
    PowerSeries.coeff j
        (qPoch ((PowerSeries.X : PowerSeries ℤ) *
          (PowerSeries.X ^ 2) ^ n) (PowerSeries.X ^ 2) k) =
      if j = 0 then 1 else 0 := by
  unfold qPoch
  exact integerProdCoeffDelta m
    (fun i => 1 - ((PowerSeries.X : PowerSeries ℤ) *
      (PowerSeries.X ^ 2) ^ n) * (PowerSeries.X ^ 2) ^ i) k
    (fun i _hi j hj => oddTailFactorDelta m n i j hmn hj) j hj

private theorem distinctPartialProdsCoeffStable
    (m n n' : ℕ) (hmn : m < n) (hnn' : n ≤ n') :
    PowerSeries.coeff m
        (qPoch (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X n') =
      PowerSeries.coeff m
        (qPoch (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  rw [integerQpochSplit]
  exact integerCoeffMulOfTruncOne _ _ m
    (distinctTailCoeffDelta m n k · hmn)

private theorem oddPartialProdsCoeffStable
    (m n n' : ℕ) (hmn : m < n) (hnn' : n ≤ n') :
    PowerSeries.coeff m
        (qPoch (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2) n') =
      PowerSeries.coeff m
        (qPoch (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2) n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  rw [integerQpochSplit]
  exact integerCoeffMulOfTruncOne _ _ m
    (oddTailCoeffDelta m n k · hmn)

private theorem distinctFactorsMultipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (-(PowerSeries.X : PowerSeries ℤ)) * PowerSeries.X ^ n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [show (fun n =>
      1 - (-(PowerSeries.X : PowerSeries ℤ)) * PowerSeries.X ^ n) =
      (fun n => 1 + (PowerSeries.X : PowerSeries ℤ) ^ (n + 1)) by
        funext n
        rw [show (PowerSeries.X : PowerSeries ℤ) ^ (n + 1) =
          PowerSeries.X * PowerSeries.X ^ n by rw [pow_succ'];]
        ring]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_X_pow]
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro d
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact ENat.coe_lt_coe.mpr (by omega)

private theorem oddFactorsMultipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X ^ 2) ^ n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [show (fun n =>
      1 - (PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X ^ 2) ^ n) =
      (fun n => 1 + (-(PowerSeries.X ^ (2 * n + 1)) : PowerSeries ℤ)) by
        funext n
        rw [show (PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X ^ 2) ^ n =
          PowerSeries.X ^ (2 * n + 1) by
            rw [← pow_mul, show 2 * n + 1 = 1 + 2 * n by omega, pow_add]
            simp]
        ring]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_neg, PowerSeries.order_X_pow]
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro d
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact ENat.coe_lt_coe.mpr (by omega)

private theorem coeffDistinctTprodEqFinite (m n : ℕ) (hmn : m < n) :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    PowerSeries.coeff m
        (∏' i, (1 - (-(PowerSeries.X : PowerSeries ℤ)) *
          PowerSeries.X ^ i)) =
      PowerSeries.coeff m
        (qPoch (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  exact tendsto_nhds_unique
    ((PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      ℤ _ _ _).mp distinctFactorsMultipliable.tendsto_prod_tprod_nat m)
    (tendsto_atTop_of_eventually_const (i₀ := n) (fun k hk =>
      distinctPartialProdsCoeffStable m n k hmn hk))

private theorem coeffOddTprodEqFinite (m n : ℕ) (hmn : m < n) :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    PowerSeries.coeff m
        (∏' i, (1 - (PowerSeries.X : PowerSeries ℤ) *
          (PowerSeries.X ^ 2) ^ i)) =
      PowerSeries.coeff m
        (qPoch (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2) n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  exact tendsto_nhds_unique
    ((PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      ℤ _ _ _).mp oddFactorsMultipliable.tendsto_prod_tprod_nat m)
    (tendsto_atTop_of_eventually_const (i₀ := n) (fun k hk =>
      oddPartialProdsCoeffStable m n k hmn hk))

theorem coeff_distinctPochhammerInf_eq_finite
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d
        (qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X) =
      PowerSeries.coeff d
        (qPoch (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X N) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  erw [integer_qPochhammerInf_eq_tprod _ _ distinctFactorsMultipliable]
  exact coeffDistinctTprodEqFinite d N h

theorem coeff_oddPochhammerInf_eq_finite
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d
        (qPochhammerInf (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2)) =
      PowerSeries.coeff d
        (qPoch (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2) N) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  erw [integer_qPochhammerInf_eq_tprod _ _ oddFactorsMultipliable]
  exact coeffOddTprodEqFinite d N h

/-- The completed distinct/odd Euler cancellation body. -/
def infiniteDistinctOddCancellation : PowerSeries ℤ :=
  qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X *
    qPochhammerInf (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2)

theorem coeff_infiniteDistinctOddCancellation_eq_finite
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d infiniteDistinctOddCancellation =
      PowerSeries.coeff d (finiteDistinctOddCancellation N) := by
  apply coeff_mul_eq_of_coeff_le
  · intro j hj
    exact coeff_distinctPochhammerInf_eq_finite j (2 * N) (by omega)
  · intro j hj
    exact coeff_oddPochhammerInf_eq_finite j N (by omega)

/-- The exact scale-two receiver used by the finite Euler recurrence. -/
def twoDilate : PowerSeries ℤ →+* PowerSeries ℤ :=
  exactDilateHom 2 (by decide)

@[simp] theorem twoDilate_X :
    twoDilate (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X ^ 2 := by
  unfold twoDilate
  exact PowerSeries.substAlgHom_X
    (PowerSeries.HasSubst.X_pow (by decide : 2 ≠ 0))

@[simp] theorem coeff_twoDilate (F : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (twoDilate F) =
      if 2 ∣ n then PowerSeries.coeff (n / 2) F else 0 := by
  exact coeff_exactDilate 2 (by decide) F n

theorem twoDilate_continuous :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Continuous twoDilate := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  refine continuous_pi_iff.mpr ?_
  intro i
  change Continuous (fun F : PowerSeries ℤ => twoDilate F i)
  have heval : (fun F : PowerSeries ℤ => twoDilate F i) =
      (fun F => PowerSeries.coeff (i ()) (twoDilate F)) := by
    funext F
    change twoDilate F i = twoDilate F (Finsupp.single () (i ()))
    have hi : i = Finsupp.single () (i ()) := by
      ext
      simp
    rw [hi]
    simp
  rw [heval]
  by_cases h : 2 ∣ i ()
  · have hc := PowerSeries.WithPiTopology.continuous_coeff ℤ ((i ()) / 2)
    convert hc using 1
    funext F
    rw [coeff_twoDilate, if_pos h]
  · have hz : (fun F : PowerSeries ℤ =>
        PowerSeries.coeff (i ()) (twoDilate F)) = fun _ => 0 := by
      funext F
      rw [coeff_twoDilate, if_neg h]
    rw [hz]
    fun_prop

/-- Exact composition of the scale-four and scale-two charts. -/
def eightDilate : PowerSeries ℤ →+* PowerSeries ℤ :=
  twoDilate.comp fourDilate

@[simp] theorem eightDilate_X :
    eightDilate (PowerSeries.X : PowerSeries ℤ) = PowerSeries.X ^ 8 := by
  simp [eightDilate]
  ring

theorem eightDilate_continuous :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Continuous eightDilate := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  exact twoDilate_continuous.comp fourDilate_continuous

theorem eightDilate_qPochhammerInf (A Q : PowerSeries ℤ)
    (hm : letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
      Multipliable (fun n => 1 - A * Q ^ n)) :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    eightDilate (qPochhammerInf A Q) =
      qPochhammerInf (eightDilate A) (eightDilate Q) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  letI : T2Space (PowerSeries ℤ) :=
    PowerSeries.WithPiTopology.instT2Space ℤ
  have hterm (n : ℕ) :
      eightDilate (1 - A * Q ^ n) =
        1 - eightDilate A * eightDilate Q ^ n := by simp
  have hmTarget : Multipliable (fun n =>
      1 - eightDilate A * eightDilate Q ^ n) := by
    exact (hm.map eightDilate eightDilate_continuous).congr hterm
  erw [integer_qPochhammerInf_eq_tprod A Q hm,
    integer_qPochhammerInf_eq_tprod _ _ hmTarget]
  calc
    eightDilate (∏' n, (1 - A * Q ^ n)) =
        ∏' n, eightDilate (1 - A * Q ^ n) :=
      hm.map_tprod eightDilate eightDilate_continuous
    _ = ∏' n, (1 - eightDilate A * eightDilate Q ^ n) := by
      congr 1
      funext n
      exact hterm n

/-- The shorter finite body whose exact doubling is the paired return. -/
def finiteDistinctOddCore (N : ℕ) : PowerSeries ℤ :=
  qPoch (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X N *
    qPoch (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 2) N

theorem coeff_infiniteDistinctOddCancellation_eq_finiteCore
    (d N : ℕ) (h : d < N) :
    PowerSeries.coeff d infiniteDistinctOddCancellation =
      PowerSeries.coeff d (finiteDistinctOddCore N) := by
  apply coeff_mul_eq_of_coeff_le
  · intro j hj
    exact coeff_distinctPochhammerInf_eq_finite j N (by omega)
  · intro j hj
    exact coeff_oddPochhammerInf_eq_finite j N (by omega)

theorem finiteDistinctOddCancellation_eq_twoDilateCore (N : ℕ) :
    finiteDistinctOddCancellation N =
      twoDilate (finiteDistinctOddCore N) := by
  calc
    finiteDistinctOddCancellation N =
        qPoch (-(PowerSeries.X ^ 2)) (PowerSeries.X ^ 2) N *
          qPoch (PowerSeries.X ^ 2) (PowerSeries.X ^ 4) N :=
      finiteDistinctOddCancellation_scaleTwo N
    _ = twoDilate (finiteDistinctOddCore N) := by
      unfold finiteDistinctOddCore
      simp only [map_mul]
      rw [map_qPoch, map_qPoch]
      simp [show ((PowerSeries.X : PowerSeries ℤ) ^ 2) ^ 2 =
        PowerSeries.X ^ 4 by ring]

/-- Completion preserves the exact finite scale-two recurrence. -/
theorem infiniteDistinctOddCancellation_eq_twoDilate :
    infiniteDistinctOddCancellation =
      twoDilate infiniteDistinctOddCancellation := by
  apply PowerSeries.ext
  intro d
  let N := d + 1
  have hdN : d < N := by simp [N]
  calc
    PowerSeries.coeff d infiniteDistinctOddCancellation =
        PowerSeries.coeff d (finiteDistinctOddCancellation N) :=
      coeff_infiniteDistinctOddCancellation_eq_finite d N hdN
    _ = PowerSeries.coeff d
          (twoDilate (finiteDistinctOddCore N)) := by
      exact congrArg (PowerSeries.coeff d)
        (finiteDistinctOddCancellation_eq_twoDilateCore N)
    _ = if 2 ∣ d then
          PowerSeries.coeff (d / 2) (finiteDistinctOddCore N) else 0 := by
      rw [coeff_twoDilate]
    _ = if 2 ∣ d then
          PowerSeries.coeff (d / 2) infiniteDistinctOddCancellation else 0 := by
      split_ifs
      rw [coeff_infiniteDistinctOddCancellation_eq_finiteCore (d / 2) N (by omega)]
      rfl
    _ = PowerSeries.coeff d
          (twoDilate infiniteDistinctOddCancellation) := by
      rw [coeff_twoDilate]

/-- **EULER DISTINCT/ODD CANCELLATION.**  The only complete power series
fixed by the exact doubling chart and with the returned constant face is the
unit series. -/
theorem infiniteDistinctOddCancellation_eq_one :
    infiniteDistinctOddCancellation = 1 := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [coeff_infiniteDistinctOddCancellation_eq_finite 0 1 (by decide)]
        simp [finiteDistinctOddCancellation, qPoch]
      · have hfixed := congrArg (PowerSeries.coeff n)
          infiniteDistinctOddCancellation_eq_twoDilate
        rw [coeff_twoDilate] at hfixed
        by_cases hdiv : 2 ∣ n
        · rw [if_pos hdiv] at hfixed
          have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
          have hpos : 0 < n / 2 := by
            obtain ⟨k, hk⟩ := hdiv
            omega
          rw [hfixed, ih (n / 2) hlt]
          simp [PowerSeries.coeff_one, hpos.ne', hn]
        · rw [if_neg hdiv] at hfixed
          rw [hfixed]
          simp [PowerSeries.coeff_one, hn]

theorem distinctOddPochhammerInf_mul_eq_one :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ)) PowerSeries.X *
        qPochhammerInf (PowerSeries.X : PowerSeries ℤ)
          (PowerSeries.X ^ 2) = 1 := by
  exact infiniteDistinctOddCancellation_eq_one

private theorem positiveOddFactorsMultipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (-(PowerSeries.X : PowerSeries ℤ)) *
        (PowerSeries.X ^ 2) ^ n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [show (fun n =>
      1 - (-(PowerSeries.X : PowerSeries ℤ)) *
        (PowerSeries.X ^ 2) ^ n) =
      (fun n => 1 + (PowerSeries.X : PowerSeries ℤ) ^ (2 * n + 1)) by
        funext n
        have hx : (PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X ^ 2) ^ n =
          PowerSeries.X ^ (2 * n + 1) := by
            rw [← pow_mul, show 2 * n + 1 = 1 + 2 * n by omega, pow_add]
            simp
        rw [show (-(PowerSeries.X : PowerSeries ℤ)) *
            (PowerSeries.X ^ 2) ^ n = -PowerSeries.X ^ (2 * n + 1) by
          rw [neg_mul, hx]]
        ring]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_X_pow]
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro d
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact ENat.coe_lt_coe.mpr (by omega)

private theorem pairedUnitFactorsMultipliable :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (PowerSeries.X : PowerSeries ℤ) ^ 2 *
        (PowerSeries.X ^ 4) ^ n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have hmul := positiveOddFactorsMultipliable.mul oddFactorsMultipliable
  exact hmul.congr (fun n => by
    have hp :
        ((PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X ^ 2) ^ n) ^ 2 =
          PowerSeries.X ^ 2 * (PowerSeries.X ^ 4) ^ n := by
      rw [mul_pow, ← pow_mul, ← pow_mul,
        show 2 * (n * 2) = 4 * n by ring]
      rw [← pow_mul]
    rw [← hp]
    ring)

/-- Opposite unit-orientation factors pair into the odd scale-two Euler
population, before any theta receiver is applied. -/
theorem positiveNegativeUnitPochhammer_pair :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ))
          (PowerSeries.X ^ 2) *
        qPochhammerInf (PowerSeries.X : PowerSeries ℤ)
          (PowerSeries.X ^ 2) =
      qPochhammerInf (PowerSeries.X ^ 2) (PowerSeries.X ^ 4) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  erw [integer_qPochhammerInf_eq_tprod _ _ positiveOddFactorsMultipliable,
    integer_qPochhammerInf_eq_tprod _ _ oddFactorsMultipliable,
    integer_qPochhammerInf_eq_tprod _ _ pairedUnitFactorsMultipliable,
    ← positiveOddFactorsMultipliable.tprod_mul oddFactorsMultipliable]
  congr 1
  funext n
  have hp :
      ((PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X ^ 2) ^ n) ^ 2 =
        PowerSeries.X ^ 2 * (PowerSeries.X ^ 4) ^ n := by
    rw [mul_pow, ← pow_mul, ← pow_mul,
      show 2 * (n * 2) = 4 * n by ring]
    rw [← pow_mul]
  rw [← hp]
  ring

theorem scaleEightDistinctOddCancellation :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ) ^ 8)
          (PowerSeries.X ^ 8) *
        qPochhammerInf (PowerSeries.X ^ 8) (PowerSeries.X ^ 16) = 1 := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have h := congrArg eightDilate distinctOddPochhammerInf_mul_eq_one
  simp only [map_mul, map_one] at h
  rw [eightDilate_qPochhammerInf _ _ distinctFactorsMultipliable,
    eightDilate_qPochhammerInf _ _ oddFactorsMultipliable] at h
  simp only [map_neg, map_pow, eightDilate_X] at h
  have h16 : ((PowerSeries.X : PowerSeries ℤ) ^ 8) ^ 2 =
      PowerSeries.X ^ 16 := by ring
  rw [h16] at h
  exact h

theorem scaleFourUnitPochhammer_pair :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ) ^ 4)
          (PowerSeries.X ^ 8) *
        qPochhammerInf (PowerSeries.X ^ 4) (PowerSeries.X ^ 8) =
      qPochhammerInf (PowerSeries.X ^ 8) (PowerSeries.X ^ 16) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have h := congrArg fourDilate positiveNegativeUnitPochhammer_pair
  simp only [map_mul] at h
  erw [fourDilate_qPochhammerInf _ _ positiveOddFactorsMultipliable,
    fourDilate_qPochhammerInf _ _ oddFactorsMultipliable,
    fourDilate_qPochhammerInf _ _ pairedUnitFactorsMultipliable] at h
  simp only [map_neg, map_pow, fourDilate_X] at h
  have h8 : ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ 2 =
      PowerSeries.X ^ 8 := by ring
  have h16 : ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ 4 =
      PowerSeries.X ^ 16 := by ring
  rw [h8, h16] at h
  exact h

theorem fourDilate_infinitePositiveEvenEulerProduct_eq_scaleEight :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    fourDilate infinitePositiveEvenEulerProduct =
      qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ) ^ 8)
        (PowerSeries.X ^ 8) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  unfold infinitePositiveEvenEulerProduct
  erw [fourDilate_qPochhammerInf _ _ integerPositiveEvenFactors_multipliable]
  simp only [map_neg, map_pow, fourDilate_X]
  have h8 : ((PowerSeries.X : PowerSeries ℤ) ^ 4) ^ 2 =
      PowerSeries.X ^ 8 := by ring
  rw [h8]

/-- **THE MISSING QUARTER-SQUARE FACTOR.**  The positive Jacobi diagonal,
the two unit-orientation faces, and Euler's exact distinct/odd cancellation
close the source-specific factor passage. -/
theorem quarterSquareTheta_factor_closure :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    quarterSquareTheta 1 *
          (quarterSquareTheta 0 + quarterSquareTheta 2) *
          (quarterSquareTheta 0 - quarterSquareTheta 2) =
      weightedQuarterSquareTheta 1 := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [quarterSquareTheta_one_eq_X_mul_fourDilate_gaussProduct]
  unfold gaussTriangularProduct
  simp only [map_mul, map_pow]
  rw [fourDilate_infiniteEvenEulerProduct_eq_scaleEight,
    fourDilate_infinitePositiveEvenEulerProduct_eq_scaleEight,
    ← evenSum_eq_scaleEightJacobiProduct,
    ← evenDifference_eq_scaleEightJacobiProduct,
    weightedQuarterSquareTheta_eq_scaleEightEulerCube]
  let E := qPochhammerInf ((PowerSeries.X : PowerSeries ℤ) ^ 8)
    (PowerSeries.X ^ 8)
  let D := qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ) ^ 8)
    (PowerSeries.X ^ 8)
  let P := qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ) ^ 4)
    (PowerSeries.X ^ 8)
  let M := qPochhammerInf ((PowerSeries.X : PowerSeries ℤ) ^ 4)
    (PowerSeries.X ^ 8)
  let O := qPochhammerInf ((PowerSeries.X : PowerSeries ℤ) ^ 8)
    (PowerSeries.X ^ 16)
  have hpair : P * M = O := by
    exact scaleFourUnitPochhammer_pair
  have hcancel : D * O = 1 := by
    exact scaleEightDistinctOddCancellation
  change (PowerSeries.X * (E * D ^ 2)) * (E * P ^ 2) *
      (E * M ^ 2) = PowerSeries.X * (E ^ 2 * E)
  calc
    (PowerSeries.X * (E * D ^ 2)) * (E * P ^ 2) * (E * M ^ 2) =
        PowerSeries.X * (E ^ 2 * E) * (D * (P * M)) ^ 2 := by ring
    _ = PowerSeries.X * (E ^ 2 * E) * (D * O) ^ 2 := by rw [hpair]
    _ = PowerSeries.X * (E ^ 2 * E) := by rw [hcancel]; ring

/-- **UNCONDITIONAL HOPF--HECKE CURRENT LAW.**  The source-specific Hopf
theta current is exactly eight copies of the Hecke coefficient current;
there is no remaining factor hypothesis. -/
theorem hopfHeckeThetaCurrent_eq_eight_mul_heckeCoefficientSeries :
    hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries := by
  unfold hopfHeckeThetaCurrent
  calc
    8 * quarterSquareTheta 1 *
          (quarterSquareTheta 0 + quarterSquareTheta 2) *
          (quarterSquareTheta 0 - quarterSquareTheta 2) ^ 2 =
        8 * (quarterSquareTheta 1 *
          (quarterSquareTheta 0 + quarterSquareTheta 2) *
          (quarterSquareTheta 0 - quarterSquareTheta 2)) *
          (quarterSquareTheta 0 - quarterSquareTheta 2) := by ring
    _ = 8 * weightedQuarterSquareTheta 1 *
          (quarterSquareTheta 0 - quarterSquareTheta 2) := by
      rw [quarterSquareTheta_factor_closure]
    _ = 8 * (weightedQuarterSquareTheta 1 *
          (quarterSquareTheta 0 - quarterSquareTheta 2)) := by ring
    _ = 8 * heckeCoefficientSeries := by
      rw [weighted_mul_evenDifference_eq_heckeCoefficientSeries]

#print axioms gaussTriangularProduct_eq_theta
#print axioms infiniteDistinctOddCancellation_eq_one
#print axioms quarterSquareTheta_factor_closure
#print axioms hopfHeckeThetaCurrent_eq_eight_mul_heckeCoefficientSeries

end Soma.Holonics.Millennium.FamilyTunnellJacobiGaussFactor
