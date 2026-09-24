import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalReceiver
import ElementaryHolonics.Millennium.FamilyTunnellJacobiRegrading

/-!
# The Jacobi product receiver is the Tunnell orientation stream

The differentiated bivariate Jacobi product already carries the signed
triangular current, but in the diagonal degree chart

`d = k² + k`.

The Tunnell quarter-residue receiver uses the affine chart

`n = 1 + 4d = 1 + 8 Tₖ`.

This file constructs that chart as an exact power-series receiver.  It proves
both parts required for equality of complete series: every admitted diagonal
coefficient returns the Jacobi weight, and every coefficient outside the
`1 mod 4` image is zero.  Thus no sampled coefficient or analytic limit is
used in the passage from the Jacobi product body to the Tunnell source.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiProductReceiver

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiEulerDerivative
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalReceiver
open Soma.Holonics.Millennium.FamilyTunnellJacobiRegrading
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift

/-- The complete diagonal coefficient stream returned from the differentiated
Jacobi product. -/
def jacobiProductDiagonalTheta : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    finiteDiagonalReceiver d (bivariateEulerDerivative lhs)

@[simp] theorem coeff_jacobiProductDiagonalTheta (d : ℕ) :
    PowerSeries.coeff d jacobiProductDiagonalTheta =
      finiteDiagonalReceiver d (bivariateEulerDerivative lhs) := by
  simp [jacobiProductDiagonalTheta]

/-- An integer root of `m²+m=d` always returns a natural pronic root.  The
negative sheet is reflected by `m ↦ -m-1`; this is the source-side swing which
pairs the two orientations. -/
private theorem exists_pronic_of_integer_root {d : ℕ} {m : ℤ}
    (hroot : m ^ 2 + m = (d : ℤ)) :
    ∃ k : ℕ, k ^ 2 + k = d := by
  by_cases hm : 0 ≤ m
  · refine ⟨m.toNat, ?_⟩
    have hmcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    have hkroot : ((m.toNat : ℤ) ^ 2 + (m.toNat : ℤ)) = (d : ℤ) := by
      rw [hmcast]
      exact hroot
    exact_mod_cast hkroot
  · have hmneg : m ≤ -1 := by omega
    let k : ℕ := (-m - 1).toNat
    have hnonneg : 0 ≤ -m - 1 := by omega
    have hkcast : ((k : ℕ) : ℤ) = -m - 1 := by
      exact Int.toNat_of_nonneg hnonneg
    have hkroot : ((k : ℤ) ^ 2 + (k : ℤ)) = (d : ℤ) := by
      rw [hkcast]
      nlinarith
    exact ⟨k, by exact_mod_cast hkroot⟩

private theorem diagonalRootPopulation_eq_empty_of_no_pronic (d : ℕ)
    (hnone : ¬ ∃ k : ℕ, k ^ 2 + k = d) :
    diagonalRootPopulation d = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  apply hnone
  exact exists_pronic_of_integer_root (Finset.mem_filter.mp hm).2

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
    have hjpronic : j ^ 2 + j = d := by
      nlinarith
    have hfactor : (j : ℤ) ^ 2 + j = (k : ℤ) ^ 2 + k := by
      exact_mod_cast hjpronic.trans hk.symm
    have hzero : ((j : ℤ) - k) * ((j : ℤ) + k + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hzero with h | h
    · exact_mod_cast (sub_eq_zero.mp h)
    · have : 0 < (j : ℤ) + k + 1 := by positivity
      exact (this.ne' h).elim
  · intro hj
    subst j
    constructor
    · nlinarith
    · have hkIndex := two_mul_triangularIndex k
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

/-- Every affine diagonal coefficient of the Tunnell triangular stream is the
finite coefficient receiver of the differentiated Jacobi product. -/
theorem coeff_shiftedJacobi_eq_jacobiProductDiagonal (d : ℕ) :
    PowerSeries.coeff (1 + 4 * d) shiftedJacobiTriangularTheta =
      PowerSeries.coeff d jacobiProductDiagonalTheta := by
  by_cases hpronic : ∃ k : ℕ, k ^ 2 + k = d
  · obtain ⟨k, hk⟩ := hpronic
    rw [coeff_shiftedJacobiTriangularTheta,
      shiftedTriangularPopulation_affine_eq_singleton hk]
    simp only [Finset.sum_singleton, jacobiTriangularWeight,
      coeff_jacobiProductDiagonalTheta]
    rw [← hk, finiteDiagonalReceiver_euler_lhs_triangular]
  · rw [coeff_shiftedJacobiTriangularTheta,
      shiftedTriangularPopulation_affine_eq_empty d hpronic]
    simp only [Finset.sum_empty, coeff_jacobiProductDiagonalTheta]
    rw [finiteDiagonalReceiver_euler_lhs, diagonalRootCurrent,
      diagonalRootPopulation_eq_empty_of_no_pronic d hpronic]
    simp

/-- The Tunnell triangular stream has no coefficient outside the affine
`1 mod 4` image. -/
theorem coeff_shiftedJacobi_eq_zero_of_mod_four_ne_one
    {n : ℕ} (hn : n % 4 ≠ 1) :
    PowerSeries.coeff n shiftedJacobiTriangularTheta = 0 := by
  rw [coeff_shiftedJacobiTriangularTheta]
  apply Finset.sum_eq_zero
  intro k hk
  exfalso
  apply hn
  have hdegree := (Finset.mem_filter.mp hk).2
  omega

/-- The exact coefficient receiver for `q · F(q⁴)`.  It retains the complete
source coefficient at `(n-1)/4` on the admitted residue and refuses every
other output address. -/
def affineFourRegrade (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    if n % 4 = 1 then PowerSeries.coeff ((n - 1) / 4) F else 0

@[simp] theorem coeff_affineFourRegrade (F : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (affineFourRegrade F) =
      if n % 4 = 1 then PowerSeries.coeff ((n - 1) / 4) F else 0 := by
  simp [affineFourRegrade]

/-- **THE DIFFERENTIATED JACOBI PRODUCT IS THE TUNNELL ORIENTATION STREAM.**
The equality is global: the complete series commutes with the affine exponent
receiver, not merely a finite prefix or one selected coefficient. -/
theorem affineFourRegrade_jacobiProductDiagonalTheta :
    affineFourRegrade jacobiProductDiagonalTheta =
      shiftedJacobiTriangularTheta := by
  apply PowerSeries.ext
  intro n
  rw [coeff_affineFourRegrade]
  by_cases hn : n % 4 = 1
  · rw [if_pos hn]
    have hnpos : 0 < n := by omega
    have hdecompose : n = 1 + 4 * ((n - 1) / 4) := by omega
    conv_rhs => rw [hdecompose]
    exact (coeff_shiftedJacobi_eq_jacobiProductDiagonal ((n - 1) / 4)).symm
  · rw [if_neg hn, coeff_shiftedJacobi_eq_zero_of_mod_four_ne_one hn]

/-- The same source lands on the existing weighted quarter-square current by
the already checked orientation equivalence. -/
theorem affineFourRegrade_jacobiProduct_eq_weightedQuarterSquareTheta :
    affineFourRegrade jacobiProductDiagonalTheta =
      weightedQuarterSquareTheta 1 := by
  rw [affineFourRegrade_jacobiProductDiagonalTheta,
    ← weightedQuarterSquareTheta_eq_shiftedJacobiTriangularTheta]

/-- The differentiated Jacobi product is not merely an isolated unary theta
stream.  After the exact affine exponent return, multiplying it by the even
quarter-square difference reconstructs the complete weight-two Hecke target.
This is the global product-origin passage used by the Tunnell line. -/
theorem jacobiProduct_regrade_mul_evenDifference_eq_heckeCoefficientSeries :
    affineFourRegrade jacobiProductDiagonalTheta *
        (quarterSquareTheta 0 - quarterSquareTheta 2) =
      heckeCoefficientSeries := by
  rw [affineFourRegrade_jacobiProduct_eq_weightedQuarterSquareTheta,
    weighted_mul_evenDifference_eq_heckeCoefficientSeries]

#print axioms coeff_shiftedJacobi_eq_jacobiProductDiagonal
#print axioms coeff_shiftedJacobi_eq_zero_of_mod_four_ne_one
#print axioms affineFourRegrade_jacobiProductDiagonalTheta
#print axioms affineFourRegrade_jacobiProduct_eq_weightedQuarterSquareTheta
#print axioms jacobiProduct_regrade_mul_evenDifference_eq_heckeCoefficientSeries

end Soma.Holonics.Millennium.FamilyTunnellJacobiProductReceiver
