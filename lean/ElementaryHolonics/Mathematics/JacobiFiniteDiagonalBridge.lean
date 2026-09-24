import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalCone
import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalReceiver

/-!
# The finite Jacobi diagonal receiver is the polynomial diagonal hom

The finite receiver and the polynomial diagonal map use different addresses:
the first is indexed by Laurent orientation `m`, while the second is indexed
by outer degree `n`.  This file constructs their exact finite chart change

`n = d - m`,  `m = d - n`.

The square-support cone then proves that the finite range contains every
nonzero diagonal occurrence.  Thus the receiver aperture is derived from the
source geometry; it is not a truncation assumption.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiFiniteDiagonalBridge

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalProduct
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalCone
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalReceiver
open Soma.Holonics.Mathematics.JacobiEulerDerivative
open Soma.Holonics.Mathematics.JacobiEulerCubeStabilization

/-- The two finite address charts on diagonal degree `d` are exactly
equivalent.  The conditional on the orientation chart is the refusal of a
negative reconstructed outer degree. -/
theorem diagonalWindow_sum_reindex (c : ℕ → ℤ → ℤ) (d : ℕ) :
    (∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
      if 0 ≤ (d : ℤ) - m then
        (-1 : ℤ) ^ m.natAbs * c (((d : ℤ) - m).toNat) m
      else 0) =
    ∑ n ∈ Finset.range (2 * d + 2),
      (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
        c n ((d : ℤ) - (n : ℤ)) := by
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
    have hnonneg : 0 ≤ (d : ℤ) - m := by
      dsimp [m]
      omega
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
    have hadd : (d : ℤ) - (((d : ℤ) - m).toNat : ℤ) = m := by
      omega
    rw [hadd]

/-- The exact nonzero population of polynomial occurrences returning to
diagonal degree `d`. -/
def polynomialDiagonalSupport (p : PolynomialBody) (d : ℕ) : Finset ℕ :=
  p.support.filter fun n => (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) ≠ 0

/-- The square cone forces every returned polynomial occurrence into the
derived outer-degree window. -/
theorem polynomialDiagonalSupport_subset_range
    (p : PolynomialBody) (d : ℕ)
    (hcone : SquareCone (polynomialPowerSeriesHom p)) :
    polynomialDiagonalSupport p d ⊆ Finset.range (2 * d + 2) := by
  intro n hn
  rw [polynomialDiagonalSupport, Finset.mem_filter] at hn
  rw [Finset.mem_range]
  have hcoeff :
      (PowerSeries.coeff n (polynomialPowerSeriesHom p)).coeff
          ((d : ℤ) - (n : ℤ)) ≠ 0 := by
    simpa using hn.2
  have hdiag : (n : ℤ) + ((d : ℤ) - (n : ℤ)) = (d : ℤ) := by ring
  have hout := SquareCone.diagonal_outer_le hcone hcoeff hdiag
  omega

private theorem polynomial_support_sum_eq_diagonalSupport
    (p : PolynomialBody) (d : ℕ) :
    (∑ n ∈ p.support,
      (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
        (p.coeff n).coeff ((d : ℤ) - (n : ℤ))) =
    ∑ n ∈ polynomialDiagonalSupport p d,
      (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
        (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) := by
  rw [polynomialDiagonalSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs with h
  · rfl
  · have hzero : (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) = 0 := by
      exact Classical.not_not.mp h
    simp [hzero]

private theorem polynomial_range_sum_eq_diagonalSupport
    (p : PolynomialBody) (d : ℕ)
    (hcone : SquareCone (polynomialPowerSeriesHom p)) :
    (∑ n ∈ Finset.range (2 * d + 2),
      (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
        (p.coeff n).coeff ((d : ℤ) - (n : ℤ))) =
    ∑ n ∈ polynomialDiagonalSupport p d,
      (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
        (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) := by
  symm
  apply Finset.sum_subset (polynomialDiagonalSupport_subset_range p d hcone)
  intro n _hnrange hnnot
  by_cases hsupp : n ∈ p.support
  · have hzero : (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) = 0 := by
      by_contra hne
      apply hnnot
      exact Finset.mem_filter.mpr ⟨hsupp, hne⟩
    simp [hzero]
  · have hpzero : p.coeff n = 0 := by
      by_contra hne
      exact hsupp (Polynomial.mem_support_iff.mpr hne)
    simp [hpzero]

/-- **FINITE RECEIVER–HOM COMMUTING SQUARE.**  Under the exact square-cone
law, the finite source receiver and the algebraic polynomial diagonal map
return the same coefficient. -/
theorem finiteDiagonalReceiver_polynomial_eq
    (p : PolynomialBody) (d : ℕ)
    (hcone : SquareCone (polynomialPowerSeriesHom p)) :
    finiteDiagonalReceiver d (polynomialPowerSeriesHom p) =
      (finiteDiagonalHom p).coeff (d : ℤ) := by
  rw [finiteDiagonalReceiver]
  simp only [coeff_polynomialPowerSeriesHom]
  calc
    (∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
        if 0 ≤ (d : ℤ) - m then
          (-1 : ℤ) ^ m.natAbs *
            (p.coeff (((d : ℤ) - m).toNat)).coeff m
        else 0) =
        ∑ n ∈ Finset.range (2 * d + 2),
          (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
            (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) :=
      diagonalWindow_sum_reindex (fun n m => (p.coeff n).coeff m) d
    _ = ∑ n ∈ polynomialDiagonalSupport p d,
          (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
            (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) :=
      polynomial_range_sum_eq_diagonalSupport p d hcone
    _ = ∑ n ∈ p.support,
          (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
            (p.coeff n).coeff ((d : ℤ) - (n : ℤ)) :=
      (polynomial_support_sum_eq_diagonalSupport p d).symm
    _ = (finiteDiagonalHom p).coeff (d : ℤ) :=
      (finiteDiagonalHom_apply p (d : ℤ)).symm

/-! ## The finite Jacobi source crosses the commuting square -/

@[simp] theorem polynomialPowerSeriesHom_q :
    polynomialPowerSeriesHom polynomialQ = q := by
  simp [polynomialPowerSeriesHom, polynomialQ, q]

@[simp] theorem polynomialPowerSeriesHom_a :
    polynomialPowerSeriesHom polynomialA = a := by
  simp [polynomialPowerSeriesHom, polynomialA, a]

@[simp] theorem polynomialPowerSeriesHom_aInv :
    polynomialPowerSeriesHom polynomialAInv = aI := by
  simp [polynomialPowerSeriesHom, polynomialAInv, aI]

@[simp] theorem polynomialPowerSeriesHom_qPoch
    (A Q : PolynomialBody) (N : ℕ) :
    polynomialPowerSeriesHom (qPoch A Q N) =
      qPoch (polynomialPowerSeriesHom A)
        (polynomialPowerSeriesHom Q) N := by
  exact map_qPoch polynomialPowerSeriesHom A Q N

/-- The finite polynomial Jacobi body and finite bivariate Jacobi body are
the same source in their two exact coefficient charts. -/
@[simp] theorem polynomialPowerSeriesHom_finiteTriple (N : ℕ) :
    polynomialPowerSeriesHom (finitePolynomialTripleProduct N) =
      finiteBivariateTripleProduct N := by
  simp [finitePolynomialTripleProduct, finiteBivariateTripleProduct,
    finitePolynomialP0, finitePolynomialP1, finitePolynomialP3]

/-- Euler differentiation preserves the finite Jacobi source's square cone. -/
theorem finiteTriple_euler_cone (N : ℕ) :
    SquareCone
      (polynomialPowerSeriesHom
        (polynomialEulerDerivative (finitePolynomialTripleProduct N))) := by
  rw [polynomialPowerSeriesHom_euler, polynomialPowerSeriesHom_finiteTriple]
  exact (finiteBivariateTripleProduct_squareCone N).eulerDerivative

/-- **FINITE JACOBI RECEIVER RETURN.**  The differentiated finite Jacobi
body returns the two neighboring Euler products exactly. -/
theorem finiteTriple_receiver_eq_neighborEuler (d N : ℕ) :
    finiteDiagonalReceiver d
      (Soma.Holonics.Mathematics.JacobiEulerDerivative.bivariateEulerDerivative
        (finiteBivariateTripleProduct (N + 1))) =
      (finiteEulerProduct (N + 1) ^ 2 * finiteEulerProduct N).coeff (d : ℤ) := by
  rw [← polynomialPowerSeriesHom_finiteTriple]
  rw [← polynomialPowerSeriesHom_euler]
  rw [finiteDiagonalReceiver_polynomial_eq _ _
    (finiteTriple_euler_cone (N + 1))]
  rw [finiteDiagonalEulerDerivative_tripleProduct]

/-! ## One common polynomial returns both finite Euler charts -/

/-- The Laurent coefficient at a nonnegative exponent is the originating
polynomial coefficient. -/
theorem coeff_toLaurent (p : Polynomial ℤ) (d : ℕ) :
    (Polynomial.toLaurent p).coeff (d : ℤ) = p.coeff d := by
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain (⇑Nat.castEmbedding) p.toFinsupp.coeff)
    (Nat.castEmbedding d) = p.coeff d
  rw [Finsupp.mapDomain_apply Nat.castEmbedding.injective, Polynomial.toFinsupp_apply]

/-- The common finite Euler source before choosing a Laurent or completed
power-series receiver. -/
def evenEulerPolynomial (N : ℕ) : Polynomial ℤ :=
  qPoch (Polynomial.X ^ 2) (Polynomial.X ^ 2) N

theorem toLaurent_evenEulerPolynomial (N : ℕ) :
    Polynomial.toLaurent (evenEulerPolynomial N) = finiteEulerProduct N := by
  rw [evenEulerPolynomial, map_qPoch]
  simp [finiteEulerProduct]

theorem toPowerSeries_evenEulerPolynomial (N : ℕ) :
    polynomialPowerSeriesHom (evenEulerPolynomial N) =
      finiteEvenEulerSeries N := by
  rw [evenEulerPolynomial, map_qPoch]
  simp [finiteEvenEulerSeries, polynomialPowerSeriesHom]

theorem coeff_finiteEulerProduct_eq_finiteEvenEulerSeries (d N : ℕ) :
    (finiteEulerProduct N).coeff (d : ℤ) =
      PowerSeries.coeff d (finiteEvenEulerSeries N) := by
  rw [← toLaurent_evenEulerPolynomial,
    coeff_toLaurent, ← toPowerSeries_evenEulerPolynomial]
  simp

/-- The full neighboring finite return commutes between the Laurent and
power-series charts because both are images of the same polynomial body. -/
theorem coeff_finiteNeighborEulerProduct_eq_series (d N : ℕ) :
    (finiteEulerProduct (N + 1) ^ 2 * finiteEulerProduct N).coeff (d : ℤ) =
      PowerSeries.coeff d (finiteNeighborEulerReturn N) := by
  let p : Polynomial ℤ :=
    evenEulerPolynomial (N + 1) ^ 2 * evenEulerPolynomial N
  have hpLaurent : Polynomial.toLaurent p =
      finiteEulerProduct (N + 1) ^ 2 * finiteEulerProduct N := by
    dsimp [p]
    rw [map_mul, map_pow, toLaurent_evenEulerPolynomial,
      toLaurent_evenEulerPolynomial]
  have hpSeries : polynomialPowerSeriesHom p =
      finiteNeighborEulerReturn N := by
    dsimp [p]
    rw [map_mul, map_pow, toPowerSeries_evenEulerPolynomial,
      toPowerSeries_evenEulerPolynomial]
    rfl
  rw [← hpLaurent, coeff_toLaurent,
    ← hpSeries, coeff_polynomialPowerSeriesHom]

/-! ## The completed Jacobi source returns the completed Euler cube -/

/-- Coefficient agreement through degree `d` composes through one Cauchy
product over any commutative coefficient ring. -/
theorem coeff_mul_eq_of_coeff_le_generic
    {S : Type*} [CommRing S]
    (F F' G G' : PowerSeries S) (d : ℕ)
    (hF : ∀ j ≤ d, PowerSeries.coeff j F = PowerSeries.coeff j F')
    (hG : ∀ j ≤ d, PowerSeries.coeff j G = PowerSeries.coeff j G') :
    PowerSeries.coeff d (F * G) = PowerSeries.coeff d (F' * G') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hF p.1 (by omega), hG p.2 (by omega)]

/-- Every coefficient below the finite factor aperture is already the exact
coefficient of the complete three-factor Jacobi source. -/
theorem coeff_lhs_eq_finiteBivariateTripleProduct
    (j N : ℕ) (h : j < N) :
    PowerSeries.coeff j lhs =
      PowerSeries.coeff j (finiteBivariateTripleProduct N) := by
  letI : TopologicalSpace R := piTop
  have h0 : ∀ k ≤ j,
      PowerSeries.coeff k (qPochhammerInf (q ^ 2) (q ^ 2) : R) =
        PowerSeries.coeff k (qPoch (q ^ 2) (q ^ 2) N : R) := by
    intro k hk
    simpa [pow_two] using lhs_coeff_stable (-q) k N (by omega)
  have h1 : ∀ k ≤ j,
      PowerSeries.coeff k (qPochhammerInf (-q * a) (q ^ 2) : R) =
        PowerSeries.coeff k (qPoch (-q * a) (q ^ 2) N : R) := by
    intro k hk
    simpa [mul_comm] using lhs_coeff_stable a k N (by omega)
  have h3 : ∀ k ≤ j,
      PowerSeries.coeff k (qPochhammerInf (-q * aI) (q ^ 2) : R) =
        PowerSeries.coeff k (qPoch (-q * aI) (q ^ 2) N : R) := by
    intro k hk
    simpa [mul_comm] using lhs_coeff_stable aI k N (by omega)
  unfold lhs finiteBivariateTripleProduct
  exact coeff_mul_eq_of_coeff_le_generic _ _ _ _ j
    (fun k hk => coeff_mul_eq_of_coeff_le_generic _ _ _ _ k
      (fun r hr => h0 r (le_trans hr hk))
      (fun r hr => h1 r (le_trans hr hk)))
    h3

/-- A diagonal receiver needs exactly the source coefficients below its
derived outer-degree aperture `2d+2`. -/
theorem finiteDiagonalReceiver_eq_of_coeff_lt
    (F G : R) (d : ℕ)
    (hcoeff : ∀ n < 2 * d + 2,
      PowerSeries.coeff n F = PowerSeries.coeff n G) :
    finiteDiagonalReceiver d (bivariateEulerDerivative F) =
      finiteDiagonalReceiver d (bivariateEulerDerivative G) := by
  rw [finiteDiagonalReceiver, finiteDiagonalReceiver]
  simp only [coeff_bivariateEulerDerivative]
  calc
    (∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
      if 0 ≤ (d : ℤ) - m then
        (-1 : ℤ) ^ m.natAbs *
          (laurentEulerDerivative
            (PowerSeries.coeff (((d : ℤ) - m).toNat) F)).coeff m
      else 0) =
      ∑ n ∈ Finset.range (2 * d + 2),
        (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
          (laurentEulerDerivative (PowerSeries.coeff n F)).coeff
            ((d : ℤ) - (n : ℤ)) :=
      diagonalWindow_sum_reindex
        (fun n m => (laurentEulerDerivative (PowerSeries.coeff n F)).coeff m) d
    _ = ∑ n ∈ Finset.range (2 * d + 2),
        (-1 : ℤ) ^ ((d : ℤ) - (n : ℤ)).natAbs *
          (laurentEulerDerivative (PowerSeries.coeff n G)).coeff
            ((d : ℤ) - (n : ℤ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      rw [hcoeff n hn]
    _ = ∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
      if 0 ≤ (d : ℤ) - m then
        (-1 : ℤ) ^ m.natAbs *
          (laurentEulerDerivative
            (PowerSeries.coeff (((d : ℤ) - m).toNat) G)).coeff m
      else 0 :=
      (diagonalWindow_sum_reindex
        (fun n m => (laurentEulerDerivative (PowerSeries.coeff n G)).coeff m) d).symm

/-- The complete Jacobi source and the finite source at its derived aperture
return exactly the same diagonal coefficient. -/
theorem complete_receiver_eq_finiteTriple (d : ℕ) :
    finiteDiagonalReceiver d (bivariateEulerDerivative lhs) =
      finiteDiagonalReceiver d
        (bivariateEulerDerivative
          (finiteBivariateTripleProduct (2 * d + 2))) := by
  apply finiteDiagonalReceiver_eq_of_coeff_lt
  intro n hn
  exact coeff_lhs_eq_finiteBivariateTripleProduct n (2 * d + 2) hn

/-- **COMPLETED JACOBI–EULER DIAGONAL IDENTITY.**  The exact finite diagonal
receiver of the differentiated complete Jacobi product is the corresponding
coefficient of the completed even Euler cube.  Every step factors through a
finite source occurrence population. -/
theorem complete_receiver_eq_infiniteEvenEulerCube (d : ℕ) :
    finiteDiagonalReceiver d (bivariateEulerDerivative lhs) =
      PowerSeries.coeff d infiniteEvenEulerCube := by
  calc
    finiteDiagonalReceiver d (bivariateEulerDerivative lhs) =
        finiteDiagonalReceiver d
          (bivariateEulerDerivative
            (finiteBivariateTripleProduct ((2 * d + 1) + 1))) := by
      simpa [Nat.add_assoc] using complete_receiver_eq_finiteTriple d
    _ = (finiteEulerProduct ((2 * d + 1) + 1) ^ 2 *
          finiteEulerProduct (2 * d + 1)).coeff (d : ℤ) :=
      finiteTriple_receiver_eq_neighborEuler d (2 * d + 1)
    _ = PowerSeries.coeff d (finiteNeighborEulerReturn (2 * d + 1)) :=
      coeff_finiteNeighborEulerProduct_eq_series d (2 * d + 1)
    _ = PowerSeries.coeff d infiniteEvenEulerCube := by
      rw [coeff_infiniteEvenEulerCube_eq_finiteNeighbor d (2 * d + 1)
        (by omega)]

#print axioms diagonalWindow_sum_reindex
#print axioms polynomialDiagonalSupport_subset_range
#print axioms finiteDiagonalReceiver_polynomial_eq
#print axioms finiteTriple_receiver_eq_neighborEuler
#print axioms coeff_finiteNeighborEulerProduct_eq_series
#print axioms coeff_lhs_eq_finiteBivariateTripleProduct
#print axioms complete_receiver_eq_infiniteEvenEulerCube

end Soma.Holonics.Mathematics.JacobiFiniteDiagonalBridge
