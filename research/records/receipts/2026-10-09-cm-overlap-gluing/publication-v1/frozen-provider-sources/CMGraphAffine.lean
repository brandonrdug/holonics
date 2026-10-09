import CMGraphSource
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Module

/-!
# The CM graph as an actual prime affine algebraic source

Source relation: the two coordinate rings are the actual Weierstrass rings.
Their tensor product is the coordinate ring of the affine product. The graph
is defined by the kernel of a *constructed surjective* algebra map to the
curve ring. The quotient is explicitly the curve ring, so its kernel is prime.
No smooth-projective cycle-class or intersection product is assumed.

The diagonal meets this graph where all iota(a)-a vanish. The fixed-locus
ideal is proved equal to (u,v), and its quotient is the coefficient field.
Thus the affine fixed locus is scheme-theoretically one reduced point.
The projective origin lies outside this chart and remains separately owed.
-/

noncomputable section

namespace Holonics.Hodge.CMGraphSource

open scoped TensorProduct

abbrev ProductRing := CurveRing ⊗[ℂ] CurveRing

def graphReceiver : ProductRing →ₐ[ℂ] CurveRing :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ CurveRing) iota
    (fun _ _ => Commute.all _ _)

theorem graphReceiver_returns (a : CurveRing) : graphReceiver (a ⊗ₜ 1) = a := by
  simp [graphReceiver]

theorem graphReceiver_surjective : Function.Surjective graphReceiver :=
  fun a => ⟨a ⊗ₜ 1, graphReceiver_returns a⟩

def graphIdeal : Ideal ProductRing := RingHom.ker graphReceiver

theorem graphIdeal_prime : graphIdeal.IsPrime := RingHom.ker_isPrime graphReceiver

def graphCoordinateEquiv : (ProductRing ⧸ graphIdeal) ≃ₐ[ℂ] CurveRing :=
  Ideal.quotientKerAlgEquivOfSurjective graphReceiver_surjective

theorem graphCoordinateEquiv_returns (a b : CurveRing) :
    graphCoordinateEquiv (Ideal.Quotient.mk graphIdeal (a ⊗ₜ b)) = a * iota b := by
  rfl

/-- All differences between the two graph participants at the diagonal. -/
def fixedIdeal : Ideal CurveRing := Ideal.span (Set.range (fun a : CurveRing => iota a - a))

def zeroPointIdeal : Ideal CurveRing := Ideal.span ({u, v} : Set CurveRing)

theorem u_mem_zeroPointIdeal : u ∈ zeroPointIdeal := Ideal.subset_span (by simp)
theorem v_mem_zeroPointIdeal : v ∈ zeroPointIdeal := Ideal.subset_span (by simp)

theorem u_mem_fixedIdeal : u ∈ fixedIdeal := by
  have hd : iota u - u ∈ fixedIdeal := Ideal.subset_span ⟨u, rfl⟩
  have hm := fixedIdeal.mul_mem_left (algebraMap ℂ CurveRing (-((1 / 2 : ℂ)))) hd
  rw [← Algebra.smul_def] at hm
  have he : -((1 / 2 : ℂ)) • (iota u - u) = u := by
    simp [iota]
    module
  rwa [he] at hm

theorem v_mem_fixedIdeal : v ∈ fixedIdeal := by
  have hd : iota v - v ∈ fixedIdeal := Ideal.subset_span ⟨v, rfl⟩
  have hi : Complex.I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hm := fixedIdeal.mul_mem_left (algebraMap ℂ CurveRing ((Complex.I - 1)⁻¹)) hd
  rw [← Algebra.smul_def] at hm
  have he : (Complex.I - 1)⁻¹ • (iota v - v) = v := by
    calc
      _ = (Complex.I - 1)⁻¹ • ((Complex.I - 1) • v) := by
        congr 1
        simp [iota, sub_smul]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ hi, one_smul]
  rwa [he] at hm

theorem fixedIdeal_eq_zeroPointIdeal : fixedIdeal = zeroPointIdeal := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let π : CurveRing →ₐ[ℂ] CurveRing ⧸ zeroPointIdeal := Ideal.Quotient.mkₐ ℂ zeroPointIdeal
    have hcomp : π.comp iota = π := by
      apply curveRing_hom_ext
      · change π (iota u) = π u
        simp [π, iota, Ideal.Quotient.eq_zero_iff_mem.mpr u_mem_zeroPointIdeal]
      · change π (iota v) = π v
        simp [π, iota, Ideal.Quotient.eq_zero_iff_mem.mpr v_mem_zeroPointIdeal]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (iota a - a) = 0
    rw [map_sub]
    have ha := congrArg (fun f : CurveRing →ₐ[ℂ] CurveRing ⧸ zeroPointIdeal => f a) hcomp
    exact sub_eq_zero.mpr ha
  · apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with h | h
    · exact h ▸ u_mem_fixedIdeal
    · have h' : a = v := Set.mem_singleton_iff.mp h
      exact h' ▸ v_mem_fixedIdeal

open Polynomial
open scoped Polynomial.Bivariate

def originCoefficient : ℂ[X] →ₐ[ℂ] ℂ := aeval (0 : ℂ)

theorem origin_relation : squareCurve.toAffine.polynomial.eval₂ originCoefficient (0 : ℂ) = 0 := by
  rw [squarePolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, map_sub, map_pow,
    originCoefficient, AlgHom.coe_toRingHom, aeval_X]
  norm_num

def originReceiver : CurveRing →ₐ[ℂ] ℂ :=
  AdjoinRoot.liftAlgHom (S := ℂ) squareCurve.toAffine.polynomial originCoefficient
    (0 : ℂ) origin_relation

@[simp] theorem originReceiver_u : originReceiver u = 0 := by
  rw [originReceiver, u, AdjoinRoot.liftAlgHom_of]
  exact aeval_X (0 : ℂ)
@[simp] theorem originReceiver_v : originReceiver v = 0 := by
  rw [originReceiver, v, AdjoinRoot.liftAlgHom_root]

theorem zeroPointIdeal_le_originKernel : zeroPointIdeal ≤ RingHom.ker originReceiver := by
  apply Ideal.span_le.mpr
  intro a ha
  rcases Set.mem_insert_iff.mp ha with h | h
  · change originReceiver a = 0
    rw [h]
    exact originReceiver_u
  · have h' := Set.mem_singleton_iff.mp h
    change originReceiver a = 0
    rw [h']
    exact originReceiver_v

def originQuotientReceiver : (CurveRing ⧸ zeroPointIdeal) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ zeroPointIdeal originReceiver
    (fun _ h => zeroPointIdeal_le_originKernel h)

theorem originQuotient_comp_scalars :
    originQuotientReceiver.comp (Algebra.ofId ℂ (CurveRing ⧸ zeroPointIdeal)) = AlgHom.id ℂ ℂ := by
  ext

theorem scalars_comp_originQuotient :
    (Algebra.ofId ℂ (CurveRing ⧸ zeroPointIdeal)).comp originQuotientReceiver =
      AlgHom.id ℂ (CurveRing ⧸ zeroPointIdeal) := by
  apply Ideal.Quotient.algHom_ext
  apply curveRing_hom_ext
  · change (algebraMap ℂ (CurveRing ⧸ zeroPointIdeal)) (originReceiver u) =
      Ideal.Quotient.mk zeroPointIdeal u
    rw [originReceiver_u, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr u_mem_zeroPointIdeal).symm
  · change (algebraMap ℂ (CurveRing ⧸ zeroPointIdeal)) (originReceiver v) =
      Ideal.Quotient.mk zeroPointIdeal v
    rw [originReceiver_v, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr v_mem_zeroPointIdeal).symm

/-- The scheme-theoretic affine intersection is exactly one reduced coefficient-field point. -/
def zeroPointCoordinateEquiv : (CurveRing ⧸ zeroPointIdeal) ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofAlgHom originQuotientReceiver (Algebra.ofId ℂ (CurveRing ⧸ zeroPointIdeal))
    originQuotient_comp_scalars scalars_comp_originQuotient

#print axioms graphReceiver_surjective
#print axioms graphIdeal_prime
#print axioms graphCoordinateEquiv
#print axioms fixedIdeal_eq_zeroPointIdeal
#print axioms zeroPointCoordinateEquiv

end Holonics.Hodge.CMGraphSource
