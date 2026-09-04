import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderTame
import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Finite-order reconstruction from the native weighted Sobolev tower

**[proved-derived]** A native order-`m+3` Fourier population carries every ordered spatial
derivative through length `m`.  This owner spends derivatives through the exact adjacent Sobolev
passages, restricts only after the addressed derivative word has been retained, and reconstructs
the resulting order-three state through the existing full-lattice inverse Fourier owner.

Every returned derivative has its exact product of unit-torus frequency multipliers.  Successive
word faces agree with genuine spatial differentiation of the reconstructed field.  The finite
family closes Mathlib's finite-dimensional `ContDiff` induction rather than assuming a smoothness
interface.
-/

noncomputable section

open Function Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Exact adjacent derivative operators -/

/-- The adjacent native derivative as a bounded complex-linear contraction. -/
def periodicWeightedSobolevDerivativeIntoPredCLM
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3) :
    PeriodicWeightedSobolev order →L[ℂ]
      PeriodicWeightedSobolev (order - 1) :=
  LinearMap.mkContinuous
    { toFun := periodicWeightedSobolevDerivativeIntoPred order hpositive coordinate
      map_add' := by
        intro left right
        apply Subtype.ext
        funext k
        simp only [periodicWeightedSobolevDerivativeIntoPred,
          coefficientWeightedRealization,
          periodicSobolevDerivativeIntoPred,
          periodicSobolevDerivativeFourier,
          weightedSobolevCoefficients, weightedSobolevRawCoefficients,
          lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        funext k
        simp only [periodicWeightedSobolevDerivativeIntoPred,
          coefficientWeightedRealization,
          periodicSobolevDerivativeIntoPred,
          periodicSobolevDerivativeFourier,
          weightedSobolevCoefficients, weightedSobolevRawCoefficients,
          lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        ring }
    1 (fun state ↦ by
      simpa using norm_periodicWeightedSobolevDerivativeIntoPred_le
        order hpositive coordinate state)

@[simp]
theorem periodicWeightedSobolevDerivativeIntoPredCLM_apply
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (state : PeriodicWeightedSobolev order) :
    periodicWeightedSobolevDerivativeIntoPredCLM
        order hpositive coordinate state =
      periodicWeightedSobolevDerivativeIntoPred
        order hpositive coordinate state :=
  rfl

/-- Spend exactly `r` addressed derivatives from native order `r+3` to native order three. -/
def orderedDerivativeToThree :
    (r : ℕ) → (Fin r → Fin 3) →
      PeriodicWeightedSobolev (r + 3) →L[ℂ] PeriodicWeightedSobolev 3
  | 0, _word => ContinuousLinearMap.id ℂ _
  | r + 1, word =>
      (orderedDerivativeToThree r (Fin.tail word)).comp
        (periodicWeightedSobolevDerivativeIntoPredCLM
          (r + 1 + 3) (by omega) (word 0))

/-! ## Ordered words and their exact native coefficient law -/

/-- The unit-three-torus Fourier symbol of one addressed spatial derivative. -/
def coordinateFourierMultiplier
    (coordinate : Fin 3) (k : SpatialFrequency) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)

/-- The ordered derivative word retains the exact product of its addressed symbols. -/
def orderedDerivativeMultiplier
    (r : ℕ) (word : Fin r → Fin 3) (k : SpatialFrequency) : ℂ :=
  ∏ i : Fin r, coordinateFourierMultiplier (word i) k

/-- Spending an ordered derivative word returns exactly its product multiplier on every mode. -/
theorem weightedSobolevCoefficients_orderedDerivativeToThree_apply :
    ∀ (r : ℕ) (word : Fin r → Fin 3)
      (state : PeriodicWeightedSobolev (r + 3)) (k : SpatialFrequency),
      (weightedSobolevCoefficients 3
        (orderedDerivativeToThree r word state)).1 k =
          orderedDerivativeMultiplier r word k *
            (weightedSobolevCoefficients (r + 3) state).1 k := by
  intro r
  induction r with
  | zero =>
      intro word state k
      simp [orderedDerivativeToThree, orderedDerivativeMultiplier]
  | succ r ih =>
      intro word state k
      rw [orderedDerivativeToThree, ContinuousLinearMap.comp_apply,
        ih (Fin.tail word), periodicWeightedSobolevDerivativeIntoPredCLM_apply]
      have horder : r + 1 + 3 - 1 = r + 3 := by omega
      have hderivativeRaw :=
        weightedSobolevCoefficients_periodicWeightedSobolevDerivativeIntoPred_apply
          (r + 1 + 3) (by omega) (word 0) state k
      rw [horder] at hderivativeRaw
      have hderivative :
          (weightedSobolevCoefficients (r + 3)
            (periodicWeightedSobolevDerivativeIntoPred
              (r + 1 + 3) (by omega) (word 0) state)).1 k =
            coordinateFourierMultiplier (word 0) k *
              (weightedSobolevCoefficients (r + 1 + 3) state).1 k := by
        simpa only [coordinateFourierMultiplier] using hderivativeRaw
      rw [hderivative]
      simp only [orderedDerivativeMultiplier, Fin.prod_univ_succ, Fin.tail]
      unfold coordinateFourierMultiplier
      ring

/-- An ordered derivative word is a contraction between the corresponding native Hilbert
carriers. -/
theorem norm_orderedDerivativeToThree_le :
    ∀ (r : ℕ) (word : Fin r → Fin 3)
      (state : PeriodicWeightedSobolev (r + 3)),
      ‖orderedDerivativeToThree r word state‖ ≤ ‖state‖ := by
  intro r
  induction r with
  | zero =>
      intro word state
      simp [orderedDerivativeToThree]
  | succ r ih =>
      intro word state
      rw [orderedDerivativeToThree, ContinuousLinearMap.comp_apply]
      exact (ih (Fin.tail word) _).trans
        (norm_periodicWeightedSobolevDerivativeIntoPred_le
          (r + 1 + 3) (by omega) (word 0) state)

/-! ## A word of length at most the supplied excess order -/

/-- Restrict a native order-`m+3` state only to the order needed by the addressed word, then
spend that word down to the common reconstructible order three. -/
def finiteOrderDerivativeToThree
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3) :
    PeriodicWeightedSobolev (m + 3) →L[ℂ] PeriodicWeightedSobolev 3 :=
  (orderedDerivativeToThree r word).comp
    (periodicWeightedSobolevRestrictCLM (r + 3) (m + 3) (by omega))

/-- Exact coefficient multiplier for every word retained by a supplied finite native order. -/
theorem weightedSobolevCoefficients_finiteOrderDerivativeToThree_apply
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicWeightedSobolev (m + 3)) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3
      (finiteOrderDerivativeToThree m r hr word state)).1 k =
        orderedDerivativeMultiplier r word k *
          (weightedSobolevCoefficients (m + 3) state).1 k := by
  rw [finiteOrderDerivativeToThree, ContinuousLinearMap.comp_apply,
    weightedSobolevCoefficients_orderedDerivativeToThree_apply]
  change orderedDerivativeMultiplier r word k *
      (weightedSobolevCoefficients (r + 3)
        (periodicWeightedSobolevRestrict (r + 3) (m + 3) (by omega) state)).1 k = _
  rw [
    weightedSobolevCoefficients_restrict_apply]

/-- Every retained finite-order word remains a norm contraction. -/
theorem norm_finiteOrderDerivativeToThree_le
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicWeightedSobolev (m + 3)) :
    ‖finiteOrderDerivativeToThree m r hr word state‖ ≤ ‖state‖ :=
  (norm_orderedDerivativeToThree_le r word _).trans
    (norm_periodicWeightedSobolevRestrict_le
      (r + 3) (m + 3) (by omega) state)

/-- Componentwise finite-word passage on the three-component native velocity carrier. -/
def finiteOrderVectorDerivativeToThree
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3) :
    PeriodicVectorWeightedSobolev (m + 3) →L[ℂ]
      PeriodicVectorWeightedSobolev 3 :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦
        finiteOrderDerivativeToThree m r hr word (state component)
      map_add' := by
        intro left right
        funext component
        exact (finiteOrderDerivativeToThree m r hr word).map_add
          (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (finiteOrderDerivativeToThree m r hr word).map_smul
          scalar (state component) }
    1 (fun state ↦ by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 * ‖state‖)]
      intro component
      calc
        ‖finiteOrderDerivativeToThree m r hr word (state component)‖ ≤
            ‖state component‖ :=
          norm_finiteOrderDerivativeToThree_le m r hr word (state component)
        _ ≤ ‖state‖ := norm_le_pi_norm state component
        _ = 1 * ‖state‖ := by ring)

@[simp]
theorem finiteOrderVectorDerivativeToThree_apply
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3)) (component : Fin 3) :
    finiteOrderVectorDerivativeToThree m r hr word state component =
      finiteOrderDerivativeToThree m r hr word (state component) :=
  rfl

/-- Componentwise exact coefficient law of the finite native derivative word. -/
theorem weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3
      (finiteOrderVectorDerivativeToThree m r hr word state component)).1 k =
        orderedDerivativeMultiplier r word k *
          (weightedSobolevCoefficients (m + 3) (state component)).1 k :=
  weightedSobolevCoefficients_finiteOrderDerivativeToThree_apply
    m r hr word (state component) k

/-- Negating a mode conjugates the exact symbol of one real spatial derivative. -/
theorem coordinateFourierMultiplier_neg
    (coordinate : Fin 3) (k : SpatialFrequency) :
    coordinateFourierMultiplier coordinate (-k) =
      conj (coordinateFourierMultiplier coordinate k) := by
  simpa only [coordinateFourierMultiplier] using
    derivativeSymbol_neg_eq_conj k coordinate

/-- Negating a mode conjugates every finite ordered derivative multiplier. -/
theorem orderedDerivativeMultiplier_neg
    (r : ℕ) (word : Fin r → Fin 3) (k : SpatialFrequency) :
    orderedDerivativeMultiplier r word (-k) =
      conj (orderedDerivativeMultiplier r word k) := by
  simp only [orderedDerivativeMultiplier, map_prod]
  apply Finset.prod_congr rfl
  intro coordinate _
  exact coordinateFourierMultiplier_neg (word coordinate) k

/-- Every finite ordered native derivative preserves the exact Fourier reality incidence. -/
theorem isWeightedFourierReal_finiteOrderVectorDerivativeToThree
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (hstate : IsWeightedFourierReal (m + 3) state) :
    IsWeightedFourierReal 3
      (finiteOrderVectorDerivativeToThree m r hr word state) := by
  intro component k
  rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    orderedDerivativeMultiplier_neg, hstate component k, map_mul]

/-- The empty word is exactly the existing componentwise order restriction to `H³`. -/
@[simp]
theorem finiteOrderVectorDerivativeToThree_zero
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3)) :
    finiteOrderVectorDerivativeToThree
        m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i) state =
      periodicVectorWeightedSobolevRestrictCLM
        3 (m + 3) (by omega) state :=
  rfl

/-! ## Reconstruction and exact derivative compatibility -/

/-- The actual continuous torus field reconstructed after retaining one finite derivative word. -/
def reconstructedFiniteOrderTorusComplexComponent
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3)) (component : Fin 3) :
    C(SpatialTorus, ℂ) :=
  reconstructedTorusComplexComponent
    (finiteOrderVectorDerivativeToThree m r hr word state) component

/-- The corresponding genuine periodic Euclidean field, pulled back from the quotient torus. -/
def reconstructedFiniteOrderComplexComponent
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3)) (component : Fin 3) :
    Space → ℂ :=
  fun x ↦ reconstructedFiniteOrderTorusComplexComponent
    m r hr word state component (euclideanToSpatialTorus x)

/-- Every addressed coefficient of the reconstructed derivative field is the exact word
multiplier of the original high-order native coefficient. -/
theorem torusSpatialFourierCoeff_reconstructedFiniteOrderTorusComplexComponent
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (k : SpatialFrequency) :
    torusSpatialFourierCoeff
        (reconstructedFiniteOrderTorusComplexComponent
          m r hr word state component) k =
      orderedDerivativeMultiplier r word k *
        (weightedSobolevCoefficients (m + 3) (state component)).1 k := by
  rw [reconstructedFiniteOrderTorusComplexComponent,
    torusSpatialFourierCoeff_reconstructedTorusComplexComponent]
  exact weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply
    m r hr word state component k

/-- The reconstructed field after any retained word is genuinely `C¹`; the three unused native
orders are exactly the common reconstruction aperture. -/
theorem contDiff_one_reconstructedFiniteOrderComplexComponent
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3)) (component : Fin 3) :
    ContDiff ℝ 1
      (reconstructedFiniteOrderComplexComponent
        m r hr word state component) :=
  contDiff_one_reconstructedComplexComponent
    (finiteOrderVectorDerivativeToThree m r hr word state) component

/-- The actual real receiver of one reconstructed finite derivative word. -/
def reconstructedFiniteOrderRealComponent
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3)) (component : Fin 3) :
    Space → ℝ :=
  fun x ↦
    (reconstructedFiniteOrderComplexComponent
      m r hr word state component x).re

/-- The real receiver after every retained word remains genuinely `C¹`. -/
theorem contDiff_one_reconstructedFiniteOrderRealComponent
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3)) (component : Fin 3) :
    ContDiff ℝ 1
      (reconstructedFiniteOrderRealComponent
        m r hr word state component) :=
  Complex.reCLM.contDiff.comp
    (contDiff_one_reconstructedFiniteOrderComplexComponent
      m r hr word state component)

/-- Prepending an addressed coordinate to a word agrees pointwise with taking the corresponding
partial derivative of its actual reconstructed Euclidean field. -/
theorem fderiv_reconstructedFiniteOrderComplexComponent_apply_single
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component coordinate : Fin 3) (x : Space) :
    fderiv ℝ
        (reconstructedFiniteOrderComplexComponent
          m r (by omega) word state component) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedFiniteOrderComplexComponent
        m (r + 1) hr (Fin.cons coordinate word) state component x := by
  have hfderiv :=
    (hasFDerivAt_reconstructedComplexComponent
      (finiteOrderVectorDerivativeToThree m r (by omega) word state)
      component x).fderiv
  change fderiv ℝ
      (fun y : Space ↦ reconstructedTorusComplexComponent
        (finiteOrderVectorDerivativeToThree m r (by omega) word state)
        component (euclideanToSpatialTorus y)) x
      (EuclideanSpace.single coordinate 1) = _
  rw [hfderiv, reconstructedComplexComponentFDeriv_apply_single]
  change (∑' k : SpatialFrequency,
      2 * Real.pi * Complex.I * (k coordinate) *
        nativeUnweightedComponent
          (finiteOrderVectorDerivativeToThree m r (by omega) word state)
          component k * euclideanFourierCharacter k x) =
    reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree
        m (r + 1) hr (Fin.cons coordinate word) state)
      component (euclideanToSpatialTorus x)
  rw [reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  rw [euclideanFourierCharacter_eq_mFourier]
  change
    2 * Real.pi * Complex.I * (k coordinate) *
        (weightedSobolevCoefficients 3
          (finiteOrderVectorDerivativeToThree
            m r (by omega) word state component)).1 k *
          UnitAddTorus.mFourier k (euclideanToSpatialTorus x) =
      (weightedSobolevCoefficients 3
        (finiteOrderVectorDerivativeToThree
          m (r + 1) hr (Fin.cons coordinate word) state component)).1 k *
        UnitAddTorus.mFourier k (euclideanToSpatialTorus x)
  rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply]
  simp only [orderedDerivativeMultiplier, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  unfold coordinateFourierMultiplier
  ring

/-- The same prepend-one-coordinate compatibility holds for the actual real receiver. -/
theorem fderiv_reconstructedFiniteOrderRealComponent_apply_single
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component coordinate : Fin 3) (x : Space) :
    fderiv ℝ
        (reconstructedFiniteOrderRealComponent
          m r (by omega) word state component) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedFiniteOrderRealComponent
        m (r + 1) hr (Fin.cons coordinate word) state component x := by
  let complexField := reconstructedFiniteOrderComplexComponent
    m r (by omega) word state component
  have hcomplex : DifferentiableAt ℝ complexField x :=
    (contDiff_one_reconstructedFiniteOrderComplexComponent
      m r (by omega) word state component).differentiable
        (by norm_num) x
  have hreal := Complex.reCLM.hasFDerivAt.comp x hcomplex.hasFDerivAt
  have hreal' : HasFDerivAt (fun y : Space ↦ (complexField y).re)
      (Complex.reCLM.comp (fderiv ℝ complexField x)) x := by
    simpa [Function.comp_def] using hreal
  change fderiv ℝ (fun y : Space ↦ (complexField y).re) x
      (EuclideanSpace.single coordinate 1) = _
  rw [hreal'.fderiv]
  change (fderiv ℝ complexField x
      (EuclideanSpace.single coordinate 1)).re = _
  rw [fderiv_reconstructedFiniteOrderComplexComponent_apply_single]
  rfl

/-! ## Finite `ContDiff` closure -/

/-- One componentwise adjacent derivative, specialized so its target is definitionally the next
member of the `m+3` reconstruction tower. -/
def periodicVectorWeightedSobolevDerivativeSuccThreeCLM
    (m : ℕ) (coordinate : Fin 3) :
    PeriodicVectorWeightedSobolev (m + 1 + 3) →L[ℂ]
      PeriodicVectorWeightedSobolev (m + 3) :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦
        periodicWeightedSobolevDerivativeIntoPredCLM
          (m + 1 + 3) (by omega) coordinate (state component)
      map_add' := by
        intro left right
        funext component
        exact (periodicWeightedSobolevDerivativeIntoPredCLM
          (m + 1 + 3) (by omega) coordinate).map_add
            (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (periodicWeightedSobolevDerivativeIntoPredCLM
          (m + 1 + 3) (by omega) coordinate).map_smul
            scalar (state component) }
    1 (fun state ↦ by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 * ‖state‖)]
      intro component
      calc
        ‖periodicWeightedSobolevDerivativeIntoPredCLM
            (m + 1 + 3) (by omega) coordinate (state component)‖ ≤
            ‖state component‖ := by
          simpa using norm_periodicWeightedSobolevDerivativeIntoPred_le
            (m + 1 + 3) (by omega) coordinate (state component)
        _ ≤ ‖state‖ := norm_le_pi_norm state component
        _ = 1 * ‖state‖ := by ring)

/-- Exact coefficient symbol of the adjacent vector derivative in the reconstruction tower. -/
theorem weightedSobolevCoefficients_periodicVectorWeightedSobolevDerivativeSuccThreeCLM_apply
    (m : ℕ) (coordinate : Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 1 + 3))
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
        m coordinate state component)).1 k =
      coordinateFourierMultiplier coordinate k *
        (weightedSobolevCoefficients (m + 1 + 3)
          (state component)).1 k := by
  change
    (weightedSobolevCoefficients (m + 3)
      (periodicWeightedSobolevDerivativeIntoPredCLM
        (m + 1 + 3) (by omega) coordinate (state component))).1 k = _
  rw [periodicWeightedSobolevDerivativeIntoPredCLM_apply]
  have horder : m + 1 + 3 - 1 = m + 3 := by omega
  have hderivative :=
    weightedSobolevCoefficients_periodicWeightedSobolevDerivativeIntoPred_apply
      (m + 1 + 3) (by omega) coordinate (state component) k
  rw [horder] at hderivative
  simpa only [coordinateFourierMultiplier] using hderivative

/-- The primary complex reconstruction from native order `m+3`. -/
def reconstructedHigherOrderComplexComponent
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) : Space → ℂ :=
  reconstructedFiniteOrderComplexComponent
    m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i) state component

/-- Its exact torus coefficient is the original unweighted high-order coefficient. -/
theorem torusSpatialFourierCoeff_reconstructedHigherOrderComplexComponent
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (k : SpatialFrequency) :
    torusSpatialFourierCoeff
        (reconstructedFiniteOrderTorusComplexComponent
          m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i) state component) k =
      (weightedSobolevCoefficients (m + 3) (state component)).1 k := by
  rw [torusSpatialFourierCoeff_reconstructedFiniteOrderTorusComplexComponent]
  simp [orderedDerivativeMultiplier]

/-- Every primary higher-order reconstruction retains the common endpoint `C¹`. -/
theorem contDiff_one_reconstructedHigherOrderComplexComponent
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) :
    ContDiff ℝ 1 (reconstructedHigherOrderComplexComponent m state component) :=
  contDiff_one_reconstructedFiniteOrderComplexComponent
    m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i) state component

/-- One partial derivative of the order-`m+4` primary reconstruction is exactly the order-`m+3`
primary reconstruction of the adjacent native derivative. -/
theorem fderiv_reconstructedHigherOrderComplexComponent_succ_apply_single
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 1 + 3))
    (component coordinate : Fin 3) (x : Space) :
    fderiv ℝ
        (reconstructedHigherOrderComplexComponent (m + 1) state component) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedHigherOrderComplexComponent m
        (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
          m coordinate state) component x := by
  let emptyWord : Fin 0 → Fin 3 := fun i ↦ Fin.elim0 i
  let oneWord : Fin 1 → Fin 3 := Fin.cons coordinate emptyWord
  have hpartial :
      fderiv ℝ
          (reconstructedFiniteOrderComplexComponent
            (m + 1) 0 (by omega) emptyWord state component) x
          (EuclideanSpace.single coordinate 1) =
        reconstructedFiniteOrderComplexComponent
          (m + 1) 1 (by omega) oneWord state component x :=
    fderiv_reconstructedFiniteOrderComplexComponent_apply_single
      (m + 1) 0 (by omega) emptyWord state component coordinate x
  change fderiv ℝ
      (reconstructedFiniteOrderComplexComponent
        (m + 1) 0 (by omega) emptyWord state component) x
      (EuclideanSpace.single coordinate 1) = _
  rw [hpartial]
  change reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree
        (m + 1) 1 (by omega) oneWord state) component
      (euclideanToSpatialTorus x) =
    reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree
        m 0 (by omega) emptyWord
          (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
            m coordinate state)) component
      (euclideanToSpatialTorus x)
  rw [reconstructedTorusComplexComponent_apply,
    reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  change
    (weightedSobolevCoefficients 3
      (finiteOrderVectorDerivativeToThree
        (m + 1) 1 (by omega) oneWord state component)).1 k *
        UnitAddTorus.mFourier k (euclideanToSpatialTorus x) =
      (weightedSobolevCoefficients 3
        (finiteOrderVectorDerivativeToThree
          m 0 (by omega) emptyWord
            (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
              m coordinate state) component)).1 k *
        UnitAddTorus.mFourier k (euclideanToSpatialTorus x)
  rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedSobolevCoefficients_periodicVectorWeightedSobolevDerivativeSuccThreeCLM_apply]
  simp [oneWord, emptyWord, orderedDerivativeMultiplier,
    coordinateFourierMultiplier]

/-- Native `H^(m+3)` returns an actual `C^(m+1)` complex periodic field.  The induction uses the
exact adjacent native derivative and finite coordinate-basis expansion of the Fréchet derivative. -/
theorem contDiff_reconstructedHigherOrderComplexComponent :
    ∀ (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3))
      (component : Fin 3),
      ContDiff ℝ (m + 1)
        (reconstructedHigherOrderComplexComponent m state component) := by
  intro m
  induction m with
  | zero =>
      intro state component
      simpa using contDiff_one_reconstructedHigherOrderComplexComponent
        0 state component
  | succ m ih =>
      intro state component
      rw [contDiff_succ_iff_fderiv_apply]
      refine ⟨?_, ?_, ?_⟩
      · exact (contDiff_one_reconstructedHigherOrderComplexComponent
          (m + 1) state component).differentiable (by norm_num)
      · intro himpossible
        simp at himpossible
      · intro direction
        let current := reconstructedHigherOrderComplexComponent
          (m + 1) state component
        have hdirection :
            (fun x : Space ↦ fderiv ℝ current x direction) =
              (fun x : Space ↦ ∑ coordinate : Fin 3,
                direction coordinate •
                  reconstructedHigherOrderComplexComponent m
                    (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
                      m coordinate state) component x) := by
          funext x
          have hdirectionBasis :
              direction = ∑ coordinate : Fin 3,
                direction coordinate • EuclideanSpace.single coordinate 1 := by
            simpa using
              ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr direction).symm
          calc
            fderiv ℝ current x direction =
                fderiv ℝ current x (∑ coordinate : Fin 3,
                  direction coordinate • EuclideanSpace.single coordinate 1) :=
              congrArg (fderiv ℝ current x) hdirectionBasis
            _ = ∑ coordinate : Fin 3, direction coordinate •
                fderiv ℝ current x
                  (EuclideanSpace.single coordinate 1) := by
              rw [map_sum]
              simp only [map_smul]
            _ = ∑ coordinate : Fin 3, direction coordinate •
                reconstructedHigherOrderComplexComponent m
                  (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
                    m coordinate state) component x := by
              apply Finset.sum_congr rfl
              intro coordinate _
              congr 1
              exact fderiv_reconstructedHigherOrderComplexComponent_succ_apply_single
                m state component coordinate x
        rw [hdirection]
        apply ContDiff.sum
        intro coordinate _
        exact (ih
          (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
            m coordinate state) component).const_smul (direction coordinate)

/-! ## Actual real vector fields and a coherent all-orders return -/

/-- Real receiver of the complete higher-order complex reconstruction. -/
def reconstructedHigherOrderVelocity
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3)) :
    Space → Space :=
  fun x ↦ vectorOfCoordinates (fun component ↦
    (reconstructedHigherOrderComplexComponent m state component x).re)

/-- The higher-order real receiver is literally the established physical `H³` reconstruction
after exact order restriction. -/
theorem reconstructedHigherOrderVelocity_eq_reconstructedVelocity_restrict
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3)) :
    reconstructedHigherOrderVelocity m state =
      reconstructedVelocity
        (periodicVectorWeightedSobolevRestrictCLM
          3 (m + 3) (by omega) state) := by
  funext x
  apply PiLp.ext
  intro component
  rfl

/-- Native vector `H^(m+3)` reconstructs to an actual real periodic `C^(m+1)` vector field. -/
theorem contDiff_reconstructedHigherOrderVelocity
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3)) :
    ContDiff ℝ (m + 1) (reconstructedHigherOrderVelocity m state) := by
  rw [contDiff_piLp]
  intro component
  change ContDiff ℝ (m + 1)
    (Complex.reCLM ∘ reconstructedHigherOrderComplexComponent m state component)
  exact Complex.reCLM.contDiff.comp
    (contDiff_reconstructedHigherOrderComplexComponent m state component)

/-- In particular, the requested finite aperture `C^m` follows without an assumed regularity
interface. -/
theorem contDiff_order_reconstructedHigherOrderVelocity
    (m : ℕ) (state : PeriodicVectorWeightedSobolev (m + 3)) :
    ContDiff ℝ m (reconstructedHigherOrderVelocity m state) :=
  (contDiff_reconstructedHigherOrderVelocity m state).of_le (by norm_num)

/-- A coherent native all-orders population: every supplied high-order state has exactly the same
order-three restriction.  This is coefficient data and an exact restriction receipt, not an
assumed smoothness predicate. -/
structure CompatibleNativeWeightedSobolevTower where
  base : PeriodicVectorWeightedSobolev 3
  lift : ∀ m : ℕ, PeriodicVectorWeightedSobolev (m + 3)
  restrict_lift : ∀ m : ℕ,
    periodicVectorWeightedSobolevRestrictCLM
      3 (m + 3) (by omega) (lift m) = base

/-- The actual real periodic velocity reconstructed from the common order-three face. -/
def reconstructedSmoothVelocity
    (tower : CompatibleNativeWeightedSobolevTower) : Space → Space :=
  reconstructedVelocity tower.base

/-- Coherent native states at every finite order reconstruct to an actual `C∞` real periodic
velocity.  Each finite receiver is discharged by its supplied native lift and the exact common
restriction receipt. -/
theorem contDiff_infty_reconstructedSmoothVelocity
    (tower : CompatibleNativeWeightedSobolevTower) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (reconstructedSmoothVelocity tower) := by
  rw [contDiff_infty]
  intro m
  have hfinite := contDiff_reconstructedHigherOrderVelocity m (tower.lift m)
  have hfield : reconstructedHigherOrderVelocity m (tower.lift m) =
      reconstructedSmoothVelocity tower := by
    rw [reconstructedHigherOrderVelocity_eq_reconstructedVelocity_restrict,
      tower.restrict_lift]
    rfl
  rw [← hfield]
  exact hfinite.of_le (by norm_num)

section Audit

#print axioms weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply
#print axioms isWeightedFourierReal_finiteOrderVectorDerivativeToThree
#print axioms torusSpatialFourierCoeff_reconstructedFiniteOrderTorusComplexComponent
#print axioms fderiv_reconstructedFiniteOrderComplexComponent_apply_single
#print axioms fderiv_reconstructedFiniteOrderRealComponent_apply_single
#print axioms contDiff_reconstructedHigherOrderVelocity
#print axioms contDiff_infty_reconstructedSmoothVelocity

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
