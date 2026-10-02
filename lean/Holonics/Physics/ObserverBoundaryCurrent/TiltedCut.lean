import Holonics.Physics.ObserverBoundaryCurrent.Slab
import Holonics.Physics.ObserverBoundaryCurrent.TiltedCut.Integral
import Holonics.Physics.Spacetime.StressEnergy

/-!
# The actual observer-current charge on the boostT image of its cut

The PLUS-sign boostT owner supplies the Lorentz map. Both Tensor and covector
fields are evaluated at the actual inverse event. The scalar integral consumer
carries the oriented measure (dy,-dtau), and proves trace integrability.
This transports the same geometric cut, rather than comparing two independent
constant-time cuts. The covector remains arbitrary: physical observer unit/future
normalization, alignment for comoving energy, stress positivity and admissible
physical domain/ordinary trace are separate consumer obligations. No PDE or
curved-spacetime claim. The transformation laws define the carried fields;
equivariance of an independently realized constitutive source is not proved.
Same-cut covariance supplies no conservation between distinct time slices.
Refs #62 / #146.
-/

noncomputable section
namespace Holonics.Physics.ObserverBoundaryCurrent.TiltedCut
open Matrix MeasureTheory
open Holonics.Physics.ReceiverStressEnergy
open Holonics.Physics.Spacetime

/-- An actual transformed stress field at its inverse event. -/
def carriedTensor (k : ℝ) (T : ℝ → ℝ → Tensor) (τ y : ℝ) : Tensor :=
  StressEnergy.boostT k * Matrix.of (T
    (inverseTime (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)
    (inverseSpace (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)) *
    (StressEnergy.boostT k)ᵀ

/-- A covector transforms contragrediently; the two fields use the SAME
inverse event. The existing Lorentz-inverse owner supplies the inverse matrix. -/
def carriedCovector (k : ℝ) (u : ℝ → ℝ → Index → ℝ) (τ y : ℝ) : Index → ℝ :=
  (StressEnergy.eta * (StressEnergy.boostT k)ᵀ * StressEnergy.eta)ᵀ *ᵥ
    u (inverseTime (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)
      (inverseSpace (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)

/-- The field-current bridge consumes the existing Lorentz inverse; no
current transformation equality is supplied as a hypothesis. -/
theorem carried_observer_current (k : ℝ) (T : ℝ → ℝ → Tensor)
    (u : ℝ → ℝ → Index → ℝ) (μ : Index) (τ y : ℝ) (hk : k ≠ 0) :
    observerCurrent (carriedTensor k T) (carriedCovector k u) μ τ y =
      (StressEnergy.boostT k *ᵥ (fun ν => observerCurrent T u ν
        (inverseTime (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)
        (inverseSpace (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y))) μ := by
  let L := StressEnergy.boostT k
  let B := StressEnergy.eta * Lᵀ * StressEnergy.eta
  let M := Matrix.of (T (inverseTime (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)
    (inverseSpace (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y))
  let v := u (inverseTime (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)
    (inverseSpace (Boost.gammaOf k) (Boost.gammaBetaOf k) τ y)
  have hInv : B * L = 1 := StressEnergy.lorentz_inverse (StressEnergy.boostT_lorentz hk)
  have hcancel : Lᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hInv, Matrix.transpose_one]
  have hv : (L * M * Lᵀ) *ᵥ (Bᵀ *ᵥ v) = L *ᵥ (M *ᵥ v) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hcancel, Matrix.mul_one]
  change (-( (L * M * Lᵀ) *ᵥ (Bᵀ *ᵥ v))) μ = (L *ᵥ (-(M *ᵥ v))) μ
  rw [hv, Matrix.mulVec_neg]

theorem carried_observer_current0 (k : ℝ) (T : ℝ → ℝ → Tensor)
    (u : ℝ → ℝ → Index → ℝ) (τ y : ℝ) (hk : k ≠ 0) :
    observerCurrent (carriedTensor k T) (carriedCovector k u) 0 τ y =
      pulledCurrent0 (Boost.gammaOf k) (Boost.gammaBetaOf k)
        (observerCurrent T u 0) (observerCurrent T u 1) τ y := by
  rw [carried_observer_current k T u 0 τ y hk]
  simp [StressEnergy.boostT, Matrix.mulVec, dotProduct, Fin.sum_univ_four, pulledCurrent0]

theorem carried_observer_current1 (k : ℝ) (T : ℝ → ℝ → Tensor)
    (u : ℝ → ℝ → Index → ℝ) (τ y : ℝ) (hk : k ≠ 0) :
    observerCurrent (carriedTensor k T) (carriedCovector k u) 1 τ y =
      pulledCurrent1 (Boost.gammaOf k) (Boost.gammaBetaOf k)
        (observerCurrent T u 0) (observerCurrent T u 1) τ y := by
  rw [carried_observer_current k T u 1 τ y hk]
  simp [StressEnergy.boostT, Matrix.mulVec, dotProduct, Fin.sum_univ_four, pulledCurrent1]

/-- The graph parameterized by y is the actual boostT image of (t,x,0,0).
This certifies which cut the integral below uses. -/
theorem graph_is_boosted_cut (k t x : ℝ) (hk : 0 < k) :
    graphTime (Boost.gammaOf k) (Boost.gammaBetaOf k) t
      ((StressEnergy.boostT k *ᵥ ![t, x, 0, 0]) 1) =
        (StressEnergy.boostT k *ᵥ ![t, x, 0, 0]) 0 := by
  have hγ : 0 < Boost.gammaOf k := by unfold Boost.gammaOf; positivity
  have hLorentz : Boost.gammaOf k ^ 2 - Boost.gammaBetaOf k ^ 2 = 1 :=
    Holonics.Physics.CompositeMassEnergy.multiplicativeScale_lorentz_identity (ne_of_gt hk)
  have ht : (Boost.gammaOf k ^ 2 - Boost.gammaBetaOf k ^ 2) * t = t := by
    rw [hLorentz, one_mul]
  simp only [StressEnergy.boostT, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    zero_mul, add_zero]
  unfold graphTime
  field_simp [ne_of_gt hγ]
  nlinarith only [ht]

/-- The surface's time argument has its actual affine derivative. Thus the
oriented measure coefficient used below is derived from the graph. -/
theorem graph_time_hasDerivAt (γ ξ t y : ℝ) :
    HasDerivAt (graphTime γ ξ t) (ξ / γ) y := by
  -- agent-inferred: the Field owner already resolves the two elaborated Real
  -- module presentations with convert!; retain the actual graph derivative.
  convert! (hasDerivAt_const_mul (x := y) (ξ / γ)).const_add (t / γ) using 1

/-- The oriented surface flux of the actual transformed Tensor/covector fields.
Its measure is (1,-xi/gamma)dy, with both readings on the tilted graph. -/
def observerSurfaceFlux (k : ℝ) (T : ℝ → ℝ → Tensor)
    (u : ℝ → ℝ → Index → ℝ) (t y : ℝ) : ℝ :=
  observerCurrent (carriedTensor k T) (carriedCovector k u) 0
    (graphTime (Boost.gammaOf k) (Boost.gammaBetaOf k) t y) y -
      (Boost.gammaBetaOf k / Boost.gammaOf k) *
        observerCurrent (carriedTensor k T) (carriedCovector k u) 1
          (graphTime (Boost.gammaOf k) (Boost.gammaBetaOf k) t y) y

/-- Integrability and integral covariance for the geometrically transported
cut. The only analytic hypothesis is the original current-density trace's
IntervalIntegrable property; no desired integral or transformed trace is assumed.
The oriented interval formulation also handles reversed or equal endpoints. -/
theorem observer_transported_cut_integral (k : ℝ) (T : ℝ → ℝ → Tensor)
    (u : ℝ → ℝ → Index → ℝ) (t l r : ℝ) (hk : 0 < k)
    (htrace : IntervalIntegrable (observerCurrent T u 0 t) volume l r) :
    IntervalIntegrable (observerSurfaceFlux k T u t) volume
      (Boost.gammaOf k * l + Boost.gammaBetaOf k * t)
      (Boost.gammaOf k * r + Boost.gammaBetaOf k * t) ∧
      (∫ y in (Boost.gammaOf k * l + Boost.gammaBetaOf k * t)..
        (Boost.gammaOf k * r + Boost.gammaBetaOf k * t), observerSurfaceFlux k T u t y) =
        ∫ x in l..r, observerCurrent T u 0 t x := by
  have hγ : 0 < Boost.gammaOf k := by unfold Boost.gammaOf; positivity
  have hLorentz : Boost.gammaOf k ^ 2 - Boost.gammaBetaOf k ^ 2 = 1 :=
    Holonics.Physics.CompositeMassEnergy.multiplicativeScale_lorentz_identity (ne_of_gt hk)
  have hflux : observerSurfaceFlux k T u t =
      orientedFlux (Boost.gammaOf k) (Boost.gammaBetaOf k)
        (observerCurrent T u 0) (observerCurrent T u 1) t := by
    funext y
    unfold observerSurfaceFlux orientedFlux
    rw [carried_observer_current0 k T u _ y (ne_of_gt hk),
      carried_observer_current1 k T u _ y (ne_of_gt hk)]
  rw [hflux]
  exact transported_cut_integral (Boost.gammaOf k) (Boost.gammaBetaOf k)
    (observerCurrent T u 0) (observerCurrent T u 1) t l r hγ hLorentz htrace

end Holonics.Physics.ObserverBoundaryCurrent.TiltedCut
