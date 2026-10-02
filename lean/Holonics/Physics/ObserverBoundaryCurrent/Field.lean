import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Convert

/-!
# Actual derivative of a finite field/covector contraction

The participating covector is arbitrary. Both participants' actual derivatives
enter the product. `ObserverBoundaryCurrent.Slab` consumes these identities to
derive an integral charge balance from local derivatives and interface flux.
This general law asserts no physical observer normalization or energy positivity.
Refs #62 / #146.
-/

noncomputable section
namespace Holonics.Physics.ObserverBoundaryCurrent

variable {ι : Type*} [Fintype ι]

/-- The actual derivative of a finite flow/observer-covector contraction.
The second participant's motion contributes beside the source's motion. -/
theorem field_contraction_hasDerivAt
    (F U : ℝ → ι → ℝ) (dF dU : ι → ℝ) (t : ℝ)
    (hF : ∀ i, HasDerivAt (fun s => F s i) (dF i) t)
    (hU : ∀ i, HasDerivAt (fun s => U s i) (dU i) t) :
    HasDerivAt (fun s => -∑ i, F s i * U s i)
      (-(∑ i, (dF i * U t i + F t i * dU i))) t := by
  convert! (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hF i).mul (hU i))).neg using 1

/-- The two-direction field equation retains both observer partials. This
identity is consumed only after they have been proved to be actual derivatives. -/
theorem field_contraction_force_balance
    (T0 T1 dtT0 dxT1 U dtU dxU force : ι → ℝ)
    (hforce : ∀ i, dtT0 i + dxT1 i = force i) :
    (-(∑ i, (dtT0 i * U i + T0 i * dtU i))) +
      (-(∑ i, (dxT1 i * U i + T1 i * dxU i))) =
      -(∑ i, (force i * U i + T0 i * dtU i + T1 i * dxU i)) := by
  have hsum :
      (∑ i, (dtT0 i * U i + T0 i * dtU i)) +
        (∑ i, (dxT1 i * U i + T1 i * dxU i)) =
        ∑ i, (force i * U i + T0 i * dtU i + T1 i * dxU i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hforce i, add_mul]
    ac_rfl
  rw [← neg_add, hsum]


end Holonics.Physics.ObserverBoundaryCurrent
