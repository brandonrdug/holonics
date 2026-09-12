import ElementaryHolonics.Physics.ReceiverStressEnergy

/-!
# Finite observer and boundary current algebra

These are finite-chart contraction identities.  Derivative arrays, force arrays,
and interface orientations are supplied by the caller; no manifold divergence
theorem is asserted here.
-/

namespace Soma.Holonics.Physics.ObserverBoundaryCurrent

noncomputable section

open ReceiverStressEnergy

def tensorContraction (T A : Tensor) : ℝ :=
  ∑ i, ∑ j, T i j * A i j

def sym (A : Tensor) : Tensor := fun i j => (A i j + A j i) / 2

theorem tensorContraction_eq_sym_of_symmetric
    (T A : Tensor) (hT : ∀ i j, T i j = T j i) :
    tensorContraction T A = tensorContraction T (sym A) := by
  classical
  have hswap : (∑ i, ∑ j, T i j * A j i) = ∑ i, ∑ j, T i j * A i j := by
    calc
      (∑ i, ∑ j, T i j * A j i) = ∑ i, ∑ j, T j i * A i j := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, T i j * A i j := by
        simp_rw [hT]
  unfold tensorContraction sym
  ring_nf
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  rw [hswap]
  ring

def observerCurrentDivergence (u force : Index → ℝ) (T dU : Tensor) : ℝ :=
  -((∑ j, force j * u j) + tensorContraction T dU)

def productJetDivergence (u : Index → ℝ) (T : Tensor)
    (dT : DerivativeJet) (dU : Tensor) : ℝ :=
  -(∑ μ, ∑ ν, (dT μ ν μ * u ν + T μ ν * dU μ ν))

theorem productJetDivergence_eq_observerCurrent
    (u force : Index → ℝ) (T dU : Tensor) (dT : DerivativeJet)
    (hforce : ∀ ν, ∑ μ, dT μ ν μ = force ν) :
    productJetDivergence u T dT dU = observerCurrentDivergence u force T dU := by
  unfold productJetDivergence observerCurrentDivergence tensorContraction
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [hforce]

theorem observerCurrentDivergence_eq
    (u force : Index → ℝ) (T dU : Tensor) :
    observerCurrentDivergence u force T dU =
      -(∑ j, force j * u j) - tensorContraction T dU := by
  unfold observerCurrentDivergence
  ring

theorem observerCurrentDivergence_eq_symmetric_gradient
    (u force : Index → ℝ) (T dU : Tensor) (hT : ∀ i j, T i j = T j i) :
    observerCurrentDivergence u force T dU =
      -(∑ j, force j * u j) - tensorContraction T (sym dU) := by
  rw [observerCurrentDivergence_eq, tensorContraction_eq_sym_of_symmetric T dU hT]

theorem observerCurrentDivergence_killing
    (u force : Index → ℝ) (T dU : Tensor)
    (hT : ∀ i j, T i j = T j i)
    (hKilling : ∀ i j, dU i j + dU j i = 0) :
    observerCurrentDivergence u force T dU = -(∑ j, force j * u j) := by
  rw [observerCurrentDivergence_eq_symmetric_gradient u force T dU hT]
  unfold tensorContraction sym
  have hz : (∑ i, ∑ j, T i j * ((dU i j + dU j i) / 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [show dU i j + dU j i = 0 from hKilling i j]
    simp
  rw [hz, sub_zero]

structure LocalBalance where
  bulk : ℝ
  interface : ℝ
  exterior : ℝ
  equation : bulk + interface = exterior

theorem joined_balance (left right : LocalBalance)
    (opposite : left.interface + right.interface = 0) :
    left.bulk + right.bulk = left.exterior + right.exterior := by
  linarith [left.equation, right.equation, opposite]

end
end Soma.Holonics.Physics.ObserverBoundaryCurrent
