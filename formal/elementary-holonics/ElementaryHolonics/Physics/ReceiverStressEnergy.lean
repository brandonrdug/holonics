import ElementaryHolonics.Millennium.HolonicMassShellFace

/-!
# Finite observer stress--energy and angular-current algebra

This file is an algebraic receiver chart.  A tensor is represented by its sixteen components in a
fixed `(-,+,+,+)` observer chart; no differentiable manifold, field equation, or physical
constitutive identification is introduced here.  The angular-current result uses a first
derivative jet and proves the usual cancellation: symmetry of `T` removes the antisymmetric
stress term, while componentwise momentum conservation removes the remaining terms.
-/

noncomputable section

namespace Soma.Holonics.Physics.ReceiverStressEnergy

abbrev Index := Fin 4
abbrev Tensor := Index → Index → ℝ
abbrev DerivativeJet := Index → Index → Index → ℝ

def minkowskiSign (i : Index) : ℝ := if i = 0 then -1 else 1

def minkowskiContraction (u : Index → ℝ) (T : Tensor) : ℝ :=
  ∑ i, ∑ j, minkowskiSign i * u i * T i j * minkowskiSign j * u j

def observerBilinear (u v : Index → ℝ) (T : Tensor) : ℝ :=
  ∑ i, ∑ j, minkowskiSign i * u i * T i j * minkowskiSign j * v j

def restObserver : Index → ℝ := ![1, 0, 0, 0]

def restEnergyDensity (T : Tensor) : ℝ := T 0 0

theorem restObserver_contraction_eq_density (T : Tensor) :
    minkowskiContraction restObserver T = restEnergyDensity T := by
  simp [minkowskiContraction, minkowskiSign, restObserver, restEnergyDensity,
    Fin.sum_univ_succ]

def minkowskiMetricComponent (i j : Index) : ℝ :=
  if i = j then minkowskiSign i else 0

theorem minkowskiMetricComponent_symmetric (i j : Index) :
    minkowskiMetricComponent i j = minkowskiMetricComponent j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [minkowskiMetricComponent, h, Ne.symm h]

def perfectFluidTensor (density pressure : ℝ) : Tensor := fun i j ↦
  (density + pressure) * restObserver i * restObserver j +
    pressure * minkowskiMetricComponent i j

theorem perfectFluidTensor_symmetric (density pressure : ℝ) :
    ∀ i j, perfectFluidTensor density pressure i j =
      perfectFluidTensor density pressure j i := by
  intro i j
  rw [perfectFluidTensor, perfectFluidTensor, minkowskiMetricComponent_symmetric]
  ring

theorem perfectFluidTensor_restEnergy (density pressure : ℝ) :
    restEnergyDensity (perfectFluidTensor density pressure) = density := by
  simp [restEnergyDensity, perfectFluidTensor, minkowskiMetricComponent,
    minkowskiSign, restObserver]

theorem perfectFluidTensor_spatialDiagonal (density pressure : ℝ) (i : Index)
    (hi : i ≠ 0) :
    perfectFluidTensor density pressure i i = pressure := by
  fin_cases i <;> simp_all [perfectFluidTensor, minkowskiMetricComponent,
    minkowskiSign, restObserver]

def spatialPressureTrace (T : Tensor) : ℝ :=
  T 1 1 + T 2 2 + T 3 3

theorem perfectFluidTensor_spatialPressureTrace (density pressure : ℝ) :
    spatialPressureTrace (perfectFluidTensor density pressure) = 3 * pressure := by
  simp [spatialPressureTrace, perfectFluidTensor, minkowskiMetricComponent,
    minkowskiSign, restObserver]
  ring

def diagonalTensor (energy pressure₁ pressure₂ pressure₃ : ℝ) : Tensor :=
  fun i j => if i = j then
    if i = 0 then energy else if i = 1 then pressure₁ else
      if i = 2 then pressure₂ else pressure₃
  else 0

def boostedObserver : Index → ℝ := ![5 / 3, 4 / 3, 0, 0]
def boostedSpacelike : Index → ℝ := ![4 / 3, 5 / 3, 0, 0]

theorem diagonalTensor_boostedEnergy (energy pressure₁ pressure₂ pressure₃ : ℝ) :
    observerBilinear boostedObserver boostedObserver
        (diagonalTensor energy pressure₁ pressure₂ pressure₃) =
      25 * energy / 9 + 16 * pressure₁ / 9 := by
  simp [observerBilinear, diagonalTensor, boostedObserver, minkowskiSign,
    Fin.sum_univ_succ]
  ring

theorem diagonalTensor_boostedMixed (energy pressure₁ pressure₂ pressure₃ : ℝ) :
    observerBilinear boostedObserver boostedSpacelike
        (diagonalTensor energy pressure₁ pressure₂ pressure₃) =
      20 * (energy + pressure₁) / 9 := by
  simp [observerBilinear, diagonalTensor, boostedObserver, boostedSpacelike,
    minkowskiSign, Fin.sum_univ_succ]
  ring

theorem diagonalTensor_vacuumBoosted (energy : ℝ) :
    observerBilinear boostedObserver boostedObserver
        (diagonalTensor energy (-energy) (-energy) (-energy)) = energy ∧
      observerBilinear boostedObserver boostedSpacelike
        (diagonalTensor energy (-energy) (-energy) (-energy)) = 0 := by
  rw [diagonalTensor_boostedEnergy, diagonalTensor_boostedMixed]
  constructor <;> ring

theorem diagonalTensor_dustBoosted (energy : ℝ) :
    observerBilinear boostedObserver boostedObserver
        (diagonalTensor energy 0 0 0) = 25 * energy / 9 ∧
      observerBilinear boostedObserver boostedSpacelike
        (diagonalTensor energy 0 0 0) = 20 * energy / 9 := by
  rw [diagonalTensor_boostedEnergy, diagonalTensor_boostedMixed]
  constructor <;> ring

def kronecker (i j : Index) : ℝ := if i = j then 1 else 0

def angularCurrent (x : Index → ℝ) (T : Tensor) (mu a b : Index) : ℝ :=
  x a * T mu b - x b * T mu a

def angularDivergence (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet)
    (a b : Index) : ℝ :=
  ∑ mu, (kronecker mu a * T mu b + x a * dT mu b mu -
    kronecker mu b * T mu a - x b * dT mu a mu)

theorem angularDivergence_expansion
    (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet) (a b : Index) :
    angularDivergence x T dT a b =
      (T a b - T b a) + x a * (∑ mu, dT mu b mu) -
        x b * (∑ mu, dT mu a mu) := by
  have hdelta_left : ∀ (a b : Index),
      (∑ mu, kronecker mu a * T mu b) = T a b := by
    intro a b
    simp [kronecker, Finset.sum_ite_eq']
  have hdelta_right : ∀ (a b : Index),
      (∑ mu, kronecker mu b * T mu a) = T b a := by
    intro a b
    simp [kronecker, Finset.sum_ite_eq']
  unfold angularDivergence
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hdelta_left, hdelta_right]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem angularDivergence_eq_antisymmetric_add_force
    (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet)
    (force : Index → ℝ)
    (hforce : ∀ j, ∑ mu, dT mu j mu = force j) (a b : Index) :
    angularDivergence x T dT a b =
      (T a b - T b a) + x a * force b - x b * force a := by
  rw [angularDivergence_expansion, hforce b, hforce a]

theorem angularDivergence_eq_zero_of_symmetric_conserved
    (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet)
    (hsym : ∀ i j, T i j = T j i)
    (hcons : ∀ j, ∑ mu, dT mu j mu = 0) (a b : Index) :
    angularDivergence x T dT a b = 0 := by
  rw [angularDivergence_expansion, hsym a b, hcons b, hcons a]
  ring

theorem angularCurrent_antisymmetric (x : Index → ℝ) (T : Tensor)
    (mu a b : Index) :
    angularCurrent x T mu b a = -angularCurrent x T mu a b := by
  unfold angularCurrent
  ring

theorem massShell_positiveRestBranch
    (c m₀ E : ℝ) (p : Fin 3 → ℝ)
    (hc : 0 < c) (hm : 0 ≤ m₀)
    (hshell : E ^ 2 = c ^ 2 * (∑ i, p i * p i) + (m₀ * c ^ 2) ^ 2)
    (hrest : (∀ i, p i = 0)) (hE : 0 ≤ E) :
    E = m₀ * c ^ 2 := by
  have hsq : E ^ 2 = (m₀ * c ^ 2) ^ 2 := by
    rw [hshell]
    simp [hrest]
  have hy : 0 ≤ m₀ * c ^ 2 := by positivity
  nlinarith [sq_nonneg (E - m₀ * c ^ 2)]

theorem massShell_positiveRestBranch_from_owner
    (c m₀ : ℝ) (P : Soma.Holonics.Millennium.HolonicMassShellFace.FourMomentum)
    (hc : 0 < c) (hm : 0 ≤ m₀)
    (hshell : Soma.Holonics.Millennium.HolonicMassShellFace.lorentzPairing c P P =
      (m₀ * c ^ 2) ^ 2)
    (hrest : ∀ i, P.momentum i = 0) (hE : 0 ≤ P.energy) :
    P.energy = m₀ * c ^ 2 := by
  have hsq :=
    (Soma.Holonics.Millennium.HolonicMassShellFace.massShell_iff c m₀ P).mp hshell
  exact massShell_positiveRestBranch c m₀ P.energy P.momentum hc hm hsq hrest hE

end Soma.Holonics.Physics.ReceiverStressEnergy
