import ElementaryHolonics.Millennium.HolonicMassShellFace

/-! # Composite mass--energy and recoil faces

The constructions here are algebraic receiver laws over the existing `FourMomentum` owner.  They
retain the complete system four-momentum; no scalar energy reading is treated as a substitute for
directional recoil or invariant mass.
-/

noncomputable section

namespace Soma.Holonics.Physics.CompositeMassEnergy

open Soma.Holonics.Millennium.HolonicMassShellFace

theorem lorentzNorm_exchange (c : ℝ) (P dP : FourMomentum) :
    lorentzPairing c (P + dP) (P + dP) - lorentzPairing c P P =
      2 * lorentzPairing c P dP + lorentzPairing c dP dP := by
  rw [lorentzPairing_add_add]
  ring

theorem massless_pair_norm
    (c e₁ e₂ cosAngle : ℝ) (P Q : FourMomentum)
    (hP : P.energy = e₁) (hQ : Q.energy = e₂)
    (hPmassless : c ^ 2 * momentumSquare P = e₁ ^ 2)
    (hQmassless : c ^ 2 * momentumSquare Q = e₂ ^ 2)
    (hdot : c ^ 2 * (∑ i, P.momentum i * Q.momentum i) =
      e₁ * e₂ * cosAngle) :
    lorentzPairing c (P + Q) (P + Q) = 2 * e₁ * e₂ * (1 - cosAngle) := by
  rw [lorentzPairing_add_add, lorentzPairing_self, lorentzPairing_self]
  unfold lorentzPairing
  rw [hP, hQ, hPmassless, hQmassless, hdot]
  ring

def unitChartVector (energy : ℝ) (direction : Fin 3 → ℝ) : FourMomentum :=
  ⟨energy, direction⟩

theorem balanced_opposite_photons :
    lorentzPairing 1
      (unitChartVector 1 ![1, 0, 0] + unitChartVector 1 ![-1, 0, 0])
      (unitChartVector 1 ![1, 0, 0] + unitChartVector 1 ![-1, 0, 0]) = 4 := by
  norm_num [unitChartVector, lorentzPairing, momentumSquare, Fin.sum_univ_succ]

theorem parallel_photons_zero_system_norm :
    lorentzPairing 1
      (unitChartVector 1 ![1, 0, 0] + unitChartVector 1 ![1, 0, 0])
      (unitChartVector 1 ![1, 0, 0] + unitChartVector 1 ![1, 0, 0]) = 0 := by
  norm_num [unitChartVector, lorentzPairing, momentumSquare, Fin.sum_univ_succ]

/-- An equal-energy opposite photon pair in the existing c=1 four-momentum chart. -/
def oppositePhotonPair (energy : ℝ) : FourMomentum :=
  unitChartVector energy ![energy, 0, 0] + unitChartVector energy ![-energy, 0, 0]

theorem oppositePhotonPair_energy (energy : ℝ) :
    (oppositePhotonPair energy).energy = 2 * energy := by
  change energy + energy = 2 * energy
  ring

theorem oppositePhotonPair_norm (energy : ℝ) :
    lorentzPairing 1 (oppositePhotonPair energy) (oppositePhotonPair energy) =
      4 * energy^2 := by
  simp [oppositePhotonPair, unitChartVector, lorentzPairing, Fin.sum_univ_succ]
  ring

/-- Positive composite invariant mass does not imply a common positive excitation threshold.
The freely scalable photon-pair source admits a positive timelike total below any positive
energy bound. This is a radiation-source statement, not a proposed Yang--Mills spectrum. -/
theorem arbitrarilyLightMassivePhotonPair (threshold : ℝ) (positive : 0 < threshold) :
    ∃ energy : ℝ, 0 < energy ∧
      (oppositePhotonPair energy).energy < threshold ∧
      0 < lorentzPairing 1 (oppositePhotonPair energy) (oppositePhotonPair energy) := by
  refine ⟨threshold / 4, by positivity, ?_, ?_⟩
  · rw [oppositePhotonPair_energy]
    linarith
  · rw [oppositePhotonPair_norm]
    positivity

def unitBoost (beta gamma : ℝ) (P : FourMomentum) : FourMomentum :=
  ⟨gamma * (P.energy - beta * P.momentum 0),
    ![gamma * (P.momentum 0 - beta * P.energy), P.momentum 1, P.momentum 2]⟩

theorem unitBoost_preserves_lorentzNorm
    (beta gamma : ℝ) (P : FourMomentum)
    (hrel : gamma ^ 2 * (1 - beta ^ 2) = 1) :
    lorentzPairing 1 (unitBoost beta gamma P) (unitBoost beta gamma P) =
      lorentzPairing 1 P P := by
  calc
    lorentzPairing 1 (unitBoost beta gamma P) (unitBoost beta gamma P) =
        gamma ^ 2 * (1 - beta ^ 2) *
          (P.energy ^ 2 - P.momentum 0 ^ 2) -
          P.momentum 1 ^ 2 - P.momentum 2 ^ 2 := by
      simp [lorentzPairing, unitBoost, Fin.sum_univ_succ]
      ring
    _ = P.energy ^ 2 - P.momentum 0 ^ 2 -
          P.momentum 1 ^ 2 - P.momentum 2 ^ 2 := by rw [hrel]; ring
    _ = lorentzPairing 1 P P := by
      simp [lorentzPairing, Fin.sum_univ_succ]
      ring

theorem rational_boost_parameters :
    ((5 / 3 : ℝ) ^ 2) * (1 - (4 / 5 : ℝ) ^ 2) = 1 := by
  norm_num

end Soma.Holonics.Physics.CompositeMassEnergy
