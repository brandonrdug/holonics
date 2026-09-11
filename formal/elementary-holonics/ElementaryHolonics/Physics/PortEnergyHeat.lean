import ElementaryHolonics.Physics.CoupledIncidence
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A port balance for quadratic capacitive/inductive storage

This is a small dynamical owner for the energy bookkeeping that is implicit in
`CoupledIncidence.diagonalStorage`.  The two coordinates may be read as a
capacitive coordinate and an inductive coordinate (the coefficients are their
storage weights).  The theorem keeps the source derivatives and the
constitutive dissipative return as hypotheses: the balance is then obtained by
the chain rule, rather than being postulated as a conservation axiom. The
coefficients are chart coefficients; a physical dimensional interpretation
requires the caller to supply the corresponding unit chart.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicComplexParametron

/-- A two-coordinate port state for a capacitive/inductive storage pair. -/
abbrev PortState := ℝ × ℝ

/-- Diagonal quadratic energy, with the two coordinates as the stored state. -/
def portStoredEnergy (capacity inverseInductance : ℝ) (state : PortState) : ℝ :=
  (1 / 2 : ℝ) *
    (capacity * state.1 ^ 2 + inverseInductance * state.2 ^ 2)

/-- The constitutive effort returned by the storage law.  Its physical units
depend on the caller's chosen coordinate chart. -/
def portEffort (capacity inverseInductance : ℝ) (state : PortState) : PortState :=
  (capacity * state.1, inverseInductance * state.2)

/-- External power supplied through the two oriented ports. -/
def externalPortPower (capacity inverseInductance : ℝ)
    (state source : PortState) : ℝ :=
  (portEffort capacity inverseInductance state).1 * source.1 +
    (portEffort capacity inverseInductance state).2 * source.2

/-- Joule/ohmic heat returned by the diagonal dissipative constitutive law. -/
def ohmicHeat (capacity inverseInductance conductance₁ conductance₂ : ℝ)
    (state : PortState) : ℝ :=
  conductance₁ * (portEffort capacity inverseInductance state).1 ^ 2 +
    conductance₂ * (portEffort capacity inverseInductance state).2 ^ 2

/-- Nonnegative constitutive coefficients return nonnegative ohmic heat. -/
theorem ohmicHeat_nonneg
    (capacity inverseInductance conductance₁ conductance₂ : ℝ)
    (hconductance₁ : 0 ≤ conductance₁) (hconductance₂ : 0 ≤ conductance₂)
    (state : PortState) :
    0 ≤ ohmicHeat capacity inverseInductance conductance₁ conductance₂ state := by
  unfold ohmicHeat
  exact add_nonneg
    (mul_nonneg hconductance₁ (sq_nonneg _))
    (mul_nonneg hconductance₂ (sq_nonneg _))

/-- The constitutive port dynamics: source flow minus dissipative return. -/
def portDynamics (capacity inverseInductance conductance₁ conductance₂ : ℝ)
    (state source : PortState) : PortState :=
  (source.1 - conductance₁ * (portEffort capacity inverseInductance state).1,
    source.2 - conductance₂ * (portEffort capacity inverseInductance state).2)

/--
Along an actually differentiable port trajectory obeying the constitutive
dynamics, stored energy changes by external port power less returned heat.

The assumptions `h₁` and `h₂` retain the observed/source flow at the declared
time.  The result therefore covers a driven capacitor/inductor pair and does
not silently identify a receiver measurement with a universal conservation law.
-/
theorem hasDerivAt_portStoredEnergy
    (capacity inverseInductance conductance₁ conductance₂ : ℝ)
    (state source : ℝ → PortState) (time : ℝ)
    (h₁ : HasDerivAt (fun t : ℝ ↦ (state t).1)
      (portDynamics capacity inverseInductance conductance₁ conductance₂
        (state time) (source time)).1 time)
    (h₂ : HasDerivAt (fun t : ℝ ↦ (state t).2)
      (portDynamics capacity inverseInductance conductance₁ conductance₂
        (state time) (source time)).2 time) :
    HasDerivAt
      (fun t ↦ portStoredEnergy capacity inverseInductance (state t))
      (externalPortPower capacity inverseInductance (state time) (source time) -
        ohmicHeat capacity inverseInductance conductance₁ conductance₂
          (state time)) time := by
  have hpow₁ : HasDerivAt (fun z : ℝ ↦ z ^ 2)
      (2 * (state time).1) (state time).1 := by
    simpa using hasDerivAt_pow 2 (state time).1
  have hpow₂ : HasDerivAt (fun z : ℝ ↦ z ^ 2)
      (2 * (state time).2) (state time).2 := by
    simpa using hasDerivAt_pow 2 (state time).2
  have hsq₁ := (hpow₁.comp time h₁).const_mul (capacity / 2)
  have hsq₂ := (hpow₂.comp time h₂).const_mul (inverseInductance / 2)
  have hsum := hsq₁.add hsq₂
  have hfun :
      (fun t ↦ portStoredEnergy capacity inverseInductance (state t)) =
        ((fun y ↦ capacity / 2 * ((fun z : ℝ ↦ z ^ 2) ∘ fun t ↦ (state t).1) y) +
          fun y ↦ inverseInductance / 2 *
            ((fun z : ℝ ↦ z ^ 2) ∘ fun t ↦ (state t).2) y) := by
    funext t
    simp [portStoredEnergy]
    ring
  have hsum' : HasDerivAt
      (fun t ↦ portStoredEnergy capacity inverseInductance (state t))
      (capacity / 2 * (2 * (state time).1 *
        (portDynamics capacity inverseInductance conductance₁ conductance₂
          (state time) (source time)).1) +
       inverseInductance / 2 * (2 * (state time).2 *
        (portDynamics capacity inverseInductance conductance₁ conductance₂
          (state time) (source time)).2)) time := by
    rw [hfun]
    exact hsum
  apply hsum'.congr_deriv
  simp only [externalPortPower, ohmicHeat, portEffort, portDynamics]
  ring

/-! ## Heat return and total energy -/

/-- Stored energy plus retained heat changes exactly by external port power. -/
theorem hasDerivAt_totalEnergy_of_ohmicLaw
    (capacity inverseInductance conductance₁ conductance₂ : ℝ)
    (state : ℝ → PortState) (heat : ℝ → ℝ) (source : ℝ → PortState)
    (time : ℝ)
    (h₁ : HasDerivAt (fun t : ℝ ↦ (state t).1)
      (portDynamics capacity inverseInductance conductance₁ conductance₂
        (state time) (source time)).1 time)
    (h₂ : HasDerivAt (fun t : ℝ ↦ (state t).2)
      (portDynamics capacity inverseInductance conductance₁ conductance₂
        (state time) (source time)).2 time)
    (hheat : HasDerivAt (fun t : ℝ ↦ heat t)
      (ohmicHeat capacity inverseInductance conductance₁ conductance₂
        (state time)) time) :
    HasDerivAt
      (fun t ↦ portStoredEnergy capacity inverseInductance (state t) + heat t)
      (externalPortPower capacity inverseInductance (state time) (source time)) time := by
  have hstored := hasDerivAt_portStoredEnergy capacity inverseInductance
    conductance₁ conductance₂ state source time h₁ h₂
  have htotal := hstored.add hheat
  apply htotal.congr_deriv
  simp only [externalPortPower, ohmicHeat, portEffort]
  ring

end Soma.Holonics.Millennium.HolonicComplexParametron
