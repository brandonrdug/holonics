import Mathlib.Tactic

/-!
# NavierStokesScaling: the exact rational weight ledger

Under the parabolic rebase `u_λ(x,t) = λ·u(λx, λ²t)` every retained face carries an
exact rational weight, and the weights decide the trichotomy that separates two
dimensions from three.  **This file is exponent bookkeeping over `ℚ`**: the weights are
declared from the standard scaling and the arithmetic here is exact; deriving each
weight from the PDE is not done here and is not claimed.

```text
                weight in dimension d      d = 2      d = 3
  energy L²          1 − d/2                 0        −1/2
  enstrophy Ḣ¹       2 − d/2                 1         1/2
  helicity ∫u·ω      3 − d                   1          0
  Lᵖ                 1 − d/p                        p=3:  0
  Ḣˢ                 1 + s − d/2                    s=½:  0
```

**The reading:** in two dimensions the *conserved* quantity is the critical one.  In
three the conserved quantity is strictly subcritical, and the scale-invariant quantity
is the **helicity** — a linking number, a winding, not a magnitude.  That is where the
energy method loses its grip, stated as exact rational arithmetic rather than as
folklore.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.NavierStokesScaling

/-- Weight of the `L²` energy under the parabolic rebase `u_λ(x,t) = λ·u(λx, λ²t)`. -/
def energyWeight (d : ℚ) : ℚ := 1 - d / 2
/-- Weight of the enstrophy `‖u‖_{Ḣ¹}`. -/
def enstrophyWeight (d : ℚ) : ℚ := 2 - d / 2
/-- Weight of the helicity `∫ u·ω`. -/
def helicityWeight (d : ℚ) : ℚ := 3 - d
/-- Weight of the `Lᵖ` norm. -/
def lpWeight (d p : ℚ) : ℚ := 1 - d / p
/-- Weight of the homogeneous Sobolev norm `Ḣˢ`. -/
def sobolevWeight (d s : ℚ) : ℚ := 1 + s - d / 2

theorem theEnergyIsCriticalExactlyInDimensionTwo (d : ℚ) :
    energyWeight d = 0 ↔ d = 2 := by
  unfold energyWeight; constructor <;> intro h <;> linarith

theorem theHelicityIsCriticalExactlyInDimensionThree (d : ℚ) :
    helicityWeight d = 0 ↔ d = 3 := by
  unfold helicityWeight; constructor <;> intro h <;> linarith

theorem theLpIsCriticalExactlyAtTheDimension {d p : ℚ} (hp : p ≠ 0) :
    lpWeight d p = 0 ↔ p = d := by
  unfold lpWeight
  rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hp]
  exact eq_comm

theorem theSobolevIsCriticalExactlyAtHalfTheDimensionMinusOne (d s : ℚ) :
    sobolevWeight d s = 0 ↔ s = d / 2 - 1 := by
  unfold sobolevWeight; constructor <;> intro h <;> linarith

/-- **THE THREE-DIMENSIONAL LEDGER**: the conserved quantity is NOT critical, and the
critical quantity is the helicity — a winding, not a magnitude. -/
theorem theScalingWeightLedger :
    energyWeight 3 = -(1/2) ∧ enstrophyWeight 3 = 1/2 ∧ helicityWeight 3 = 0 ∧
      lpWeight 3 3 = 0 ∧ sobolevWeight 3 (1/2) = 0 ∧
      energyWeight 2 = 0 ∧ helicityWeight 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [energyWeight, enstrophyWeight, helicityWeight, lpWeight, sobolevWeight] <;> norm_num

end Soma.Holonics.Millennium.NavierStokesScaling
