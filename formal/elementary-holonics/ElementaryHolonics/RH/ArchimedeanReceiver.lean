import ElementaryHolonics.RH.ExplicitFormulaReceiver
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The archimedean receiver of the explicit formula, constructed

`RH.ExplicitFormulaReceiver` leaves the archimedean term of the explicit formula as a parameter of
`HasPrimeArchimedeanResidualIdentity` — "independently still-unconstructed".  This file constructs
it.

With `ξ′/ξ(s) = 1/s + 1/(s − 1) − ½ log π + ½ ψ(s/2) + ζ′/ζ(s)`, the Γ-factor contribution to
`Σ_ρ Φ(ρ)` on the line `Re s = ½` is

```
    (1/2π) ∫ ĥ(t) · Re ψ(¼ + it/2) dt,        ĥ(t) = Φ(½ + it),
```

and with the integral representation `ψ(z) = −γ_E + ∫₀^∞ (e^{−u} − e^{−zu})/(1 − e^{−u}) du`
(`Re z > 0`) and Fourier inversion `(1/2π) ∫ ĥ(t) cos(tu/2) dt = (h(u/2) + h(−u/2))/2`, the
`t`-integral becomes an integral on the logarithmic line, `u = 2x`:

```
    −γ_E h(0) + 2 ∫₀^∞ [ e^{−2x} h(0) − e^{−x/2} (h(x) + h(−x))/2 ] / (1 − e^{−2x}) dx .
```

Together with `−h(0) log π` this is the whole archimedean side.  In the sign convention of
`HasPrimeArchimedeanResidualIdentity` (`contour = polar − prime − archimedean + boundary`) the
receiver is the negative of that sum: `archimedeanReceiver`.

**Cross-validation, exterior to this file.**  With the same constants the arithmetic side of the
Weil pairing on the step family `1_{[−a,a]}`, `a ∈ {1/2, …, 6}`, computed from the primes alone,
intersects the spectral side computed from the 649 certified zeros below `T = 1000` at all 78
Gram entries (`.local/artifacts/the_weil_form_is_positive_on_the_primes_and_the_zeros_agree/receipt-12-members-to-6.txt`,
2026-08-28).  An earlier form of the constant `γ_E` that was high by `4.1·10⁻⁴` was refuted by
that check.  The identity itself remains the named residual port; nothing here asserts the
explicit formula.
-/

noncomputable section

namespace Soma.Holonics.RH.ArchimedeanReceiver

open Soma.Holonics.RH.ExplicitFormulaReceiver
open Real MeasureTheory

/-- [definition] The even part of the arithmetic kernel: the only part the Γ-factor reads. -/
def evenKernel (T : WeilTestFunction) (x : ℝ) : ℂ :=
  (T.arithmeticKernel x + T.arithmeticKernel (-x)) / 2

/-- [definition] The archimedean integrand on the logarithmic half-line
`[e^{−2x} h(0) − e^{−x/2} · evenKernel x] / (1 − e^{−2x})`.  At `x → 0⁺` it has the finite limit
`−(3/4) h(0) − h′_even(0)`; the singularity is removable. -/
def archimedeanIntegrand (T : WeilTestFunction) (x : ℝ) : ℂ :=
  (((Real.exp (-2 * x) : ℝ) : ℂ) * T.arithmeticKernel 0
      - ((Real.exp (-x / 2) : ℝ) : ℂ) * evenKernel T x)
    / (1 - ((Real.exp (-2 * x) : ℝ) : ℂ))

/-- [definition] **The archimedean receiver**, in the sign convention of
`HasPrimeArchimedeanResidualIdentity`:

```
    h(0) (log π + γ_E) − 2 ∫₀^∞ archimedeanIntegrand .
```
-/
def archimedeanReceiver (T : WeilTestFunction) : ℂ :=
  T.arithmeticKernel 0 * ((Real.log Real.pi + eulerMascheroniConstant : ℝ) : ℂ)
    - 2 * ∫ x in Set.Ioi (0 : ℝ), archimedeanIntegrand T x

/-- [definition] The residual identity with the constructed archimedean receiver: the one named
port that remains between the contour and the explicit formula. -/
def HasArchimedeanResidualIdentity (T : WeilTestFunction) (c : ℂ) (R : ℝ) (N : ℕ)
    (boundary : ℂ) : Prop :=
  HasPrimeArchimedeanResidualIdentity T c R N (archimedeanReceiver T) boundary

/-- [proved-derived; formal-checked] Composing the weighted argument principle with the
constructed residual identity gives the truncated explicit formula with every term named. -/
theorem truncatedExplicitFormula_of_archimedeanPorts
    {T : WeilTestFunction} {c : ℂ} {R : ℝ} {N : ℕ} {boundary : ℂ}
    (harg : HasWeightedArgumentPrinciple T c R)
    (hresidual : HasArchimedeanResidualIdentity T c R N boundary) :
    truncatedZeroReceiver T c R =
      polarReceiver T - truncatedPrimeReceiver T N - archimedeanReceiver T + boundary :=
  truncatedExplicitFormula_of_ports harg hresidual

/-- [proved-derived; formal-checked] For an even kernel the Γ-factor reads the kernel itself. -/
theorem evenKernel_of_even (T : WeilTestFunction)
    (heven : ∀ x, T.arithmeticKernel (-x) = T.arithmeticKernel x) (x : ℝ) :
    evenKernel T x = T.arithmeticKernel x := by
  unfold evenKernel
  rw [heven]
  ring

/-- [proved-derived; formal-checked] The archimedean receiver is a receiver of the even part
alone: two test charts with the same even kernel return the same archimedean scalar. -/
theorem archimedeanReceiver_congr_even (T U : WeilTestFunction)
    (h : ∀ x, evenKernel T x = evenKernel U x) :
    archimedeanReceiver T = archimedeanReceiver U := by
  have h0 : T.arithmeticKernel 0 = U.arithmeticKernel 0 := by
    have := h 0
    unfold evenKernel at this
    simp only [neg_zero] at this
    have h2 : (T.arithmeticKernel 0 + T.arithmeticKernel 0) / 2 = T.arithmeticKernel 0 := by ring
    have h3 : (U.arithmeticKernel 0 + U.arithmeticKernel 0) / 2 = U.arithmeticKernel 0 := by ring
    rw [h2, h3] at this
    exact this
  unfold archimedeanReceiver
  rw [h0]
  congr 2
  apply integral_congr_ae
  filter_upwards with x
  unfold archimedeanIntegrand
  rw [h0, h x]

section Audit

#print axioms truncatedExplicitFormula_of_archimedeanPorts
#print axioms evenKernel_of_even
#print axioms archimedeanReceiver_congr_even

end Audit

end Soma.Holonics.RH.ArchimedeanReceiver
