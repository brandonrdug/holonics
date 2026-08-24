import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.Winding
import ElementaryHolonics.RH.WeilVector

/-!
# A typed receiver for the Riemann explicit formula

This file does not postulate the explicit formula.  It fixes the object, test-function
chart, zero receiver, prime receiver, polar receiver, and logarithmic-derivative contour
whose equality has to be proved.

The test chart is a smooth compactly supported complex-valued kernel on the real logarithmic
line together with its bilateral Laplace transform.  The zero receiver uses the divisor of the
actual entire Riemann xi function from `RiemannXi`, retaining multiplicity.  The finite-place
receiver uses von Mangoldt weights at the two logarithmic orientations.  Two independently
named ports remain:

1. the weighted argument principle, from the contour to the xi divisor; and
2. the residual identity targeted by contour deformation, from the logarithmic derivative to
   independently still-unconstructed archimedean and boundary terms.

Their composition is the truncated explicit formula.  A global formula additionally
owes a cofinal family of contours and a proof that the boundary term vanishes.
-/

noncomputable section

namespace Soma.Holonics.RH.ExplicitFormulaReceiver

open Complex Metric Real MeromorphicOn MeasureTheory
open ArithmeticFunction
open Soma.Holonics.RH.RiemannXi

/-- A declared Weil test chart: a smooth compactly supported complex-valued kernel on
the real logarithmic line and its bilateral Laplace transform on the spectral plane. -/
structure WeilTestFunction where
  arithmeticKernel : ℝ → ℂ
  spectralKernel : ℂ → ℂ
  smooth : ContDiff ℝ ⊤ arithmeticKernel
  compactSupport : HasCompactSupport arithmeticKernel
  spectralAnalytic : Differentiable ℂ spectralKernel
  spectral_eq_bilateralLaplace : ∀ s : ℂ,
    spectralKernel s = ∫ x : ℝ,
      Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) * arithmeticKernel x

/-- The xi-zero population inside one closed disc, weighted by a spectral test and
counted with exact divisor multiplicity. -/
def truncatedZeroReceiver (T : WeilTestFunction) (c : ℂ) (R : ℝ) : ℂ :=
  ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℂ) *
    T.spectralKernel u

/-- The finite prime-power receiver through address `N`, with the two logarithmic
orientations and the standard square-root normalization. -/
def truncatedPrimeReceiver (T : WeilTestFunction) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (((vonMangoldt n : ℝ) : ℂ) / ((Real.sqrt n : ℝ) : ℂ)) *
      (T.arithmeticKernel (Real.log n) + T.arithmeticKernel (-Real.log n))

/-- The two removed polar addresses in the completed zeta chart. -/
def polarReceiver (T : WeilTestFunction) : ℂ :=
  T.spectralKernel 0 + T.spectralKernel 1

/-- The independently defined logarithmic-derivative contour receiver. -/
def contourReceiver (T : WeilTestFunction) (c : ℂ) (R : ℝ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    ∮ z in C(c, R),
      T.spectralKernel z * (deriv riemannXi z / riemannXi z)

/-- A positively oriented xi contour whose boundary meets no zero.  These hypotheses are part of
the argument-principle port rather than being hidden behind its desired equality. -/
structure AdmissibleXiContour (c : ℂ) (R : ℝ) : Prop where
  radius_pos : 0 < R
  zero_free : ∀ z ∈ sphere c R, riemannXi z ≠ 0

/-- The first exact missing port: a weighted argument principle on an admitted xi contour. -/
structure HasWeightedArgumentPrinciple
    (T : WeilTestFunction) (c : ℂ) (R : ℝ) : Prop where
  admissible : AdmissibleXiContour c R
  equation : contourReceiver T c R = truncatedZeroReceiver T c R

/-- The second exact equality target: decomposition of the same contour into polar, finite-place,
archimedean, and boundary scalars.  The last two terms remain parameters because their actual
receiver definitions and lineage have not yet been constructed.  Consequently this structure is
residual bookkeeping at fixed values, not by itself a contour-deformation proof. -/
structure HasPrimeArchimedeanResidualIdentity
    (T : WeilTestFunction) (c : ℂ) (R : ℝ) (N : ℕ)
    (archimedean boundary : ℂ) : Prop where
  admissible : AdmissibleXiContour c R
  equation : contourReceiver T c R =
    polarReceiver T - truncatedPrimeReceiver T N - archimedean + boundary

/-- Composing the two addressed ports gives the exact truncated explicit formula. -/
theorem truncatedExplicitFormula_of_ports
    {T : WeilTestFunction} {c : ℂ} {R : ℝ} {N : ℕ}
    {archimedean boundary : ℂ}
    (harg : HasWeightedArgumentPrinciple T c R)
    (hresidual : HasPrimeArchimedeanResidualIdentity T c R N archimedean boundary) :
    truncatedZeroReceiver T c R =
      polarReceiver T - truncatedPrimeReceiver T N - archimedean + boundary := by
  rw [← harg.equation]
  exact hresidual.equation

/-- The argument-principle defect is retained rather than silently discarded. -/
def argumentPrincipleDefect (T : WeilTestFunction) (c : ℂ) (R : ℝ) : ℂ :=
  contourReceiver T c R - truncatedZeroReceiver T c R

theorem hasWeightedArgumentPrinciple_iff_defect_eq_zero
    {T : WeilTestFunction} {c : ℂ} {R : ℝ}
    (hadmissible : AdmissibleXiContour c R) :
    HasWeightedArgumentPrinciple T c R ↔
      argumentPrincipleDefect T c R = 0 := by
  constructor
  · intro h
    exact sub_eq_zero.mpr h.equation
  · intro h
    exact ⟨hadmissible, sub_eq_zero.mp h⟩

/-- Agreement of two spectral kernels on every occupied divisor address suffices for equal zero
receivers.  Cancellation can make the scalar receivers equal under weaker conditions, so this is
a support-local congruence theorem rather than a complete reconstruction-fibre characterization. -/
theorem truncatedZeroReceiver_congr
    {T U : WeilTestFunction} {c : ℂ} {R : ℝ}
    (h : ∀ u,
      MeromorphicOn.divisor riemannXi (closedBall c |R|) u ≠ 0 →
        T.spectralKernel u = U.spectralKernel u) :
    truncatedZeroReceiver T c R = truncatedZeroReceiver U c R := by
  unfold truncatedZeroReceiver
  apply finsum_congr
  intro u
  by_cases hu : MeromorphicOn.divisor riemannXi (closedBall c |R|) u = 0
  · simp [hu]
  · rw [h u hu]

/-- Agreement on every admitted finite logarithmic address and its reflection suffices for equal
prime receivers.  The hypothesis deliberately includes addresses whose von Mangoldt coefficient
may vanish; it is not claimed to characterize the receiver's exact fibre. -/
theorem truncatedPrimeReceiver_congr
    {T U : WeilTestFunction} {N : ℕ}
    (hpos : ∀ n ∈ Finset.Icc 1 N,
      T.arithmeticKernel (Real.log n) = U.arithmeticKernel (Real.log n))
    (hneg : ∀ n ∈ Finset.Icc 1 N,
      T.arithmeticKernel (-Real.log n) = U.arithmeticKernel (-Real.log n)) :
    truncatedPrimeReceiver T N = truncatedPrimeReceiver U N := by
  unfold truncatedPrimeReceiver
  apply Finset.sum_congr rfl
  intro n hn
  rw [hpos n hn, hneg n hn]

/-- The untruncated Dirichlet prime receiver already equals the logarithmic derivative
on its half-plane of absolute convergence. -/
def dirichletPrimeReceiver (s : ℂ) : ℂ :=
  LSeries (fun n => (vonMangoldt n : ℂ)) s

theorem dirichletPrimeReceiver_eq_logarithmicDerivative
    {s : ℂ} (hs : 1 < s.re) :
    dirichletPrimeReceiver s = -deriv riemannZeta s / riemannZeta s :=
  Soma.Holonics.RH.theFinitePlaceTermIsTheLogarithmicDerivative hs

end Soma.Holonics.RH.ExplicitFormulaReceiver
