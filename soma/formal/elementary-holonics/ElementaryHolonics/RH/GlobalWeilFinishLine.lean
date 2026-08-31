import ElementaryHolonics.RH.WeilPositivity

/-!
# The global Weil finish line for the Riemann hypothesis

**[definition]** The fixed-disc receiver in `RH.WeilPositivity` and the global Weil finish line are
kept as different objects.  This file records the source-specific construction targets without
replacing the standard terminal proposition:

* a nested cofinal family of zero-free xi contours;
* a cofinal prime cutoff, the weighted argument principle, and the prime/archimedean residual
  identity on every member of that family;
* convergence of the zero, prime, and boundary receivers, including the limiting explicit
  formula; and
* a complete off-critical-line test separator against the same global receiver whose arithmetic
  face is proved nonnegative.

**[proved-derived; formal-checked]** The last theorem has codomain literally `RH.Statement`.  No
field of the finish-line certificate stores `RH.Statement` or an implication to it.
-/

noncomputable section

namespace Soma.Holonics.RH

open Filter Metric Topology
open Soma.Holonics.RH.ExplicitFormulaReceiver
open Soma.Holonics.RH.ArchimedeanReceiver
open Soma.Holonics.RH.WeilPositivity

/-- [project-postulate] A nested, cofinal population of positively oriented xi contours centred at
the origin.  Cofinality is stated metrically and zero-freeness is retained at every boundary. -/
structure CofinalXiContours where
  radius : ℕ → ℝ
  radius_pos : ∀ n, 0 < radius n
  nested : Monotone radius
  cofinal : ∀ R : ℝ, ∃ n, R ≤ radius n
  admissible : ∀ n, AdmissibleXiContour 0 (radius n)

/-- [project-postulate] The complete global explicit-formula return for one declared Weil test.
The three convergence fields retain the actual cofinal populations; `limitPassage` is the
remaining passage through those limits, rather than a silently totalized infinite sum. -/
structure GlobalExplicitFormulaWitness (T : WeilTestFunction) (value : ℂ) where
  contours : CofinalXiContours
  primeCutoff : ℕ → ℕ
  primeCofinal : ∀ N : ℕ, ∃ n, N ≤ primeCutoff n
  boundary : ℕ → ℂ
  argumentPrinciple : ∀ n,
    HasWeightedArgumentPrinciple T 0 (contours.radius n)
  residualIdentity : ∀ n,
    HasArchimedeanResidualIdentity T 0 (contours.radius n) (primeCutoff n) (boundary n)
  primeLimit : ℂ
  zeroConverges :
    Tendsto (fun n ↦ truncatedZeroReceiver T 0 (contours.radius n)) atTop (nhds value)
  primeConverges :
    Tendsto (fun n ↦ truncatedPrimeReceiver T (primeCutoff n)) atTop (nhds primeLimit)
  boundaryVanishes : Tendsto boundary atTop (nhds 0)
  limitPassage :
    value = polarReceiver T - primeLimit - archimedeanReceiver T

/-- [proved-derived; formal-checked] Every member of the cofinal family carries the exact
truncated explicit formula with the constructed archimedean term. -/
theorem GlobalExplicitFormulaWitness.truncatedFormula
    {T : WeilTestFunction} {value : ℂ} (w : GlobalExplicitFormulaWitness T value) (n : ℕ) :
    truncatedZeroReceiver T 0 (w.contours.radius n) =
      polarReceiver T - truncatedPrimeReceiver T (w.primeCutoff n) -
        archimedeanReceiver T + w.boundary n :=
  truncatedExplicitFormula_of_archimedeanPorts
    (w.argumentPrinciple n) (w.residualIdentity n)

/-- [project-postulate] One canonical global receiver value for every admitted Weil test,
together with its complete cofinal explicit-formula reconstruction fibre. -/
structure GlobalWeilAtlas where
  receiver : WeilTestFunction → ℂ
  explicitFormula : ∀ T, GlobalExplicitFormulaWitness T (receiver T)

/-- [definition] A complex receiver lies in the nonnegative real ray. -/
def IsNonnegativeReal (z : ℂ) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

/-- [project-postulate] The arithmetic face of the global explicit formula is nonnegative on
every Weil square. -/
def GlobalWeilAtlas.IsPositive (atlas : GlobalWeilAtlas) : Prop :=
  ∀ (T : WeilTestFunction), WeilSquare T → IsNonnegativeReal (atlas.receiver T)

/-- [project-postulate] An off-critical-line zero is separated by an actual Weil square whose
value in this very atlas is outside the nonnegative real ray.  This is the complete-test-family
obligation; it cannot be discharged by a finite numerical test family. -/
structure OffLineWeilSeparator (atlas : GlobalWeilAtlas) where
  test : WeilTestFunction
  square : WeilSquare test
  separates : ¬ IsNonnegativeReal (atlas.receiver test)

/-- [project-postulate] The exact RH finish line: construct the global explicit-formula atlas,
prove arithmetic positivity, and construct a Weil separator for every alleged nontrivial
off-line zero.  The fields expose the missing analytic objects and do not contain RH itself. -/
structure GlobalWeilFinishLine where
  atlas : GlobalWeilAtlas
  arithmeticPositivity : atlas.IsPositive
  offLineSeparation : ∀ (s : ℂ),
    riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) →
    s ≠ 1 →
    s.re ≠ 1 / 2 →
    Nonempty (OffLineWeilSeparator atlas)

/-- [proved-derived; formal-checked] The global Weil construction closes the repository's exact
standard RH proposition.  The contradiction uses the same receiver occurrence on both the
arithmetic-positive and off-line-separating faces. -/
theorem statement_of_globalWeilFinishLine (finish : GlobalWeilFinishLine) : RH.Statement := by
  intro s hzero htrivial hnotPole
  by_contra hoffLine
  obtain ⟨separator⟩ := finish.offLineSeparation s hzero htrivial hnotPole hoffLine
  exact separator.separates
    (finish.arithmeticPositivity separator.test separator.square)

section Audit

#print axioms GlobalExplicitFormulaWitness.truncatedFormula
#print axioms statement_of_globalWeilFinishLine

end Audit

end Soma.Holonics.RH
