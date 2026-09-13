import ElementaryHolonics.Millennium.Pivots

/-!
# The Yang–Mills row: a receiver gap, vacuum reduction, and a perturbation passage

`MillenniumCoupling` proves coercivity for positive-definite finite-dimensional receiver forms
and excludes coercivity for compact forms on infinite-dimensional carriers. The results below
quantify the bound, retain the vacuum complement and transport the bound through a controlled
quadratic difference.

**The gap is a number.**  `theGapIsThePositivityOfTheSphereInfimum`: a form is coercive exactly
when its quadratic readings on the unit sphere stay above some positive `Δ`.  Homogeneity does the
rest, so "the form has a gap" and "the sphere readings are bounded away from zero" are one
statement.  This is a quadratic/spectral receiver bound; identifying it with a physical energy or
mass scale requires a declared physical operator, units, and receiver map.

**The vacuum is invisible to the form, and it forces the reduction.**  `theVacuumIsInvisible`: if
`e` returns nothing under a positive form, adding any amount of it changes no diagonal reading of
that form — the vacuum lies in the radical and the reading factors through the quotient by it.
`theVacuumRefusesAGlobalGap`
then shows any form with a nonzero vacuum is non-coercive.  So stating the mass gap *above the
vacuum* is not a convention: on the whole space no gap can exist, and the only place one can live
is the quotient.  The frame makes that reduction automatic rather than stipulated.

**And the dichotomy is not vacuous.**  `theAnchorIsNonCompactInInfiniteDimensions`: the identity has
gap one, while its unit-ball image is not totally bounded on an infinite-dimensional space.  A gap
can therefore occur in infinite dimensions; this witness does not classify all non-compact forms.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.MassGap

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.MillenniumCoupling.ReceiverForm
open Soma.Holonics.Millennium.Pivots Metric Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **THE ANCHOR WITNESSES THAT A GAP CAN OCCUR IN INFINITE DIMENSIONS.**  The identity has gap one,
so by `theGapRefusesACompactForm` its unit-ball image is not totally bounded unless the space is
finite-dimensional.  This witness does not classify all non-compact forms. -/
theorem theAnchorIsNonCompactInInfiniteDimensions [CompleteSpace V]
    (hinf : ¬ FiniteDimensional ℝ V) :
    ¬ TotallyBounded ((euclidean V).T '' Metric.closedBall (0 : V) 1) := by
  intro hcpt
  exact hinf ((euclidean V).theGapRefusesACompactForm hcpt theEuclideanFormIsCoercive)

/-! ## The gap is a number: the infimum of the reading over the unit sphere -/

/-- The readings on the unit sphere. -/
def sphereReadings (F : ReceiverForm V) : Set ℝ := (fun v => F.B v v) '' Metric.sphere (0 : V) 1

/-- **A GAP IS A LOWER BOUND ON THE SPHERE READINGS.** -/
theorem theGapBoundsTheSphere {F : ReceiverForm V} (h : F.IsCoercive) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ r ∈ sphereReadings F, Δ ≤ r := by
  obtain ⟨Δ, hΔ, hB⟩ := h
  refine ⟨Δ, hΔ, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  have hn : ‖v‖ = 1 := by simpa using hv
  have := hB v
  rwa [hn, one_pow, mul_one] at this

/-- **AND A POSITIVE LOWER BOUND ON THE SPHERE READINGS IS A GAP.**  Homogeneity does the rest, so
"the form is coercive" and "the sphere readings stay above zero" are one statement.  The bound is a
quadratic/spectral receiver value; a physical mass or energy interpretation requires its declared
operator, units, and receiver map. -/
theorem theSphereBoundIsAGap {F : ReceiverForm V} {Δ : ℝ} (hΔ : 0 < Δ)
    (h : ∀ r ∈ sphereReadings F, Δ ≤ r) : F.IsCoercive := by
  refine ⟨Δ, hΔ, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [ReceiverForm.B]
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    set w : V := ‖v‖⁻¹ • v with hw
    have hws : w ∈ Metric.sphere (0 : V) 1 := by simp [hw, norm_smul, hnv]
    have hbw : Δ ≤ F.B w w := h _ ⟨w, hws, rfl⟩
    have hvw : v = ‖v‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hnv, one_smul]
    have hq : F.B v v = ‖v‖ ^ 2 * F.B w w := by
      have hqq : F.B (‖v‖ • w) (‖v‖ • w) = ‖v‖ ^ 2 * F.B w w := F.theReadingIsQuadratic _ _
      rwa [← hvw] at hqq
    rw [hq]
    nlinarith [hbw, sq_nonneg ‖v‖]

/-- **SO THE MASS GAP IS EXACTLY THE POSITIVITY OF ONE INFIMUM.** -/
theorem theGapIsThePositivityOfTheSphereInfimum (F : ReceiverForm V) :
    F.IsCoercive ↔ ∃ Δ : ℝ, 0 < Δ ∧ ∀ r ∈ sphereReadings F, Δ ≤ r :=
  ⟨theGapBoundsTheSphere, fun ⟨_, hΔ, h⟩ => theSphereBoundIsAGap hΔ h⟩

/-- The signed lower return, rather than an absolute-value projection, is enough to transport
the lower gap. The complete forms and oriented difference remain in the statement. -/
theorem theGapSurvivesReceiverDifference (F G : ReceiverForm V) {Δ ε : ℝ}
    (_hΔ : 0 < Δ) (hF : ∀ v : V, Δ * ‖v‖ ^ 2 ≤ F.B v v)
    (hDifference : ∀ v : V, -(ε * ‖v‖ ^ 2) ≤ G.B v v - F.B v v)
    (hε : ε < Δ) : G.IsCoercive := by
  refine ⟨Δ - ε, sub_pos.mpr hε, fun v => ?_⟩
  nlinarith [hF v, hDifference v]

/-- The quantitative inequality itself is exposed for physical scaling/remainder consumers. -/
theorem receiverDifference_lower_bound (F G : ReceiverForm V) {Δ ε : ℝ}
    (hF : ∀ v : V, Δ * ‖v‖ ^ 2 ≤ F.B v v)
    (hDifference : ∀ v : V, -(ε * ‖v‖ ^ 2) ≤ G.B v v - F.B v v) (v : V) :
    (Δ - ε) * ‖v‖ ^ 2 ≤ G.B v v := by
  nlinarith [hF v, hDifference v]

/-- The upper return has its own polarity and allowance; it need not mirror the lower one. -/
theorem receiverDifference_upper_bound (F G : ReceiverForm V) {ceiling ε : ℝ}
    (hF : ∀ v : V, F.B v v ≤ ceiling * ‖v‖ ^ 2)
    (hDifference : ∀ v : V, G.B v v - F.B v v ≤ ε * ‖v‖ ^ 2) (v : V) :
    G.B v v ≤ (ceiling + ε) * ‖v‖ ^ 2 := by
  nlinarith [hF v, hDifference v]

/-- The same perturbation bound can be reused at every index of a family on one carrier. -/
theorem familyGapSurvivesReceiverDifference {Index : Type*}
    (F G : Index → ReceiverForm V) {Δ ε : ℝ}
    (_hΔ : 0 < Δ) (hF : ∀ (index : Index) (v : V), Δ * ‖v‖ ^ 2 ≤ (F index).B v v)
    (hDifference : ∀ (index : Index) (v : V),
      -(ε * ‖v‖ ^ 2) ≤ (G index).B v v - (F index).B v v)
    (hε : ε < Δ) :
    0 < Δ - ε ∧ ∀ (index : Index) (v : V), (Δ - ε) * ‖v‖ ^ 2 ≤ (G index).B v v := by
  refine ⟨sub_pos.mpr hε, ?_⟩
  intro index v
  exact receiverDifference_lower_bound (F index) (G index) (hF index) (hDifference index) v

/-! ## The vacuum, and why the gap is measured above it -/

/-- **A VACUUM IS INVISIBLE TO A POSITIVE FORM.**  If `e` returns nothing, adding any amount of it
changes no diagonal reading of that form — the vacuum lies in the radical, so this unnormalized
quadratic reading factors through the quotient by it.  This statement does not cover arbitrary
observables or normalized expectation values.

This is why a mass gap is stated *above the vacuum* rather than on the whole space: on the whole
space the form is never definite once a vacuum exists, and the question is not about the vacuum at
all.  The frame makes the reduction automatic instead of stipulated. -/
theorem theVacuumIsInvisible {F : ReceiverForm V} (hpos : F.IsPositive) {e : V}
    (he : F.B e e = 0) (v : V) (c : ℝ) : F.B (v + c • e) (v + c • e) = F.B v v := by
  have hev : F.B e v = 0 := F.theNullDirectionIsOrthogonal hpos he v
  have hve : F.B v e = 0 := by
    have : F.B v e = F.B e v := by
      simp only [ReceiverForm.B]
      rw [F.selfAdjoint, real_inner_comm]
    rw [this, hev]
  rw [F.theReadingExpands, hve, he]
  ring

/-- **AND A VACUUM REFUSES A GAP ON THE WHOLE SPACE.**  So the reduction is forced, not chosen: any
form with a nonzero vacuum is non-coercive, and the only place a gap can live is the quotient. -/
theorem theVacuumRefusesAGlobalGap {F : ReceiverForm V} {e : V} (hne : e ≠ 0)
    (he : F.B e e = 0) : ¬ F.IsCoercive := by
  intro h
  exact hne (F.theGapForcesDefiniteness h e he)

end Soma.Holonics.Millennium.MassGap
