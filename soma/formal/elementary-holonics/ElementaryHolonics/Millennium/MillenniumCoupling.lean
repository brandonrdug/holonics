import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import ElementaryHolonics.Millennium.Separation

/-!
# The coupling: six problems, one receiver form and its null cone

Worked as six problems they are six research programmes.  Worked as one object they are one
question asked of six forms, and the theorems below are shared rather than repeated.

| problem | the form | what it asserts |
|---|---|---|
| **Riemann** | the Weil pairing on the explicit formula's test functions | **positive** — a zero off the line is a null direction |
| **Hodge** | the Hodge–Riemann form on primitive classes | **definite** there — a class with no realizer is a null direction |
| **Birch–Swinnerton-Dyer** | the Néron–Tate height on `MW ⊗ ℝ` | the rank is where it is definite; `Ш` is the **collapsed population** |
| **Yang–Mills** | the Hamiltonian above the vacuum | **coercive**, not merely definite — that gap *is* the mass |
| **Navier–Stokes** | dissipation against the nonlinear transfer | **coercive** — blow-up is the gap closing |
| **P vs NP** | — | **separation**: a distinguishing direction exists |

The solved one belongs in the table as evidence rather than as history: Ricci flow's monotone
functionals are second variations, and Perelman's monotonicity is a positivity statement about
exactly this kind of form.  The frame is not proposed here; it is the one that already worked.

## What is actually proved, and why it couples

**The null cone of a positive form is a subspace** (`theNullDirectionIsOrthogonal`, semidefinite
Cauchy–Schwarz).  So *the collapsed population is linear*, and "the form is definite" and "the
receiver family separates" are one sentence rather than two.  That is the join between the
positivity problems and the separation problem.

**The gap is free in finite dimensions** (`theGapIsFreeInFiniteDimensions`): positive plus definite
gives coercive, because the sphere is compact and the reading is continuous.  So a *mass gap is
not a question at all* when the receiver family is finite — it becomes one exactly where
compactness of the sphere fails.

**And the gap refuses a compact form** (`theGapRefusesACompactForm`): if the operator carries the
unit ball to a totally bounded set, a gap forces finite dimension.  Contrapositive: **on an
infinite-dimensional space a compact receiver form has no gap.**  So a mass gap is not a property
a form may happen to have; it is a demand that the form be non-compact, its spectrum not
accumulating at zero.  Those two theorems are a dichotomy: compactness of the *sphere* hands you
the gap, compactness of the *operator* takes it away, and the Yang–Mills and Navier–Stokes rows
of the table live in the space between them.

**Positivity transports** (`theDefinitenessTransports`, `thePositivityTransports`) backward along
any form-preserving injection — this is the coupling engine, and it runs *from* the two rows where
positivity is a theorem in a special case (Castelnuovo positivity of the Rosati involution for
curves; the Hodge index theorem for surfaces) *to* the rows where it is open.  **The gap transports
only along an embedding bounded below** (`theGapTransports`): a quantitative statement needs a
quantitative injection, which is the definite-versus-coercive distinction one level up.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.Millennium.MillenniumCoupling

open Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A **receiver form**: a self-adjoint operator, read as the pairing `⟪Tx, y⟫`.  This is the
shape shared by the Weil pairing, the Hodge–Riemann form, the Néron–Tate height, a Yang–Mills
Hamiltonian, and the Navier–Stokes dissipation — an operator, not a table. -/
structure ReceiverForm (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  T : V →L[ℝ] V
  selfAdjoint : ∀ x y : V, inner ℝ (T x) y = inner ℝ x (T y)

namespace ReceiverForm

variable (F : ReceiverForm V)

/-- The reading. -/
def B (x y : V) : ℝ := inner ℝ (F.T x) y

/-- The **null cone**: where traversal returns nothing. -/
def nullCone : Set V := {v | F.B v v = 0}

/-- **DEFINITE**: no nonzero construction self-pairs to nothing. -/
def IsDefinite : Prop := ∀ v : V, F.B v v = 0 → v = 0

/-- **POSITIVE**: the form never returns a negative reading. -/
def IsPositive : Prop := ∀ v : V, 0 ≤ F.B v v

/-- **COERCIVE — there is a gap.**  Strictly stronger than definite, and the difference between
the two is the entire content of a mass gap. -/
def IsCoercive : Prop := ∃ Δ : ℝ, 0 < Δ ∧ ∀ v : V, Δ * ‖v‖ ^ 2 ≤ F.B v v

theorem theGapForcesDefiniteness (h : F.IsCoercive) : F.IsDefinite := by
  obtain ⟨Δ, hΔ, hB⟩ := h
  intro v hv
  have h1 : Δ * ‖v‖ ^ 2 ≤ 0 := hv ▸ hB v
  have hsq : ‖v‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right h1 hΔ
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp this

theorem theGapForcesPositivity (h : F.IsCoercive) : F.IsPositive := by
  obtain ⟨Δ, hΔ, hB⟩ := h
  exact fun v => le_trans (by positivity) (hB v)

/-- The diagonal reading is continuous — an operator, not a table. -/
theorem theReadingIsContinuous : Continuous fun v : V => F.B v v := by
  unfold B
  fun_prop

/-- The form is homogeneous of degree two. -/
theorem theReadingIsQuadratic (c : ℝ) (v : V) : F.B (c • v) (c • v) = c ^ 2 * F.B v v := by
  simp [B, inner_smul_left, inner_smul_right, map_smul]
  ring

/-- **THE GAP IS FREE IN FINITE DIMENSIONS.**  A positive definite receiver form on a
finite-dimensional space is automatically coercive: the unit sphere is compact, the reading is
continuous, so it attains a minimum, and definiteness makes that minimum strictly positive.

**So a mass gap is not a question at all when the receiver family is finite.**  It becomes a
question exactly when compactness of the sphere fails — which is the corpus's own division
between the finite strata, where the answer is a table, and the generic stratum, where it is
not. -/
theorem theGapIsFreeInFiniteDimensions [FiniteDimensional ℝ V]
    (hpos : F.IsPositive) (hdef : F.IsDefinite) : F.IsCoercive := by
  rcases subsingleton_or_nontrivial V with hs | hn
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := Subsingleton.elim v 0
    simp [hv, B]
  · have hsph : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : V) 1).Nonempty := by
      obtain ⟨w, hw⟩ := exists_ne (0 : V)
      exact ⟨‖w‖⁻¹ • w, by simp [norm_smul, norm_ne_zero_iff.mpr hw]⟩
    obtain ⟨u, hu, hmin⟩ :=
      hsph.exists_isMinOn hne (F.theReadingIsContinuous).continuousOn
    have hune : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    have hΔ : 0 < F.B u u := lt_of_le_of_ne (hpos u) (fun h => hune (hdef u h.symm))
    refine ⟨F.B u u, hΔ, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [B]
    · set w : V := ‖v‖⁻¹ • v with hw
      have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hws : w ∈ Metric.sphere (0 : V) 1 := by simp [hw, norm_smul, hnv]
      have hbw : F.B u u ≤ F.B w w := hmin hws
      have hvw : v = ‖v‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hnv, one_smul]
      have hq : F.B v v = ‖v‖ ^ 2 * F.B w w := by
        have hqq : F.B (‖v‖ • w) (‖v‖ • w) = ‖v‖ ^ 2 * F.B w w := F.theReadingIsQuadratic _ _
        rwa [← hvw] at hqq
      rw [hq]
      nlinarith [sq_nonneg ‖v‖, hbw]

/-- A gap bounds the operator below. -/
theorem theGapBoundsTheOperatorBelow {Δ : ℝ} (hΔ : 0 < Δ)
    (hB : ∀ v : V, Δ * ‖v‖ ^ 2 ≤ F.B v v) (v : V) : Δ * ‖v‖ ≤ ‖F.T v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hcs : F.B v v ≤ ‖F.T v‖ * ‖v‖ := real_inner_le_norm _ _
    have h := hB v
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    nlinarith [h, hcs, hn]

/-- **AND THE GAP REFUSES A COMPACT FORM.**  If the operator carries the closed unit ball to a
totally bounded set — a *compact* form — then a gap forces the space to be finite-dimensional.

Contrapositive, which is the physical statement: **on an infinite-dimensional space a compact
receiver form has no gap.**  So a mass gap is not a property the form may or may not happen to
have; it is a demand that the form be **non-compact**, and its spectrum therefore not accumulate
at zero.  Together with the finite-dimensional theorem above this is a dichotomy: compactness of
the sphere hands you the gap, compactness of the *operator* takes it away. -/
theorem theGapRefusesACompactForm [CompleteSpace V]
    (hcpt : TotallyBounded (F.T '' Metric.closedBall (0 : V) 1))
    (hco : F.IsCoercive) : FiniteDimensional ℝ V := by
  obtain ⟨Δ, hΔ, hB⟩ := hco
  have hlow : ∀ v : V, Δ * ‖v‖ ≤ ‖F.T v‖ := F.theGapBoundsTheOperatorBelow hΔ hB
  have hanti : AntilipschitzWith (Real.toNNReal Δ⁻¹) F.T := by
    refine AntilipschitzWith.of_le_mul_dist (fun x y => ?_)
    have h := hlow (x - y)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ hΔ]
    linarith [h]
  have hui : IsUniformInducing F.T :=
    hanti.isUniformInducing (F.T : V →L[ℝ] V).uniformContinuous
  have htb : TotallyBounded (Metric.closedBall (0 : V) 1) :=
    (totallyBounded_image_iff hui).mp hcpt
  have hcompact : IsCompact (Metric.closedBall (0 : V) 1) :=
    htb.isCompact_of_isClosed Metric.isClosed_closedBall
  exact FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos hcompact

/-! ## The antisymmetric part is invisible to the diagonal reading -/

/-- **AN ANTISYMMETRIC OPERATOR RETURNS NOTHING ON THE DIAGONAL.**  `⟪Tv,v⟫ = −⟪v,Tv⟫ = −⟪Tv,v⟫`,
so it is zero — no computation, just the two symmetries meeting.

This is the phase-object theorem in operator form: **a structure living entirely in the
antisymmetric part is invisible to every magnitude reading**, however many of them are taken.  It
is also, exactly, why the Navier–Stokes nonlinearity conserves energy: `⟪(u·∇)u, u⟫ = 0` is this
identity, not a computation about fluids.  The consequence for the frame is sharp — **the energy
receiver cannot see the term that would break regularity**, so no amount of energy estimation
closes that row; a finer receiver is required. -/
theorem theAntisymmetricPartIsInvisible (T : V →L[ℝ] V)
    (hanti : ∀ x y : V, inner ℝ (T x) y = -inner ℝ x (T y)) (v : V) :
    inner ℝ (T v) v = (0:ℝ) := by
  have h1 : inner ℝ (T v) v = -inner ℝ v (T v) := hanti v v
  have h2 : (inner ℝ v (T v) : ℝ) = inner ℝ (T v) v := real_inner_comm _ _
  linarith [h1, h2]

/-! ## Perturbation: when a gap survives, and when it closes -/

/-- Forms add. -/
instance : Add (ReceiverForm V) where
  add F G := ⟨F.T + G.T, fun x y => by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, inner_add_left,
      inner_add_right, F.selfAdjoint, G.selfAdjoint]⟩

/-- And negate. -/
instance : Neg (ReceiverForm V) where
  neg F := ⟨-F.T, fun x y => by
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply, inner_neg_left,
      inner_neg_right, F.selfAdjoint]⟩

@[simp] theorem theSumReading (F G : ReceiverForm V) (x y : V) :
    (F + G).B x y = F.B x y + G.B x y := by
  show inner ℝ ((F.T + G.T) x) y = _
  rw [ContinuousLinearMap.add_apply, inner_add_left]
  rfl

@[simp] theorem theNegReading (F : ReceiverForm V) (x y : V) : (-F).B x y = -F.B x y := by
  show inner ℝ ((-F.T) x) y = _
  rw [ContinuousLinearMap.neg_apply, inner_neg_left]
  rfl

/-- So a receiver form is decided entirely by the symmetric part of its operator: adding any
antisymmetric operator changes no reading on the diagonal, hence changes neither positivity,
definiteness, nor the gap. -/
theorem theGapIgnoresTheAntisymmetricPart (F : ReceiverForm V) (G : V →L[ℝ] V)
    (hanti : ∀ x y : V, inner ℝ (G x) y = -inner ℝ x (G y)) (v : V) :
    inner ℝ ((F.T + G) v) v = F.B v v := by
  rw [ContinuousLinearMap.add_apply, inner_add_left]
  have hzero : inner ℝ (G v) v = 0 := theAntisymmetricPartIsInvisible G hanti v
  rw [hzero, add_zero]
  rfl

/-- **A GAP SURVIVES ANY PERTURBATION SMALLER THAN ITSELF.**  This is the mechanism under both the
mass gap and global regularity: the free part supplies `Δ‖v‖²`, the interaction is bounded by
`ε‖v‖²`, and the gap persists exactly while `ε < Δ`.  Nothing about the perturbation matters
except its size against the gap. -/
theorem theGapSurvivesASmallPerturbation (F G : ReceiverForm V) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hF : ∀ v : V, Δ * ‖v‖ ^ 2 ≤ F.B v v)
    (hG : ∀ v : V, |G.B v v| ≤ ε * ‖v‖ ^ 2) (hε : ε < Δ) : (F + G).IsCoercive := by
  refine ⟨Δ - ε, by linarith, fun v => ?_⟩
  have h1 := hF v
  have h3 : -(ε * ‖v‖ ^ 2) ≤ G.B v v := neg_le_of_abs_le (hG v)
  rw [theSumReading]
  nlinarith [h1, h3]

/-- **AND A PERTURBATION AS LARGE AS THE GAP CLOSES IT.**  `F + (−F)` is the zero form: positive,
definite nowhere, and with no gap on any nontrivial space.  So `ε < Δ` is not an artefact of the
proof — at `ε = Δ` the conclusion is false, and that boundary is where regularity is decided. -/
theorem theGapClosesAtEquality (F : ReceiverForm V) [Nontrivial V] :
    ¬ (F + (-F)).IsCoercive := by
  intro h
  obtain ⟨Δ, hΔ, hB⟩ := h
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have hz : (F + (-F)).B w w = 0 := by rw [theSumReading, theNegReading]; ring
  have hbw := hB w
  rw [hz] at hbw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  nlinarith [hbw, mul_pos hΔ (pow_pos hn 2)]

/-! ## The collapsed population of a positive form is a subspace -/

/-- The polarisation expansion. -/
theorem theReadingExpands (v w : V) (t : ℝ) :
    F.B (v + t • w) (v + t • w) = F.B v v + 2 * t * F.B v w + t ^ 2 * F.B w w := by
  have hsym : F.B w v = F.B v w := by
    simp only [B]
    rw [F.selfAdjoint, real_inner_comm]
  simp only [B, map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at *
  rw [hsym]
  ring

/-- **A NULL DIRECTION OF A POSITIVE FORM IS ORTHOGONAL TO EVERYTHING.**  Semidefinite
Cauchy–Schwarz: if the form returns nothing on `v`, it returns nothing on every pairing with `v`.

So **the null cone of a positive form is a subspace — the collapsed population is linear**, and
that is why "the form is definite" and "the receiver family separates" are the same sentence
rather than two. -/
theorem theNullDirectionIsOrthogonal (hpos : F.IsPositive) {v : V} (hv : F.B v v = 0) (w : V) :
    F.B v w = 0 := by
  by_contra hne
  have hall : ∀ t : ℝ, 0 ≤ 2 * t * F.B v w + t ^ 2 * F.B w w := by
    intro t
    have := hpos (v + t • w)
    rw [F.theReadingExpands, hv] at this
    linarith
  set r : ℝ := F.B v w with hr
  set q : ℝ := F.B w w with hq
  have hbw : 0 ≤ q := hpos w
  have hden : 0 < q + 1 := by linarith
  have h1 := hall (-(r / (q + 1)))
  have h2 : 2 * (-(r / (q + 1))) * r + (-(r / (q + 1))) ^ 2 * q
      = r ^ 2 * (-q - 2) / (q + 1) ^ 2 := by field_simp; ring
  rw [h2] at h1
  have h3 : 0 < r ^ 2 := by positivity
  have h4 : r ^ 2 * (-q - 2) < 0 := by nlinarith [h3, hbw]
  have h5 : (0:ℝ) < (q + 1) ^ 2 := by positivity
  rw [le_div_iff₀ h5] at h1
  linarith

/-! ## The bridge to separation: the null cone IS the collapsed population -/

/-- The receiver family a form induces: one reading per pairing partner. -/
def readings : Separation.ReceiverFamily V ℝ := {g | ∃ w : V, g = fun v => F.B v w}

/-- **THE NULL CONE OF A POSITIVE FORM IS EXACTLY THE COLLAPSED POPULATION OF ITS READINGS.**
`B v v = 0` and *"no reading in the family tells `v` from `0`"* are the same statement.  This is
the join between the positivity rows of the table and the separation row: a definite form is a
separating family, and a null direction is a collapsed pair. -/
theorem theNullConeIsTheCollapsedPopulation (hpos : F.IsPositive) (v : V) :
    F.B v v = 0 ↔ Separation.collapseOf F.readings v 0 := by
  constructor
  · intro hv g hg
    obtain ⟨w, rfl⟩ := hg
    simp only [B, map_zero, inner_zero_left]
    exact F.theNullDirectionIsOrthogonal hpos hv w
  · intro h
    have := h (fun x => F.B x v) ⟨v, rfl⟩
    simpa [B] using this

/-- **SO DEFINITENESS AND SEPARATION ARE ONE PROPERTY.** -/
theorem theDefinitenessIsSeparation (hpos : F.IsPositive) :
    F.IsDefinite ↔ ∀ v : V, Separation.collapseOf F.readings v 0 → v = 0 := by
  constructor
  · exact fun h v hc => h v ((F.theNullConeIsTheCollapsedPopulation hpos v).mpr hc)
  · exact fun h v hv => h v ((F.theNullConeIsTheCollapsedPopulation hpos v).mp hv)

/-- And a null direction is certified by a *separator's absence*, which is the form the corpus
already carries: off-collapse is exactly carrying a distinguishing reading. -/
theorem theNullDirectionCarriesNoSeparator (hpos : F.IsPositive) {v : V} (hv : F.B v v = 0) :
    ¬ ∃ g ∈ F.readings, g v ≠ g 0 := by
  intro hc
  exact ((Separation.theCollapsedPopulationHasASeparator F.readings).2 v 0).mpr hc
    ((F.theNullConeIsTheCollapsedPopulation hpos v).mp hv)

/-! ## Transport: one positivity proof carries to every instance that maps into it -/

section Transport
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **DEFINITENESS TRANSPORTS BACKWARD ALONG A FORM-PRESERVING INJECTION.**  This is the coupling
engine: a positivity theorem proved at *one* receiver form is a positivity theorem at every form
that embeds into it preserving the reading. -/
theorem theDefinitenessTransports (F : ReceiverForm V) (G : ReceiverForm W) (f : W →L[ℝ] V)
    (hpres : ∀ x y : W, F.B (f x) (f y) = G.B x y)
    (hinj : ∀ x : W, f x = 0 → x = 0) (h : F.IsDefinite) : G.IsDefinite := by
  intro v hv
  exact hinj v (h (f v) (by rw [hpres]; exact hv))

/-- Positivity transports the same way. -/
theorem thePositivityTransports (F : ReceiverForm V) (G : ReceiverForm W) (f : W →L[ℝ] V)
    (hpres : ∀ x y : W, F.B (f x) (f y) = G.B x y) (h : F.IsPositive) : G.IsPositive := by
  intro v
  rw [← hpres]
  exact h (f v)

/-- **AND THE GAP TRANSPORTS ONLY IF THE EMBEDDING IS BOUNDED BELOW.**  A gap is a *quantitative*
statement, so carrying it needs a quantitative injection — injectivity alone is not enough.  That
distinction is the same one as definite-versus-coercive, one level up. -/
theorem theGapTransports (F : ReceiverForm V) (G : ReceiverForm W) (f : W →L[ℝ] V) {c : ℝ}
    (hc : 0 < c) (hbelow : ∀ x : W, c * ‖x‖ ≤ ‖f x‖)
    (hpres : ∀ x y : W, F.B (f x) (f y) = G.B x y) (h : F.IsCoercive) : G.IsCoercive := by
  obtain ⟨Δ, hΔ, hB⟩ := h
  refine ⟨Δ * c ^ 2, by positivity, fun v => ?_⟩
  have h1 : Δ * ‖f v‖ ^ 2 ≤ F.B (f v) (f v) := hB (f v)
  have h2 : c * ‖v‖ ≤ ‖f v‖ := hbelow v
  have h3 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
  have h4 : (c * ‖v‖) ^ 2 ≤ ‖f v‖ ^ 2 := by
    have : 0 ≤ c * ‖v‖ := mul_nonneg hc.le h3
    nlinarith [h2, this, norm_nonneg (f v)]
  rw [← hpres]
  calc Δ * c ^ 2 * ‖v‖ ^ 2 = Δ * (c * ‖v‖) ^ 2 := by ring
    _ ≤ Δ * ‖f v‖ ^ 2 := by nlinarith [h4, hΔ]
    _ ≤ F.B (f v) (f v) := h1

end Transport

end ReceiverForm

end Soma.Holonics.Millennium.MillenniumCoupling
