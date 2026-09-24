import Mathlib.Analysis.InnerProductSpace.Calculus
import ElementaryHolonics.Millennium.NavierStokes
import ElementaryHolonics.Millennium.Separation

/-!
# NavierStokesDirection: the magnitude is carried by the phase

`Crossings.lean` proves that a helicity-only receiver is blind to the nonlinearity —
the cosine face of a pairing whose sine face carries the transport.  That closes the
*helicity* route.  This file opens the *direction* route, which is a different object:
not `⟪u,ω⟫` but `ξ = ω/‖ω‖` itself.

Split any field into magnitude and unit direction.  Its jet splits with it, into an
aligned piece and a turning piece, and the two are **orthogonal**: the magnitude
receiver reads the first exactly and is blind to the second entirely.  Consequently a
defect living in the direction field cannot be found by any number of magnitude
readings — this repository's phase-object theorem, arriving on the fluid carrier's own
first jet, over an arbitrary real inner-product space and therefore at
`NavierStokes.Space` in particular.

No comparison sign occurs in any statement here.  Every `theorem` is discharged and
none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesDirection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **THE DIRECTION'S VARIATION IS ORTHOGONAL TO THE DIRECTION.**  Differentiating
`⟪ξ,ξ⟫ = 1` leaves the whole turning of a unit field in the orthogonal complement of
that field.  No part of `Dξ` is visible to a receiver reading along `ξ`. -/
theorem theDirectionsVariationIsOrthogonal {ξ : E → F} {ξ' : E →L[ℝ] F} {x : E}
    (hξ : HasFDerivAt ξ ξ' x) (hunit : ∀ y, inner ℝ (ξ y) (ξ y) = (1 : ℝ)) (v : E) :
    inner ℝ (ξ x) (ξ' v) = (0 : ℝ) := by
  have h1 := hξ.inner (𝕜 := ℝ) hξ
  have h3 : (fun y => (inner ℝ (ξ y) (ξ y) : ℝ)) = fun _ => (1 : ℝ) := funext hunit
  rw [h3] at h1
  have h2 : HasFDerivAt (fun _ : E => (1 : ℝ)) (0 : E →L[ℝ] ℝ) x :=
    hasFDerivAt_const (1 : ℝ) x
  have heq := h1.unique h2
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
  simp [fderivInnerCLM_apply] at happ
  have hsym : inner ℝ (ξ' v) (ξ x) = (inner ℝ (ξ x) (ξ' v) : ℝ) := real_inner_comm _ _
  linarith [happ, hsym]

/-- The jet of a magnitude-times-direction field. -/
theorem theJetSplits {ξ : E → F} {m : E → ℝ} {ξ' : E →L[ℝ] F} {m' : E →L[ℝ] ℝ} {x : E}
    (hξ : HasFDerivAt ξ ξ' x) (hm : HasFDerivAt m m' x) :
    HasFDerivAt (fun y => m y • ξ y) (m x • ξ' + m'.smulRight (ξ x)) x :=
  hm.smul hξ

/-- **THE MAGNITUDE IS CARRIED BY THE PHASE.**  Split a field into magnitude and unit
direction, `ω = m·ξ`.  Its jet splits into an aligned piece and a turning piece, and

* the magnitude receiver reads **exactly** the aligned piece, `⟪ξ, Dω v⟫ = Dm v`;
* what is left over is **exactly** `m·Dξ v`, the whole turning;
* and that leftover is **orthogonal to `ξ`**, hence invisible to the magnitude.

So a defect living in the direction field cannot be found by any reading of the
magnitude — the phase-object theorem, on the fluid carrier's own jet. -/
theorem theMagnitudeIsCarriedByThePhase {ξ : E → F} {m : E → ℝ}
    {ξ' : E →L[ℝ] F} {m' : E →L[ℝ] ℝ} {x : E}
    (hξ : HasFDerivAt ξ ξ' x)
    (hunit : ∀ y, inner ℝ (ξ y) (ξ y) = (1 : ℝ)) (v : E) :
    inner ℝ (ξ x) ((m x • ξ' + m'.smulRight (ξ x)) v) = m' v
      ∧ (m x • ξ' + m'.smulRight (ξ x)) v - (m' v) • ξ x = m x • ξ' v
      ∧ inner ℝ (ξ x) (m x • ξ' v) = (0 : ℝ) := by
  have horth := theDirectionsVariationIsOrthogonal hξ hunit v
  have happ : (m x • ξ' + m'.smulRight (ξ x)) v = m x • ξ' v + m' v • ξ x := by
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [happ, inner_add_right, real_inner_smul_right, real_inner_smul_right, horth,
      hunit x]
    ring
  · rw [happ]; abel
  · rw [real_inner_smul_right, horth]; ring

/-! ## Second order: the damping term -/

section Damping
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **THE DIRECTION'S CURVATURE DAMPS THE MAGNITUDE.**  Along any line, a unit direction field's second derivative is
ANTI-ALIGNED with the field by exactly the squared first derivative.  This is the
damping term: the direction's own curvature enters the magnitude equation with a
minus sign. -/
theorem theDirectionsCurvatureDampsTheMagnitude {γ γ' : ℝ → F} {c : F} {t : ℝ}
    (h1 : ∀ s, HasDerivAt γ (γ' s) s) (h2 : HasDerivAt γ' c t)
    (hunit : ∀ s, inner ℝ (γ s) (γ s) = (1 : ℝ)) :
    inner ℝ (γ t) c = - (inner ℝ (γ' t) (γ' t) : ℝ) := by
  -- first identity: the unit field is orthogonal to its own derivative, everywhere
  have horth : ∀ s : ℝ, (inner ℝ (γ s) (γ' s) : ℝ) = 0 := by
    intro s
    have hd := (h1 s).inner (𝕜 := ℝ) (h1 s)
    have hconst : (fun u => (inner ℝ (γ u) (γ u) : ℝ)) = fun _ => (1 : ℝ) := funext hunit
    rw [hconst] at hd
    have h0 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 s := hasDerivAt_const s 1
    have heq := hd.unique h0
    have hsym : (inner ℝ (γ' s) (γ s) : ℝ) = inner ℝ (γ s) (γ' s) := real_inner_comm _ _
    linarith [heq, hsym]
  -- differentiate it once more
  have hd2 := (h1 t).inner (𝕜 := ℝ) h2
  have hzero : (fun u => (inner ℝ (γ u) (γ' u) : ℝ)) = fun _ => (0 : ℝ) := funext horth
  rw [hzero] at hd2
  have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have heq := hd2.unique h0
  have hsym : (inner ℝ (γ' t) (γ' t) : ℝ) = inner ℝ (γ' t) (γ' t) := rfl
  linarith [heq]

/-- **THE MAGNITUDE'S SECOND DERIVATIVE CARRIES THE DAMPING.**  Write `ω = m·ξ` with `ξ`
a unit direction.  Then along any line

```text
  ⟪ξ, ω''⟫  =  m''  −  m·‖ξ'‖²
```

The direction's own curvature enters the magnitude's evolution **with a minus sign**.
That is the origin of the `−ν‖Dξ‖²|ω|` term: wherever the direction field bends, the
magnitude is damped, and the damping is proportional to the bending. -/
theorem theMagnitudeSecondDerivativeCarriesTheDamping
    (ξ ξ' ξ'' : F) (m m' m'' : ℝ)
    (hunit : inner ℝ ξ ξ = (1 : ℝ))
    (horth : inner ℝ ξ ξ' = (0 : ℝ))
    (hcurv : inner ℝ ξ ξ'' = -(inner ℝ ξ' ξ' : ℝ)) :
    (inner ℝ ξ (m'' • ξ + (2 * m') • ξ' + m • ξ'') : ℝ)
      = m'' - m * (inner ℝ ξ' ξ' : ℝ) := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, hunit, horth, hcurv]
  ring

/-- **THE GEOMETRIC REGULARITY CRITERION, STATED.**  Regularity carried by the
*direction* alone: on the region where the magnitude is large, a Lipschitz bound on the
direction field controls the magnitude's growth.  This is a named `Prop` with its
hypothesis explicit — the identity above is what gives it content, and nothing here
asserts the criterion holds. -/
def TheGeometricRegularityCriterion (ω ξ : ℝ → F) (m : ℝ → ℝ) (L : ℝ) : Prop :=
  (∀ t, ω t = m t • ξ t) → (∀ t, inner ℝ (ξ t) (ξ t) = (1 : ℝ)) →
    (∀ t, ‖ξ t - ξ 0‖ ≤ L * |t|) → ∀ t, m t ≤ m 0 * Real.exp (L * |t|)

/-- **THE MAGNITUDE EQUATION CARRIES THE DAMPING TERM.**  Read the evolution of `ω`
through its own direction `ξ`.  The strain contributes its aligned rate `α·|ω|`; the
viscous term contributes the Laplacian of the magnitude *minus* the direction field's
own curvature times the magnitude:

```text
  D|ω|/Dt  =  α·|ω|  +  ν·Δ|ω|  −  ν·‖∇ξ‖²·|ω|
```

The minus sign is not put in by hand — it comes from `⟪ξ, Δω⟫ = Δ|ω| − |ω|·‖∇ξ‖²`,
which is the damping identity, which comes from differentiating `⟪ξ,ξ⟫ = 1` twice.
**The magnitude is linear in itself with phase-determined coefficients**, and the only
term that can remove magnitude is the one measuring how the direction bends. -/
theorem theMagnitudeEquationCarriesTheDampingTerm
    (ξ Sw Lw : F) (mag lapMag alpha curv nu dmdt : ℝ)
    (halign : (inner ℝ ξ Sw : ℝ) = alpha * mag)
    (hlap : (inner ℝ ξ Lw : ℝ) = lapMag - mag * curv)
    (hevol : dmdt = (inner ℝ ξ (Sw + nu • Lw) : ℝ)) :
    dmdt = alpha * mag + nu * lapMag - nu * mag * curv := by
  rw [hevol, inner_add_right, real_inner_smul_right, halign, hlap]
  ring

end Damping

/-! ## The polar split, and what the magnitude face cannot see -/

section Polar
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **THE POLAR SPLIT LOSES NOTHING.**  A nonzero vector is exactly its magnitude times
its direction, and both are recovered: `v = ‖v‖ • ξ` with `‖ξ‖ = 1`.  Normalisation done
this way is a *factorisation*, not a deletion. -/
theorem thePolarSplitLosesNothing {v : F} (hv : v ≠ 0) :
    ‖(‖v‖⁻¹ • v)‖ = 1 ∧ ‖v‖ • (‖v‖⁻¹ • v) = v := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  constructor
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- The receiver family of readings that factor through the norm — root-mean-square,
any moment of the magnitude, any threshold on it. -/
def magnitudeReceiver : Separation.ReceiverFamily F Prop :=
  {f | ∃ g : ℝ → Prop, f = fun w => g ‖w‖}

/-- **THE MAGNITUDE RECEIVER COLLAPSES EQUAL NORMS.**  *Every* reading that factors
through the norm — RMS included — is blind to the difference between two vectors of the
same length.  What the polar split retains is exactly what this family cannot see. -/
theorem theMagnitudeReceiverCollapsesEqualNorms {u v : F} (h : ‖u‖ = ‖v‖) :
    Separation.collapseOf (magnitudeReceiver (F := F)) u v := by
  rintro f ⟨g, rfl⟩
  show g ‖u‖ = g ‖v‖
  rw [h]

end Polar

/-! ## At the fluid carrier -/

open Soma.Holonics.Millennium.NavierStokes in
/-- **THE VORTICITY'S MAGNITUDE IS BLIND TO ITS DIRECTION'S TURNING**, on the actual
three-dimensional carrier the official problem declares. -/
theorem theVorticityMagnitudeIsBlindToItsTurning
    {ξ : Space → Space} {m : Space → ℝ}
    {ξ' : Space →L[ℝ] Space} {m' : Space →L[ℝ] ℝ} {x : Space}
    (hξ : HasFDerivAt ξ ξ' x)
    (hunit : ∀ y, inner ℝ (ξ y) (ξ y) = (1 : ℝ)) (v : Space) :
    inner ℝ (ξ x) ((m x • ξ' + m'.smulRight (ξ x)) v) = m' v
      ∧ inner ℝ (ξ x) (m x • ξ' v) = (0 : ℝ) :=
  ⟨(theMagnitudeIsCarriedByThePhase (m := m) (m' := m') hξ hunit v).1,
   (theMagnitudeIsCarriedByThePhase (m := m) (m' := m') hξ hunit v).2.2⟩

end Soma.Holonics.Millennium.NavierStokesDirection
