import ElementaryHolonics.Geometry.CrossRatio
import ElementaryHolonics.Millennium.Chronology
import ElementaryHolonics.Millennium.Paying
import ElementaryHolonics.Millennium.WindingLedger

/-!
# Exact bridges around the Swing

This file settles the primitive identities which previously lived only in prose between the
projective, affine, alternating, and reachability charts.  The projective carrier stays undivided;
the affine theorem is stated as a finite chart law; and the parity-kernel overclaim is rejected by
an exact configuration whose lattice area cannot arise by Swing moves.
-/

namespace Soma.Holonics.Millennium.SwingBridges

open Soma.Holonics
open Soma.Holonics.Millennium.Swing

/-! ## Harmonic and projective faces -/

section Projective

variable {K : Type*} [Field K]

/-- The undivided harmonic equation for the ordering `(a,a';b,d)`. -/
def HarmonicEquation (a conjugate b d : K) : Prop :=
  (swingPair a conjugate b d).num = -(swingPair a conjugate b d).den

/-- The deposited harmonic-conjugate formula satisfies the exact cross-multiplied equation. -/
theorem harmonicConjugate_satisfies {a b d : K} (hden : 2 * a - b - d ≠ 0) :
    HarmonicEquation a (harmonicConjugate b d a) b d := by
  have hden' : -b + (a * 2 - d) ≠ 0 := by
    convert hden using 1 <;> ring
  have hden2 : -b + a * 2 - d ≠ 0 := by
    convert hden using 1 <;> ring
  have hden3 : a * 2 - b - d ≠ 0 := by
    convert hden using 1 <;> ring
  unfold HarmonicEquation swingPair harmonicConjugate
  field_simp [hden, hden2, hden3]
  ring

/-- The harmonic equation determines that conjugate whenever its linear coefficient is nonzero. -/
theorem harmonicConjugate_unique {a conjugate b d : K}
    (hden : 2 * a - b - d ≠ 0) (harmonic : HarmonicEquation a conjugate b d) :
    conjugate = harmonicConjugate b d a := by
  unfold HarmonicEquation swingPair at harmonic
  unfold harmonicConjugate
  apply (eq_div_iff hden).2
  linear_combination harmonic

/-- Inversion transports both exact Swing coordinates by one common projective scale. -/
theorem swingPair_inversion_projectively {a b c d : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    RatioPresentation.ProjectivelyEq
      (swingPair a⁻¹ b⁻¹ c⁻¹ d⁻¹) (swingPair a b c d) := by
  unfold RatioPresentation.ProjectivelyEq swingPair
  field_simp [ha, hb, hc, hd]
  ring

end Projective

/-! ## The finite affine chart and the alternating face -/

section Affine

variable {G : Type*} [AddCommGroup G]

/-- Frozen-board Swing is the unique finite affine point whose anchor displacement is negated. -/
theorem affineSwing_is_the_unique_negated_displacement (a b x : G) :
    x - b = -(a - b) ↔ x = swing b a := by
  constructor
  · intro h
    rw [show x = (x - b) + b by abel, h]
    simp only [swing]
    abel
  · rintro rfl
    exact theSwingNegatesTheDisplacementFromTheAnchor b a

end Affine

/-- The three existing coordinate spellings denote one exact alternating pairing. -/
theorem orientedSpan_eq_paying_eq_winding (a b c : Site) :
    orientedSpan a b c =
      Paying.spanOf (b - a) (c - a) ∧
    Paying.spanOf (b - a) (c - a) =
      WindingLedger.cross (b - a) (c - a) := by
  constructor
  · exact Paying.theOrientedSpanIsThePairingOnItsEdges a b c
  · rfl

/-! ## Parity is necessary and not sufficient for whole-configuration reachability -/

/-- The oriented primitive-cell face of all three addressed bodies. -/
def configurationSpan (c : Config) : ℤ := orientedSpan (c 0) (c 1) (c 2)

/-- A move fixes the span when a body anchors itself and negates it between distinct bodies. -/
theorem step_configurationSpan (c : Config) (i j : Fin 3) :
    configurationSpan (step i j c) =
      if i = j then configurationSpan c else -configurationSpan c := by
  fin_cases i <;> fin_cases j <;>
    simp [configurationSpan, step, swing, orientedSpan, Function.update, Fin.isValue] <;>
    ring_nf

/-- One Swing move preserves the absolute lattice area of the complete configuration. -/
theorem step_preserves_configurationSpan_natAbs (c : Config) (i j : Fin 3) :
    (configurationSpan (step i j c)).natAbs = (configurationSpan c).natAbs := by
  rw [step_configurationSpan]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Every reachable configuration retains the initial primitive-cell area. -/
theorem reachable_preserves_configurationSpan_natAbs {c d : Config} (h : Reachable c d) :
    (configurationSpan d).natAbs = (configurationSpan c).natAbs := by
  induction h with
  | refl => rfl
  | step i j _ ih => rw [step_preserves_configurationSpan_natAbs, ih]

/-- Same per-body parity, but with the primitive cell dilated by three. -/
def parityMatchedExpanded : Config := ![(0, 0), (3, 0), (0, 3)]

/-- The expanded configuration passes the complete per-body parity receiver. -/
theorem parityMatchedExpanded_has_initial_parity (k : Fin 3) :
    parityClass (parityMatchedExpanded k) = parityClass (initial k) := by
  fin_cases k <;> decide

/-- The parity-matched expanded configuration is not reachable: its retained area is nine. -/
theorem parityMatchedExpanded_is_not_reachable : ¬ Reachable initial parityMatchedExpanded := by
  intro h
  have area := reachable_preserves_configurationSpan_natAbs h
  have expandedArea : (configurationSpan parityMatchedExpanded).natAbs = 9 := by decide
  have initialArea : (configurationSpan initial).natAbs = 1 := by decide
  rw [expandedArea, initialArea] at area
  omega

/-- Hence the inductive reachable population is strictly finer than the parity-kernel reading. -/
theorem reachability_is_not_characterized_by_perBodyParity :
    ¬ (∀ d : Config,
      (∀ k, parityClass (d k) = parityClass (initial k)) → Reachable initial d) := by
  intro h
  exact parityMatchedExpanded_is_not_reachable
    (h parityMatchedExpanded parityMatchedExpanded_has_initial_parity)

end Soma.Holonics.Millennium.SwingBridges

section Audit
open Soma.Holonics.Millennium.SwingBridges
#print axioms harmonicConjugate_satisfies
#print axioms harmonicConjugate_unique
#print axioms swingPair_inversion_projectively
#print axioms affineSwing_is_the_unique_negated_displacement
#print axioms orientedSpan_eq_paying_eq_winding
#print axioms reachability_is_not_characterized_by_perBodyParity
end Audit
