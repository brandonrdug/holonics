import ElementaryHolonics.Millennium.Swing
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Pantographic swings and addressed derivative jets

[proved-standard] A mechanical pantograph with anchor `O`, tracer `P`, output `Q`, and constant
scale `s` realizes the affine law `Q - O = s • (P - O)`.  This file packages that law without
forgetting the anchor.  Scale `-1` is exactly the existing frozen-board holonic swing, and serial
pantographic passages multiply their scales.

[proved-derived; formal-checked] The pantograph functional-differential recurrence has a triangular
scale ledger.  If the successive jet coefficients obey

`j_(n+1) = gain * scale^n * j_n`,

then `j_n = gain^n * scale^(Nat.choose n 2) * j_0`.  Analytically, this is the coefficient law
obtained by repeatedly differentiating `y'(t) = gain * y(scale * t)` when the required derivatives
exist.  The present theorem proves the algebraic recurrence, not analytic existence.

[definition] Higher kinematic jets retain an ordered word of addressed time axes.  Their dimension
receiver forgets the order and records only one inverse factor for each incidence.  Force and
length jets remain different typed carriers: after a declared constant-mass dynamical passage,
the derivative dimensions satisfy `D^r F = mass + D^(r+2) position`.  Thus yank, tug, snatch, and
shake are force-current readings corresponding respectively to jerk, snap, crackle, and pop; they
do not redefine those kinematic jets.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicPantographicSwingJets

open Soma.Holonics.Millennium

/-! ## The affine pantograph and the swing -/

section AffinePantograph

variable {Scalar Carrier : Type*}
variable [CommRing Scalar] [AddCommGroup Carrier] [Module Scalar Carrier]

/-- [definition] Affine dilation of one input occurrence about a retained anchor. -/
def pantographicPoint (anchor : Carrier) (scale : Scalar) (input : Carrier) : Carrier :=
  anchor + scale • (input - anchor)

/-- [proved-derived; formal-checked] The output displacement is the scaled input displacement. -/
theorem pantographicPoint_sub_anchor
    (anchor : Carrier) (scale : Scalar) (input : Carrier) :
    pantographicPoint anchor scale input - anchor = scale • (input - anchor) := by
  simp [pantographicPoint]

/-- [proved-derived; formal-checked] Serial pantographic passages about one anchor multiply their
scales.  This is the exact local-to-global composition law for a constant-scale chain. -/
theorem pantographicPoint_comp
    (anchor : Carrier) (outerScale innerScale : Scalar) (input : Carrier) :
    pantographicPoint anchor outerScale (pantographicPoint anchor innerScale input) =
      pantographicPoint anchor (outerScale * innerScale) input := by
  rw [pantographicPoint, pantographicPoint_sub_anchor]
  simp [pantographicPoint, mul_smul]

/-- [proved-derived; formal-checked] The existing frozen-board swing is precisely the pantographic
scale `-1`: the displacement crosses the anchor and reverses orientation. -/
theorem pantographicPoint_neg_one_eq_swing (anchor input : Carrier) :
    pantographicPoint anchor (-1 : Scalar) input = Swing.swing anchor input := by
  simp [pantographicPoint, Swing.swing]
  abel

end AffinePantograph

/-! ## The triangular scale accumulated by the pantograph equation -/

section PantographRecurrence

variable {Coefficient : Type*} [CommMonoid Coefficient]

/-- [definition] The coefficient accumulated after `order` pantographic differentiations. -/
def pantographicJetCoefficient (gain scale : Coefficient) (order : ℕ) : Coefficient :=
  gain ^ order * scale ^ Nat.choose order 2

/-- [proved-standard; formal-checked] The triangular exponent grows by the current order. -/
theorem chooseTwo_succ (order : ℕ) :
    Nat.choose (order + 1) 2 = order + Nat.choose order 2 := by
  rw [show 2 = Nat.succ 1 by rfl, Nat.choose_succ_succ]
  simp

/-- [proved-derived; formal-checked] One further derivative contributes one gain and the current
scale power. -/
theorem pantographicJetCoefficient_succ
    (gain scale : Coefficient) (order : ℕ) :
    pantographicJetCoefficient gain scale (order + 1) =
      gain * scale ^ order * pantographicJetCoefficient gain scale order := by
  rw [pantographicJetCoefficient, pantographicJetCoefficient, chooseTwo_succ,
    pow_succ, pow_add]
  ac_rfl

/-- [proved-derived; formal-checked] Any coefficient jet obeying the pantographic recurrence has
the closed triangular-scale form. -/
theorem pantographicJet_closedForm
    (gain scale seed : Coefficient) (jet : ℕ → Coefficient)
    (initial : jet 0 = seed)
    (successor : ∀ order, jet (order + 1) = gain * scale ^ order * jet order) :
    ∀ order, jet order = pantographicJetCoefficient gain scale order * seed := by
  intro order
  induction order with
  | zero => simpa [pantographicJetCoefficient] using initial
  | succ order inductionHypothesis =>
      rw [successor order, inductionHypothesis, pantographicJetCoefficient_succ]
      ac_rfl

end PantographRecurrence

/-! ## Ordered time-axis words and the force-current rebase -/

inductive JetQuantityAxis (TimeAxis : Type*) where
  | length
  | mass
  | time : TimeAxis → JetQuantityAxis TimeAxis
  deriving DecidableEq

/-- [definition] A physical dimension before the receiver identifies time-axis incidences. -/
abbrev JetDimension (TimeAxis : Type*) := JetQuantityAxis TimeAxis → ℤ

/-- [definition] One positive basis incidence of a quantity axis. -/
def jetAxisDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (axis : JetQuantityAxis TimeAxis) : JetDimension TimeAxis :=
  fun candidate => if candidate = axis then 1 else 0

/-- [definition] The ordered causal word crossed by an iterated derivative. -/
abbrev TimeAxisWord (TimeAxis : Type*) := List TimeAxis

/-- [definition] The dimension receiver of a time-axis word.  It sums incidences and therefore
forgets their order; the source `List` retains that chronology in the reconstruction fibre. -/
def timeWordDimension {TimeAxis : Type*} [DecidableEq TimeAxis] :
    TimeAxisWord TimeAxis → JetDimension TimeAxis
  | [] => 0
  | axis :: remainder =>
      jetAxisDimension (.time axis) + timeWordDimension remainder

/-- [proved-derived; formal-checked] Concatenating derivative histories adds their dimensional
time incidences. -/
theorem timeWordDimension_append
    {TimeAxis : Type*} [DecidableEq TimeAxis]
    (left right : TimeAxisWord TimeAxis) :
    timeWordDimension (left ++ right) = timeWordDimension left + timeWordDimension right := by
  induction left with
  | nil => simp [timeWordDimension]
  | cons axis remainder inductionHypothesis =>
      simp [timeWordDimension, inductionHypothesis, add_assoc]

/-- [definition] Position differentiated along one ordered word: one length incidence and one
inverse time incidence for every crossed axis. -/
def lengthJetDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (word : TimeAxisWord TimeAxis) : JetDimension TimeAxis :=
  jetAxisDimension .length - timeWordDimension word

/-- [definition] Force is the constant-mass image of a two-axis acceleration occurrence. -/
def forceDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (sourceTime receiverTime : TimeAxis) : JetDimension TimeAxis :=
  jetAxisDimension .mass + lengthJetDimension [sourceTime, receiverTime]

/-- [definition] Further derivatives of force retain their own ordered time-axis tail. -/
def forceDerivativeDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (sourceTime receiverTime : TimeAxis) (tail : TimeAxisWord TimeAxis) :
    JetDimension TimeAxis :=
  forceDimension sourceTime receiverTime - timeWordDimension tail

/-- [proved-derived; formal-checked] The constant-mass dynamical passage commutes with every
ordered derivative tail at the dimension receiver: `D^r F` has mass plus the dimension of the
`(r+2)`-axis position jet.  This theorem does not assert constant mass or a force law physically;
those are the hypotheses a realization must supply before using this rebase. -/
theorem forceDerivativeDimension_eq_mass_add_lengthJetDimension
    {TimeAxis : Type*} [DecidableEq TimeAxis]
    (sourceTime receiverTime : TimeAxis) (tail : TimeAxisWord TimeAxis) :
    forceDerivativeDimension sourceTime receiverTime tail =
      jetAxisDimension .mass +
        lengthJetDimension ([sourceTime, receiverTime] ++ tail) := by
  unfold forceDerivativeDimension forceDimension lengthJetDimension
  rw [timeWordDimension_append]
  funext axis
  simp
  ring

/-! ### Conventional names are receiver labels on two related towers -/

def jerkDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third : TimeAxis) : JetDimension TimeAxis :=
  lengthJetDimension [first, second, third]

def snapDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth : TimeAxis) : JetDimension TimeAxis :=
  lengthJetDimension [first, second, third, fourth]

def crackleDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth fifth : TimeAxis) : JetDimension TimeAxis :=
  lengthJetDimension [first, second, third, fourth, fifth]

def popDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth fifth sixth : TimeAxis) : JetDimension TimeAxis :=
  lengthJetDimension [first, second, third, fourth, fifth, sixth]

def yankDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third : TimeAxis) : JetDimension TimeAxis :=
  forceDerivativeDimension first second [third]

def tugDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth : TimeAxis) : JetDimension TimeAxis :=
  forceDerivativeDimension first second [third, fourth]

def snatchDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth fifth : TimeAxis) : JetDimension TimeAxis :=
  forceDerivativeDimension first second [third, fourth, fifth]

def shakeDimension {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth fifth sixth : TimeAxis) : JetDimension TimeAxis :=
  forceDerivativeDimension first second [third, fourth, fifth, sixth]

theorem yankDimension_eq_mass_add_jerkDimension
    {TimeAxis : Type*} [DecidableEq TimeAxis] (first second third : TimeAxis) :
    yankDimension first second third =
      jetAxisDimension .mass + jerkDimension first second third := by
  exact forceDerivativeDimension_eq_mass_add_lengthJetDimension first second [third]

theorem tugDimension_eq_mass_add_snapDimension
    {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth : TimeAxis) :
    tugDimension first second third fourth =
      jetAxisDimension .mass + snapDimension first second third fourth := by
  exact forceDerivativeDimension_eq_mass_add_lengthJetDimension
    first second [third, fourth]

theorem snatchDimension_eq_mass_add_crackleDimension
    {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth fifth : TimeAxis) :
    snatchDimension first second third fourth fifth =
      jetAxisDimension .mass + crackleDimension first second third fourth fifth := by
  exact forceDerivativeDimension_eq_mass_add_lengthJetDimension
    first second [third, fourth, fifth]

theorem shakeDimension_eq_mass_add_popDimension
    {TimeAxis : Type*} [DecidableEq TimeAxis]
    (first second third fourth fifth sixth : TimeAxis) :
    shakeDimension first second third fourth fifth sixth =
      jetAxisDimension .mass + popDimension first second third fourth fifth sixth := by
  exact forceDerivativeDimension_eq_mass_add_lengthJetDimension
    first second [third, fourth, fifth, sixth]

section Audit

#print axioms pantographicPoint_sub_anchor
#print axioms pantographicPoint_comp
#print axioms pantographicPoint_neg_one_eq_swing
#print axioms chooseTwo_succ
#print axioms pantographicJetCoefficient_succ
#print axioms pantographicJet_closedForm
#print axioms timeWordDimension_append
#print axioms forceDerivativeDimension_eq_mass_add_lengthJetDimension
#print axioms yankDimension_eq_mass_add_jerkDimension
#print axioms tugDimension_eq_mass_add_snapDimension
#print axioms snatchDimension_eq_mass_add_crackleDimension
#print axioms shakeDimension_eq_mass_add_popDimension

end Audit

end Soma.Holonics.Millennium.HolonicPantographicSwingJets
