import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.Perm.Basic
import ElementaryHolonics.Millennium.Swing

/-!
# The chronology — why a transport is a word and not a value

An operation that reads as *one* operation in a chart is intrinsically several steps with a
trajectory parameter whenever the steps fail to commute.  This file makes that precise:

**A chain series exists exactly when the transports do not commute.**  `orderBlind_iff_commute`
proves that a family of transports collapses every word to its multiset — no chronology, no
series, nothing for a parameter to index — *if and only if* the transports commute pairwise.  So
the series is not an artifact of a method; it is the record of order that non-commutation forces
into existence.

Sections 3 to 6 then rebuild three standard results on that basis: the hand of a configuration is
the parity of the word that produced it, the mean value theorem is the flat statement read out of
the chart the two constraints declare, the squeeze is a pair of constraints closing on a body,
and a closed triple of transports has its third member forced.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Chronology

open Soma.Holonics.Millennium.Swing

/-! ## 1. A transport is a word -/

universe u v

variable {ι : Type u} {X : Type v}

/-- The transport a **word** of moves performs, read right to left: the rightmost letter acts
first, so the list is a chronology and not a set. -/
def transportWord (T : ι → X → X) : List ι → X → X
  | [], x => x
  | i :: w, x => T i (transportWord T w x)

@[simp] theorem transportWord_nil (T : ι → X → X) (x : X) : transportWord T [] x = x := rfl

@[simp] theorem transportWord_cons (T : ι → X → X) (i : ι) (w : List ι) (x : X) :
    transportWord T (i :: w) x = T i (transportWord T w x) := rfl

/-- **Equivariance on the generators extends to every ordered transport word.**

This is the exact local-to-composite bridge used by a geometric action: if `f` intertwines each
declared generator `T i` with `S i`, it intertwines the chronology they generate, with its order
retained. The theorem does not claim that the actions or the intertwiner were recovered from
material; those are exterior hypotheses. -/
theorem generatorEquivarianceExtendsToEveryTransportWord
    {Y : Type*} (T : ι → X → X) (S : ι → Y → Y) (f : X → Y)
    (h : ∀ i x, f (T i x) = S i (f x)) (w : List ι) (x : X) :
    f (transportWord T w x) = transportWord S w (f x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [transportWord_cons, h, ih, transportWord_cons]

/-- A family of transports is **order-blind** when every word's result depends only on which
moves occurred and not on when — that is, when the chronology carries no information. -/
def OrderBlind (T : ι → X → X) : Prop :=
  ∀ w v : List ι, w.Perm v → ∀ x : X, transportWord T w x = transportWord T v x

/-! ## 2. The chain series exists exactly because the transports do not commute -/

/-- **Order-blindness is exactly pairwise commutation.**

If the moves commute, every word collapses to its multiset: there is no chronology to record, no
parameter for a series to run over, and no order-dependent term for a correction to carry.  If any
two moves fail to commute, the word is irreducible information and a chronology exists.

*Aside: this is the elementary reason the chain series of a non-autonomous linear transport — the
time-ordered exponential, whose logarithm is a series of nested commutators — has any terms past
the first.  A commuting family's series terminates immediately.* -/
theorem orderBlind_iff_commute {T : ι → X → X} :
    OrderBlind T ↔ ∀ i j : ι, ∀ x : X, T i (T j x) = T j (T i x) := by
  constructor
  · intro h i j x
    have hp : ([j, i] : List ι).Perm [i, j] := List.Perm.swap i j []
    simpa using (h [j, i] [i, j] hp x).symm
  · intro hc w v hperm
    induction hperm with
    | nil => intro x; rfl
    | cons a _ ih => intro x; simp [ih x]
    | swap a b l => intro x; simpa using hc b a (transportWord T l x)
    | trans _ _ ih₁ ih₂ => intro x; rw [ih₁ x, ih₂ x]

/-- **The swing family is not order-blind**, so the chronology it produces is real.

Two swings about different anchors differ by four times the anchor displacement, which is nonzero
whenever the anchors are.  An abstract order-dependence with no witness would be an untested
gauge; this is the witness. -/
theorem theSwingFamilyIsNotOrderBlind : ¬ OrderBlind (swing : Site → Site → Site) := by
  rw [orderBlind_iff_commute]
  intro h
  have := h ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ))
  simp only [swing, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq] at this
  omega

/-! ## 3. The hand of a configuration is the parity of the word that produced it

A single crossing negates the oriented span; the span is only restored after an even number of
them.  So the "cross product" a configuration exhibits is not a property of the endpoint — it is a
function of the chronology's length, and no unsigned reading of the endpoint recovers it. -/

/-- **After a word of `n` swings about one anchor, the hand is `(−1)^n`.**

The magnitude is invariant and the sign is the parity of the word.  This is the precise sense in
which the operation "takes multiple steps to complete": the span returns only on even words. -/
theorem theHandIsTheParityOfTheWord (a b c : Site) (n : ℕ) :
    orientedSpan ((swing b)^[n] a) b c = (-1 : ℤ) ^ n * orientedSpan a b c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', theSwingNegatesTheOrientedSpan, ih, pow_succ]
    ring

/-- **An even word restores the hand; an odd word reverses it.**  Even words are therefore the
ones that preserve the oriented form, and odd words are the ones that reverse it. -/
theorem theEvenWordRestoresTheHand (a b c : Site) {n : ℕ} (hn : Even n) :
    orientedSpan ((swing b)^[n] a) b c = orientedSpan a b c := by
  rw [theHandIsTheParityOfTheWord, hn.neg_one_pow, one_mul]

theorem theOddWordReversesTheHand (a b c : Site) {n : ℕ} (hn : Odd n) :
    orientedSpan ((swing b)^[n] a) b c = - orientedSpan a b c := by
  rw [theHandIsTheParityOfTheWord, hn.neg_one_pow, neg_one_mul]

/-! ## 4. The chart two constraints declare, and what it does to the mean value theorem -/

/-- The affine transport the two endpoint constraints declare — the chord. -/
noncomputable def chordLine (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun x => (f b - f a) / (b - a) * x + (f a - (f b - f a) / (b - a) * a)

/-- The **constraint chart**: the body read against the chord its own two constraints span.

*Aside: this is the auxiliary function by which the mean value theorem is classically reduced to
its flat case.  Naming it a chart is the point — it is the same construction as the chart the
anchor and the board declare for a swing.* -/
noncomputable def chordChart (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := f - chordLine f a b

/-- **In the chart the constraints declare, the body vanishes at both of them.**  The chart is
chosen exactly so that the two constraints become indistinguishable. -/
theorem theChordChartVanishesAtBothConstraints {f : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b) :
    chordChart f a b a = 0 ∧ chordChart f a b b = 0 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  constructor <;> · simp only [chordChart, chordLine, Pi.sub_apply]; field_simp; ring

/-- **The chart shifts every rate by the mean rate, and by nothing else.** -/
theorem theChordChartShiftsTheRate {f : ℝ → ℝ} {a b c f' : ℝ} (hab : a ≠ b)
    (h : HasDerivAt f f' c) :
    HasDerivAt (chordChart f a b) (f' - (f b - f a) / (b - a)) c := by
  have hline : HasDerivAt (chordLine f a b) ((f b - f a) / (b - a)) c := by
    have h0 := (((hasDerivAt_id c).const_mul ((f b - f a) / (b - a))).add_const
      (f a - (f b - f a) / (b - a) * a))
    simp only [id_eq, mul_one] at h0
    exact h0
  exact h.sub hline

/-- **The flat anchor of the chart and the mean-rate anchor of the body are the same point.**

The mean value theorem is therefore not a separate statement: it is the flat statement, read back
out of the chart that the two constraints declared.  What the chart does is exactly what the
constraint chart does for a swing — it makes the symmetric case visible. -/
theorem theFlatAnchorIsTheMeanRateAnchor {f : ℝ → ℝ} {a b c f' : ℝ} (hab : a ≠ b)
    (h : HasDerivAt f f' c) :
    HasDerivAt (chordChart f a b) 0 c ↔ f' = (f b - f a) / (b - a) := by
  constructor
  · intro hflat
    have := (theChordChartShiftsTheRate hab h).unique hflat
    linarith
  · intro hmean
    have hshift := theChordChartShiftsTheRate hab h
    rwa [hmean, sub_self] at hshift

/-! ## 5. Two constraints closing on a body place it

The squeeze is the pin picture with the gap named: two constraints bound a body, the gap between
them is the population no receiver in the declared family can separate, and when that population
collapses the body's placement is determined. -/

variable {β : Type*}

/-- The **constraint gap**: what the two constraints leave undetermined about the body. -/
def constraintGap (lo hi : β → ℝ) : β → ℝ := hi - lo

/-- **When the two constraints converge, the body between them is placed.** -/
theorem theBodyIsPlacedWhenTheConstraintsClose {lo f hi : β → ℝ} {l : Filter β} {L : ℝ}
    (hlo : Filter.Tendsto lo l (nhds L)) (hhi : Filter.Tendsto hi l (nhds L))
    (h1 : lo ≤ f) (h2 : f ≤ hi) : Filter.Tendsto f l (nhds L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi h1 h2

/-- **And what collapses is the gap itself.**  The placement is not obtained by measuring the body
more finely; it is obtained because the population the constraints could not separate went to
nothing. -/
theorem theGapCollapses {lo hi : β → ℝ} {l : Filter β} {L : ℝ}
    (hlo : Filter.Tendsto lo l (nhds L)) (hhi : Filter.Tendsto hi l (nhds L)) :
    Filter.Tendsto (constraintGap lo hi) l (nhds 0) := by
  have := hhi.sub hlo
  change Filter.Tendsto (fun x => hi x - lo x) l (nhds 0)
  simpa [sub_self] using this

/-! ## 6. A closed triple forces its third transport

Three transports whose composite returns is the shape a three-constraint transport problem carries.
Two of them determine the third, which is why such a problem is finite data rather than a search.

*Aside: this is the shape of a Riemann scheme's monodromy — three local transports whose product
is the identity.  Nothing here formalizes a hypergeometric equation; only the closure shape.* -/

/-- Three transports whose composite returns. -/
structure ClosedTriple (X : Type v) where
  /-- The first transport. -/
  first : Equiv.Perm X
  /-- The second. -/
  second : Equiv.Perm X
  /-- The third. -/
  third : Equiv.Perm X
  /-- The loop closes. -/
  closes : first * second * third = 1

namespace ClosedTriple

variable (S : ClosedTriple X)

/-- **Two of the three transports force the third.** -/
theorem theThirdIsForced : S.third = (S.first * S.second)⁻¹ :=
  eq_inv_of_mul_eq_one_right S.closes

/-- **A closed triple has no free third choice**: two triples agreeing on the first two agree
entirely.  A three-constraint transport problem is therefore finite data. -/
theorem theTripleIsDeterminedByTwo (S' : ClosedTriple X)
    (h1 : S.first = S'.first) (h2 : S.second = S'.second) : S.third = S'.third := by
  rw [S.theThirdIsForced, S'.theThirdIsForced, h1, h2]

end ClosedTriple

end Soma.Holonics.Millennium.Chronology
