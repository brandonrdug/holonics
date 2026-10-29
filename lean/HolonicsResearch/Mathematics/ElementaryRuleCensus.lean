import HolonicsResearch.Mathematics.AdditiveRuleJump
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The elementary rules by chart: 16 affine, 104 threshold, 8 both, and five that conserve count

The record `research/records/2026-10-23_A_POCKET_OF_REDUCIBILITY_IS_A_FACE_THAT_COMMUTES_WITH_THE_STEP_AND_THE_RECEIVERS_CHART_DECIDES_WHICH.md`
(§2; atlas `arith.rule-binding-by-chart`) reads an elementary cellular automaton rule as one crossing
in a chart exactly where its binding vanishes: in the GF(2) chart where its algebraic normal form
has degree at most one, in the chart of one locked sheet where it is a threshold
`[w_l l + w_c c + w_r r ≥ t]`. It counted the 256 rules exhaustively and found the count-conserving
rules on cyclic configurations up to length 12. #410 owed the counts and the five rules as decided
statements; this file proves them, the conservation for every length.

[proved-derived; formal-checked] What is proved.

1. **The GF(2) chart** (`affine_rules`, `affine_count`): 16 rules have a normal form
   `δ + α l + β c + γ r`, exactly those whose mixed differences all vanish mod 2
   (`affine_iff_mixedFlat`). They are the jump's rules at offset one (`affine_step`, joined to
   `AdditiveRuleJump.rule`). By degree (`constant_rules`, `pair_count`, `pair_not_affine_count`,
   `cubic_form`): rules 0 and 255 are the constants (rule 0 the empty form), 14 have degree one,
   112 degree two and 128 degree three. Rule 30 is `l + c + r + cr`, rule 110 is `c + r + cr + lcr`,
   rule 232 (majority) is `lc + lr + cr` (`rule30_form`, `rule110_form`, `rule232_form`),
   degree two and yet one locked sheet (`rule232_threshold`).
2. **The threshold chart** (`isThreshold_iff`, `threshold_count`): 104 rules are thresholds over
   the reals. Each comes with integer weights in `[−2, 2]` (`ThresholdCert`, `isThreshold_of_cert`);
   each of the other 152 comes with two neighbourhoods read `1` and two read `0` of equal
   coordinate sums (`SummableCert`, `not_isThreshold_of_cert`), and no real weights separate them,
   because the two sums of weights would be both at least `2t` and below it. The kernel checks the
   256 certificates (`certificate_ok`).
3. **Both and either** (`both_rules`, `either_count`): the 8 rules in both charts are the constants,
   the three copies and their negations (0, 15, 51, 85, 170, 204, 240, 255); 112 rules are in one
   or the other.
4. **Count conservation** (`conserving_iff_fluxForm`, `conserving_rules`): a rule conserves the
   count of ones on every cyclic configuration of every length exactly when it has the flux form
   `f(l, c, r) = l + J(c, r) − J(l, c)` with `J(u, v) = f(0, u, v) + f(0, 0, u)` (Boccara–Fukś).
   The flux form telescopes around any cycle; conversely the two configurations `abc00` and `bc000`
   of length five force it. Exactly five rules have it: 170, 184, 204, 226, 240.

[agent-inferred] The threshold is over the reals, the chart of one locked sheet; integer weights
are only its certificate. Conservation is asked of every length `L ≥ 1`, which length five already
decides.

The computational object is the helical pair interaction: each cell's update is a contact with its
two neighbours. The degree of the normal form is the order of the binding (two a pair contact,
three a triple), a threshold is one locked sheet, and the flux `J` is the current a conserving rule
carries across each contact. Of the winding guide's six general objects this touches faces and
placement (the two charts) and cell holonomy (the flux telescoping around a cycle); the helix, the
pair, the tube and the tower thread stay attached.

Consumers: the atlas row `arith.rule-binding-by-chart`.

No `sorry`, no `axiom`, no `native_decide`. The certificate and census statements are checked by
the kernel (`decide +kernel`).
-/

namespace Holonics.Mathematics.ElementaryRuleCensus

open scoped BigOperators

/-- [definition] Wolfram's numbering: rule `n` sends the neighbourhood `(l, c, r)` to bit
`4l + 2c + r` of `n`. -/
def ruleOut (n : ℕ) (l c r : Bool) : Bool :=
  n.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-! ## 1. The GF(2) chart -/

/-- [definition] **Affine over GF(2)**: a normal form of degree at most one,
`f = δ + α l + β c + γ r`. -/
def IsAffine (n : ℕ) : Prop :=
  ∃ δ α β γ : Bool, ∀ l c r : Bool,
    ruleOut n l c r = (δ ^^ (α && l) ^^ (β && c) ^^ (γ && r))

instance : DecidablePred IsAffine := fun n => by unfold IsAffine; infer_instance

/-- [definition] A normal form of degree at most zero: the rule is constant. -/
def IsConstant (n : ℕ) : Prop :=
  ∃ δ : Bool, ∀ l c r : Bool, ruleOut n l c r = δ

instance : DecidablePred IsConstant := fun n => by unfold IsConstant; infer_instance

/-- [definition] A normal form of degree at most two: no triple binding. -/
def IsAtMostPair (n : ℕ) : Prop :=
  ∃ δ α β γ a b g : Bool, ∀ l c r : Bool,
    ruleOut n l c r = (δ ^^ (α && l) ^^ (β && c) ^^ (γ && r) ^^
      (a && l && c) ^^ (b && l && r) ^^ (g && c && r))

instance : DecidablePred IsAtMostPair := fun n => by unfold IsAtMostPair; infer_instance

/-- [definition] The full normal form, degree at most three, with its eight coefficients. -/
def cubicForm (a : ℕ) (l c r : Bool) : Bool :=
  a.testBit 0 ^^ (a.testBit 1 && l) ^^ (a.testBit 2 && c) ^^ (a.testBit 3 && r) ^^
    (a.testBit 4 && l && c) ^^ (a.testBit 5 && l && r) ^^ (a.testBit 6 && c && r) ^^
    (a.testBit 7 && l && c && r)

/-- [definition] The normal form's coefficients by Möbius inversion: the coefficient of a monomial
is the sum over GF(2) of the rule's values on the neighbourhoods below it. -/
def anf (n : ℕ) : ℕ :=
  let f := fun l c r => (ruleOut n l c r).toNat
  let bit := fun (b : ℕ) (k : ℕ) => (b % 2) * 2 ^ k
  bit (f false false false) 0 +
    bit (f false false false + f true false false) 1 +
    bit (f false false false + f false true false) 2 +
    bit (f false false false + f false false true) 3 +
    bit (f false false false + f true false false + f false true false + f true true false) 4 +
    bit (f false false false + f true false false + f false false true + f true false true) 5 +
    bit (f false false false + f false true false + f false false true + f false true true) 6 +
    bit (f false false false + f true false false + f false true false + f false false true +
      f true true false + f true false true + f false true true + f true true true) 7

/-- [proved-derived; formal-checked] **Every rule has a normal form of degree at most three**, the
Möbius coefficients `anf n`. -/
theorem cubic_form : ∀ n < 256, ∀ l c r : Bool, ruleOut n l c r = cubicForm (anf n) l c r := by
  decide +kernel

/-- [proved-derived; formal-checked] The constants are rules 0 (the empty form) and 255. -/
theorem constant_rules : (Finset.range 256).filter IsConstant = {0, 255} := by
  decide +kernel

/-- [proved-derived; formal-checked] **The 16 affine rules.** -/
theorem affine_rules :
    (Finset.range 256).filter IsAffine =
      {0, 15, 51, 60, 85, 90, 102, 105, 150, 153, 165, 170, 195, 204, 240, 255} := by
  decide +kernel

/-- [proved-derived; formal-checked] 16 rules are affine. -/
theorem affine_count : ((Finset.range 256).filter IsAffine).card = 16 := by
  rw [affine_rules]; rfl

/-- [proved-derived; formal-checked] 128 rules need no triple binding. -/
theorem pair_count : ((Finset.range 256).filter IsAtMostPair).card = 128 := by
  decide +kernel

/-- [proved-derived; formal-checked] 112 rules need a pair binding and no triple: degree two. -/
theorem pair_not_affine_count :
    ((Finset.range 256).filter (fun n => IsAtMostPair n ∧ ¬ IsAffine n)).card = 112 := by
  decide +kernel

/-- [definition] **Every mixed difference vanishes mod 2**: flipping two inputs together changes
the output by the sum of the two single flips. -/
def IsMixedFlat (n : ℕ) : Prop :=
  ∀ l c r : Bool,
    (ruleOut n l c r ^^ ruleOut n (!l) c r ^^ ruleOut n l (!c) r ^^ ruleOut n (!l) (!c) r) =
        false ∧
      (ruleOut n l c r ^^ ruleOut n (!l) c r ^^ ruleOut n l c (!r) ^^ ruleOut n (!l) c (!r)) =
        false ∧
      (ruleOut n l c r ^^ ruleOut n l (!c) r ^^ ruleOut n l c (!r) ^^ ruleOut n l (!c) (!r)) =
        false

instance : DecidablePred IsMixedFlat := fun n => by unfold IsMixedFlat; infer_instance

/-- [proved-derived; formal-checked] **Degree at most one is a vanishing binding**: a rule is affine
exactly when every mixed difference vanishes mod 2. -/
theorem affine_iff_mixedFlat : ∀ n < 256, IsAffine n ↔ IsMixedFlat n := by
  decide +kernel

/-- [proved-derived; formal-checked] Rule 30 is `l + c + r + cr`. -/
theorem rule30_form : ∀ l c r : Bool, ruleOut 30 l c r = (l ^^ c ^^ r ^^ (c && r)) := by
  decide

/-- [proved-derived; formal-checked] Rule 110 is `c + r + cr + lcr`. -/
theorem rule110_form :
    ∀ l c r : Bool, ruleOut 110 l c r = (c ^^ r ^^ (c && r) ^^ (l && c && r)) := by
  decide

/-- [proved-derived; formal-checked] Rule 232, majority, is `lc + lr + cr`. -/
theorem rule232_form :
    ∀ l c r : Bool, ruleOut 232 l c r = ((l && c) ^^ (l && r) ^^ (c && r)) := by
  decide

/-- [proved-derived; formal-checked] **The affine rules are the jump's rules at offset one.** A rule
with normal form `δ + α l + β c + γ r`, read on `ZMod 2`, steps every configuration as
`AdditiveRuleJump.rule δ α β γ 1`, so `AdditiveRuleJump.rule_iterate` jumps it. -/
theorem affine_step {n : ℕ} {δ α β γ : Bool}
    (h : ∀ l c r : Bool, ruleOut n l c r = (δ ^^ (α && l) ^^ (β && c) ^^ (γ && r)))
    (x : ℤ → Bool) (i : ℤ) :
    ((ruleOut n (x (i - 1)) (x i) (x (i + 1))).toNat : ZMod 2) =
      AdditiveRuleJump.rule δ.toNat α.toNat β.toNat γ.toNat 1 (fun j => (x j).toNat) i := by
  rw [h]
  simp only [AdditiveRuleJump.rule]
  generalize x (i - 1) = l, x i = c, x (i + 1) = r
  cases δ <;> cases α <;> cases β <;> cases γ <;> cases l <;> cases c <;> cases r <;> decide

/-! ## 2. The threshold chart -/

/-- [definition] **One locked sheet**: `f = [w_l l + w_c c + w_r r ≥ t]` for real weights. -/
def IsThreshold (n : ℕ) : Prop :=
  ∃ wl wc wr t : ℝ, ∀ l c r : Bool,
    ruleOut n l c r = true ↔ t ≤ wl * l.toNat + wc * c.toNat + wr * r.toNat

/-- [definition] An integer threshold certificate `(w_l, w_c, w_r, t)`. -/
def ThresholdCert (n : ℕ) (w : ℤ × ℤ × ℤ × ℤ) : Prop :=
  ∀ l c r : Bool,
    ruleOut n l c r = decide (w.2.2.2 ≤ w.1 * l.toNat + w.2.1 * c.toNat + w.2.2.1 * r.toNat)

instance (n : ℕ) (w : ℤ × ℤ × ℤ × ℤ) : Decidable (ThresholdCert n w) := by
  unfold ThresholdCert; infer_instance

/-- [definition] The neighbourhood with code `k = 4l + 2c + r`. -/
def point (k : ℕ) : Bool × Bool × Bool := (k.testBit 2, k.testBit 1, k.testBit 0)

/-- [definition] The rule's value at the neighbourhood with code `k`. -/
def ruleAt (n k : ℕ) : Bool := ruleOut n (point k).1 (point k).2.1 (point k).2.2

/-- [definition] A summability certificate: neighbourhoods `p, q` read `1`, `u, v` read `0`, and
`p + q = u + v` coordinatewise. -/
def SummableCert (n : ℕ) (k : ℕ × ℕ × ℕ × ℕ) : Prop :=
  ruleAt n k.1 = true ∧ ruleAt n k.2.1 = true ∧ ruleAt n k.2.2.1 = false ∧
    ruleAt n k.2.2.2 = false ∧
    (point k.1).1.toNat + (point k.2.1).1.toNat =
      (point k.2.2.1).1.toNat + (point k.2.2.2).1.toNat ∧
    (point k.1).2.1.toNat + (point k.2.1).2.1.toNat =
      (point k.2.2.1).2.1.toNat + (point k.2.2.2).2.1.toNat ∧
    (point k.1).2.2.toNat + (point k.2.1).2.2.toNat =
      (point k.2.2.1).2.2.toNat + (point k.2.2.2).2.2.toNat

instance (n : ℕ) (k : ℕ × ℕ × ℕ × ℕ) : Decidable (SummableCert n k) := by
  unfold SummableCert; infer_instance

/-- [proved-derived; formal-checked] Integer weights make a real threshold. -/
theorem isThreshold_of_cert {n : ℕ} {w : ℤ × ℤ × ℤ × ℤ} (h : ThresholdCert n w) :
    IsThreshold n := by
  obtain ⟨wl, wc, wr, t⟩ := w
  refine ⟨wl, wc, wr, t, fun l c r => ?_⟩
  rw [h l c r, decide_eq_true_iff]
  constructor <;> intro hh <;> exact_mod_cast hh

/-- [proved-derived; formal-checked] **A summable quadruple refuses every threshold**: the weights
of `p` and `q` sum to at least `2t`, those of `u` and `v` to less, and the two sums are equal. -/
theorem not_isThreshold_of_cert {n : ℕ} {k : ℕ × ℕ × ℕ × ℕ} (h : SummableCert n k) :
    ¬ IsThreshold n := by
  unfold SummableCert ruleAt at h
  generalize point k.1 = p, point k.2.1 = q, point k.2.2.1 = u, point k.2.2.2 = v at h
  obtain ⟨pl, pc, pr⟩ := p
  obtain ⟨ql, qc, qr⟩ := q
  obtain ⟨ul, uc, ur⟩ := u
  obtain ⟨vl, vc, vr⟩ := v
  obtain ⟨hp, hq, hu, hv, e1, e2, e3⟩ := h
  rintro ⟨wl, wc, wr, t, hw⟩
  have a := (hw pl pc pr).mp hp
  have b := (hw ql qc qr).mp hq
  have c := (hw ul uc ur).not.mp (by simp [hu])
  have d := (hw vl vc vr).not.mp (by simp [hv])
  have e1' : (pl.toNat : ℝ) + ql.toNat = ul.toNat + vl.toNat := by exact_mod_cast e1
  have e2' : (pc.toNat : ℝ) + qc.toNat = uc.toNat + vc.toNat := by exact_mod_cast e2
  have e3' : (pr.toNat : ℝ) + qr.toNat = ur.toNat + vr.toNat := by exact_mod_cast e3
  rw [not_le] at c d
  have key : wl * pl.toNat + wc * pc.toNat + wr * pr.toNat +
      (wl * ql.toNat + wc * qc.toNat + wr * qr.toNat) =
      wl * ul.toNat + wc * uc.toNat + wr * ur.toNat +
      (wl * vl.toNat + wc * vc.toNat + wr * vr.toNat) := by
    linear_combination wl * e1' + wc * e2' + wr * e3'
  linarith

/-- [definition] A certificate's claim: integer weights, or a summable quadruple. -/
def CertOK (n : ℕ) : (ℤ × ℤ × ℤ × ℤ) ⊕ (ℕ × ℕ × ℕ × ℕ) → Prop
  | .inl w => ThresholdCert n w
  | .inr k => SummableCert n k

instance (n : ℕ) (c : (ℤ × ℤ × ℤ × ℤ) ⊕ (ℕ × ℕ × ℕ × ℕ)) : Decidable (CertOK n c) := by
  cases c <;> unfold CertOK <;> infer_instance

/-- [definition] The certificates of the 256 rules in Wolfram order: integer weights
`(w_l, w_c, w_r, t)` with the least `|w_l| + |w_c| + |w_r| + |t|`, or the codes `(p, q, u, v)` of
the first summable quadruple. -/
def certificates : List ((ℤ × ℤ × ℤ × ℤ) ⊕ (ℕ × ℕ × ℕ × ℕ)) := [
    -- rules 0 to 15
    .inl (0, 0, 0, 1), .inl (-1, -1, -1, 0), .inl (-1, -1, 1, 1), .inl (-1, -1, 0, 0),
    .inl (-1, 1, -1, 1), .inl (-1, 0, -1, 0), .inr (1, 2, 0, 3), .inl (-2, -1, -1, -1),
    .inl (-1, 1, 1, 2), .inr (0, 3, 1, 2), .inl (-1, 0, 1, 1), .inl (-2, -1, 1, 0),
    .inl (-1, 1, 0, 1), .inl (-2, 1, -1, 0), .inl (-2, 1, 1, 1), .inl (-1, 0, 0, 0),
    -- rules 16 to 31
    .inl (1, -1, -1, 1), .inl (0, -1, -1, 0), .inr (1, 4, 0, 5), .inl (-1, -2, -1, -1),
    .inr (2, 4, 0, 6), .inl (-1, -1, -2, -1), .inr (1, 2, 0, 3), .inl (-1, -1, -1, -1),
    .inr (3, 4, 0, 7), .inr (0, 3, 1, 2), .inr (1, 4, 0, 5), .inr (3, 4, 2, 5),
    .inr (2, 4, 0, 6), .inr (3, 4, 1, 6), .inr (1, 4, 0, 5), .inl (-2, -1, -1, -2),
    -- rules 32 to 47
    .inl (1, -1, 1, 2), .inr (0, 5, 1, 4), .inl (0, -1, 1, 1), .inl (-1, -2, 1, 0),
    .inr (2, 5, 0, 7), .inr (0, 5, 1, 4), .inr (1, 2, 0, 3), .inr (2, 5, 3, 4),
    .inr (3, 5, 1, 7), .inr (0, 3, 1, 2), .inl (-1, -1, 2, 1), .inl (-1, -1, 1, 0),
    .inr (2, 5, 0, 7), .inr (0, 5, 1, 4), .inr (2, 5, 0, 7), .inl (-2, -1, 1, -1),
    -- rules 48 to 63
    .inl (1, -1, 0, 1), .inl (1, -2, -1, 0), .inl (1, -2, 1, 1), .inl (0, -1, 0, 0),
    .inr (2, 4, 0, 6), .inr (2, 5, 1, 6), .inr (1, 2, 0, 3), .inl (-1, -2, -1, -2),
    .inr (3, 4, 0, 7), .inr (0, 3, 1, 2), .inr (3, 4, 0, 7), .inl (-1, -2, 1, -1),
    .inr (2, 4, 0, 6), .inr (2, 5, 1, 6), .inr (2, 4, 0, 6), .inl (-1, -1, 0, -1),
    -- rules 64 to 79
    .inl (1, 1, -1, 2), .inr (0, 6, 2, 4), .inr (1, 6, 0, 7), .inr (0, 6, 2, 4),
    .inl (0, 1, -1, 1), .inl (-1, 1, -2, 0), .inr (1, 2, 0, 3), .inr (1, 6, 3, 4),
    .inr (3, 6, 2, 7), .inr (0, 3, 1, 2), .inr (1, 6, 0, 7), .inr (0, 6, 2, 4),
    .inl (-1, 2, -1, 1), .inl (-1, 1, -1, 0), .inr (1, 6, 0, 7), .inl (-2, 1, -1, -1),
    -- rules 80 to 95
    .inl (1, 0, -1, 1), .inl (1, -1, -2, 0), .inr (1, 4, 0, 5), .inr (1, 6, 2, 5),
    .inl (1, 1, -2, 1), .inl (0, 0, -1, 0), .inr (1, 2, 0, 3), .inl (-1, -1, -2, -2),
    .inr (3, 4, 0, 7), .inr (0, 3, 1, 2), .inr (1, 4, 0, 5), .inr (1, 6, 2, 5),
    .inr (3, 4, 0, 7), .inl (-1, 1, -2, -1), .inr (1, 4, 0, 5), .inl (-1, 0, -1, -1),
    -- rules 96 to 111
    .inr (5, 6, 4, 7), .inr (0, 5, 1, 4), .inr (1, 6, 0, 7), .inr (0, 6, 2, 4),
    .inr (2, 5, 0, 7), .inr (0, 5, 1, 4), .inr (1, 2, 0, 3), .inr (1, 6, 3, 4),
    .inr (3, 5, 1, 7), .inr (0, 3, 1, 2), .inr (1, 6, 0, 7), .inr (0, 6, 2, 4),
    .inr (2, 5, 0, 7), .inr (0, 5, 1, 4), .inr (1, 6, 0, 7), .inr (5, 6, 4, 7),
    -- rules 112 to 127
    .inl (2, -1, -1, 1), .inl (1, -1, -1, 0), .inr (1, 6, 0, 7), .inl (1, -2, -1, -1),
    .inr (2, 5, 0, 7), .inl (1, -1, -2, -1), .inr (1, 2, 0, 3), .inl (0, -1, -1, -1),
    .inr (3, 4, 0, 7), .inr (0, 3, 1, 2), .inr (1, 6, 0, 7), .inr (3, 6, 2, 7),
    .inr (2, 5, 0, 7), .inr (3, 5, 1, 7), .inr (1, 6, 0, 7), .inl (-1, -1, -1, -2),
    -- rules 128 to 143
    .inl (1, 1, 1, 3), .inr (0, 7, 1, 6), .inr (1, 7, 3, 5), .inr (0, 7, 2, 5),
    .inr (2, 7, 3, 6), .inr (0, 7, 1, 6), .inr (1, 2, 0, 3), .inr (0, 7, 3, 4),
    .inl (0, 1, 1, 2), .inr (0, 3, 1, 2), .inl (-1, 1, 2, 2), .inr (0, 7, 2, 5),
    .inl (-1, 2, 1, 2), .inr (0, 7, 1, 6), .inl (-1, 1, 1, 1), .inl (-2, 1, 1, 0),
    -- rules 144 to 159
    .inr (4, 7, 5, 6), .inr (0, 7, 1, 6), .inr (1, 4, 0, 5), .inr (0, 7, 2, 5),
    .inr (2, 4, 0, 6), .inr (0, 7, 1, 6), .inr (1, 2, 0, 3), .inr (1, 7, 3, 5),
    .inr (3, 4, 1, 6), .inr (0, 3, 1, 2), .inr (1, 4, 0, 5), .inr (0, 7, 2, 5),
    .inr (2, 4, 0, 6), .inr (0, 7, 1, 6), .inr (1, 4, 0, 5), .inr (4, 7, 5, 6),
    -- rules 160 to 175
    .inl (1, 0, 1, 2), .inr (0, 5, 1, 4), .inl (1, -1, 2, 2), .inr (0, 7, 3, 4),
    .inr (2, 5, 1, 6), .inr (0, 5, 1, 4), .inr (1, 2, 0, 3), .inr (0, 7, 3, 4),
    .inl (1, 1, 2, 3), .inr (0, 3, 1, 2), .inl (0, 0, 1, 1), .inl (-1, -1, 2, 0),
    .inr (2, 5, 1, 6), .inr (0, 5, 1, 4), .inl (-1, 1, 2, 1), .inl (-1, 0, 1, 0),
    -- rules 176 to 191
    .inl (2, -1, 1, 2), .inr (0, 7, 1, 6), .inl (1, -1, 1, 1), .inl (1, -2, 1, 0),
    .inr (2, 4, 0, 6), .inr (0, 7, 1, 6), .inr (1, 2, 0, 3), .inr (2, 7, 3, 6),
    .inr (3, 4, 1, 6), .inr (0, 3, 1, 2), .inl (1, -1, 2, 1), .inl (0, -1, 1, 0),
    .inr (2, 4, 0, 6), .inr (0, 7, 1, 6), .inr (2, 4, 0, 6), .inl (-1, -1, 1, -1),
    -- rules 192 to 207
    .inl (1, 1, 0, 2), .inr (0, 6, 2, 4), .inr (1, 6, 2, 5), .inr (0, 6, 2, 4),
    .inl (1, 2, -1, 2), .inr (0, 7, 3, 4), .inr (1, 2, 0, 3), .inr (0, 7, 3, 4),
    .inl (1, 2, 1, 3), .inr (0, 3, 1, 2), .inr (1, 6, 2, 5), .inr (0, 6, 2, 4),
    .inl (0, 1, 0, 1), .inl (-1, 2, -1, 0), .inl (-1, 2, 1, 1), .inl (-1, 1, 0, 0),
    -- rules 208 to 223
    .inl (2, 1, -1, 2), .inr (0, 7, 2, 5), .inr (1, 4, 0, 5), .inr (0, 7, 2, 5),
    .inl (1, 1, -1, 1), .inl (1, 1, -2, 0), .inr (1, 2, 0, 3), .inr (1, 7, 3, 5),
    .inr (3, 4, 2, 5), .inr (0, 3, 1, 2), .inr (1, 4, 0, 5), .inr (0, 7, 2, 5),
    .inl (1, 2, -1, 1), .inl (0, 1, -1, 0), .inr (1, 4, 0, 5), .inl (-1, 1, -1, -1),
    -- rules 224 to 239
    .inl (2, 1, 1, 3), .inr (0, 5, 1, 4), .inr (1, 6, 3, 4), .inr (0, 6, 2, 4),
    .inr (2, 5, 3, 4), .inr (0, 5, 1, 4), .inr (1, 2, 0, 3), .inr (0, 7, 3, 4),
    .inl (1, 1, 1, 2), .inr (0, 3, 1, 2), .inl (1, 1, 2, 2), .inr (0, 6, 2, 4),
    .inl (1, 2, 1, 2), .inr (0, 5, 1, 4), .inl (0, 1, 1, 1), .inl (-1, 1, 1, 0),
    -- rules 240 to 255
    .inl (1, 0, 0, 1), .inl (2, -1, -1, 0), .inl (2, -1, 1, 1), .inl (1, -1, 0, 0),
    .inl (2, 1, -1, 1), .inl (1, 0, -1, 0), .inr (1, 2, 0, 3), .inl (1, -1, -1, -1),
    .inl (2, 1, 1, 2), .inr (0, 3, 1, 2), .inl (1, 0, 1, 1), .inl (1, -1, 1, 0),
    .inl (1, 1, 0, 1), .inl (1, 1, -1, 0), .inl (1, 1, 1, 1), .inl (0, 0, 0, 0)
  ]

/-- [definition] The certificate of rule `n`. -/
def certificate (n : ℕ) : (ℤ × ℤ × ℤ × ℤ) ⊕ (ℕ × ℕ × ℕ × ℕ) :=
  certificates.getD n (.inl (0, 0, 0, 0))

/-- [proved-derived; formal-checked] Every certificate holds. -/
theorem certificate_ok : ∀ n < 256, CertOK n (certificate n) := by
  decide +kernel

/-- [definition] The table's reading: rule `n` carries integer weights. -/
def certIsThreshold (n : ℕ) : Bool := (certificate n).isLeft

/-- [proved-derived; formal-checked] A rule is a real threshold exactly when its certificate is
integer weights. -/
theorem isThreshold_iff {n : ℕ} (hn : n < 256) : IsThreshold n ↔ certIsThreshold n = true := by
  have h := certificate_ok n hn
  unfold certIsThreshold
  cases hc : certificate n with
  | inl w =>
    rw [hc] at h
    exact ⟨fun _ => rfl, fun _ => isThreshold_of_cert h⟩
  | inr k =>
    rw [hc] at h
    exact ⟨fun ht => absurd ht (not_isThreshold_of_cert h), fun hf => by simp at hf⟩

open Classical in
/-- [proved-derived; formal-checked] **104 rules are one locked sheet.** -/
theorem threshold_count : ((Finset.range 256).filter IsThreshold).card = 104 := by
  rw [Finset.filter_congr (q := fun n => certIsThreshold n = true)
    (fun n hn => isThreshold_iff (Finset.mem_range.mp hn))]
  decide +kernel

/-- [proved-derived; formal-checked] Majority, rule 232, is one locked sheet though its normal form
has degree two. -/
theorem rule232_threshold : IsThreshold 232 :=
  (isThreshold_iff (by norm_num)).mpr (by decide +kernel)

/-! ## 3. Both charts and either -/

open Classical in
/-- [proved-derived; formal-checked] **The 8 rules in both charts**: the constants, the three copies
and their negations. -/
theorem both_rules :
    (Finset.range 256).filter (fun n => IsAffine n ∧ IsThreshold n) =
      {0, 15, 51, 85, 170, 204, 240, 255} := by
  rw [Finset.filter_congr (q := fun n => IsAffine n ∧ certIsThreshold n = true)
    (fun n hn => and_congr_right' (isThreshold_iff (Finset.mem_range.mp hn)))]
  decide +kernel

open Classical in
/-- [proved-derived; formal-checked] 112 rules are one crossing in one chart or the other. -/
theorem either_count :
    ((Finset.range 256).filter (fun n => IsAffine n ∨ IsThreshold n)).card = 112 := by
  rw [Finset.filter_congr (q := fun n => IsAffine n ∨ certIsThreshold n = true)
    (fun n hn => or_congr_right (isThreshold_iff (Finset.mem_range.mp hn)))]
  decide +kernel

/-! ## 4. Count conservation -/

/-- [definition] One step of rule `n` on a cyclic configuration of length `L`. -/
def cyclicStep (n L : ℕ) (x : ZMod L → Bool) (i : ZMod L) : Bool :=
  ruleOut n (x (i - 1)) (x i) (x (i + 1))

/-- [definition] Rule `n` conserves the count of ones on every cyclic configuration of every
length. -/
def Conserving (n : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (x : ZMod L → Bool),
    ∑ i, (cyclicStep n L x i).toNat = ∑ i, (x i).toNat

/-- [definition] **The flux form** (Boccara–Fukś): `f(l, c, r) = l + J(c, r) − J(l, c)` with the
flux `J(u, v) = f(0, u, v) + f(0, 0, u)` across the contact between `u` and `v`. -/
def FluxForm (n : ℕ) : Prop :=
  ∀ l c r : Bool,
    ((ruleOut n l c r).toNat : ℤ) =
      l.toNat + ((ruleOut n false c r).toNat + (ruleOut n false false c).toNat) -
        ((ruleOut n false l c).toNat + (ruleOut n false false l).toNat)

instance : DecidablePred FluxForm := fun n => by unfold FluxForm; infer_instance

/-- [proved-derived; formal-checked] **The flux form conserves count**: around a cycle the fluxes
telescope and the copied term `l` is the configuration shifted by one. -/
theorem conserving_of_fluxForm {n : ℕ} (h : FluxForm n) : Conserving n := by
  intro L _ x
  have shift : ∀ F : ZMod L → ℤ, ∑ i, F (i - 1) = ∑ i, F i :=
    fun F => (Equiv.subRight (1 : ZMod L)).sum_comp F
  let A : ZMod L → ℤ := fun j => (x j).toNat
  let J : ZMod L → ℤ := fun j =>
    (ruleOut n false (x j) (x (j + 1))).toNat + (ruleOut n false false (x j)).toNat
  have key : ∀ i, ((cyclicStep n L x i).toNat : ℤ) = A (i - 1) + J i - J (i - 1) := by
    intro i
    simp only [cyclicStep, A, J, sub_add_cancel]
    exact h _ _ _
  have hz : ((∑ i, (cyclicStep n L x i).toNat : ℕ) : ℤ) = ((∑ i, (x i).toNat : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      shift A, shift J]
    simp [A]
  exact_mod_cast hz

/-- [proved-derived; formal-checked] **Conservation forces the flux form**: on the cycles of length
five, `abc00` and `bc000` differ by exactly the flux form, and `00000` gives `f(0, 0, 0) = 0`. -/
theorem fluxForm_of_conserving {n : ℕ} (h : Conserving n) : FluxForm n := by
  intro a b c
  have five : ∀ F : ZMod 5 → ℕ, ∑ i, F i = F 0 + F 1 + F 2 + F 3 + F 4 :=
    fun F => Fin.sum_univ_five F
  have h1 := h 5 (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else false)
  have h2 := h 5 (fun i => if i = 0 then b else if i = 1 then c else false)
  have h0 := h 5 (fun _ => false)
  simp (config := { decide := true }) only [five, cyclicStep, ↓reduceIte, Bool.toNat_false]
    at h1 h2 h0
  omega

/-- [proved-derived; formal-checked] **Conservation is the flux form.** -/
theorem conserving_iff_fluxForm (n : ℕ) : Conserving n ↔ FluxForm n :=
  ⟨fluxForm_of_conserving, conserving_of_fluxForm⟩

open Classical in
/-- [proved-derived; formal-checked] **The five count-conserving rules**: 170, 204 and 240 copy
(the left shift, the identity and the right shift), 184 and 226 are traffic in its two
directions. -/
theorem conserving_rules :
    (Finset.range 256).filter Conserving = {170, 184, 204, 226, 240} := by
  rw [Finset.filter_congr (q := FluxForm) (fun n _ => conserving_iff_fluxForm n)]
  decide +kernel

end Holonics.Mathematics.ElementaryRuleCensus
