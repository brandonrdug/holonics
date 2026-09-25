import Holonics.Aeon.Production.PathReversal
import Holonics.Physics.TwoCellEntropyTransport

/-!
# Schnakenberg's production across a neck, carried as ratios

[definition] Rebuild step 6, K3 (#74), battle test 5, and the egg record §5 ("the production
across a neck is the flux through it times the log-ratio drop"). A **neck** is a finite family of
oriented junctions, each with a forward flow `J₊` and a backward flow `J₋` on one clock (exact
rationals). Schnakenberg's production across it is

```text
σ = ½ Σ_(ordered pairs) (J₊ − J₋) log(J₊/J₋) = Σ_(junctions) (J₊ − J₋) log(J₊/J₋)
```

(`neckProduction`). **The operands are the exact pairs** `(J₊ − J₋, J₊/J₋)`: the net current and
the flow ratio. The logarithm is only the face that turns the ratio into a magnitude; the sign of
every junction's production is decided on the rationals by the certificate
`(J₊ − J₋)(J₊/J₋ − 1) = (J₊ − J₋)²/J₋ ≥ 0` (`certificate_eq`), whose vanishing is balance
(`certificate_eq_zero_iff`), and the real term has the certificate's sign (`term_nonneg`,
`term_eq_zero_iff`).

[proved-derived; formal-checked] What is proved.

1. **`σ ≥ 0`, and `σ = 0` exactly when the neck is balanced**, `J₊ = J₋` on every junction
   (`neckProduction_nonneg`, `neckProduction_eq_zero_iff`). The production is the edge code
   production of `Foundation/ReceiverCodeCost` in natural units (`neckProduction_eq_edgeCode`),
   the same term `Aeon/Production/PathReversal.epochProduction_eq_edgeCode` sums.
2. **The two-cell exchange is a one-junction neck.** The production of
   `Physics/TwoCellEntropyTransport` is `neckProduction` over one junction with `J₊ = κa`,
   `J₋ = κb` (`twoCell_is_neck`, rational `κ, a, b > 0`): the flux times the log-ratio drop.
3. **A neck inside a chain.** For a finite chain with law `π` and a section `A`, the epoch
   production of `PathReversal` splits exactly into the production across the cut between `A` and
   its complement and half the production inside each side
   (`epochProduction_eq_cut_add_interior`). So the cut's production is at most the epoch
   production (`cutProduction_le_epochProduction`), with equality exactly when every junction
   inside either side is balanced (`cutProduction_eq_epochProduction_iff`).

No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Thermal.Schnakenberg

open Finset Holonics.Foundation.ReceiverCodeCost Holonics.Aeon.Production.PathReversal

/-! ## 1. One junction: the rational certificate and its log face -/

/-- [definition] **The rational sign certificate** of a junction: `(J₊ − J₋)(J₊/J₋ − 1)`. -/
def certificate (f b : ℚ) : ℚ := (f - b) * (f / b - 1)

theorem certificate_eq {f b : ℚ} (hb : b ≠ 0) : certificate f b = (f - b) ^ 2 / b := by
  unfold certificate; field_simp

theorem certificate_nonneg {f b : ℚ} (hb : 0 < b) : 0 ≤ certificate f b := by
  rw [certificate_eq hb.ne']; positivity

/-- [proved-derived; formal-checked] The certificate vanishes exactly on a balanced junction. -/
theorem certificate_eq_zero_iff {f b : ℚ} (hb : 0 < b) : certificate f b = 0 ↔ f = b := by
  rw [certificate_eq hb.ne', div_eq_zero_iff, or_iff_left hb.ne', pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]

/-- [definition] **The production of one junction**, `(J₊ − J₋) log(J₊/J₋)`: the exact net
current times the log face of the exact flow ratio. -/
noncomputable def term (f b : ℚ) : ℝ := ((f - b : ℚ) : ℝ) * Real.log ((f / b : ℚ) : ℝ)

theorem term_eq_edgeCode {f b : ℚ} (hf : 0 < f) (hb : 0 < b) :
    term f b = Real.log 2 * edgeCodeProduction f b := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold term edgeCodeProduction
  push_cast
  rw [Real.log_div hf'.ne' hb'.ne']
  have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-- [proved-derived; formal-checked] A junction's production is nonnegative. -/
theorem term_nonneg {f b : ℚ} (hf : 0 < f) (hb : 0 < b) : 0 ≤ term f b := by
  rw [term_eq_edgeCode hf hb]
  exact mul_nonneg (Real.log_pos (by norm_num)).le
    (edgeCodeProduction_nonnegative (by exact_mod_cast hf) (by exact_mod_cast hb))

/-- [proved-derived; formal-checked] **A junction produces nothing exactly when it is balanced**,
which the rational certificate decides. -/
theorem term_eq_zero_iff {f b : ℚ} (hf : 0 < f) (hb : 0 < b) : term f b = 0 ↔ f = b := by
  rw [term_eq_edgeCode hf hb, mul_eq_zero, or_iff_right (Real.log_pos (by norm_num)).ne',
    RealChart.edgeCodeProduction_eq_zero_iff (by exact_mod_cast hf) (by exact_mod_cast hb)]
  exact_mod_cast Iff.rfl

/-- [proved-derived; formal-checked] **The log face has the certificate's sign**: the junction
produces exactly when its rational certificate is positive. -/
theorem term_pos_iff_certificate_pos {f b : ℚ} (hf : 0 < f) (hb : 0 < b) :
    0 < term f b ↔ 0 < certificate f b := by
  rw [(term_nonneg hf hb).lt_iff_ne, (certificate_nonneg hb).lt_iff_ne, ne_comm, ne_comm (a := 0),
    Ne, Ne, term_eq_zero_iff hf hb, certificate_eq_zero_iff hb]

/-! ## 2. The neck -/

variable {ι : Type*}

/-- [definition] **Schnakenberg's production across a neck.** -/
noncomputable def neckProduction (N : Finset ι) (Jf Jb : ι → ℚ) : ℝ := ∑ e ∈ N, term (Jf e) (Jb e)

/-- [proved-derived; formal-checked] The neck production is the edge code production in natural
units. -/
theorem neckProduction_eq_edgeCode (N : Finset ι) {Jf Jb : ι → ℚ} (hf : ∀ e, 0 < Jf e)
    (hb : ∀ e, 0 < Jb e) :
    neckProduction N Jf Jb = Real.log 2 * ∑ e ∈ N, edgeCodeProduction (Jf e) (Jb e) := by
  unfold neckProduction
  rw [mul_sum]
  exact sum_congr rfl fun e _ => term_eq_edgeCode (hf e) (hb e)

/-- [proved-derived; formal-checked] **`σ ≥ 0`.** -/
theorem neckProduction_nonneg (N : Finset ι) {Jf Jb : ι → ℚ} (hf : ∀ e, 0 < Jf e)
    (hb : ∀ e, 0 < Jb e) : 0 ≤ neckProduction N Jf Jb :=
  sum_nonneg fun e _ => term_nonneg (hf e) (hb e)

/-- [proved-derived; formal-checked] **`σ = 0` exactly when the neck is balanced.** -/
theorem neckProduction_eq_zero_iff (N : Finset ι) {Jf Jb : ι → ℚ} (hf : ∀ e, 0 < Jf e)
    (hb : ∀ e, 0 < Jb e) : neckProduction N Jf Jb = 0 ↔ ∀ e ∈ N, Jf e = Jb e := by
  unfold neckProduction
  rw [sum_eq_zero_iff_of_nonneg fun e _ => term_nonneg (hf e) (hb e)]
  exact forall₂_congr fun e _ => term_eq_zero_iff (hf e) (hb e)

/-! ## 3. The two-cell exchange is a one-junction neck -/

/-- [proved-derived; formal-checked] **The two-cell production is a one-junction neck**: for
rational `κ, a, b > 0`, the flux of `Physics/TwoCellEntropyTransport` times the log-ratio drop is
`neckProduction` over the single junction with `J₊ = κa`, `J₋ = κb` (the conductance cancels in
the flow ratio). -/
theorem twoCell_is_neck {κ a b : ℚ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    TwoCellEntropyTransport.flux κ a b * (Real.log a - Real.log b) =
      neckProduction ({()} : Finset Unit) (fun _ => κ * a) (fun _ => κ * b) := by
  have hκ' : (κ : ℝ) ≠ 0 := by exact_mod_cast hκ.ne'
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold neckProduction term TwoCellEntropyTransport.flux
  rw [Finset.sum_singleton]
  push_cast
  rw [mul_div_mul_left _ _ hκ', Real.log_div ha'.ne' hb'.ne']
  ring

/-! ## 4. A neck inside a chain -/

section Chain

variable {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ} {P : S → S → ℝ}

/-- [definition] The production of the ordered pair `(x, y)` of a chain, in natural units. -/
noncomputable def pairProduction (π : S → ℝ) (P : S → S → ℝ) (x y : S) : ℝ :=
  Real.log 2 * edgeCodeProduction (flow π P x y) (flow π P y x)

omit [Fintype S] [DecidableEq S] in
theorem pairProduction_swap (x y : S) : pairProduction π P x y = pairProduction π P y x := by
  unfold pairProduction; rw [edgeCodeProduction_swap]

omit [Fintype S] [DecidableEq S] in
theorem pairProduction_nonneg (hA : Admissible π P) (x y : S) : 0 ≤ pairProduction π P x y :=
  mul_nonneg (Real.log_pos (by norm_num)).le (RealChart.edgeCode_nonneg hA x y)

/-- [definition] **The production across the cut** between a section `A` and its complement. -/
noncomputable def cutProduction (π : S → ℝ) (P : S → S → ℝ) (A : Finset S) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ Aᶜ, pairProduction π P x y

/-- [definition] The production inside the two sides of the cut. -/
noncomputable def interiorProduction (π : S → ℝ) (P : S → S → ℝ) (A : Finset S) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ A, pairProduction π P x y + ∑ x ∈ Aᶜ, ∑ y ∈ Aᶜ, pairProduction π P x y

/-- [proved-derived; formal-checked] **The epoch production splits at a cut**: the production
across the cut plus half the production inside its two sides. -/
theorem epochProduction_eq_cut_add_interior (hA : Admissible π P) (A : Finset S) :
    RealChart.epochProduction π P = cutProduction π P A + (1 / 2) * interiorProduction π P A := by
  rw [RealChart.epochProduction_eq_edgeCode hA]
  have hfull : Real.log 2 / 2 * ∑ x, ∑ y, edgeCodeProduction (flow π P x y) (flow π P y x) =
      (1 / 2) * ∑ x, ∑ y, pairProduction π P x y := by
    unfold pairProduction; simp only [← mul_sum]; ring
  have hrow : ∀ x, ∑ y, pairProduction π P x y =
      ∑ y ∈ A, pairProduction π P x y + ∑ y ∈ Aᶜ, pairProduction π P x y :=
    fun x => (sum_add_sum_compl A _).symm
  have hcross : ∑ x ∈ Aᶜ, ∑ y ∈ A, pairProduction π P x y = cutProduction π P A := by
    unfold cutProduction
    rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => pairProduction_swap x y
  rw [hfull, ← sum_add_sum_compl A (fun x => ∑ y, pairProduction π P x y)]
  simp only [hrow, sum_add_distrib]
  rw [hcross]
  unfold interiorProduction cutProduction
  ring

theorem interiorProduction_nonneg (hA : Admissible π P) (A : Finset S) :
    0 ≤ interiorProduction π P A :=
  add_nonneg (sum_nonneg fun x _ => sum_nonneg fun y _ => pairProduction_nonneg hA x y)
    (sum_nonneg fun x _ => sum_nonneg fun y _ => pairProduction_nonneg hA x y)

/-- [proved-derived; formal-checked] **The production across a cut is at most the epoch
production.** -/
theorem cutProduction_le_epochProduction (hA : Admissible π P) (A : Finset S) :
    cutProduction π P A ≤ RealChart.epochProduction π P := by
  rw [epochProduction_eq_cut_add_interior hA A]
  have := interiorProduction_nonneg hA A
  linarith

omit [Fintype S] [DecidableEq S] in
/-- The production of an ordered pair vanishes exactly when the pair is balanced. -/
theorem pairProduction_eq_zero_iff (hA : Admissible π P) (x y : S) :
    pairProduction π P x y = 0 ↔ flow π P x y = flow π P y x := by
  unfold pairProduction
  rw [mul_eq_zero, or_iff_right (Real.log_pos (by norm_num)).ne']
  rcases (flow_nonneg hA x y).eq_or_lt with h0 | hpos
  · rw [← h0, flow_zero_of_zero hA h0.symm]; simp [edgeCodeProduction]
  · exact RealChart.edgeCodeProduction_eq_zero_iff hpos (flow_support hA hpos)

/-- [proved-derived; formal-checked] **The cut carries the whole epoch production exactly when
every junction inside either side is balanced.** -/
theorem cutProduction_eq_epochProduction_iff (hA : Admissible π P) (A : Finset S) :
    cutProduction π P A = RealChart.epochProduction π P ↔
      ∀ x y, (x ∈ A ↔ y ∈ A) → flow π P x y = flow π P y x := by
  rw [epochProduction_eq_cut_add_interior hA A]
  have hnn := fun x y => pairProduction_nonneg hA (π := π) (P := P) x y
  have hin : (∑ x ∈ A, ∑ y ∈ A, pairProduction π P x y = 0 ↔
      ∀ x ∈ A, ∀ y ∈ A, pairProduction π P x y = 0) := by
    rw [sum_eq_zero_iff_of_nonneg fun x _ => sum_nonneg fun y _ => hnn x y]
    exact forall₂_congr fun x _ => sum_eq_zero_iff_of_nonneg fun y _ => hnn x y
  have hout : (∑ x ∈ Aᶜ, ∑ y ∈ Aᶜ, pairProduction π P x y = 0 ↔
      ∀ x ∈ Aᶜ, ∀ y ∈ Aᶜ, pairProduction π P x y = 0) := by
    rw [sum_eq_zero_iff_of_nonneg fun x _ => sum_nonneg fun y _ => hnn x y]
    exact forall₂_congr fun x _ => sum_eq_zero_iff_of_nonneg fun y _ => hnn x y
  have h1 : 0 ≤ ∑ x ∈ A, ∑ y ∈ A, pairProduction π P x y :=
    sum_nonneg fun x _ => sum_nonneg fun y _ => hnn x y
  have h2 : 0 ≤ ∑ x ∈ Aᶜ, ∑ y ∈ Aᶜ, pairProduction π P x y :=
    sum_nonneg fun x _ => sum_nonneg fun y _ => hnn x y
  constructor
  · intro heq x y hxy
    have hzero : interiorProduction π P A = 0 := by linarith
    unfold interiorProduction at hzero
    have hA0 : ∑ x ∈ A, ∑ y ∈ A, pairProduction π P x y = 0 := by linarith
    have hB0 : ∑ x ∈ Aᶜ, ∑ y ∈ Aᶜ, pairProduction π P x y = 0 := by linarith
    rw [← pairProduction_eq_zero_iff hA]
    by_cases hx : x ∈ A
    · exact hin.mp hA0 x hx y (hxy.mp hx)
    · have hy : y ∉ A := fun hy => hx (hxy.mpr hy)
      exact hout.mp hB0 x (mem_compl.mpr hx) y (mem_compl.mpr hy)
  · intro hbal
    have hA0 : ∑ x ∈ A, ∑ y ∈ A, pairProduction π P x y = 0 :=
      hin.mpr fun x hx y hy => (pairProduction_eq_zero_iff hA x y).mpr
        (hbal x y ⟨fun _ => hy, fun _ => hx⟩)
    have hB0 : ∑ x ∈ Aᶜ, ∑ y ∈ Aᶜ, pairProduction π P x y = 0 :=
      hout.mpr fun x hx y hy => (pairProduction_eq_zero_iff hA x y).mpr
        (hbal x y ⟨fun h => absurd h (mem_compl.mp hx), fun h => absurd h (mem_compl.mp hy)⟩)
    unfold interiorProduction
    rw [hA0, hB0]
    ring

end Chain

section Audit

#print axioms certificate_eq_zero_iff
#print axioms term_pos_iff_certificate_pos
#print axioms neckProduction_eq_zero_iff
#print axioms twoCell_is_neck
#print axioms epochProduction_eq_cut_add_interior
#print axioms cutProduction_eq_epochProduction_iff

end Audit

end Holonics.Physics.Thermal.Schnakenberg
