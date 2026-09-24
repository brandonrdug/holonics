import Holonics.Objects.Deposition

/-!
# The minimal retention of a depositing medium

[definition] Object 8 of `docs/ELEMENTARY_OBJECTS.md` with `Foundation/Standing.lean`: retention
is the future-sufficient quotient of the present, never a record of what shaped it.
`Objects/Deposition` proved that the constitution is a lawful retention (`constitutionStanding`)
and that it is not minimal: on the parallel pair under the square law, `(1,1)` and `(2,2)` have
identical futures (`constitution_is_not_minimal`). This module finds the minimal retention.

[proved-derived; formal-checked] What is proved.

1. **The exact future-agreement relation on the parallel pair.** Under the square law
   `Γ_e = j_e²`, two presents have identical admitted futures, for every solver, **iff** their
   constitutions are equal or both symmetric (`parallel_futureAgreement_iff`). The separation is
   explicit: unequal shares `Θ₀/(Θ₀+Θ₁)` are separated by one unit source; equal shares `r ≠ 1/2`
   with unequal totals `T ≠ T'` are separated by one unit source after one unit stroke, since the
   new shares differ by a factor `r (T − T')(2r − 1)(r − 1)` (`stroke_separates_equal_shares`).
2. **The minimal retention.** `minimalRetain` retains `none` for a symmetric constitution and the
   constitution itself otherwise. Its kernel is exactly future agreement
   (`minimalRetain_eq_iff_futureAgreement`); it carries a lawful `StandingLaw`
   (`minimalStanding_exists`, via `Standing.standingLaw_exists_iff_future_factors`); and it is the
   **least** such retention: every retention carrying a `StandingLaw` for the same medium refines
   it (`minimalRetain_factors_through_every_standing`). The constitution is sufficient but
   collapses only on the symmetric class.
3. **General weighted graphs: the solve sees the projective class.** On any incidence, scaling the
   constitution by `c > 0` leaves every present observation unchanged
   (`observeConstitution_scale`): the one-step invariant of the solve is the projective class of
   `Θ`. It is not future-sufficient for the square law: `(1,2)` and `(2,4)` are projectively
   equal, agree on every present source, and are separated after one stroke
   (`projective_class_is_not_a_retention`), because the square law does not commute with scaling.

[open] The minimal retention for the square law on a general weighted graph (the orbit structure
of deposition on projective classes beyond two parallel edges), and for other deposition laws.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.Retention

open Holonics
open Holonics.Objects.Deposition
open Holonics.Foundation.Standing
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Millennium.Chronology
open Matrix

/-! ## 1. The unit source on the parallel pair -/

/-- [definition] The total conductance of a parallel-pair constitution. -/
def total (Θ : Constitution 2) : ℚ := Θ.1 0 + Θ.1 1

theorem total_pos (Θ : Constitution 2) : 0 < total Θ := add_pos (Θ.2 0) (Θ.2 1)

/-- [definition] The unit-source potential `(0, 1/T)`. -/
def unitPotential (Θ : Constitution 2) : Fin 2 → ℚ := ![0, 1 / total Θ]

theorem solves_unitPotential (Θ : Constitution 2) :
    Solves parallel Θ (unitPotential Θ) unitSource := by
  rw [parallel_solves_iff]
  have := (total_pos Θ).ne'
  simp only [unitPotential, total] at this ⊢
  simp
  field_simp

/-- [proved-derived; formal-checked] The unit source splits in proportion to the conductances. -/
theorem flux_unitPotential (Θ : Constitution 2) :
    flux parallel Θ (unitPotential Θ) = ![Θ.1 0 / total Θ, Θ.1 1 / total Θ] := by
  have := (total_pos Θ).ne'
  funext e
  fin_cases e <;> simp [flux, parallel, unitPotential, mulVec, dotProduct] <;> field_simp

/-- [proved-derived; formal-checked] Every solver reads the proportional split. -/
theorem observe_unit (S : Solver parallel) (state : DepositState 2) :
    observe S unitSource state =
      some ![state.constitution.1 0 / total state.constitution,
        state.constitution.1 1 / total state.constitution] := by
  rw [observe_of_solves S (solves_unitPotential _), flux_unitPotential]

/-- [proved-derived; formal-checked] One unit stroke under the square law deposits the squared
shares. -/
theorem step_unit_constitution (S : Solver parallel) (state : DepositState 2) (e : Fin 2) :
    (step squareLaw S unitSource state).constitution.1 e =
      state.constitution.1 e + (state.constitution.1 e / total state.constitution) ^ 2 := by
  rw [step_of_solves squareLaw S (solves_unitPotential _)]
  simp only [deposit, squareLaw, flux_unitPotential]
  fin_cases e <;> simp

/-! ## 2. The exact future-agreement relation -/

/-- [proved-derived; formal-checked] Two symmetric constitutions have identical futures, for every
solver and every record (the argument of `constitution_is_not_minimal`, for every symmetric pair). -/
theorem symmetric_futureAgreement (S : Solver parallel) {left right : DepositState 2}
    (hl : Deposition.Symmetric left.constitution) (hr : Deposition.Symmetric right.constitution) :
    futureAgreement (observe S) (step squareLaw S) left right := by
  intro σ word
  rw [observe_eq_observeConstitution, observe_eq_observeConstitution,
    transportWord_constitution, transportWord_constitution,
    symmetric_observe (symmetric_transportWord hl word),
    symmetric_observe (symmetric_transportWord hr word)]

/-- [proved-derived; formal-checked] **Equal shares, unequal totals, not symmetric: one stroke
separates.** With `a = rT`, `a' = rT'`, the new shares are `(rT + r²)/(T + c)` and
`(rT' + r²)/(T' + c)` with `c = r² + (1 − r)²`, and they differ by
`r (T − T')(2r − 1)(r − 1) ≠ 0`. -/
theorem stroke_separates_equal_shares {a b a' b' : ℚ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a')
    (hb' : 0 < b') (hshare : a * (a' + b') = a' * (a + b)) (htotal : a + b ≠ a' + b')
    (hasym : a ≠ b) :
    (a + (a / (a + b)) ^ 2) / ((a + (a / (a + b)) ^ 2) + (b + (b / (a + b)) ^ 2)) ≠
      (a' + (a' / (a' + b')) ^ 2) / ((a' + (a' / (a' + b')) ^ 2) + (b' + (b' / (a' + b')) ^ 2)) := by
  set T := a + b with hT
  set T' := a' + b' with hT'
  have hTp : 0 < T := by positivity
  have hT'p : 0 < T' := by positivity
  set r := a / T with hr
  have har : a = r * T := by rw [hr]; field_simp
  have ha'r : a' = r * T' := by
    rw [hr]; field_simp; linarith
  have hbr : b = (1 - r) * T := by rw [sub_mul, one_mul, ← har]; linarith
  have hb'r : b' = (1 - r) * T' := by rw [sub_mul, one_mul, ← ha'r]; linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≠ 1 := by
    intro h; rw [h, sub_self, zero_mul] at hbr; linarith
  have hrhalf : 2 * r - 1 ≠ 0 := by
    intro h
    apply hasym
    rw [har, hbr]
    have : r = 1 / 2 := by linarith
    rw [this]; ring
  have hsq : a / T = r := rfl
  have hsq' : a' / T' = r := by rw [ha'r]; field_simp
  have hbq : b / T = 1 - r := by rw [hbr]; field_simp
  have hbq' : b' / T' = 1 - r := by rw [hb'r]; field_simp
  rw [hsq', hbq, hbq']
  intro h
  have hc : 0 < r ^ 2 + (1 - r) ^ 2 := by positivity
  have hden : a + r ^ 2 + (b + (1 - r) ^ 2) = T + (r ^ 2 + (1 - r) ^ 2) := by
    rw [hT]; ring
  have hden' : a' + r ^ 2 + (b' + (1 - r) ^ 2) = T' + (r ^ 2 + (1 - r) ^ 2) := by
    rw [hT']; ring
  rw [hden, hden', div_eq_div_iff (by positivity) (by positivity), har, ha'r] at h
  have key : r * (T - T') * (2 * r - 1) * (r - 1) = 0 := by linear_combination h
  have hTT : T - T' ≠ 0 := sub_ne_zero.mpr htotal
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hr0.ne' hTT) hrhalf) hr1' key

/-- [proved-derived; formal-checked] **The exact future-agreement relation.** Under the square
law on the parallel pair, two presents have identical admitted futures (for a given solver) iff
their constitutions are equal or both symmetric. -/
theorem parallel_futureAgreement_iff (S : Solver parallel) (left right : DepositState 2) :
    futureAgreement (observe S) (step squareLaw S) left right ↔
      left.constitution = right.constitution ∨
        (Deposition.Symmetric left.constitution ∧ Deposition.Symmetric right.constitution) := by
  constructor
  · intro h
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne, hsym⟩ := hcon
    set Θ := left.constitution with hΘ
    set Θ' := right.constitution with hΘ'
    have h0 := h unitSource []
    simp only [transportWord_nil, observe_unit] at h0
    have hfirst := congrFun (Option.some.inj h0) 0
    simp only [Matrix.cons_val_zero] at hfirst
    have hTp := total_pos Θ
    have hT'p := total_pos Θ'
    have hshare : Θ.1 0 * total Θ' = Θ'.1 0 * total Θ := by
      rw [div_eq_div_iff hTp.ne' hT'p.ne'] at hfirst; linarith
    have htotal : total Θ ≠ total Θ' := by
      intro ht
      apply hne
      apply Subtype.ext
      funext e
      have h0' : Θ.1 0 = Θ'.1 0 := by
        rw [ht] at hshare; exact mul_right_cancel₀ hT'p.ne' hshare
      fin_cases e
      · exact h0'
      · have : Θ.1 1 = total Θ - Θ.1 0 := by simp [total]
        have h' : Θ'.1 1 = total Θ' - Θ'.1 0 := by simp [total]
        simp only [Fin.mk_one]
        rw [this, h', ht, h0']
    have hasym : Θ.1 0 ≠ Θ.1 1 := by
      intro hs
      apply hsym
      refine ⟨hs, ?_⟩
      -- equal shares force the right constitution to be symmetric too
      unfold Deposition.Symmetric
      have h2 : Θ'.1 0 * (2 * Θ.1 0) = Θ.1 0 * (Θ'.1 0 + Θ'.1 1) := by
        have := hshare; simp only [total, ← hs] at this; linarith
      have hpos := Θ.2 0
      have : 2 * Θ'.1 0 = Θ'.1 0 + Θ'.1 1 := by
        apply mul_left_cancel₀ hpos.ne'; linarith
      linarith
    have h1 := h unitSource [unitSource]
    simp only [transportWord_cons, transportWord_nil, observe_unit] at h1
    have hfirst1 := congrFun (Option.some.inj h1) 0
    simp only [Matrix.cons_val_zero, total, step_unit_constitution] at hfirst1
    exact stroke_separates_equal_shares (Θ.2 0) (Θ.2 1) (Θ'.2 0) (Θ'.2 1)
      (by simpa [total] using hshare) (by simpa [total] using htotal) hasym hfirst1
  · rintro (h | ⟨hl, hr⟩)
    · exact equal_constitution_equal_future squareLaw S h
    · exact symmetric_futureAgreement S hl hr

/-! ## 3. The minimal retention -/

open Classical in
/-- [definition] **The minimal retention** of the square-law parallel pair: the symmetric class
collapses to one point; every other constitution is retained. -/
def minimalRetain (state : DepositState 2) : Option (Constitution 2) :=
  if Deposition.Symmetric state.constitution then none else some state.constitution

/-- [proved-derived; formal-checked] **The kernel of the minimal retention is future agreement.** -/
theorem minimalRetain_eq_iff_futureAgreement (S : Solver parallel) (left right : DepositState 2) :
    minimalRetain left = minimalRetain right ↔
      futureAgreement (observe S) (step squareLaw S) left right := by
  rw [parallel_futureAgreement_iff]
  unfold minimalRetain
  by_cases hl : Deposition.Symmetric left.constitution <;>
    by_cases hr : Deposition.Symmetric right.constitution <;>
    simp only [hl, hr, if_true, if_false, reduceCtorEq, Option.some.injEq, and_true,
      and_false, or_false, or_true, false_iff]
  · intro h; exact hr (h ▸ hl)
  · intro h; exact hl (h ▸ hr)

/-- [proved-derived; formal-checked] **The minimal retention is a lawful standing**, by
`Standing.standingLaw_exists_iff_future_factors`. -/
theorem minimalStanding_exists (S : Solver parallel) :
    ∃ L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState 2) (Option (Constitution 2))
        (Option (Fin 2 → ℚ)),
      L.transport = step squareLaw S ∧ L.observe = observe S ∧ L.retain = minimalRetain := by
  rw [standingLaw_exists_iff_future_factors]
  intro left right h
  exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
    ((minimalRetain_eq_iff_futureAgreement S left right).mp h)

/-- [proved-derived; formal-checked] **The minimal retention is least.** Every retention map that
carries a `StandingLaw` for the same medium refines it: equal retention forces equal minimal
retention. -/
theorem minimalRetain_factors_through_every_standing (S : Solver parallel) {Retained : Type*}
    (L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState 2) Retained (Option (Fin 2 → ℚ)))
    (htransport : L.transport = step squareLaw S) (hobserve : L.observe = observe S)
    {left right : DepositState 2} (h : L.retain left = L.retain right) :
    minimalRetain left = minimalRetain right := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact (minimalRetain_eq_iff_futureAgreement S left right).mpr hagree

/-- [counterexample; formal-checked] The minimal retention is strictly coarser than the
constitution and strictly finer than nothing: `(1,1)` and `(2,2)` merge, `(1,2)` and `(2,4)` do
not. -/
theorem minimalRetain_witness :
    minimalRetain ⟨Θone, []⟩ = minimalRetain ⟨Θtwo, []⟩ ∧ Θone ≠ Θtwo ∧
      minimalRetain ⟨Θ₀, []⟩ ≠
        minimalRetain ⟨⟨![2, 4], by intro e; fin_cases e <;> norm_num⟩, []⟩ := by
  refine ⟨?_, (constitution_is_not_minimal ⟨fun _ _ σ => canonicalSolve parallel _ σ,
    fun _ _ _ h => canonicalSolve_solves h⟩ [] []).1, ?_⟩
  · simp [minimalRetain, Deposition.Symmetric, Θone, Θtwo]
  · simp only [minimalRetain, Deposition.Symmetric, Θ₀]
    norm_num

/-! ## 4. General incidence: the solve sees the projective class -/

variable {p q : ℕ}

/-- [definition] Scale a constitution by a positive factor. -/
def scaleConstitution (c : ℚ) (hc : 0 < c) (Θ : Constitution q) : Constitution q :=
  ⟨fun e => c * Θ.1 e, fun e => mul_pos hc (Θ.2 e)⟩

theorem solves_scale_iff (d : Matrix (Fin q) (Fin p) ℚ) {c : ℚ} (hc : 0 < c) (Θ : Constitution q)
    (φ σ : Fin p → ℚ) :
    Solves d (scaleConstitution c hc Θ) φ σ ↔ Solves d Θ (c • φ) σ := by
  rw [solves_iff_boundary_flux, solves_iff_boundary_flux]
  have : flux d (scaleConstitution c hc Θ) φ = flux d Θ (c • φ) := by
    funext e; simp [flux, scaleConstitution, mulVec_smul]; ring
  rw [this]

/-- [proved-derived; formal-checked] **The present observation sees only the projective class of
the constitution**, on every incidence: scaling by `c > 0` changes no solvability and no flux. -/
theorem observeConstitution_scale (d : Matrix (Fin q) (Fin p) ℚ) {c : ℚ} (hc : 0 < c)
    (Θ : Constitution q) (σ : Fin p → ℚ) :
    observeConstitution d σ (scaleConstitution c hc Θ) = observeConstitution d σ Θ := by
  have hex : (∃ φ, Solves d (scaleConstitution c hc Θ) φ σ) ↔ ∃ φ, Solves d Θ φ σ := by
    constructor
    · rintro ⟨φ, h⟩; exact ⟨c • φ, (solves_scale_iff d hc Θ φ σ).mp h⟩
    · rintro ⟨φ, h⟩
      refine ⟨c⁻¹ • φ, (solves_scale_iff d hc Θ _ σ).mpr ?_⟩
      rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  by_cases h : ∃ φ, Solves d Θ φ σ
  · have h' := hex.mpr h
    rw [observeConstitution, if_pos h', observeConstitution, if_pos h]
    congr 1
    have hs := canonicalSolve_solves h'
    have hs' := (solves_scale_iff d hc Θ _ σ).mp hs
    rw [show flux d (scaleConstitution c hc Θ) (canonicalSolve d (scaleConstitution c hc Θ) σ) =
        flux d Θ (c • canonicalSolve d (scaleConstitution c hc Θ) σ) by
      funext e; simp [flux, scaleConstitution, mulVec_smul]; ring]
    exact flux_unique hs' (canonicalSolve_solves h)
  · rw [observeConstitution, if_neg (fun h' => h (hex.mp h')), observeConstitution, if_neg h]

/-- [counterexample; formal-checked] **The projective class is not a retention under the square
law.** `(1,2)` and `(2,4)` are projectively equal and agree on every present source, yet one
unit stroke separates them. -/
theorem projective_class_is_not_a_retention (S : Solver parallel) :
    let Θ₂ : Constitution 2 := ⟨![2, 4], by intro e; fin_cases e <;> norm_num⟩
    Θ₂ = scaleConstitution 2 two_pos Θ₀ ∧
      (∀ σ, observeConstitution parallel σ Θ₂ = observeConstitution parallel σ Θ₀) ∧
      ¬ futureAgreement (observe S) (step squareLaw S) ⟨Θ₀, []⟩ ⟨Θ₂, []⟩ := by
  intro Θ₂
  have hscale : Θ₂ = scaleConstitution 2 two_pos Θ₀ := by
    apply Subtype.ext; funext e; fin_cases e <;> norm_num [Θ₂, scaleConstitution, Θ₀]
  refine ⟨hscale, fun σ => by rw [hscale, observeConstitution_scale], ?_⟩
  rw [parallel_futureAgreement_iff]
  rintro (h | ⟨hl, -⟩)
  · have := congrArg (fun Θ : Constitution 2 => Θ.1 0) h
    norm_num [Θ₂, Θ₀] at this
  · norm_num [Deposition.Symmetric, Θ₀] at hl

section Audit
#print axioms flux_unitPotential
#print axioms observe_unit
#print axioms step_unit_constitution
#print axioms symmetric_futureAgreement
#print axioms stroke_separates_equal_shares
#print axioms parallel_futureAgreement_iff
#print axioms minimalRetain_eq_iff_futureAgreement
#print axioms minimalStanding_exists
#print axioms minimalRetain_factors_through_every_standing
#print axioms minimalRetain_witness
#print axioms observeConstitution_scale
#print axioms projective_class_is_not_a_retention
end Audit

end Holonics.Objects.Retention
