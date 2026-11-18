import Mathlib

/-!
# The circle theorem for finitely many coupled locks (Lee and Yang, by Asano's contraction)

[definition] A finite family `V` of locks, each with two sheets, with a real symmetric coupling
`a i j` between locks `i` and `j`.  A configuration is the set `S` of locks on the raised sheet; it
is weighed by the couplings its cut crosses and by the fugacities of its raised locks:

  `lockPoly a z = ∑ S, (∏ i ∈ S, ∏ j ∈ Sᶜ, a i j) · ∏ i ∈ S, z i`.

For two locks with `a 0 1 = y` and a common fugacity `ζ` this is `1 + 2 y ζ + ζ²`
(`lockPoly_two`), the coupled-sheet polynomial of `Objects/ParametronLock`
(atlas `parametron.coupled-locks-lee-yang`).  For a ferromagnet, `a i j = exp (−2 β J i j)` with
`β J i j ≥ 0`, it is the partition function in the fugacity `ζ = exp (−2 β h)`, up to a monomial.

[proved-standard; formal-checked] What is proved here (Lee and Yang 1952; the proof is Asano's
contraction, 1970, in the form Ruelle gave it, 1971).  Throughout `−1 ≤ a i j ≤ 1` and
`a i j = a j i` for `i ≠ j`; the diagonal `a i i` never enters (`lockPoly_congr_offDiag`).

1. **The pair** (`pair_ne_zero`).  One coupled pair, `1 + a u + a v + u v`, has no zero with both
   fugacities inside the open unit disc: `|1 + a u|² − |a + u|² = (1 − a²)(1 − |u|²) ≥ 0`.
2. **The contraction** (`asano_contraction`).  If `α + β x + γ y + δ x y` has no zero on the open
   bidisc, then `α + δ t` has none on the open disc.  Two ports of one lock are joined into one:
   the mixed terms are dropped and the product `x y` becomes the lock's one fugacity.
3. **One contact** (`edge_update`, `edge_step_sum`, `genPoly_edge_step`).  If
   `A + B x + C y + D x y` has no zero on the open bidisc, neither has
   `A + a B x + a C y + D x y`.  The pair of item 1 is multiplied in on two fresh ports and each
   fresh port is contracted with its lock.  Read on configurations: weighing every configuration
   whose cut separates `i` from `j` by `a` keeps the polynomial free of zeros on the open polydisc.
4. **No zero inside** (`lockPoly_ne_zero_of_norm_lt_one`, `partialCoupling_ne_zero`).
   `|z i| < 1` for every lock gives `lockPoly a z ≠ 0`.  The induction is over the set of contacts
   switched on (`partialCoupling`), from the uncoupled product `∏ (1 + z i)` (`lockPoly_one`);
   switching on the contact `{i, j}` weighs the configurations whose cut separates `i` from `j` by
   `a i j`, once (`cutWeight_insert`).
5. **The reversal** (`lockPoly_reversal`, `lockPoly_ne_zero_of_one_lt_norm`).  Complementing the
   configuration, `S ↦ Sᶜ`, is the functional equation
   `lockPoly a z = (∏ z i) · conj (lockPoly a (1 / conj z))`, so there is no zero with every
   `|z i| > 1` either.
6. **The circle theorem** (`lockPoly_zero_on_circle`, `ferromagnet_zero_on_circle`,
   `two_locks_on_circle`).  With one common fugacity, `lockPoly a (fun _ => ζ) = 0` gives
   `|ζ| = 1`.  The couplings `exp (−2 β J i j)` of exchange energies `J i j ≥ 0` at `β ≥ 0` are an
   instance, and the tree's two coupled locks are the case of two.

[counterexample; formal-checked] **The bound on the coupling is load-bearing**
(`two_locks_off_circle_of_one_lt`).  Two locks with `y > 1` have the real zero `−y − √(y² − 1)`,
off the circle.

[interpretation] On the objects: the reversal (item 5) is the half-turn of every lock at once and
it exchanges the inside of the circle with its outside; the positivity that leaves no zero inside
(item 4) is the bound `|a| ≤ 1` of every contact, a contact that does not amplify.  A reversal and
a contraction place the zeros on the fixed circle of the reversal, which is the form of
`key.scaled-form-places-modes` on the machine's own locks.

**What this does not state.**  The theorem is for couplings in `[−1, 1]`; read through
`a = exp (−2 β J)` it covers `β J ≥ 0` (and the limit `a = 0`).  An antiferromagnetic contact,
`a > 1`, is outside it, as the counterexample shows.  Nothing is said about where on the circle
the zeros sit, their density, or a limit of many locks; the statement is for a finite family.  The
identity of `lockPoly` with a partition function is stated in this header only, and the join to
`Objects/ParametronLock` is by the polynomial `ζ² + 2 y ζ + 1`, which this module restates and
does not import.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Holonics.Coupling.LeeYangCircle

open Finset

/-! ## The pair, the contraction and one contact -/

section Analytic

/-- [proved-standard; formal-checked] `|1 + a u|² − |a + u|² = (1 − a²)(1 − |u|²)`. -/
theorem normSq_one_add_sub (a : ℝ) (u : ℂ) :
    Complex.normSq (1 + (a : ℂ) * u) - Complex.normSq ((a : ℂ) + u) =
      (1 - a ^ 2) * (1 - Complex.normSq u) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im]
  ring

/-- [proved-standard; formal-checked] **The pair.**  One coupled pair of locks with a coupling in
`[−1, 1]` has no zero with both fugacities in the open unit disc. -/
theorem pair_ne_zero (a : ℝ) (ha : -1 ≤ a) (ha' : a ≤ 1) (u v : ℂ) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    1 + (a : ℂ) * u + (a : ℂ) * v + u * v ≠ 0 := by
  intro h
  have h1 : 1 + (a : ℂ) * u = -(v * ((a : ℂ) + u)) := by linear_combination h
  have hle : ‖(a : ℂ) + u‖ ≤ ‖1 + (a : ℂ) * u‖ := by
    have hsq : Complex.normSq ((a : ℂ) + u) ≤ Complex.normSq (1 + (a : ℂ) * u) := by
      have := normSq_one_add_sub a u
      have h2 : 0 ≤ (1 - a ^ 2) * (1 - Complex.normSq u) := by
        apply mul_nonneg
        · nlinarith
        · have : Complex.normSq u ≤ 1 := by
            rw [← Complex.sq_norm]
            nlinarith [norm_nonneg u]
          linarith
      linarith
    rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have hnorm : ‖1 + (a : ℂ) * u‖ = ‖v‖ * ‖(a : ℂ) + u‖ := by
    rw [h1, norm_neg, norm_mul]
  rcases eq_or_lt_of_le (norm_nonneg ((a : ℂ) + u)) with h0 | hpos
  · -- `a + u = 0`: then `1 + a u = 0` and `u = −a`, so `a² = 1` and `|u| = 1`.
    have hau : (a : ℂ) + u = 0 := norm_eq_zero.mp h0.symm
    have hu' : u = -(a : ℂ) := by linear_combination hau
    have h3 : 1 + (a : ℂ) * u = 0 := by rw [h1, hau, mul_zero, neg_zero]
    rw [hu'] at h3
    have h4 : (1 : ℂ) - ((a ^ 2 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h3
    have h5 : (1 : ℝ) - a ^ 2 = 0 := by exact_mod_cast h4
    have h6 : ‖u‖ = |a| := by rw [hu', norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have h7 : |a| = 1 := by
      have : |a| ^ 2 = 1 := by rw [sq_abs]; linarith
      nlinarith [abs_nonneg a]
    rw [h6, h7] at hu
    exact lt_irrefl _ hu
  · have : ‖v‖ * ‖(a : ℂ) + u‖ < ‖(a : ℂ) + u‖ := by nlinarith
    linarith

/-- [proved-standard; formal-checked] **Asano's contraction.**  A polynomial of degree one in each
of two ports, free of zeros on the open bidisc, stays free of zeros on the open disc when the two
ports are joined into one: the mixed terms are dropped and `x y` becomes `t`. -/
theorem asano_contraction (α β γ δ : ℂ)
    (h : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 → α + β * x + γ * y + δ * x * y ≠ 0) :
    ∀ t : ℂ, ‖t‖ < 1 → α + δ * t ≠ 0 := by
  have hα : α ≠ 0 := by
    have := h 0 0 (by simp) (by simp)
    simpa using this
  have hδα : ‖δ‖ ≤ ‖α‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hδ : δ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      exact absurd hlt (not_lt.mpr (norm_nonneg α))
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim δ (β + γ) α)
    have hroot := quadratic_eq_zero_iff hδ hs
    set w₁ : ℂ := (-(β + γ) + s) / (2 * δ) with hw₁
    set w₂ : ℂ := (-(β + γ) - s) / (2 * δ) with hw₂
    have hprod : w₁ * w₂ = α / δ := by
      rw [hw₁, hw₂]
      have hs' : s * s = (β + γ) ^ 2 - 4 * δ * α := by rw [← hs, discrim]
      field_simp
      linear_combination -hs'
    have hnprod : ‖w₁‖ * ‖w₂‖ < 1 := by
      rw [← norm_mul, hprod, norm_div, div_lt_one (norm_pos_iff.mpr hδ)]
      exact hlt
    have hex : ‖w₁‖ < 1 ∨ ‖w₂‖ < 1 := by
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      nlinarith [hcon.1, hcon.2, norm_nonneg w₁, norm_nonneg w₂]
    rcases hex with hw | hw
    · have hz : δ * (w₁ * w₁) + (β + γ) * w₁ + α = 0 := (hroot w₁).mpr (Or.inl rfl)
      exact h w₁ w₁ hw hw (by linear_combination hz)
    · have hz : δ * (w₂ * w₂) + (β + γ) * w₂ + α = 0 := (hroot w₂).mpr (Or.inr rfl)
      exact h w₂ w₂ hw hw (by linear_combination hz)
  intro t ht h0
  have h1 : α = -(δ * t) := by linear_combination h0
  have h2 : ‖α‖ = ‖δ‖ * ‖t‖ := by rw [h1, norm_neg, norm_mul]
  have h3 : 0 < ‖α‖ := norm_pos_iff.mpr hα
  nlinarith [norm_nonneg δ, norm_nonneg t]

/-- [proved-standard; formal-checked] **One contact.**  If `A + B x + C y + D x y` has no zero on
the open bidisc, neither has `A + a B x + a C y + D x y` for a real coupling `a` in `[−1, 1]`:
the pair is multiplied in on two fresh ports and each fresh port is contracted with its lock. -/
theorem edge_update (A B C D : ℂ) (a : ℝ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (h : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 → A + B * x + C * y + D * x * y ≠ 0) :
    ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 → A + (a : ℂ) * B * x + (a : ℂ) * C * y + D * x * y ≠ 0 := by
  -- first contraction: the lock `x` with the fresh port `u`
  have step1 : ∀ y v t : ℂ, ‖y‖ < 1 → ‖v‖ < 1 → ‖t‖ < 1 →
      (A + C * y) * (1 + (a : ℂ) * v) + (B + D * y) * ((a : ℂ) + v) * t ≠ 0 := by
    intro y v t hy hv ht
    refine asano_contraction ((A + C * y) * (1 + (a : ℂ) * v)) ((B + D * y) * (1 + (a : ℂ) * v))
      ((A + C * y) * ((a : ℂ) + v)) ((B + D * y) * ((a : ℂ) + v)) ?_ t ht
    intro x u hx hu
    have h1 := h x y hx hy
    have h2 := pair_ne_zero a ha ha' u v hu hv
    have h3 := mul_ne_zero h1 h2
    intro h0
    apply h3
    linear_combination h0
  -- second contraction: the lock `y` with the fresh port `v`
  intro x y hx hy
  have := asano_contraction (A + (a : ℂ) * B * x) (C + (a : ℂ) * D * x)
    ((a : ℂ) * A + B * x) ((a : ℂ) * C + D * x) ?_ y hy
  · intro h0
    apply this
    linear_combination h0
  · intro y' v hy' hv
    have h1 := step1 y' v x hy' hv hx
    intro h0
    apply h1
    linear_combination h0

end Analytic

/-! ## Configurations -/

section Configurations

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [definition] A sum over configurations with a weight `w S` on the configuration `S` and the
fugacity `z i` on each raised lock. -/
def genPoly (w : Finset V → ℂ) (z : V → ℂ) : ℂ :=
  ∑ S : Finset V, w S * ∏ i ∈ S, z i

/-- [definition] **The lock polynomial.**  A configuration `S` is weighed by the couplings its cut
crosses, `∏ i ∈ S, ∏ j ∈ Sᶜ, a i j`, and by the fugacities of its raised locks. -/
def lockPoly (a : V → V → ℝ) (z : V → ℂ) : ℂ :=
  ∑ S : Finset V, (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, z i

theorem lockPoly_eq_genPoly (a : V → V → ℝ) (z : V → ℂ) :
    lockPoly a z = genPoly (fun S => ∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) z := rfl

/-- The four classes of configurations by two predicates: a sum weighed by `c` on the classes
where exactly one holds is `A + c B x + c C y + D x y`. -/
theorem sum_four_classes {ι : Type*} [Fintype ι] (g : ι → ℂ) (p q : ι → Prop) [DecidablePred p]
    [DecidablePred q] (c x y : ℂ) :
    ∑ s, g s * (if (p s ↔ q s) then 1 else c) * (if p s then x else 1) * (if q s then y else 1) =
      (∑ s, if ¬p s ∧ ¬q s then g s else 0) + c * (∑ s, if p s ∧ ¬q s then g s else 0) * x +
        c * (∑ s, if ¬p s ∧ q s then g s else 0) * y +
          (∑ s, if p s ∧ q s then g s else 0) * x * y := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hp : p s <;> by_cases hq : q s <;> simp [hp, hq, mul_comm]

/-- [proved-standard; formal-checked] **One contact, on a sum over classes.**  If the sum is free
of zeros on the open bidisc of the two marked fugacities, it stays free of zeros when every term
that one predicate marks and the other does not is weighed by a coupling in `[−1, 1]`. -/
theorem edge_step_sum {ι : Type*} [Fintype ι] (g : ι → ℂ) (p q : ι → Prop) [DecidablePred p]
    [DecidablePred q] (a : ℝ) (ha : -1 ≤ a) (ha' : a ≤ 1)
    (h : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 →
      ∑ s, g s * (if p s then x else 1) * (if q s then y else 1) ≠ 0) :
    ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 →
      ∑ s, g s * (if (p s ↔ q s) then 1 else (a : ℂ)) * (if p s then x else 1) *
        (if q s then y else 1) ≠ 0 := by
  intro x y hx hy
  rw [sum_four_classes]
  refine edge_update _ _ _ _ a ha ha' ?_ x y hx hy
  intro x' y' hx' hy'
  have h1 := h x' y' hx' hy'
  have h2 := sum_four_classes g p q 1 x' y'
  simp only [ite_self, mul_one, one_mul] at h2
  rwa [h2] at h1

omit [Fintype V] in
/-- A product over a configuration, with two distinct locks split off. -/
theorem prod_split_pair (S : Finset V) (f : V → ℂ) {i j : V} (hij : i ≠ j) :
    ∏ k ∈ S, f k =
      (if i ∈ S then f i else 1) * (if j ∈ S then f j else 1) *
        ∏ k ∈ (S.erase i).erase j, f k := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    rw [if_pos hi, if_pos hj, mul_assoc, Finset.mul_prod_erase _ _ hj',
      Finset.mul_prod_erase _ _ hi]
  · have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    rw [if_pos hi, if_neg hj, mul_one, Finset.erase_eq_of_notMem hj',
      Finset.mul_prod_erase _ _ hi]
  · have hj' : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    rw [if_neg hi, if_pos hj, one_mul, Finset.mul_prod_erase _ _ hj',
      Finset.erase_eq_of_notMem hi]
  · rw [if_neg hi, if_neg hj, one_mul, one_mul, Finset.erase_eq_of_notMem hi,
      Finset.erase_eq_of_notMem hj]

omit [Fintype V] in
/-- The same split with the two fugacities replaced. -/
theorem prod_update_pair (S : Finset V) (z : V → ℂ) {i j : V} (hij : i ≠ j) (x y : ℂ) :
    ∏ k ∈ S, Function.update (Function.update z i x) j y k =
      (if i ∈ S then x else 1) * (if j ∈ S then y else 1) *
        ∏ k ∈ (S.erase i).erase j, z k := by
  rw [prod_split_pair S _ hij, Function.update_self, Function.update_of_ne hij,
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  simp only [Finset.mem_erase] at hk
  rw [Function.update_of_ne hk.1, Function.update_of_ne hk.2.1]

/-- [proved-standard; formal-checked] **One contact, on configurations.**  If a weighed sum over
configurations has no zero on the open polydisc, it has none after every configuration whose cut
separates `i` from `j` is weighed by a coupling in `[−1, 1]`. -/
theorem genPoly_edge_step (w : Finset V → ℂ) {i j : V} (hij : i ≠ j) (a : ℝ) (ha : -1 ≤ a)
    (ha' : a ≤ 1) (h : ∀ z : V → ℂ, (∀ k, ‖z k‖ < 1) → genPoly w z ≠ 0) :
    ∀ z : V → ℂ, (∀ k, ‖z k‖ < 1) →
      genPoly (fun S => w S * (if (i ∈ S ↔ j ∈ S) then 1 else (a : ℂ))) z ≠ 0 := by
  intro z hz
  have hyp : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 →
      ∑ S : Finset V, (w S * ∏ k ∈ (S.erase i).erase j, z k) * (if i ∈ S then x else 1) *
        (if j ∈ S then y else 1) ≠ 0 := by
    intro x y hx hy
    have hupd : ∀ k, ‖Function.update (Function.update z i x) j y k‖ < 1 := by
      intro k
      by_cases hkj : k = j
      · rw [hkj, Function.update_self]
        exact hy
      · rw [Function.update_of_ne hkj]
        by_cases hki : k = i
        · rw [hki, Function.update_self]
          exact hx
        · rw [Function.update_of_ne hki]
          exact hz k
    have h1 := h _ hupd
    intro h0
    apply h1
    rw [← h0, genPoly]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [prod_update_pair S z hij]
    ring
  have key := edge_step_sum (fun S : Finset V => w S * ∏ k ∈ (S.erase i).erase j, z k)
    (fun S => i ∈ S) (fun S => j ∈ S) a ha ha' hyp (z i) (z j) (hz i) (hz j)
  intro h0
  apply key
  rw [← h0, genPoly]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_split_pair S z hij]
  ring

/-! ## The contacts switched on one at a time -/

/-- [definition] The coupling with only the contacts in `T` switched on; every other pair is
uncoupled (coupling one). -/
def partialCoupling (T : Finset (Sym2 V)) (a : V → V → ℝ) : V → V → ℝ :=
  fun i j => if s(i, j) ∈ T then a i j else 1

omit [Fintype V] in
theorem partialCoupling_empty (a : V → V → ℝ) :
    partialCoupling (∅ : Finset (Sym2 V)) a = fun _ _ => 1 := by
  funext i j
  simp [partialCoupling]

theorem partialCoupling_univ (a : V → V → ℝ) :
    partialCoupling (Finset.univ : Finset (Sym2 V)) a = a := by
  funext i j
  simp [partialCoupling]

/-- The weight of a cut reads only couplings between distinct locks. -/
theorem cutWeight_congr_offDiag {c c' : V → V → ℂ} (h : ∀ i j, i ≠ j → c i j = c' i j)
    (S : Finset V) : ∏ i ∈ S, ∏ j ∈ Sᶜ, c i j = ∏ i ∈ S, ∏ j ∈ Sᶜ, c' i j := by
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => h i j ?_
  rintro rfl
  exact (Finset.mem_compl.mp hj) hi

/-- [proved-derived; formal-checked] **The diagonal never enters.**  Two couplings that agree
between distinct locks have the same lock polynomial. -/
theorem lockPoly_congr_offDiag {a a' : V → V → ℝ} (h : ∀ i j, i ≠ j → a i j = a' i j)
    (z : V → ℂ) : lockPoly a z = lockPoly a' z := by
  unfold lockPoly
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [cutWeight_congr_offDiag (c := fun i j => (a i j : ℂ)) (c' := fun i j => (a' i j : ℂ))
    (fun i j hij => by rw [h i j hij]) S]

/-- [proved-standard; formal-checked] The uncoupled locks: the polynomial is the product of the
single locks' `1 + z i`. -/
theorem lockPoly_one (z : V → ℂ) : lockPoly (fun _ _ => (1 : ℝ)) z = ∏ i, (1 + z i) := by
  unfold lockPoly
  rw [Finset.prod_one_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp

theorem one_add_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro h
  have hz' : z = -1 := by linear_combination h
  rw [hz', norm_neg, norm_one] at hz
  exact lt_irrefl _ hz

omit [Fintype V] in
/-- A double product of a mark at one ordered pair. -/
theorem prod_prod_ite_pair (S U : Finset V) (i j : V) (t : ℂ) :
    ∏ k ∈ S, ∏ l ∈ U, (if k = i ∧ l = j then t else 1) = if i ∈ S ∧ j ∈ U then t else 1 := by
  have inner : ∀ k, ∏ l ∈ U, (if k = i ∧ l = j then t else 1) =
      if k = i then (if j ∈ U then t else 1) else 1 := by
    intro k
    by_cases hk : k = i
    · simp [hk, Finset.prod_ite_eq']
    · simp [hk]
  simp_rw [inner]
  rw [Finset.prod_ite_eq']
  by_cases hi : i ∈ S <;> simp [hi]

/-- [proved-derived; formal-checked] Switching on the contact `{i, j}` weighs every configuration
whose cut separates `i` from `j` by `a i j`, once. -/
theorem cutWeight_insert (T : Finset (Sym2 V)) (a : V → V → ℝ) {i j : V} (hij : i ≠ j)
    (hsym : a j i = a i j) (hT : s(i, j) ∉ T) (S : Finset V) :
    ∏ k ∈ S, ∏ l ∈ Sᶜ, ((partialCoupling (insert s(i, j) T) a k l : ℝ) : ℂ) =
      (∏ k ∈ S, ∏ l ∈ Sᶜ, ((partialCoupling T a k l : ℝ) : ℂ)) *
        (if (i ∈ S ↔ j ∈ S) then 1 else (a i j : ℂ)) := by
  have hpt : ∀ k l, ((partialCoupling (insert s(i, j) T) a k l : ℝ) : ℂ) =
      ((partialCoupling T a k l : ℝ) : ℂ) * ((if k = i ∧ l = j then (a i j : ℂ) else 1) *
        (if k = j ∧ l = i then (a i j : ℂ) else 1)) := by
    intro k l
    unfold partialCoupling
    by_cases h1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hT, hij]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        have hs : s(k, l) = s(l, k) := Sym2.eq_swap
        rw [hs]
        simp [hT, Ne.symm hij, hsym]
      · have hne : s(k, l) ≠ s(i, j) := by
          rw [Ne, Sym2.eq_iff]
          tauto
        simp [h1, h2, hne]
  simp_rw [hpt, Finset.prod_mul_distrib]
  rw [prod_prod_ite_pair, prod_prod_ite_pair]
  congr 1
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]

/-- [proved-standard; formal-checked] With any set `T` of contacts switched on, the lock
polynomial has no zero on the open polydisc.  Induction on `T`, one contact at a time. -/
theorem partialCoupling_ne_zero (a : V → V → ℝ) (hsymm : ∀ i j, i ≠ j → a i j = a j i)
    (hlo : ∀ i j, i ≠ j → -1 ≤ a i j) (hhi : ∀ i j, i ≠ j → a i j ≤ 1) (T : Finset (Sym2 V)) :
    ∀ z : V → ℂ, (∀ k, ‖z k‖ < 1) → lockPoly (partialCoupling T a) z ≠ 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro z hz
    rw [partialCoupling_empty, lockPoly_one]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => one_add_ne_zero_of_norm_lt_one (hz i)
  | insert e T he ih =>
    induction e using Sym2.ind with
    | _ i j =>
      by_cases hij : i = j
      · subst hij
        intro z hz
        have hcongr : ∀ k l, k ≠ l →
            partialCoupling (insert s(i, i) T) a k l = partialCoupling T a k l := by
          intro k l hkl
          unfold partialCoupling
          have hne : s(k, l) ≠ s(i, i) := by
            rw [Ne, Sym2.eq_iff]
            rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hkl rfl
          simp [hne]
        rw [lockPoly_congr_offDiag hcongr]
        exact ih z hz
      · intro z hz
        have step := genPoly_edge_step
          (fun S => ∏ k ∈ S, ∏ l ∈ Sᶜ, ((partialCoupling T a k l : ℝ) : ℂ)) hij (a i j)
          (hlo i j hij) (hhi i j hij) ih z hz
        have heq : lockPoly (partialCoupling (insert s(i, j) T) a) z =
            genPoly (fun S => (∏ k ∈ S, ∏ l ∈ Sᶜ, ((partialCoupling T a k l : ℝ) : ℂ)) *
              (if (i ∈ S ↔ j ∈ S) then 1 else ((a i j : ℝ) : ℂ))) z := by
          unfold lockPoly genPoly
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [cutWeight_insert T a hij (hsymm j i (Ne.symm hij)) he S]
        rw [heq]
        exact step

/-! ## The circle theorem -/

/-- [proved-standard; formal-checked] **No zero inside** (Lee and Yang 1952; Asano 1970).  For a
symmetric coupling in `[−1, 1]` the lock polynomial has no zero with every fugacity in the open
unit disc. -/
theorem lockPoly_ne_zero_of_norm_lt_one (a : V → V → ℝ) (hsymm : ∀ i j, i ≠ j → a i j = a j i)
    (hlo : ∀ i j, i ≠ j → -1 ≤ a i j) (hhi : ∀ i j, i ≠ j → a i j ≤ 1) (z : V → ℂ)
    (hz : ∀ i, ‖z i‖ < 1) : lockPoly a z ≠ 0 := by
  have h := partialCoupling_ne_zero a hsymm hlo hhi Finset.univ z hz
  rwa [partialCoupling_univ] at h

/-- The weight of a cut is the weight of the complementary cut, for a symmetric coupling. -/
theorem cutWeight_compl (a : V → V → ℝ) (hsymm : ∀ i j, i ≠ j → a i j = a j i) (S : Finset V) :
    ∏ i ∈ Sᶜ, ∏ j ∈ Sᶜᶜ, (a i j : ℂ) = ∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ) := by
  rw [compl_compl, Finset.prod_comm]
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
  rw [hsymm j i ?_]
  rintro rfl
  exact (Finset.mem_compl.mp hj) hi

/-- [proved-standard; formal-checked] **The reversal.**  Complementing the configuration is the
functional equation of the lock polynomial: the half-turn of every lock at once exchanges the
inside of the unit circle with its outside. -/
theorem lockPoly_reversal (a : V → V → ℝ) (hsymm : ∀ i j, i ≠ j → a i j = a j i) (z : V → ℂ)
    (hz : ∀ i, z i ≠ 0) :
    lockPoly a z =
      (∏ i, z i) * (starRingEnd ℂ) (lockPoly a (fun i => 1 / (starRingEnd ℂ) (z i))) := by
  unfold lockPoly
  rw [map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (compl_involutive.toPerm (compl : Finset V → Finset V)) _ _ ?_
  intro S
  simp only [Function.Involutive.coe_toPerm, map_mul, map_prod, map_div₀, map_one,
    Complex.conj_ofReal, Complex.conj_conj]
  rw [cutWeight_compl a hsymm S, ← Finset.prod_mul_prod_compl S z]
  have hone : (∏ i ∈ Sᶜ, z i) * ∏ i ∈ Sᶜ, (1 / z i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_one_div_cancel (hz i)
  linear_combination
    -((∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, z i) * hone

/-- [proved-standard; formal-checked] **No zero outside.**  By the reversal, the lock polynomial
has no zero with every fugacity outside the closed unit disc. -/
theorem lockPoly_ne_zero_of_one_lt_norm (a : V → V → ℝ) (hsymm : ∀ i j, i ≠ j → a i j = a j i)
    (hlo : ∀ i j, i ≠ j → -1 ≤ a i j) (hhi : ∀ i j, i ≠ j → a i j ≤ 1) (z : V → ℂ)
    (hz : ∀ i, 1 < ‖z i‖) : lockPoly a z ≠ 0 := by
  have hz0 : ∀ i, z i ≠ 0 := fun i => norm_pos_iff.mp (lt_trans zero_lt_one (hz i))
  rw [lockPoly_reversal a hsymm z hz0]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hz0 i) ?_
  rw [Ne, map_eq_zero]
  refine lockPoly_ne_zero_of_norm_lt_one a hsymm hlo hhi _ fun i => ?_
  rw [norm_div, norm_one, RCLike.norm_conj]
  exact (div_lt_one (lt_trans zero_lt_one (hz i))).mpr (hz i)

/-- [proved-standard; formal-checked] **The circle theorem** (Lee and Yang 1952).  With one common
fugacity, every zero of the lock polynomial of a symmetric coupling in `[−1, 1]` lies on the unit
circle. -/
theorem lockPoly_zero_on_circle (a : V → V → ℝ) (hsymm : ∀ i j, i ≠ j → a i j = a j i)
    (hlo : ∀ i j, i ≠ j → -1 ≤ a i j) (hhi : ∀ i j, i ≠ j → a i j ≤ 1) (ζ : ℂ)
    (h : lockPoly a (fun _ => ζ) = 0) : ‖ζ‖ = 1 := by
  rcases lt_trichotomy ‖ζ‖ 1 with hlt | heq | hgt
  · exact absurd h (lockPoly_ne_zero_of_norm_lt_one a hsymm hlo hhi _ fun _ => hlt)
  · exact heq
  · exact absurd h (lockPoly_ne_zero_of_one_lt_norm a hsymm hlo hhi _ fun _ => hgt)

/-- [proved-standard; formal-checked] **A ferromagnet's zeros lie on the circle.**  The couplings
`exp (−2 β J i j)` of exchange energies `J i j ≥ 0` at `β ≥ 0` lie in `(0, 1]`. -/
theorem ferromagnet_zero_on_circle (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i)
    (hJ0 : ∀ i j, 0 ≤ J i j) (β : ℝ) (hβ : 0 ≤ β) (ζ : ℂ)
    (h : lockPoly (fun i j => Real.exp (-2 * β * J i j)) (fun _ => ζ) = 0) : ‖ζ‖ = 1 := by
  refine lockPoly_zero_on_circle _ (fun i j _ => ?_) (fun i j _ => ?_) (fun i j _ => ?_) ζ h
  · rw [hJ i j]
  · exact le_trans (by norm_num) (Real.exp_pos _).le
  · rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hβ (hJ0 i j)]

end Configurations

/-! ## Two locks: the tree's coupled-sheet polynomial -/

section TwoLocks

/-- [proved-derived; formal-checked] For two locks the lock polynomial in a common fugacity is
`1 + (a 0 1 + a 1 0) ζ + ζ²`. -/
theorem lockPoly_two (a : Fin 2 → Fin 2 → ℝ) (ζ : ℂ) :
    lockPoly a (fun _ => ζ) = 1 + ((a 0 1 : ℂ) + (a 1 0 : ℂ)) * ζ + ζ ^ 2 := by
  unfold lockPoly
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have h0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  have h1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  have h01 : ({0, 1} : Finset (Fin 2))ᶜ = ∅ := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [h0, h1, h01]
  ring

/-- [proved-standard; formal-checked] The two coupled locks of `Objects/ParametronLock`
(atlas `parametron.coupled-locks-lee-yang`), as the two-lock case of the circle theorem:
`ζ² + 2 y ζ + 1 = 0` with `−1 ≤ y ≤ 1` gives `|ζ| = 1`. -/
theorem two_locks_on_circle (y : ℝ) (hy : -1 ≤ y) (hy' : y ≤ 1) (ζ : ℂ)
    (h : ζ ^ 2 + 2 * (y : ℂ) * ζ + 1 = 0) : ‖ζ‖ = 1 := by
  refine lockPoly_zero_on_circle (V := Fin 2) (fun _ _ => y) (fun _ _ _ => rfl)
    (fun _ _ _ => hy) (fun _ _ _ => hy') ζ ?_
  rw [lockPoly_two]
  linear_combination h

/-- [counterexample; formal-checked] **The bound on the coupling is load-bearing.**  Two locks
with a coupling `y > 1` (an antiferromagnetic contact) have a zero off the unit circle: the real
zero `−y − √(y² − 1)`. -/
theorem two_locks_off_circle_of_one_lt (y : ℝ) (hy : 1 < y) :
    ∃ ζ : ℂ, ζ ^ 2 + 2 * (y : ℂ) * ζ + 1 = 0 ∧ ‖ζ‖ ≠ 1 := by
  have hr : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ Real.sqrt (y ^ 2 - 1) := Real.sqrt_nonneg _
  refine ⟨((-y - Real.sqrt (y ^ 2 - 1) : ℝ) : ℂ), ?_, ?_⟩
  · have h : (-y - Real.sqrt (y ^ 2 - 1)) ^ 2 + 2 * y * (-y - Real.sqrt (y ^ 2 - 1)) + 1 = 0 := by
      nlinarith
    exact_mod_cast h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    intro h
    linarith

end TwoLocks

section Audit

#print axioms pair_ne_zero
#print axioms asano_contraction
#print axioms edge_update
#print axioms edge_step_sum
#print axioms genPoly_edge_step
#print axioms cutWeight_insert
#print axioms partialCoupling_ne_zero
#print axioms lockPoly_one
#print axioms lockPoly_congr_offDiag
#print axioms lockPoly_ne_zero_of_norm_lt_one
#print axioms lockPoly_reversal
#print axioms lockPoly_ne_zero_of_one_lt_norm
#print axioms lockPoly_zero_on_circle
#print axioms ferromagnet_zero_on_circle
#print axioms lockPoly_two
#print axioms two_locks_on_circle
#print axioms two_locks_off_circle_of_one_lt

end Audit

end Holonics.Coupling.LeeYangCircle
