import Mathlib

/-!
# Rings ticking together close at their least common multiple; a carried cascade closes at their product

The winding guide (`docs/WINDING_CARRY_AND_PLACEMENT.md` §9, the [conditional] paragraph) states: "Simultaneous primitive
ring ticks close at their LCM; product is valid under pairwise coprimality. For `[7,11,33]` the LCM is `231`, whereas the
product is `2541`; `11` divides `33`, so these periods are not pairwise coprime. An HNN's carried clock cascade must be read
through its actual tick/carry law rather than ticking every ring once per cell." Its §10 says of the carried field face:
"It is not an independent simultaneous-tick model and its modulus is not an LCM." The chord record of November 10
(`research/records/2026-11-10_A_CHORD_IS_CIRCLES_CLOSING_AT_THEIR_LEAST_COMMON_MULTIPLE_…`, §2.3) reads the same rings as a
chord: periods 33, 7 and 11 close at `231 = 3·7·11`, and as frequencies of that closing cycle they are `7 : 33 : 21`.

This file states the two laws on one count and proves where they part.

[proved-standard; formal-checked] What is proved.

1. **Simultaneous ticks close at the least common multiple** (`diag`, `closing`, `nsmul_diag_eq_zero_iff`,
   `nsmul_diag_eq_iff`, `addOrderOf_diag`, `card_orbit`, `card_joint`): on `Π i, ZMod (n i)` the diagonal tick returns
   at `t` exactly when `closing n = lcm_i (n i)` divides `t`; two counts give one joint phase exactly when they agree
   modulo the closing; the tick's order is the closing, so it visits `closing n` of the `∏ n i` joint states.
2. **The closing is the product exactly under pairwise coprimality** (`lcm_mul_iff`, `finset_lcm_eq_prod_iff`,
   `closing_eq_prod_iff`, `zmultiples_diag_eq_top_iff`): for positive periods, `lcm = ∏` holds when and only when the
   periods are pairwise coprime, and that is when the diagonal visits every joint state. The guide's conditional is an
   equivalence. One direction is Mathlib's `Finset.lcm_eq_prod`; the two-ring case of the visit is
   `Geometry/PairResonance.diagonal_step_generates_the_coprime_torus`.
3. **A closing cycle's windings are jointly coprime** (`turns`, `period_mul_turns`, `turns_gcd_eq_one`): in one closing
   cycle ring `i` makes `closing n / n i` whole turns, and those counts have no common factor, so the rings read as
   frequencies of the closing cycle are a chord in lowest terms.
4. **The instance `7, 11, 33`** (`rings`, `closing_rings`, `prod_rings`, `factorizations`, `rings_not_pairwise_coprime`,
   `card_orbit_rings`, `card_joint_rings`, `diag_rings_not_top`, `chord_rings`): the closing is `231 = 3·7·11`, the product
   `2541 = 3·7·11² = 11·231`, `11 ∣ 33`; the diagonal reaches 231 of the 2541 joint states, one in eleven; the chord is
   `7 : 33 : 21` read against periods `33, 7, 11`, jointly coprime.
5. **The carried cascade closes at the product** (`digits`, `winding`, `value`, `value_digits`, `winding_eq`,
   `value_add_prod_mul_winding`, `digits_eq_iff`, `digits_add_iff`, `digits_cons_add_radix`, `digits_add_prod`,
   `winding_add_prod`): with mixed-radix digits (ring `k` ticks on the carry of the rings before it), two counts have one
   digit word exactly when they agree modulo the product of the radices, whatever factors the radices share;
   `count = value(digits) + (∏ radices) · winding`; one closing of the cascade returns the word and adds one winding.
6. **The two laws on one count** (`phases`, `lcmList`, `phases_eq_iff`, `lcmList_dvd_prod`, `lcmList_eq_prod_iff`,
   `digits_eq_imp_phases_eq`, `same_reading_iff`, `cascade_231_2541`): the residue word `t mod r_k` (every ring ticking
   once a cell) agrees on two counts exactly modulo the least common multiple, the digit word exactly modulo the product,
   the digit word always refines the residue word, and for positive radices the two words separate the same counts when
   and only when the radices are pairwise coprime. **The two laws differ exactly when two radices share a factor.** For
   `7, 11, 33` the residue word returns at 231 and the digit word first at 2541.

Limits. Periods are natural numbers and ticks are uniform: one count drives every ring. The carried cascade here is the
plain mixed-radix odometer; the HNN's field face (`Current::step`, `Odometer`, Lock and Own rings, class increments from the
field fits) is not modelled, and §10's statement about that face is cited, not proved. No claim is made about a pump, a
lock domain or a fluid reading (the guide's own cautions in the same paragraph). The chord reading is arithmetic on
periods; roughness and consonance are the chord record's interpretations and are not stated.

Existing owners, cited and not repeated: `Geometry/PhaseCarry` (`digits_succ`, `odometer_iterate`: the one-level odometer
and its carry cocycle); `Geometry/PairResonance.diagonal_step_generates_the_coprime_torus` (two coprime rings);
`HNN/Prediction.joint_residue_determines_position` (coprime frames meet once below their product);
`Mathematics/BaseAction` (agreement on every ring of a set of integers iff agreement modulo its `Finset.lcm`).

The computational object is the helical pair interaction: a set of rings on one count is a set of helices sharing a
parameter, their pairwise locks are the common factors, and the carried cascade is the helix's carry threading the rings.
Of the winding guide's six general objects this is the helix (circle + carry: `digits`, `winding`) and the pair (a torus
with a modular address: `diag`, `closing`); faces and placement, cell holonomy, the tube and the tower thread stay attached.

Consumers: the guide's §9 and §10 paragraphs; the chord record's §2.3; atlas `lock.coprime-torus-diagonal`,
`encoding.frame-explosion` and `winding.odometer`, which this file extends to several rings and to shared factors.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.RingClosure

/-! ## 1. Simultaneous ticks -/

section Simultaneous

variable {ι : Type*} [Fintype ι]

/-- [definition] **The diagonal tick**: every ring advances one place a cell. -/
def diag (n : ι → ℕ) : ∀ i, ZMod (n i) := fun _ => 1

/-- [definition] **The closing length** of rings ticking together: the least common multiple of their periods. -/
def closing (n : ι → ℕ) : ℕ := Finset.univ.lcm n

omit [Fintype ι] in
/-- [formal-checked] After `t` ticks ring `i` reads `t` on its own circle. -/
theorem nsmul_diag_apply (n : ι → ℕ) (t : ℕ) (i : ι) : (t • diag n) i = (t : ZMod (n i)) := by
  simp [diag]

/-- [proved-standard; formal-checked] **Simultaneous ticks return exactly at the multiples of the least common
multiple.** -/
theorem nsmul_diag_eq_zero_iff (n : ι → ℕ) (t : ℕ) : t • diag n = 0 ↔ closing n ∣ t := by
  rw [funext_iff]
  simp only [nsmul_diag_apply, Pi.zero_apply, ZMod.natCast_eq_zero_iff, closing, Finset.lcm_dvd_iff,
    Finset.mem_univ, true_implies]

/-- [proved-standard; formal-checked] **Two counts give one joint phase exactly when they agree modulo the closing.** -/
theorem nsmul_diag_eq_iff (n : ι → ℕ) (t t' : ℕ) :
    t • diag n = t' • diag n ↔ t ≡ t' [MOD closing n] := by
  rw [funext_iff]
  simp only [nsmul_diag_apply, ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd, closing]
  rw [Int.natCast_dvd]
  simp only [Finset.lcm_dvd_iff, Finset.mem_univ, true_implies, Int.natCast_dvd]

/-- [proved-standard; formal-checked] **The diagonal tick's order is the closing length.** -/
theorem addOrderOf_diag (n : ι → ℕ) : addOrderOf (diag n) = closing n := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_of_nsmul_eq_zero ((nsmul_diag_eq_zero_iff n _).mpr dvd_rfl)
  · exact (nsmul_diag_eq_zero_iff n _).mp (addOrderOf_nsmul_eq_zero _)

/-- [proved-standard; formal-checked] **The diagonal visits `closing n` joint states.** -/
theorem card_orbit (n : ι → ℕ) : Nat.card (AddSubgroup.zmultiples (diag n)) = closing n := by
  rw [Nat.card_zmultiples, addOrderOf_diag]

/-- [proved-standard; formal-checked] The joint states number the product of the periods. -/
theorem card_joint (n : ι → ℕ) : Nat.card (∀ i, ZMod (n i)) = ∏ i, n i := by
  simp [Nat.card_pi, Nat.card_zmod]

/-- [proved-standard; formal-checked] The closing length divides the product of the periods. -/
theorem closing_dvd_prod (n : ι → ℕ) : closing n ∣ ∏ i, n i :=
  Finset.lcm_dvd_prod _ _

end Simultaneous

/-! ## 2. The closing is the product exactly under pairwise coprimality -/

/-- [formal-checked] **The step of both inductions**: for `a > 0`, `P > 0` and `L ∣ P`, the least common multiple of `a`
and `L` is `a · P` exactly when `L = P` and `a` is coprime to `L`. -/
theorem lcm_mul_iff {a L P : ℕ} (ha : 0 < a) (hP : 0 < P) (hLP : L ∣ P) :
    Nat.lcm a L = a * P ↔ L = P ∧ Nat.Coprime a L := by
  constructor
  · intro h
    have hg := Nat.gcd_mul_lcm a L
    rw [h] at hg
    have hgP : Nat.gcd a L * P = L := by
      have : a * (Nat.gcd a L * P) = a * L := by rw [← hg]; ring
      exact Nat.eq_of_mul_eq_mul_left ha this
    have hLle : L ≤ P := Nat.le_of_dvd hP hLP
    have hgpos : 0 < Nat.gcd a L := Nat.gcd_pos_of_pos_left L ha
    have hg1 : Nat.gcd a L = 1 := by
      by_contra hne
      have h2 : 2 ≤ Nat.gcd a L := by omega
      have : 2 * P ≤ Nat.gcd a L * P := Nat.mul_le_mul_right P h2
      omega
    refine ⟨?_, hg1⟩
    rw [hg1, one_mul] at hgP
    exact hgP.symm
  · rintro ⟨rfl, hc⟩
    exact hc.lcm_eq_mul

/-- [proved-standard; formal-checked] **For positive periods the least common multiple is the product exactly when the
periods are pairwise coprime.** The direction from coprimality is Mathlib's `Finset.lcm_eq_prod`. -/
theorem finset_lcm_eq_prod_iff {ι : Type*} (s : Finset ι) (n : ι → ℕ) (hpos : ∀ i ∈ s, 0 < n i) :
    s.lcm n = ∏ i ∈ s, n i ↔ (s : Set ι).Pairwise (Nat.Coprime.onFun n) := by
  classical
  refine ⟨?_, Finset.lcm_eq_prod⟩
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro h
    have hposs : ∀ i ∈ s, 0 < n i := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
    have hPpos : 0 < ∏ i ∈ s, n i := Finset.prod_pos hposs
    rw [Finset.lcm_insert, Finset.prod_insert ha, lcm_eq_nat_lcm] at h
    obtain ⟨hL, hc⟩ :=
      (lcm_mul_iff (hpos a (Finset.mem_insert_self a s)) hPpos (Finset.lcm_dvd_prod s n)).mp h
    have hs := ih hposs hL
    rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hs, fun b hb _ => ?_⟩
    have hab : Nat.Coprime (n a) (n b) := Nat.Coprime.coprime_dvd_right (Finset.dvd_lcm hb) hc
    exact ⟨hab, hab.symm⟩

section Simultaneous

variable {ι : Type*} [Fintype ι]

/-- [proved-standard; formal-checked] **Rings ticking together close at the product of their periods exactly when the
periods are pairwise coprime.** -/
theorem closing_eq_prod_iff (n : ι → ℕ) (hpos : ∀ i, 0 < n i) :
    closing n = ∏ i, n i ↔ Pairwise (Nat.Coprime.onFun n) := by
  rw [closing, finset_lcm_eq_prod_iff _ _ (fun i _ => hpos i), Finset.coe_univ, Set.pairwise_univ]

/-- [proved-standard; formal-checked] **The diagonal visits every joint state exactly when the periods are pairwise
coprime**: the several-ring form of the coprime torus's diagonal, with its converse. -/
theorem zmultiples_diag_eq_top_iff (n : ι → ℕ) (hpos : ∀ i, 0 < n i) :
    AddSubgroup.zmultiples (diag n) = ⊤ ↔ Pairwise (Nat.Coprime.onFun n) := by
  have : ∀ i, NeZero (n i) := fun i => ⟨(hpos i).ne'⟩
  rw [← AddSubgroup.card_eq_iff_eq_top, card_orbit, card_joint, closing_eq_prod_iff n hpos]

/-- [definition] **The whole turns ring `i` makes in one closing cycle.** -/
def turns (n : ι → ℕ) (i : ι) : ℕ := closing n / n i

/-- [formal-checked] A ring's period times its turns is the closing length. -/
theorem period_mul_turns (n : ι → ℕ) (i : ι) : n i * turns n i = closing n :=
  Nat.mul_div_cancel' (Finset.dvd_lcm (Finset.mem_univ i))

/-- [proved-standard; formal-checked] **The rings' turns in one closing cycle are jointly coprime**: read as frequencies
of the closing cycle the rings are a chord in lowest terms. -/
theorem turns_gcd_eq_one [Nonempty ι] (n : ι → ℕ) (hpos : ∀ i, 0 < n i) :
    Finset.univ.gcd (turns n) = 1 := by
  set g := Finset.univ.gcd (turns n) with hg
  have hLpos : 0 < closing n :=
    Nat.pos_of_ne_zero (by
      rw [closing, Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨i, -, hi⟩
      exact (hpos i).ne' hi)
  have hgdvd : ∀ i, g ∣ turns n i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hgL : g ∣ closing n := (hgdvd i₀).trans ⟨n i₀, by rw [mul_comm, period_mul_turns]⟩
  obtain ⟨q, hq⟩ := hgL
  have hgpos : 0 < g := Nat.pos_of_ne_zero (by rintro h0; rw [h0, zero_mul] at hq; omega)
  -- every period divides `q = closing / g`
  have hdiv : ∀ i, n i ∣ q := by
    intro i
    obtain ⟨m, hm⟩ := hgdvd i
    have h1 : n i * (g * m) = g * q := by rw [← hm, period_mul_turns, hq]
    have h2 : g * (n i * m) = g * q := by rw [← h1]; ring
    exact ⟨m, (Nat.eq_of_mul_eq_mul_left hgpos h2).symm⟩
  have hLq : closing n ∣ q := Finset.lcm_dvd fun i _ => hdiv i
  rw [hq] at hLq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (by rintro h0; rw [h0, mul_zero] at hq; omega)
  have : g * q ≤ q := Nat.le_of_dvd hqpos hLq
  have : g * q ≤ 1 * q := by omega
  have : g ≤ 1 := Nat.le_of_mul_le_mul_right this hqpos
  omega

end Simultaneous

/-! ## 3. The instance `7, 11, 33` -/

/-- [definition] The guide's three rings, of periods 7, 11 and 33. -/
def rings : Fin 3 → ℕ := ![7, 11, 33]

/-- [formal-checked] Every period of the instance is positive. -/
theorem rings_pos : ∀ i, 0 < rings i := by decide

/-- [proved-standard; formal-checked] **Rings of periods 7, 11 and 33 ticking together close at 231.** -/
theorem closing_rings : closing rings = 231 := by
  have h : closing rings = Nat.lcm 7 (Nat.lcm 11 33) := by
    simp [closing, rings, Fin.univ_succ, Finset.lcm_insert, lcm_eq_nat_lcm]
  exact h.trans (by decide)

/-- [formal-checked] The product of the three periods is 2541. -/
theorem prod_rings : ∏ i, rings i = 2541 := by
  simp [rings, Fin.prod_univ_succ]

/-- [formal-checked] `231 = 3·7·11`, `2541 = 3·7·11²`, `2541 = 11·231`, and `11` divides `33`. -/
theorem factorizations :
    (231 : ℕ) = 3 * 7 * 11 ∧ (2541 : ℕ) = 3 * 7 * 11 ^ 2 ∧ (2541 : ℕ) = 11 * 231 ∧ (11 : ℕ) ∣ 33 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide⟩

/-- [formal-checked] The three periods are not pairwise coprime: 11 and 33 share 11. -/
theorem rings_not_pairwise_coprime : ¬ Pairwise (Nat.Coprime.onFun rings) := by
  intro h
  have := h (show (1 : Fin 3) ≠ 2 by decide)
  revert this
  decide

/-- [proved-standard; formal-checked] **The diagonal reaches 231 joint states.** -/
theorem card_orbit_rings : Nat.card (AddSubgroup.zmultiples (diag rings)) = 231 := by
  rw [card_orbit, closing_rings]

/-- [formal-checked] The joint states number 2541, so the diagonal reaches one in eleven. -/
theorem card_joint_rings : Nat.card (∀ i, ZMod (rings i)) = 2541 := by
  rw [card_joint, prod_rings]

/-- [formal-checked] The diagonal of the three rings does not visit every joint state. -/
theorem diag_rings_not_top : AddSubgroup.zmultiples (diag rings) ≠ ⊤ := fun h =>
  rings_not_pairwise_coprime ((zmultiples_diag_eq_top_iff rings rings_pos).mp h)

/-- [proved-standard; formal-checked] **The chord of the closing cycle**: against periods 33, 7 and 11 the rings turn 7, 33
and 21 times in the 231 ticks, and `7 : 33 : 21` is in lowest terms. -/
theorem chord_rings :
    231 / 33 = 7 ∧ 231 / 7 = 33 ∧ 231 / 11 = 21 ∧ Nat.gcd (Nat.gcd 7 33) 21 = 1 ∧
      turns rings 0 = 33 ∧ turns rings 1 = 21 ∧ turns rings 2 = 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, ?_, ?_, ?_⟩ <;>
    (rw [turns, closing_rings]; decide)

/-! ## 4. The carried cascade -/

/-- [definition] **The carried cascade's digit word**: the first ring reads the count on its own circle, and each later ring
reads the carry of the rings before it. -/
def digits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | r :: rs, t => (t % r) :: digits rs (t / r)

/-- [definition] **The cascade's winding**: the carry out of the last ring. -/
def winding : List ℕ → ℕ → ℕ
  | [], t => t
  | r :: rs, t => winding rs (t / r)

/-- [definition] **The value of a digit word** in its mixed radix. -/
def value : List ℕ → List ℕ → ℕ
  | r :: rs, d :: ds => d + r * value rs ds
  | _, _ => 0

/-- [formal-checked] The digit word has one digit a ring. -/
theorem digits_length (rs : List ℕ) (t : ℕ) : (digits rs t).length = rs.length := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih => simp [digits, ih]

/-- [formal-checked] The winding is the count over the product of the radices. -/
theorem winding_eq (rs : List ℕ) (t : ℕ) : winding rs t = t / rs.prod := by
  induction rs generalizing t with
  | nil => simp [winding]
  | cons r rs ih => simp [winding, ih, Nat.div_div_eq_div_mul]

/-- [formal-checked] The digit word's value is the count modulo the product of the radices. -/
theorem value_digits (rs : List ℕ) (t : ℕ) : value rs (digits rs t) = t % rs.prod := by
  induction rs generalizing t with
  | nil => simp [value, Nat.mod_one]
  | cons r rs ih =>
    simp only [digits, value, ih, List.prod_cons]
    exact Nat.mod_mul.symm

/-- [proved-standard; formal-checked] **The lift of the cascade**: `count = value(digits) + (∏ radices) · winding`. -/
theorem value_add_prod_mul_winding (rs : List ℕ) (t : ℕ) :
    value rs (digits rs t) + rs.prod * winding rs t = t := by
  rw [value_digits, winding_eq]
  exact Nat.mod_add_div t _

/-- [proved-standard; formal-checked] **Two counts have one digit word exactly when they agree modulo the product of the
radices**, whatever factors the radices share. -/
theorem digits_eq_iff (rs : List ℕ) (t t' : ℕ) : digits rs t = digits rs t' ↔ t ≡ t' [MOD rs.prod] := by
  constructor
  · intro h
    have := congrArg (value rs) h
    rwa [value_digits, value_digits] at this
  · induction rs generalizing t t' with
    | nil => intro _; rfl
    | cons r rs ih =>
      intro h
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · have : t = t' := by simpa [Nat.ModEq] using h
        rw [this]
      · have h' : t % (r * rs.prod) = t' % (r * rs.prod) := by simpa [Nat.ModEq] using h
        have h1 : t % r = t' % r := Nat.ModEq.of_mul_right rs.prod h'
        rw [Nat.mod_mul, Nat.mod_mul, h1] at h'
        have h2 : t / r % rs.prod = t' / r % rs.prod :=
          Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel h')
        simp only [digits, h1, ih _ _ h2]

/-- [proved-standard; formal-checked] **The digit word returns exactly at the multiples of the product.** -/
theorem digits_add_iff (rs : List ℕ) (t k : ℕ) : digits rs (t + k) = digits rs t ↔ rs.prod ∣ k := by
  rw [digits_eq_iff]
  constructor
  · intro h
    have := (Nat.modEq_iff_dvd' (Nat.le_add_right t k)).mp h.symm
    simpa using this
  · intro h
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right t k)).mpr (by simpa using h)).symm

/-- [formal-checked] **The tick and carry law of the first ring**: after `r` cells the first ring has returned and the
rings above it have received one carry. The upper rings do not tick once a cell. -/
theorem digits_cons_add_radix (r : ℕ) (hr : 0 < r) (rs : List ℕ) (t : ℕ) :
    digits (r :: rs) (t + r) = (t % r) :: digits rs (t / r + 1) := by
  simp [digits, Nat.add_div_right t hr]

/-- [formal-checked] One closing of the cascade returns the digit word. -/
theorem digits_add_prod (rs : List ℕ) (t : ℕ) : digits rs (t + rs.prod) = digits rs t :=
  (digits_add_iff rs t rs.prod).mpr dvd_rfl

/-- [formal-checked] One closing of the cascade adds one winding. -/
theorem winding_add_prod (rs : List ℕ) (hpos : 0 < rs.prod) (t : ℕ) :
    winding rs (t + rs.prod) = winding rs t + 1 := by
  rw [winding_eq, winding_eq, Nat.add_div_right t hpos]

/-! ## 5. The two laws on one count -/

/-- [definition] **The residue word of rings ticking together**: every ring reads the count on its own circle. -/
def phases (rs : List ℕ) (t : ℕ) : List ℕ := rs.map (t % ·)

/-- [definition] The least common multiple of a list of periods. -/
def lcmList (rs : List ℕ) : ℕ := rs.foldr Nat.lcm 1

/-- [formal-checked] Congruence modulo a least common multiple is congruence modulo both. -/
theorem modEq_lcm_iff (a b m n : ℕ) : a ≡ b [MOD Nat.lcm m n] ↔ a ≡ b [MOD m] ∧ a ≡ b [MOD n] := by
  simp only [Nat.modEq_iff_dvd, Int.natCast_dvd, Nat.lcm_dvd_iff]

/-- [proved-standard; formal-checked] **Two counts have one residue word exactly when they agree modulo the least common
multiple.** The list form of `nsmul_diag_eq_iff`. -/
theorem phases_eq_iff (rs : List ℕ) (t t' : ℕ) : phases rs t = phases rs t' ↔ t ≡ t' [MOD lcmList rs] := by
  induction rs with
  | nil => simp [phases, lcmList, Nat.modEq_one]
  | cons r rs ih =>
    have : lcmList (r :: rs) = Nat.lcm r (lcmList rs) := rfl
    rw [this, modEq_lcm_iff, ← ih]
    simp [phases, Nat.ModEq]

/-- [formal-checked] Every period divides the list's least common multiple. -/
theorem dvd_lcmList {rs : List ℕ} {r : ℕ} (hr : r ∈ rs) : r ∣ lcmList rs := by
  induction rs with
  | nil => simp at hr
  | cons a rs ih =>
    have : lcmList (a :: rs) = Nat.lcm a (lcmList rs) := rfl
    rw [this]
    rcases List.mem_cons.mp hr with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (ih h).trans (Nat.dvd_lcm_right _ _)

/-- [formal-checked] The least common multiple divides the product. -/
theorem lcmList_dvd_prod (rs : List ℕ) : lcmList rs ∣ rs.prod := by
  induction rs with
  | nil => simp [lcmList]
  | cons a rs ih =>
    have : lcmList (a :: rs) = Nat.lcm a (lcmList rs) := rfl
    rw [this, List.prod_cons]
    exact Nat.lcm_dvd (Dvd.intro _ rfl) (ih.trans (Dvd.intro_left _ rfl))

/-- [proved-standard; formal-checked] **For positive radices the least common multiple is the product exactly when the
radices are pairwise coprime** (the list form of `finset_lcm_eq_prod_iff`). -/
theorem lcmList_eq_prod_iff (rs : List ℕ) (hpos : ∀ r ∈ rs, 0 < r) :
    lcmList rs = rs.prod ↔ rs.Pairwise Nat.Coprime := by
  induction rs with
  | nil => simp [lcmList]
  | cons a rs ih =>
    have hposs : ∀ r ∈ rs, 0 < r := fun r hr => hpos r (List.mem_cons_of_mem a hr)
    have hPpos : 0 < rs.prod := List.prod_pos hposs
    have hcons : lcmList (a :: rs) = Nat.lcm a (lcmList rs) := rfl
    rw [hcons, List.prod_cons, lcm_mul_iff (hpos a List.mem_cons_self) hPpos (lcmList_dvd_prod rs),
      List.pairwise_cons, ih hposs]
    constructor
    · rintro ⟨hL, hc⟩
      exact ⟨fun b hb => Nat.Coprime.coprime_dvd_right (dvd_lcmList hb) hc, hL⟩
    · rintro ⟨hc, hL⟩
      refine ⟨hL, ?_⟩
      rw [(ih hposs).mpr hL]
      exact Nat.coprime_list_prod_right_iff.mpr hc

/-- [proved-standard; formal-checked] **The digit word refines the residue word**: counts the cascade does not tell apart,
rings ticking together do not tell apart. -/
theorem digits_eq_imp_phases_eq (rs : List ℕ) (t t' : ℕ) (h : digits rs t = digits rs t') :
    phases rs t = phases rs t' :=
  (phases_eq_iff rs t t').mpr (((digits_eq_iff rs t t').mp h).of_dvd (lcmList_dvd_prod rs))

/-- [proved-standard; formal-checked] **The two laws differ exactly when two radices share a factor**: for positive radices
the residue word of rings ticking together and the digit word of the carried cascade separate the same counts when and only
when the radices are pairwise coprime. -/
theorem same_reading_iff (rs : List ℕ) (hpos : ∀ r ∈ rs, 0 < r) :
    (∀ t t', phases rs t = phases rs t' ↔ digits rs t = digits rs t') ↔ rs.Pairwise Nat.Coprime := by
  rw [← lcmList_eq_prod_iff rs hpos]
  constructor
  · intro h
    have h0 : phases rs (lcmList rs) = phases rs 0 := by
      rw [phases_eq_iff]
      exact (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
    have hd := (digits_eq_iff rs _ _).mp ((h _ _).mp h0)
    exact Nat.dvd_antisymm (lcmList_dvd_prod rs) ((Nat.modEq_zero_iff_dvd).mp hd)
  · intro h t t'
    rw [phases_eq_iff, digits_eq_iff, h]

/-- [proved-standard; formal-checked] **The instance on one count**: for radices 7, 11 and 33 the least common multiple is
231 and the product 2541; at count 231 every ring ticking with the count reads zero again, while the carried cascade reads
`0, 0, 3`; the cascade's word returns exactly at the multiples of 2541, where its winding has gained one. -/
theorem cascade_231_2541 :
    lcmList [7, 11, 33] = 231 ∧ [7, 11, 33].prod = 2541 ∧
      phases [7, 11, 33] 231 = phases [7, 11, 33] 0 ∧
      digits [7, 11, 33] 231 = [0, 0, 3] ∧ digits [7, 11, 33] 0 = [0, 0, 0] ∧
      (∀ k, digits [7, 11, 33] k = digits [7, 11, 33] 0 ↔ 2541 ∣ k) ∧
      winding [7, 11, 33] 2541 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide⟩
  intro k
  have := digits_add_iff [7, 11, 33] 0 k
  simpa using this

end Holonics.Geometry.RingClosure
