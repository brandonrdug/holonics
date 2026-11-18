import Mathlib

/-!
# A symbol's word on its rings: the terms a function holds by the rings it reads, and Kraft's inequality for its length

[proved-standard] The source is the symbol record of November 12
(`research/records/2026-11-12_THE_STORE_CODES_HELD_TEXT_AT_THE_LEVEL_OF_TWO_KNOWN_NEIGHBOURS_A_SIDE_A_SYMBOL_IS_A_WORD_ON_LOCATED_RINGS_AND_A_DARK_PLACE_IS_THE_INTERIOR_OF_A_COMPOSITE.md`,
§8.1 and §8.2; atlas `code.symbol-word-located-rings`, `radix.residue-address`). A symbol carries a key
`(r_1, …, r_J)`, `r_j ∈ ℤ/m_j`, and its encoding is a series whose terms are grouped by the rings they read.

What is proved.

1. **A function on a product of rings is the sum of its terms, one for each set `J` of rings** (`sum_term`). The term
   on `J` reads only the rings of `J` (`term_reads_only`: it is constant on every ring outside `J`) and has mean zero
   along each ring of `J` (`term_mean_zero`), and the functions with those two properties are the terms on `J`
   (`term_fixes_iff`). The terms are projections that annihilate each other (`term_term`), so a function that is a
   sum of terms has those terms and no others (`term_unique`).
2. **A term on `J` holds `Π_(j∈J) (m_j − 1)` free rows**: the term's kernel has that trace (`kernel_trace`) and the
   space of terms on `J` has that dimension (`finrank_term_range`). The counts add to the whole: the first order holds
   `1 + Σ_j (m_j − 1)` (`first_order_rows`) and the whole series `Π_j m_j` (`rows_sum`).
3. **On `ℤ/M`**, `M = Π_j m_j` with the `m_j` pairwise coprime, the same through the Chinese remainder equivalence
   (`ringTerm`, `sum_ringTerm`, `ringTerm_reads_only`).
4. **Kraft's inequality for a symbol's lengths** over rings in a fixed order: if each symbol's prefix
   `(r_1(u), …, r_ℓ(u)(u))` is held by no other symbol, then `Σ_u Π_(j < ℓ(u)) m_j⁻¹ ≤ 1` (`kraft_prefix`,
   `kraft_rings`), from the general form for symbols that read any sets of rings and are told apart on a ring both read
   (`kraft_of_separated`); and the lengths the record defines, the least `ℓ` at which a symbol's prefix is held by no
   other, satisfy it whenever the keys are distinct (`kraft_least_length`).

Limits. Statement 1 is for functions with values in a field of characteristic zero; a row with several entries is one
such function an entry. The terms are the characters trivial off `J` in the record's wording; the character sums are
not used, the kernel `Π_(i∈J) (δ − 1/m_i) · Π_(i∉J) 1/m_i` being the same projection. Statement 4 says nothing of which
lengths a state's keys give, which is the record's ruler.

The computational object is the helical pair interaction: a ring is a parametron ring whose residue a contact reads,
and a term on `J` is what the contacts of the rings in `J` hold together and no fewer hold. Of the winding guide's six
general objects this touches the helix (the rings and their residues), faces and placement (a term is placed on the
rings it reads; a prefix is a cell) and the tower thread (the order of the rings a length reads along); the pair, cell
holonomy and the tube stay attached.

Consumers: #410's boxes "The tensor decomposition of functions on `ℤ/M` by the rings a term reads" and "Kraft's
inequality for a symbol's lengths"; atlas `code.symbol-word-located-rings`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.SymbolWord

open Finset

/-! ## 1. The terms of a function on a product of rings -/

section Terms

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {K : Type*} [Field K]

/-- One ring's difference kernel: `δ(a, b) − 1/m`. -/
def dker (i : ι) (a b : α i) : K := (if a = b then 1 else 0) - (Fintype.card (α i) : K)⁻¹

/-- One ring's factor of the term on `J`: the difference kernel on a ring of `J`, the mean on a ring outside it. -/
def factor (J : Finset ι) (i : ι) (a b : α i) : K :=
  if i ∈ J then dker i a b else (Fintype.card (α i) : K)⁻¹

/-- The kernel of the term on `J`: `Π_(i∈J) (δ − 1/m_i) · Π_(i∉J) 1/m_i`. -/
def kernel (J : Finset ι) (ω η : ∀ i, α i) : K := ∏ i, factor J i (ω i) (η i)

/-- The term of `f` on the set `J` of rings. -/
def term (J : Finset ι) (f : (∀ i, α i) → K) (ω : ∀ i, α i) : K := ∑ η, kernel J ω η * f η

/-- [proved-standard] The kernel in its two blocks. -/
theorem kernel_eq (J : Finset ι) (ω η : ∀ i, α i) :
    (kernel J ω η : K) = (∏ i ∈ J, dker i (ω i) (η i)) * ∏ i ∈ Jᶜ, (Fintype.card (α i) : K)⁻¹ := by
  unfold kernel
  rw [← Finset.prod_mul_prod_compl J]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by rw [factor, if_pos hi]
  · exact Finset.prod_congr rfl fun i hi => by rw [factor, if_neg (Finset.mem_compl.mp hi)]

/-- [proved-standard] **The kernels of all the sets of rings add to the identity.** -/
theorem sum_kernel (ω η : ∀ i, α i) : ∑ J : Finset ι, (kernel J ω η : K) = if ω = η then 1 else 0 := by
  simp_rw [kernel_eq]
  have h := Fintype.prod_add (fun i => (dker i (ω i) (η i) : K)) fun i => (Fintype.card (α i) : K)⁻¹
  rw [← h]
  have hpt : ∀ i, (dker i (ω i) (η i) : K) + (Fintype.card (α i) : K)⁻¹ = if ω i = η i then 1 else 0 := by
    intro i
    unfold dker
    ring
  simp_rw [hpt]
  rw [Fintype.prod_boole]
  simp [funext_iff]

/-- [proved-standard] **A function is the sum of its terms, one for each set of rings.** -/
theorem sum_term (f : (∀ i, α i) → K) (ω : ∀ i, α i) : ∑ J : Finset ι, term J f ω = f ω := by
  unfold term
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_kernel]
  simp

/-- [proved-standard] **A term on `J` reads only the rings of `J`**: it is constant on every ring outside `J`. -/
theorem term_reads_only (J : Finset ι) (f : (∀ i, α i) → K) {ω ω' : ∀ i, α i} (h : ∀ i ∈ J, ω i = ω' i) :
    term J f ω = term J f ω' := by
  unfold term
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 1
  unfold kernel
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold factor
  split_ifs with hi
  · rw [h i hi]
  · rfl

variable [CharZero K] [∀ i, Nonempty (α i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)] in
private theorem card_ne_zero' (i : ι) : (Fintype.card (α i) : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard] One ring's difference kernel has mean zero in its first reading. -/
theorem dker_sum_left (i : ι) (b : α i) : ∑ a, (dker i a b : K) = 0 := by
  unfold dker
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ b fun _ => (1 : K), if_pos (Finset.mem_univ b),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (card_ne_zero' i), sub_self]

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard] One ring's difference kernel has mean zero in its second reading. -/
theorem dker_sum_right (i : ι) (a : α i) : ∑ b, (dker i a b : K) = 0 := by
  unfold dker
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq Finset.univ a fun _ => (1 : K), if_pos (Finset.mem_univ a),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (card_ne_zero' i), sub_self]

/-- [proved-standard] **A term on `J` has mean zero along each ring of `J`.** -/
theorem term_mean_zero (J : Finset ι) (f : (∀ i, α i) → K) {j : ι} (hj : j ∈ J) (ω : ∀ i, α i) :
    ∑ a : α j, term J f (Function.update ω j a) = 0 := by
  unfold term
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun η _ => ?_
  rw [← Finset.sum_mul]
  have hker : ∀ a : α j, (kernel J (Function.update ω j a) η : K) =
      dker j a (η j) * ∏ i ∈ Finset.univ.erase j, factor J i (ω i) (η i) := by
    intro a
    unfold kernel
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self, factor, if_pos hj]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp_rw [hker]
  rw [← Finset.sum_mul, dker_sum_left, zero_mul, zero_mul]


/-! ### The space of terms on `J` -/

omit [Fintype ι] [∀ i, DecidableEq (α i)] [CharZero K] [∀ i, Nonempty (α i)] in
/-- A sum over the addresses, each reread at every residue of one ring, is the ring's period times the sum. -/
private theorem sum_update [Fintype ι] (j : ι) (F : (∀ i, α i) → K) :
    ∑ η : ∀ i, α i, ∑ a : α j, F (Function.update η j a) = (Fintype.card (α j) : K) * ∑ η, F η := by
  have hinv : Function.Involutive fun p : (∀ i, α i) × α j => (Function.update p.1 j p.2, p.1 j) := by
    rintro ⟨η, a⟩
    simp
  have h := Fintype.sum_equiv hinv.toPerm (fun p : (∀ i, α i) × α j => F (Function.update p.1 j p.2))
    (fun p => F p.1) fun p => rfl
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  rw [h]
  simp [Finset.mul_sum]

omit [CharZero K] [∀ i, Nonempty (α i)] in
/-- [proved-standard] The kernel with one ring of its second reading reread. -/
theorem kernel_update_right (J : Finset ι) (ω η : ∀ i, α i) (j : ι) (a : α j) :
    (kernel J ω (Function.update η j a) : K) =
      factor J j (ω j) a * ∏ i ∈ Finset.univ.erase j, factor J i (ω i) (η i) := by
  unfold kernel
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- [proved-standard] **A function that reads only the rings of `J`, with mean zero along each, has no term on any other
set of rings.** -/
theorem term_eq_zero_of (J' J : Finset ι) (g : (∀ i, α i) → K)
    (hread : ∀ ω ω' : ∀ i, α i, (∀ i ∈ J, ω i = ω' i) → g ω = g ω')
    (hmean : ∀ j ∈ J, ∀ ω : ∀ i, α i, ∑ a : α j, g (Function.update ω j a) = 0)
    (hne : J' ≠ J) (ω : ∀ i, α i) : term J' g ω = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ J' ↔ j ∈ J) := by
    by_contra hcon
    push Not at hcon
    exact hne (Finset.ext hcon)
  have hsum := sum_update j fun η => (kernel J' ω η : K) * g η
  have hzero : ∑ η : ∀ i, α i, ∑ a : α j,
      (kernel J' ω (Function.update η j a) : K) * g (Function.update η j a) = 0 := by
    refine Finset.sum_eq_zero fun η _ => ?_
    simp_rw [kernel_update_right]
    by_cases h1 : j ∈ J'
    · have h2 : j ∉ J := fun h2 => hj ⟨fun _ => h2, fun _ => h1⟩
      have hg : ∀ a : α j, g (Function.update η j a) = g η := fun a =>
        hread _ _ fun i hi => by
          have hij : i ≠ j := fun hij => h2 (hij ▸ hi)
          rw [Function.update_of_ne hij]
      have hterm : ∀ a : α j, (factor J' j (ω j) a : K) * (∏ i ∈ Finset.univ.erase j, factor J' i (ω i) (η i)) *
          g (Function.update η j a) =
          dker j (ω j) a * ((∏ i ∈ Finset.univ.erase j, factor J' i (ω i) (η i)) * g η) := by
        intro a
        have hfac : (factor J' j (ω j) a : K) = dker j (ω j) a := by rw [factor, if_pos h1]
        rw [hfac, hg a]
        ring
      simp_rw [hterm]
      rw [← Finset.sum_mul, dker_sum_right, zero_mul]
    · have h2 : j ∈ J := by
        by_contra h2
        exact hj ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      have hterm : ∀ a : α j, (factor J' j (ω j) a : K) * (∏ i ∈ Finset.univ.erase j, factor J' i (ω i) (η i)) *
          g (Function.update η j a) =
          ((Fintype.card (α j) : K)⁻¹ * ∏ i ∈ Finset.univ.erase j, factor J' i (ω i) (η i)) *
            g (Function.update η j a) := by
        intro a
        have hfac : (factor J' j (ω j) a : K) = (Fintype.card (α j) : K)⁻¹ := by rw [factor, if_neg h1]
        rw [hfac]
      simp_rw [hterm]
      rw [← Finset.mul_sum, hmean j h2 η, mul_zero]
  have hc0 : (Fintype.card (α j) : K) * ∑ η, (kernel J' ω η : K) * g η = 0 := hsum.symm.trans hzero
  exact (mul_eq_zero.mp hc0).resolve_left (card_ne_zero' j)

/-- [proved-standard] **Such a function is its own term on `J`.** -/
theorem term_fixes (J : Finset ι) (g : (∀ i, α i) → K)
    (hread : ∀ ω ω' : ∀ i, α i, (∀ i ∈ J, ω i = ω' i) → g ω = g ω')
    (hmean : ∀ j ∈ J, ∀ ω : ∀ i, α i, ∑ a : α j, g (Function.update ω j a) = 0) (ω : ∀ i, α i) :
    term J g ω = g ω := by
  have h := sum_term g ω
  rwa [Finset.sum_eq_single J (fun J' _ hne => term_eq_zero_of J' J g hread hmean hne ω)
    fun h => absurd (Finset.mem_univ J) h] at h

/-- [proved-standard] **The terms on `J` are the functions that read only the rings of `J` and have mean zero along
each of them.** -/
theorem term_fixes_iff (J : Finset ι) (g : (∀ i, α i) → K) :
    (∀ ω, term J g ω = g ω) ↔
      (∀ ω ω' : ∀ i, α i, (∀ i ∈ J, ω i = ω' i) → g ω = g ω') ∧
        ∀ j ∈ J, ∀ ω : ∀ i, α i, ∑ a : α j, g (Function.update ω j a) = 0 := by
  constructor
  · intro h
    refine ⟨fun ω ω' hω => ?_, fun j hj ω => ?_⟩
    · rw [← h ω, ← h ω']
      exact term_reads_only J g hω
    · rw [← term_mean_zero J g hj ω]
      exact Finset.sum_congr rfl fun a _ => (h _).symm
  · rintro ⟨hread, hmean⟩ ω
    exact term_fixes J g hread hmean ω

/-! ### The terms are projections that annihilate each other -/

omit [Fintype ι] [DecidableEq ι] in
private theorem dker_comp (i : ι) (x y : α i) : ∑ a, (dker i x a : K) * dker i a y = dker i x y := by
  have hcu : (Fintype.card (α i) : K) * (Fintype.card (α i) : K)⁻¹ = 1 := mul_inv_cancel₀ (card_ne_zero' i)
  have e1 : ∑ a : α i, (if x = a then (1 : K) else 0) * (if a = y then 1 else 0) = if x = y then 1 else 0 := by
    simp
  have e2 : ∑ a : α i, (if x = a then (1 : K) else 0) = 1 := by simp
  have e3 : ∑ a : α i, (if a = y then (1 : K) else 0) = 1 := by simp
  have e4 : ∑ _a : α i, (1 : K) = (Fintype.card (α i) : K) := by simp
  unfold dker
  have hpt : ∀ a : α i, ((if x = a then (1 : K) else 0) - (Fintype.card (α i) : K)⁻¹) *
      ((if a = y then 1 else 0) - (Fintype.card (α i) : K)⁻¹) =
      (if x = a then (1 : K) else 0) * (if a = y then 1 else 0) -
        (Fintype.card (α i) : K)⁻¹ * (if x = a then 1 else 0) -
        (Fintype.card (α i) : K)⁻¹ * (if a = y then 1 else 0) +
        (Fintype.card (α i) : K)⁻¹ * (Fintype.card (α i) : K)⁻¹ * 1 := by
    intro a
    ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, e1, e2, e3, e4]
  linear_combination (Fintype.card (α i) : K)⁻¹ * hcu

omit [Fintype ι] in
/-- [proved-standard] One ring's factors compose: a difference with a difference is the difference, a mean with a mean
the mean, and a difference with a mean nothing. -/
theorem factor_comp (J J' : Finset ι) (i : ι) (x y : α i) :
    ∑ a, (factor J i x a : K) * factor J' i a y = if (i ∈ J ↔ i ∈ J') then factor J i x y else 0 := by
  have hcu : (Fintype.card (α i) : K) * (Fintype.card (α i) : K)⁻¹ = 1 := mul_inv_cancel₀ (card_ne_zero' i)
  by_cases h : i ∈ J <;> by_cases h' : i ∈ J'
  · simpa [factor, h, h'] using dker_comp (K := K) i x y
  · have hdu : ∑ a, (dker i x a : K) * (Fintype.card (α i) : K)⁻¹ = 0 := by
      rw [← Finset.sum_mul, dker_sum_right, zero_mul]
    simpa [factor, h, h'] using hdu
  · have hud : ∑ a, (Fintype.card (α i) : K)⁻¹ * (dker i a y : K) = 0 := by
      rw [← Finset.mul_sum, dker_sum_left, mul_zero]
    simpa [factor, h, h'] using hud
  · have huu : ∑ _a : α i, (Fintype.card (α i) : K)⁻¹ * (Fintype.card (α i) : K)⁻¹ = (Fintype.card (α i) : K)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcu, one_mul]
    simp only [factor, h, h', ↓reduceIte, iff_self]
    exact huu

/-- [proved-standard] **The kernels compose as projections that annihilate each other.** -/
theorem kernel_comp (J J' : Finset ι) (ω η : ∀ i, α i) :
    ∑ ζ, (kernel J ω ζ : K) * kernel J' ζ η = if J = J' then kernel J ω η else 0 := by
  unfold kernel
  simp_rw [← Finset.prod_mul_distrib]
  refine (Fintype.prod_sum fun i (a : α i) => (factor J i (ω i) a : K) * factor J' i a (η i)).symm.trans ?_
  simp_rw [factor_comp]
  by_cases h : J = J'
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ J ↔ i ∈ J') := by
      by_contra hcon
      push Not at hcon
      exact h (Finset.ext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- [proved-standard] **The term on `J` of a term on `J′` is that term when `J = J′` and nothing otherwise.** -/
theorem term_term (J J' : Finset ι) (f : (∀ i, α i) → K) (ω : ∀ i, α i) :
    term J (term J' f) ω = if J = J' then term J f ω else 0 := by
  have h : term J (term J' f) ω = ∑ η, (∑ ζ, (kernel J ω ζ : K) * kernel J' ζ η) * f η := by
    unfold term
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ζ _ => ?_
    ring
  rw [h]
  simp_rw [kernel_comp]
  by_cases hJ : J = J'
  · simp [hJ, term]
  · simp [hJ]

/-- [proved-standard] **A sum of terms has those terms and no others**: if `f = Σ_(J′) term J′ (g J′)`, the term of `f`
on `J` is the term of `g J` on `J`. -/
theorem term_unique (g : Finset ι → (∀ i, α i) → K) (J : Finset ι) (ω : ∀ i, α i) :
    term J (fun ω' => ∑ J', term J' (g J') ω') ω = term J (g J) ω := by
  have h : term J (fun ω' => ∑ J', term J' (g J') ω') ω = ∑ J', term J (term J' (g J')) ω := by
    unfold term
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h]
  simp_rw [term_term]
  rw [Finset.sum_ite_eq Finset.univ J fun J' => term J (g J') ω, if_pos (Finset.mem_univ J)]

/-- [proved-standard] **A term on `J` holds `Π_(j∈J) (m_j − 1)` free rows**, as its kernel's trace. -/
theorem kernel_trace (J : Finset ι) :
    ∑ ω : ∀ i, α i, (kernel J ω ω : K) = ∏ i ∈ J, ((Fintype.card (α i) : K) - 1) := by
  unfold kernel
  refine (Fintype.prod_sum fun i (a : α i) => (factor J i a a : K)).symm.trans ?_
  have hpt : ∀ i, ∑ a : α i, (factor J i a a : K) = if i ∈ J then (Fintype.card (α i) : K) - 1 else 1 := by
    intro i
    by_cases h : i ∈ J
    · simp only [factor, dker, h, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_sub, mul_one, mul_inv_cancel₀ (card_ne_zero' i)]
    · simp only [factor, h, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_inv_cancel₀ (card_ne_zero' i)]
  simp_rw [hpt]
  exact Fintype.prod_ite_mem J _

/-- The term on `J` as a linear map on the functions of the rings. -/
noncomputable def termLin (J : Finset ι) : ((∀ i, α i) → K) →ₗ[K] ((∀ i, α i) → K) :=
  Matrix.toLin' (Matrix.of fun ω η => (kernel J ω η : K))

omit [CharZero K] [∀ i, Nonempty (α i)] in
/-- [proved-standard] The linear map is the term. -/
theorem termLin_apply (J : Finset ι) (f : (∀ i, α i) → K) (ω : ∀ i, α i) : termLin J f ω = term J f ω := by
  simp [termLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, term]

/-- [proved-standard] The term on `J` is a projection. -/
theorem termLin_idem (J : Finset ι) : IsIdempotentElem (termLin (K := K) (α := α) J) := by
  refine LinearMap.ext fun f => funext fun ω => ?_
  rw [Module.End.mul_apply, termLin_apply]
  have hfun : termLin J f = term J f := funext fun ω' => termLin_apply J f ω'
  rw [hfun, term_term, if_pos rfl]

/-- [proved-standard] **The space of terms on `J` has dimension `Π_(j∈J) (m_j − 1)`.** -/
theorem finrank_term_range (J : Finset ι) :
    Module.finrank K (LinearMap.range (termLin (K := K) (α := α) J)) = ∏ i ∈ J, (Fintype.card (α i) - 1) := by
  have hproj := LinearMap.IsIdempotentElem.isProj_range _ (termLin_idem (K := K) (α := α) J)
  have htr := hproj.trace
  rw [termLin, Matrix.trace_toLin'_eq] at htr
  have hK : (Module.finrank K (LinearMap.range (termLin (K := K) (α := α) J)) : K) =
      ((∏ i ∈ J, (Fintype.card (α i) - 1) : ℕ) : K) := by
    rw [← termLin] at htr
    rw [← htr, Matrix.trace, Nat.cast_prod]
    simp only [Matrix.diag_apply, Matrix.of_apply]
    rw [kernel_trace]
    exact Finset.prod_congr rfl fun i _ => (Nat.cast_pred Fintype.card_pos).symm
  exact_mod_cast hK

end Terms


/-! ### The rows add to the whole -/

/-- [proved-standard] **The whole series holds `Π_j m_j` rows**: `Σ_J Π_(j∈J) (m_j − 1) = Π_j m_j`. -/
theorem rows_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (hm : ∀ i, 0 < m i) :
    ∑ J : Finset ι, ∏ j ∈ J, (m j - 1) = ∏ j, m j := by
  have h := Finset.prod_one_add (f := fun j => m j - 1) (Finset.univ : Finset ι)
  rw [Finset.powerset_univ] at h
  rw [← h]
  refine Finset.prod_congr rfl fun j _ => ?_
  have := hm j
  omega

/-- [proved-standard] **The first order holds `1 + Σ_j (m_j − 1)` rows**: the term on no ring and the terms on one. -/
theorem first_order_rows {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) :
    (∑ J ∈ Finset.powersetCard 0 (Finset.univ : Finset ι), ∏ j ∈ J, (m j - 1)) +
      ∑ J ∈ Finset.powersetCard 1 (Finset.univ : Finset ι), ∏ j ∈ J, (m j - 1) = 1 + ∑ j, (m j - 1) := by
  rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, Finset.powersetCard_one, Finset.sum_map]
  simp

/-- [proved-standard] The record's rings `(16, 17)`: `1 + 15 + 16 = 32` rows at first order, `272` in the whole. -/
theorem rows_sixteen_seventeen : 1 + (16 - 1) + (17 - 1) = 32 ∧ 16 * 17 = 272 ∧ 32 + (16 - 1) * (17 - 1) = 272 := by
  norm_num

/-! ## 2. On `ℤ/M` through the Chinese remainder equivalence -/

section Rings

open scoped Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) [∀ i, NeZero (m i)]
variable (hm : Pairwise (Nat.Coprime on m)) {K : Type*} [Field K]

/-- The term on the set `J` of rings of a function on `ℤ/M`, `M = Π_j m_j`. -/
noncomputable def ringTerm (J : Finset ι) (F : ZMod (∏ i, m i) → K) (a : ZMod (∏ i, m i)) : K :=
  term J (fun ω => F ((ZMod.prodEquivPi m hm).symm ω)) (ZMod.prodEquivPi m hm a)

/-- [proved-standard] **A function on `ℤ/M` is the sum of its terms, one for each set of rings.** -/
theorem sum_ringTerm (F : ZMod (∏ i, m i) → K) (a : ZMod (∏ i, m i)) : ∑ J : Finset ι, ringTerm m hm J F a = F a := by
  unfold ringTerm
  rw [sum_term]
  simp

/-- [proved-standard] **A term on `J` is constant on every ring outside `J`**: two addresses with the same residues on
the rings of `J` have the same term. -/
theorem ringTerm_reads_only (J : Finset ι) (F : ZMod (∏ i, m i) → K) {a a' : ZMod (∏ i, m i)}
    (h : ∀ i ∈ J, ZMod.prodEquivPi m hm a i = ZMod.prodEquivPi m hm a' i) :
    ringTerm m hm J F a = ringTerm m hm J F a' :=
  term_reads_only J _ h

/-- [proved-standard] The same for two counts: congruent modulo every ring of `J`, they have the same term on `J`. -/
theorem ringTerm_natCast_congr (J : Finset ι) (F : ZMod (∏ i, m i) → K) {x x' : ℕ}
    (h : ∀ i ∈ J, x ≡ x' [MOD m i]) :
    ringTerm m hm J F (x : ZMod (∏ i, m i)) = ringTerm m hm J F (x' : ZMod (∏ i, m i)) := by
  refine ringTerm_reads_only m hm J F fun i hi => ?_
  rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply, map_natCast, map_natCast]
  exact (ZMod.natCast_eq_natCast_iff x x' (m i)).mpr (h i hi)

end Rings

/-! ## 3. Kraft's inequality -/

section Kraft

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
variable {U : Type*}

/-- The cell of a key read on the rings of `S`: the addresses that agree with `r` on every ring of `S`. -/
def cell (S : Finset ι) (r : ∀ i, α i) : Finset (∀ i, α i) :=
  Fintype.piFinset fun i => if i ∈ S then {r i} else Finset.univ

/-- [proved-standard] An address is in the cell iff it agrees with the key on the rings read. -/
theorem mem_cell {S : Finset ι} {r ω : ∀ i, α i} : ω ∈ cell S r ↔ ∀ i ∈ S, ω i = r i := by
  unfold cell
  rw [Fintype.mem_piFinset]
  constructor
  · intro h i hi
    have hmem := h i
    rw [if_pos hi] at hmem
    exact Finset.mem_singleton.mp hmem
  · intro h i
    split_ifs with hi
    · exact Finset.mem_singleton.mpr (h i hi)
    · exact Finset.mem_univ _

/-- [proved-standard] **A cell's count times the rings it reads is the whole**: `|cell| · Π_(i∈S) m_i = Π_i m_i`. -/
theorem card_cell_mul (S : Finset ι) (r : ∀ i, α i) :
    (cell S r).card * ∏ i ∈ S, Fintype.card (α i) = ∏ i, Fintype.card (α i) := by
  unfold cell
  rw [Fintype.card_piFinset, ← Fintype.prod_ite_mem S fun i => Fintype.card (α i), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

variable [∀ i, Nonempty (α i)]

/-- [proved-standard] **A cell's measure is the product of the inverse periods it reads.** -/
theorem cell_measure (S : Finset ι) (r : ∀ i, α i) :
    ((cell S r).card : ℚ) / ∏ i, (Fintype.card (α i) : ℚ) = ∏ i ∈ S, (Fintype.card (α i) : ℚ)⁻¹ := by
  have hS : (∏ i ∈ S, (Fintype.card (α i) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hall : (∏ i, (Fintype.card (α i) : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcast : ((cell S r).card : ℚ) * ∏ i ∈ S, (Fintype.card (α i) : ℚ) = ∏ i, (Fintype.card (α i) : ℚ) := by
    exact_mod_cast card_cell_mul S r
  rw [Finset.prod_inv_distrib, div_eq_iff hall, ← hcast]
  field_simp

/-- [proved-standard] **Kraft's inequality for symbols told apart on a ring both read**: if every two symbols differ on
some ring that both read, the cells' measures add to at most one. -/
theorem kraft_of_separated (s : Finset U) (S : U → Finset ι) (key : U → ∀ i, α i)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ∃ i, i ∈ S u ∧ i ∈ S v ∧ key u i ≠ key v i) :
    ∑ u ∈ s, ∏ i ∈ S u, (Fintype.card (α i) : ℚ)⁻¹ ≤ 1 := by
  classical
  have hdisj : (s : Set U).PairwiseDisjoint fun u => cell (S u) (key u) := by
    intro u hu v hv huv
    rw [Function.onFun, Finset.disjoint_left]
    intro ω hωu hωv
    obtain ⟨i, hiu, hiv, hne⟩ := hsep u hu v hv huv
    exact hne ((mem_cell.mp hωu i hiu).symm.trans (mem_cell.mp hωv i hiv))
  have hcard : ∑ u ∈ s, (cell (S u) (key u)).card ≤ ∏ i, Fintype.card (α i) := by
    rw [← Finset.card_biUnion hdisj, ← Fintype.card_pi]
    exact Finset.card_le_univ _
  have hall : (0 : ℚ) < ∏ i, (Fintype.card (α i) : ℚ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr Fintype.card_pos
  rw [← Finset.sum_congr rfl fun u _ => cell_measure (S u) (key u), ← Finset.sum_div, div_le_one hall]
  exact_mod_cast hcard

end Kraft

section Prefix

variable {J : ℕ} {α : Fin J → Type*} [∀ j, Fintype (α j)] [∀ j, Nonempty (α j)]
variable {U : Type*}

/-- [proved-standard] **Kraft's inequality for a symbol's lengths**, the rings in a fixed order: if each symbol's prefix
of its own length is held by no other symbol, then `Σ_u Π_(j < ℓ(u)) m_j⁻¹ ≤ 1`. -/
theorem kraft_prefix (s : Finset U) (len : U → ℕ) (key : U → ∀ j, α j)
    (hfree : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ∃ j : Fin J, (j : ℕ) < len u ∧ key u j ≠ key v j) :
    ∑ u ∈ s, ∏ j : Fin J with j.val < len u, (Fintype.card (α j) : ℚ)⁻¹ ≤ 1 := by
  refine kraft_of_separated s (fun u => ({j : Fin J | j.val < len u} : Finset (Fin J))) key ?_
  intro u hu v hv huv
  rcases Nat.le_total (len u) (len v) with hle | hle
  · obtain ⟨j, hj, hne⟩ := hfree u hu v hv huv
    exact ⟨j, by simpa using hj, by simpa using lt_of_lt_of_le hj hle, hne⟩
  · obtain ⟨j, hj, hne⟩ := hfree v hv u hu (Ne.symm huv)
    exact ⟨j, by simpa using lt_of_lt_of_le hj hle, by simpa using hj, Ne.symm hne⟩

/-- A symbol's length among the symbols of `s`: the least count of leading rings at which its prefix is held by no
other symbol. -/
noncomputable def leastLength (s : Finset U) (key : U → ∀ j, α j) (u : U) : ℕ :=
  sInf {l : ℕ | ∀ v ∈ s, v ≠ u → ∃ j : Fin J, (j : ℕ) < l ∧ key u j ≠ key v j}

omit [∀ j, Fintype (α j)] [∀ j, Nonempty (α j)] in
/-- [proved-standard] With distinct keys every symbol has a length, and at it no other symbol holds its prefix. -/
theorem leastLength_spec (s : Finset U) (key : U → ∀ j, α j) (hkey : ∀ u ∈ s, ∀ v ∈ s, key u = key v → u = v)
    {u : U} (hu : u ∈ s) :
    ∀ v ∈ s, v ≠ u → ∃ j : Fin J, (j : ℕ) < leastLength s key u ∧ key u j ≠ key v j := by
  have hne : {l : ℕ | ∀ v ∈ s, v ≠ u → ∃ j : Fin J, (j : ℕ) < l ∧ key u j ≠ key v j}.Nonempty := by
    refine ⟨J, fun v hv hvu => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hvu (hkey v hv u hu (funext fun j => (hcon j j.isLt).symm))
  exact Nat.sInf_mem hne

/-- [proved-standard] **The located lengths satisfy Kraft's inequality**: with distinct keys, the lengths at which each
symbol's prefix is held by no other have `Σ_u Π_(j < ℓ(u)) m_j⁻¹ ≤ 1`. -/
theorem kraft_least_length (s : Finset U) (key : U → ∀ j, α j) (hkey : ∀ u ∈ s, ∀ v ∈ s, key u = key v → u = v) :
    ∑ u ∈ s, ∏ j : Fin J with j.val < leastLength s key u, (Fintype.card (α j) : ℚ)⁻¹ ≤ 1 :=
  kraft_prefix s (leastLength s key) key fun _ hu v hv huv => leastLength_spec s key hkey hu v hv (Ne.symm huv)

end Prefix

/-- [proved-standard] **Kraft's inequality on rings `ℤ/m_j`**: `Σ_u Π_(j < ℓ(u)) m_j⁻¹ ≤ 1`. -/
theorem kraft_rings {J : ℕ} (m : Fin J → ℕ) [∀ j, NeZero (m j)] {U : Type*} (s : Finset U) (len : U → ℕ)
    (key : U → ∀ j, ZMod (m j))
    (hfree : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ∃ j : Fin J, (j : ℕ) < len u ∧ key u j ≠ key v j) :
    ∑ u ∈ s, ∏ j : Fin J with j.val < len u, ((m j : ℚ))⁻¹ ≤ 1 := by
  have h := kraft_prefix s len key hfree
  simpa [ZMod.card] using h

end Holonics.Compression.SymbolWord
