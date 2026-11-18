import Mathlib

/-!
# A signature is what a change of frame cannot touch: faithful modes of a ring, the frame potential, a loop's remainders, a commutator that is an AND, and a common scale

The record of November 16 (`research/records/2026-11-16_A_CODE_READ_WITHOUT_ITS_KEY_IS_A_CIPHER_…`, §4 and §5; atlas
`prime.faithful-modes-and-towers`, `frame.moment-map-loudness-colour`, `helical.loop-geometric-phase-remainder`, and
the Doppler signature read on `lorentz.doppler-ratio-chart`) held five finite statements as host rulers or as
theorems taken from their papers. This file states their finite parts in Lean.

[proved-standard; formal-checked] What is proved.

1. **A mode of a ring reads a residue** (`mode_reads_residue`): on `ℤ/n` the mode `k` tells `x` from `y` just when
   they differ modulo `n / gcd(k, n)`. A mode is faithful (it tells every two residues apart) if and only if `k` is
   coprime to `n` (`faithful_iff_coprime`), so the faithful modes of `ℤ/n` number `φ(n)` (`faithful_count`): all 96
   nonzero modes of `ℤ/97` (`faithful_97`, `faithful_count_97`) against 32 of `ℤ/96`'s 95 (`faithful_count_96`,
   `zero_not_faithful`). On a prime power a mode whose gcd with `p^m` is `p^j` reads the residue modulo `p^(m − j)`
   (`mode_reads_prime_power`). In the complex chart `χ_k(x) = e^(2πi kx/n)` two places read alike just when
   `kx ≡ ky (mod n)` (`mode_eq_iff`), and the comb `δ₀ − δ₈` on `ℤ/16` is silent at a mode if and only if the mode is
   even (`comb_silent_iff_even`, `comb_silent_at_even`).
2. **The frame potential is the frame operator's second trace** (`framePotential_eq_trace_sq`): for a frame `F` with
   places as columns, `Σ_(i,j) ‖⟨f_i, f_j⟩‖² = tr((FFᴴ)²)`; the places' powers sum to `tr(FFᴴ)`
   (`trace_frameOperator`); their squares sum to at most the potential (`sum_sq_placePower_le`), so the count of modes
   a region's color fills is at most the count of places its loudness fills, `(tr S)²/tr S² ≤ (Σr)²/Σr²`
   (`participation_le`).
3. **A loop's face reads only the remainders** (`loopFace_add_int`, `loopFace_fract`, `loopFace_eq_of_fract_eq`):
   `Z = Σ_j λ_j e^(2πi n_j)` is unchanged when each `n_j` moves by a whole number, so it is a function of the
   fractional parts alone, and so is its argument, the geometric phase (`loopPhase_eq_of_fract_eq`).
4. **A commutator is an AND** (`commutator_and`): with `a = (0 1 2 3 4)` and `b = (0 1 3 4 2)` in the permutations
   of five places, both 5-cycles of sign one (`fiveCycleA_cycleType`, `fiveCycleB_cycleType`, `fiveCycle_sign`),
   `a b a⁻¹ b⁻¹ = (0 4 1 3 2)` is a 5-cycle (`commutator_eq`, `commutator_isCycle`, `commutator_cycleType`), and the
   commutator is the identity when either argument is (`commutator_one_left`, `commutator_one_right`). Every commutator
   of permutations has sign one (`sign_commutator`); in a commutative group every commutator is the identity
   (`commutator_trivial_of_comm`), and a word there depends on its counts alone (`abelian_word_counts`).
5. **A common scale leaves the intervals** (`doppler_ratio`, `doppler_log`, `doppler_interval`): multiplying every
   frequency by `k` keeps each ratio and moves each logarithm by `log k`, so differences of logarithms stay.

Limits. Statement 1 does not state Chebotarev's theorem on the minors of a prime ring's Fourier chart, Tao's bound
`|supp f| + |supp f̂| ≥ p + 1`, the comb on `ℤ/12` or the join of two coprime towers. Statement 2 is the two traces and
one inequality: no moment map, no Schur–Horn majorization and no connectivity of a level set is stated. Statement 3 is
the face `Z` as a sum; the loop of steady states, its covariance and the weak-drive expansion are not constructed.
Statement 4 is one pair: the record's sentence "the commutator of two 5-cycles of `A₅` is a 5-cycle" holds for a
chosen pair and not for every pair (`commutator_self`: a 5-cycle against itself gives the identity), and Barrington's
theorem on words over a non-solvable group is not stated. Statement 5 is the scale's algebra; the boost of
`lorentz.doppler-ratio-chart` and the song's family of `holon.song-is-a-family` are their own owners.

Neighbours, not repeated here: `HolonicsResearch/Compression/CipherCode.lean` (the same record's §3),
`Holonics/Foundation/RelationLadder.lean` (a song is the family of its enactments).

The computational object is the helical pair interaction: a mode is a ring's turn read at a contact, and a frame's
Gram entry is the pairing of two places. Of the winding guide's six general objects this touches the helix (a mode's
residue and a loop's remainder are the circle part, the whole windings the carry), the pair (the Gram entries and the
commutator of two moves) and cell holonomy (the loop's face); faces and placement, the tube and the tower thread stay
attached, the tower thread through the prime-power reading.

Consumers: the atlas rows named above; the record's §6 (a region's color read beside its loudness, and a signature
read on the clock of news).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.FaithfulModes

open Finset Matrix

/-! ## 1. A mode of a ring reads a residue -/

/-- [proved-standard; formal-checked] **A mode reads a residue**: on `ℤ/n` the mode `k` gives `x` and `y` the same
reading, `kx ≡ ky (mod n)`, if and only if `x ≡ y` modulo `n / gcd(k, n)`. -/
theorem mode_reads_residue {n : ℕ} (hn : 0 < n) (k x y : ℤ) :
    k * x ≡ k * y [ZMOD n] ↔ x ≡ y [ZMOD ((n / Int.gcd k n : ℕ) : ℤ)] := by
  have hgpos : 0 < Int.gcd k n := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn.ne')
  have hkdvd : ((Int.gcd k n : ℕ) : ℤ) ∣ k := Int.gcd_dvd_left ..
  have hndvd : Int.gcd k n ∣ n := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..)
  generalize hg : Int.gcd k n = g at hgpos hkdvd hndvd ⊢
  obtain ⟨k', rfl⟩ := hkdvd
  obtain ⟨n', rfl⟩ := hndvd
  have hg1 : Int.gcd k' n' = 1 := by
    rw [Nat.cast_mul, Int.gcd_mul_left, Int.natAbs_natCast] at hg
    exact Nat.eq_of_mul_eq_mul_left hgpos (hg.trans (mul_one g).symm)
  have hcop : IsCoprime (n' : ℤ) k' := (Int.isCoprime_iff_gcd_eq_one.mpr hg1).symm
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, Nat.mul_div_cancel_left _ hgpos, Nat.cast_mul,
    show (g : ℤ) * k' * y - g * k' * x = g * (k' * (y - x)) by ring, mul_dvd_mul_iff_left hg0]
  exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h _⟩

/-- [definition] A mode `k` of `ℤ/n` is faithful when it tells every two residues apart: equal readings only at
equal residues. -/
def Faithful (n : ℕ) (k : ℤ) : Prop := ∀ x y : ℤ, k * x ≡ k * y [ZMOD n] → x ≡ y [ZMOD n]

/-- [proved-standard; formal-checked] **A mode is faithful if and only if it is a unit**: `gcd(k, n) = 1`. -/
theorem faithful_iff_coprime {n : ℕ} (hn : 0 < n) (k : ℤ) : Faithful n k ↔ Int.gcd k n = 1 := by
  constructor
  · intro h
    have hgpos : 0 < Int.gcd k n := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn.ne')
    have h1 : k * ((n / Int.gcd k n : ℕ) : ℤ) ≡ k * 0 [ZMOD n] :=
      (mode_reads_residue hn k _ 0).mpr (by
        rw [Int.modEq_iff_dvd]; simp)
    have h2 := h _ _ h1
    rw [Int.modEq_iff_dvd] at h2
    have h3 : n ∣ n / Int.gcd k n := by
      have : ((n : ℕ) : ℤ) ∣ ((n / Int.gcd k n : ℕ) : ℤ) := by simpa using h2
      exact Int.natCast_dvd_natCast.mp this
    by_contra hne
    have hlt : n / Int.gcd k n < n := Nat.div_lt_self hn (by omega)
    have hpos : 0 < n / Int.gcd k n :=
      Nat.div_pos (Nat.le_of_dvd hn (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..))) hgpos
    exact absurd (Nat.le_of_dvd hpos h3) (by omega)
  · intro h x y hxy
    have := (mode_reads_residue hn k x y).mp hxy
    rwa [h, Nat.div_one] at this

open Classical in
/-- [proved-standard; formal-checked] **The faithful modes of `ℤ/n` number `φ(n)`**, counted over the modes
`0, …, n − 1`. -/
theorem faithful_count {n : ℕ} (hn : 0 < n) :
    ((range n).filter fun k : ℕ => Faithful n (k : ℤ)).card = Nat.totient n := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [faithful_iff_coprime hn, Int.gcd_natCast_natCast, Nat.Coprime, Nat.gcd_comm]

/-- [formal-checked] The mode `0` is faithful on no ring of more than one residue, so the faithful modes are among
the nonzero ones. -/
theorem zero_not_faithful {n : ℕ} (hn : 1 < n) : ¬ Faithful n 0 := by
  rw [faithful_iff_coprime (by omega)]
  simp only [Int.gcd_zero_left, Int.natAbs_natCast]
  omega

/-- [formal-checked] The ruler on a prime ring: every nonzero mode of `ℤ/97` is faithful. -/
theorem faithful_97 (k : ℕ) (hk0 : 0 < k) (hk : k < 97) : Faithful 97 (k : ℤ) := by
  rw [faithful_iff_coprime (by norm_num), Int.gcd_natCast_natCast]
  exact (Nat.coprime_of_lt_prime hk0.ne' hk (by norm_num)).symm

open Classical in
/-- [formal-checked] The ruler: `ℤ/97` has 96 faithful modes, all of its nonzero ones. -/
theorem faithful_count_97 : ((range 97).filter fun k : ℕ => Faithful 97 (k : ℤ)).card = 96 := by
  rw [faithful_count (by norm_num), Nat.totient_prime (by norm_num)]

open Classical in
/-- [formal-checked] The ruler: `ℤ/96` has `32 = φ(96)` faithful modes among its 95 nonzero ones. -/
theorem faithful_count_96 : ((range 96).filter fun k : ℕ => Faithful 96 (k : ℤ)).card = 32 := by
  rw [faithful_count (by norm_num)]
  decide

/-- [proved-standard; formal-checked] **A mode's valuation is its level**: on `ℤ/p^m` a mode whose gcd with `p^m` is
`p^j` reads the residue modulo `p^(m − j)`; for a prime `p` that is a mode of valuation `j`, and only `j = 0` reads
the whole residue. -/
theorem mode_reads_prime_power {p m j : ℕ} (hp : 0 < p) (hj : j ≤ m) (k x y : ℤ)
    (hk : Int.gcd k ((p ^ m : ℕ) : ℤ) = p ^ j) :
    k * x ≡ k * y [ZMOD ((p ^ m : ℕ) : ℤ)] ↔ x ≡ y [ZMOD ((p ^ (m - j) : ℕ) : ℤ)] := by
  rw [mode_reads_residue (pow_pos hp m), hk, Nat.pow_div hj hp]

open Real in
/-- [definition] The complex chart of a mode: `χ_k(x) = e^(2πi kx/n)` on `ℤ/n`. -/
noncomputable def mode (n : ℕ) (k x : ℤ) : ℂ := Complex.exp (2 * π * Complex.I * (k * x) / n)

open Real in
/-- [proved-standard; formal-checked] **The complex chart reads the same residue**: `χ_k(x) = χ_k(y)` if and only if
`kx ≡ ky (mod n)`. -/
theorem mode_eq_iff {n : ℕ} (hn : 0 < n) (k x y : ℤ) :
    mode n k x = mode n k y ↔ k * x ≡ k * y [ZMOD n] := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [mode, mode, Complex.exp_eq_exp_iff_exists_int, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    field_simp at hm
    have h' : k * x = k * y + n * m := by exact_mod_cast hm
    linear_combination -h'
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    have h : ((k : ℂ) * y - k * x) = n * m := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hm
    field_simp
    push_cast
    linear_combination -h

/-- [formal-checked] The ruler on a composite ring: the comb `δ₀ − δ₈` on `ℤ/16` reads zero at the mode `k`,
`χ_k(0) = χ_k(8)`, if and only if `k` is even. -/
theorem comb_silent_iff_even (k : ℤ) : mode 16 k 0 = mode 16 k 8 ↔ Even k := by
  rw [mode_eq_iff (by norm_num), Int.modEq_iff_dvd, even_iff_two_dvd]
  simp only [mul_zero, sub_zero, Nat.cast_ofNat]
  omega

/-- [formal-checked] The comb `δ₀ − δ₈` on `ℤ/16` is silent at every even mode. -/
theorem comb_silent_at_even (k : ℤ) (hk : Even k) : mode 16 k 0 - mode 16 k 8 = 0 :=
  sub_eq_zero.mpr ((comb_silent_iff_even k).mpr hk)

/-! ## 2. The frame potential is the frame operator's second trace -/

section Frame

variable {ι κ : Type*} [Fintype κ]

/-- [definition] A place's power in a frame `F` whose places are its columns: `r_j = ‖f_j‖²`. -/
noncomputable def placePower (F : Matrix κ ι ℂ) (j : ι) : ℝ := ∑ i, ‖F i j‖ ^ 2

/-- [proved-standard; formal-checked] The Gram matrix's diagonal holds the places' powers. -/
theorem gram_diag (F : Matrix κ ι ℂ) (j : ι) : (Fᴴ * F) j j = (placePower F j : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, placePower]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

variable [Fintype ι]

/-- [definition] The frame potential: the summed squared pairings of the places, `Σ_(i,j) ‖⟨f_i, f_j⟩‖²`. -/
noncomputable def framePotential (F : Matrix κ ι ℂ) : ℝ := ∑ i, ∑ j, ‖(Fᴴ * F) i j‖ ^ 2

/-- [proved-standard; formal-checked] **Loudness is the frame operator's trace**: `tr(FFᴴ) = Σ_j ‖f_j‖²`. -/
theorem trace_frameOperator (F : Matrix κ ι ℂ) :
    (F * Fᴴ).trace = ((∑ j, placePower F j : ℝ) : ℂ) := by
  rw [Matrix.trace_mul_comm, Matrix.trace]
  push_cast
  exact Finset.sum_congr rfl fun j _ => gram_diag F j

/-- [proved-standard; formal-checked] **The frame potential is the frame operator's second trace**:
`Σ_(i,j) ‖⟨f_i, f_j⟩‖² = tr((FFᴴ)²)`. -/
theorem framePotential_eq_trace_sq (F : Matrix κ ι ℂ) :
    (framePotential F : ℂ) = ((F * Fᴴ) * (F * Fᴴ)).trace := by
  have hH : (Fᴴ * F).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self F
  have h1 : (framePotential F : ℂ) = ((Fᴴ * F) * (Fᴴ * F)).trace := by
    simp only [framePotential, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply (M := Fᴴ * F)]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj', ← Complex.star_def, hH.apply j i]
  rw [h1, show Fᴴ * F * (Fᴴ * F) = Fᴴ * (F * Fᴴ * F) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- [proved-standard; formal-checked] The squared powers sum to at most the frame potential: the diagonal's share of
the Gram matrix's squared entries. -/
theorem sum_sq_placePower_le (F : Matrix κ ι ℂ) :
    ∑ j, placePower F j ^ 2 ≤ framePotential F := by
  unfold framePotential
  refine Finset.sum_le_sum fun j _ => ?_
  have h : ‖(Fᴴ * F) j j‖ ^ 2 ≤ ∑ i, ‖(Fᴴ * F) j i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖(Fᴴ * F) j i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [gram_diag] at h
  have habs : ‖((placePower F j : ℝ) : ℂ)‖ ^ 2 = placePower F j ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rwa [habs] at h

/-- [proved-standard; formal-checked] **Color fills no more modes than loudness fills places**: the participation
`(tr S)²/tr S²`, with `tr S = Σ_j r_j` and `tr S²` the frame potential, is at most `(Σ_j r_j)²/Σ_j r_j²`. -/
theorem participation_le (F : Matrix κ ι ℂ) (hpos : 0 < ∑ j, placePower F j ^ 2) :
    (∑ j, placePower F j) ^ 2 / framePotential F ≤
      (∑ j, placePower F j) ^ 2 / ∑ j, placePower F j ^ 2 :=
  div_le_div_of_nonneg_left (sq_nonneg _) hpos (sum_sq_placePower_le F)

end Frame

/-! ## 3. A loop's face reads only the remainders -/

section Loop

variable {ι : Type*} [Fintype ι]

open Real in
/-- [definition] A loop's face: `Z = Σ_j λ_j e^(2πi n_j)`, the modes' densities `λ_j` against their numbers `n_j`
after one winding of the receiver's phase. -/
noncomputable def loopFace (lam : ι → ℂ) (n : ι → ℝ) : ℂ :=
  ∑ j, lam j * Complex.exp (2 * π * Complex.I * n j)

open Real in
/-- [proved-standard; formal-checked] **The whole windings drop out**: moving each mode's number by a whole number
leaves the face. -/
theorem loopFace_add_int (lam : ι → ℂ) (n : ι → ℝ) (W : ι → ℤ) :
    loopFace lam (fun j => n j + W j) = loopFace lam n := by
  unfold loopFace
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have : (2 * π * Complex.I * ((n j + W j : ℝ) : ℂ)) =
      2 * π * Complex.I * n j + W j * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- [proved-standard; formal-checked] **The face reads the remainders**: each mode's number may be replaced by its
fractional part. -/
theorem loopFace_fract (lam : ι → ℂ) (n : ι → ℝ) :
    loopFace lam (fun j => Int.fract (n j)) = loopFace lam n := by
  have := loopFace_add_int lam n (fun j => -⌊n j⌋)
  rw [← this]
  congr 1
  funext j
  rw [Int.fract]; push_cast; ring

/-- [proved-derived; formal-checked] Two loops whose modes share their remainders share their face. -/
theorem loopFace_eq_of_fract_eq (lam : ι → ℂ) (n n' : ι → ℝ)
    (h : ∀ j, Int.fract (n j) = Int.fract (n' j)) : loopFace lam n = loopFace lam n' := by
  rw [← loopFace_fract lam n, ← loopFace_fract lam n']
  congr 1
  funext j
  exact h j

/-- [proved-derived; formal-checked] **The geometric phase is a function of the remainders**: `Γ_g = arg Z` agrees
on two loops whose modes share their remainders. -/
theorem loopPhase_eq_of_fract_eq (lam : ι → ℂ) (n n' : ι → ℝ)
    (h : ∀ j, Int.fract (n j) = Int.fract (n' j)) :
    Complex.arg (loopFace lam n) = Complex.arg (loopFace lam n') := by
  rw [loopFace_eq_of_fract_eq lam n n' h]

end Loop

/-! ## 4. A commutator is an AND -/

/-- [definition] The first move of the ruler: the 5-cycle `(0 1 2 3 4)`. -/
def fiveCycleA : Equiv.Perm (Fin 5) := c[0, 1, 2, 3, 4]

/-- [definition] The second move of the ruler: the 5-cycle `(0 1 3 4 2)`. -/
def fiveCycleB : Equiv.Perm (Fin 5) := c[0, 1, 3, 4, 2]

/-- [definition] The ruler's commutator: the 5-cycle `(0 4 1 3 2)`. -/
def fiveCycleC : Equiv.Perm (Fin 5) := c[0, 4, 1, 3, 2]

/-- [formal-checked] The first move is a cycle on all five places. -/
theorem fiveCycleA_cycleType : fiveCycleA.cycleType = {5} := by
  have hc : fiveCycleA.IsCycle :=
    Cycle.isCycle_formPerm _ (by decide) ⟨0, 1, by decide, by simp, by simp⟩
  have hs : fiveCycleA.support.card = 5 := by decide
  rw [hc.cycleType, hs]

/-- [formal-checked] The second move is a cycle on all five places. -/
theorem fiveCycleB_cycleType : fiveCycleB.cycleType = {5} := by
  have hc : fiveCycleB.IsCycle :=
    Cycle.isCycle_formPerm _ (by decide) ⟨0, 1, by decide, by simp, by simp⟩
  have hs : fiveCycleB.support.card = 5 := by decide
  rw [hc.cycleType, hs]

/-- [formal-checked] **The commutator of the two moves**: `a b a⁻¹ b⁻¹ = (0 4 1 3 2)`. -/
theorem commutator_eq : fiveCycleA * fiveCycleB * fiveCycleA⁻¹ * fiveCycleB⁻¹ = fiveCycleC := by decide

/-- [formal-checked] The commutator is a cycle. -/
theorem commutator_isCycle : (fiveCycleA * fiveCycleB * fiveCycleA⁻¹ * fiveCycleB⁻¹).IsCycle := by
  rw [commutator_eq]
  exact Cycle.isCycle_formPerm _ (by decide) ⟨0, 4, by decide, by simp, by simp⟩

/-- [formal-checked] **The commutator of the two 5-cycles is a 5-cycle.** -/
theorem commutator_cycleType :
    (fiveCycleA * fiveCycleB * fiveCycleA⁻¹ * fiveCycleB⁻¹).cycleType = {5} := by
  have hs : (fiveCycleA * fiveCycleB * fiveCycleA⁻¹ * fiveCycleB⁻¹).support.card = 5 := by decide
  rw [commutator_isCycle.cycleType, hs]

/-- [proved-standard; formal-checked] The commutator is the identity when its first argument is. -/
theorem commutator_one_left {G : Type*} [Group G] (b : G) : (1 : G) * b * 1⁻¹ * b⁻¹ = 1 := by simp

/-- [proved-standard; formal-checked] The commutator is the identity when its second argument is. -/
theorem commutator_one_right {G : Type*} [Group G] (a : G) : a * 1 * a⁻¹ * 1⁻¹ = 1 := by simp

/-- [formal-checked] A move against itself commutes: the record's sentence on two 5-cycles needs its pair chosen. -/
theorem commutator_self {G : Type*} [Group G] (a : G) : a * a * a⁻¹ * a⁻¹ = 1 := by simp

/-- [formal-checked] **A commutator is an AND**: with each move present or absent, the commutator is the 5-cycle
`(0 4 1 3 2)` when both are present and the identity otherwise. -/
theorem commutator_and (x y : Bool) :
    (if x then fiveCycleA else 1) * (if y then fiveCycleB else 1) * (if x then fiveCycleA else 1)⁻¹ *
        (if y then fiveCycleB else 1)⁻¹ = if x && y then fiveCycleC else 1 := by
  cases x <;> cases y <;> decide

/-- [proved-standard; formal-checked] **In a commutative group every commutator is the identity**, so no word there
is an AND. -/
theorem commutator_trivial_of_comm {G : Type*} [CommGroup G] (a b : G) : a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_comm a b, mul_inv_cancel_right, mul_inv_cancel]

/-- [proved-standard; formal-checked] Every commutator of permutations has sign one: it lies in the alternating
group. -/
theorem sign_commutator {α : Type*} [DecidableEq α] [Fintype α] (a b : Equiv.Perm α) :
    Equiv.Perm.sign (a * b * a⁻¹ * b⁻¹) = 1 := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutator_trivial_of_comm _ _

/-- [formal-checked] The ruler's two moves have sign one. -/
theorem fiveCycle_sign : Equiv.Perm.sign fiveCycleA = 1 ∧ Equiv.Perm.sign fiveCycleB = 1 := by
  constructor <;> decide

/-- [proved-standard; formal-checked] **A word over a commutative monoid depends on its counts alone**: two words
with the same letters in another order have the same product. -/
theorem abelian_word_counts {G : Type*} [CommMonoid G] {w w' : List G} (h : w.Perm w') : w.prod = w'.prod :=
  h.prod_eq

/-! ## 5. A common scale leaves the intervals -/

/-- [proved-standard; formal-checked] A common scale `k` leaves every ratio of two frequencies. -/
theorem doppler_ratio (k a b : ℝ) (hk : k ≠ 0) : (k * a) / (k * b) = a / b := mul_div_mul_left a b hk

/-- [proved-standard; formal-checked] In the logarithm's chart a common scale is a translation by `log k`. -/
theorem doppler_log {k a : ℝ} (hk : 0 < k) (ha : 0 < a) : Real.log (k * a) = Real.log k + Real.log a :=
  Real.log_mul hk.ne' ha.ne'

/-- [proved-standard; formal-checked] **The intervals stay**: a common scale leaves every difference of
logarithms. -/
theorem doppler_interval {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) :
    Real.log (k * a) - Real.log (k * b) = Real.log a - Real.log b := by
  rw [doppler_log hk ha, doppler_log hk hb]
  ring

end Holonics.Compression.FaithfulModes
