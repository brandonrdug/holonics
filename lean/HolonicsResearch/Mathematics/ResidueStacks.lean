import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# A lattice of the natural numbers by slices: live stacks, dark stacks, and what crosses a ray

The record `research/records/2026-11-25_A_RECEIVER_MEETS_A_MEDIUM_THROUGH_A_TAPER_A_ROD_READS_AN_EFFORT_ALONG_IT_A_CONE_A_FLOW_THROUGH_ITS_MOUTH_IT_CARRIES_BY_A_STROKE_THAT_DOES_NOT_RETRACE_AND_SHE_GAINS_FROM_THE_FAR_PAST_ONLY_WHERE_IT_REPEATS_ITSELF.md`
(atlas `prime.slice-lattice-live-and-dark-stacks`, `winding.closed-curves-link-only-in-three`) lays the
natural numbers in slices of `M = w h` places, a slice a depth, and asks how the primes stand in the
stack over one place of the slice.

A place `n` stands in the stack `n % M` at depth `n / M` (`stack`, `depth`). Read through two crossing
rings of `w` and `h` places, the stack is the pair `(n % w, n % h)`.

[proved-derived; formal-checked] What is proved.

1. **Two coprime rings weave one strand** (`coprime_rings_one_strand`): places that agree on both rings
   stand in one stack, so the pair of remainders is the stack. **Rings with a common factor weave
   several** (`common_factor_several_strands`): a place nearer than `w h` already repeats the pair.
2. **A dark stack holds at most one prime, its own common factor with the slice**
   (`dark_stack_holds_its_gcd`). **A live stack holds a prime beyond every depth**
   (`live_stack_holds_primes_beyond_every_depth`, Dirichlet's theorem as Mathlib proves it).
3. **The slice of three by five** (`stack_two_one_three_by_five` and its three other readings;
   `live_stacks_of_fifteen`): eight live stacks, and the stack at `(2, 1)` is `11`, `7`, `5` or `7`
   by the reading.
4. **A shape matched to its load** (`matched_shape`): `N` cells, `s` in series by `p` side by side,
   matched to a load `R` where `s r = p R`, have `s² r = N R`: the load picks the factorization.
5. **What crosses a ray, counted** (`one_turn_across_a_ray`, `two_hands_each`, `rim_is_a_circle`,
   `curves_link_curves`): with `k` directions across a ray the turns among them are one circle only
   at `k = 2`; a wave of one index and a wave of two symmetric trace-free indices then have equally
   many states, two; the rim of the cell dual to a line is a circle only in three dimensions; and
   two closed curves link only there. These are the counts alone.

Scope. Not proved here: that the live stacks hold equal shares (de la Vallée Poussin), the lag of the
stacks that hold squares (Chebyshev's bias), or any statement of dimension beyond its count. The
counts of item 5 are arithmetic; that they count the states of a wave, the turns across a ray and the
linking of cycles is stated in the record.

The computational object is the helical pair interaction along a strand: two rings read one strand,
and the pair of their residues is its address. Of the winding guide's six general objects this
touches the helix (a ring and its carry: the stack and the depth), the pair (two rings crossing) and
faces and placement (a stack is a place of the slice); the cell holonomy, the tube and the tower
thread stay attached.

Consumers: the atlas rows above and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.ResidueStacks

/-- The stack a place stands in, in a lattice whose slices hold `M` places. -/
def stack (M n : ℕ) : ℕ := n % M

/-- The depth of a place: the count of whole slices before it. -/
def depth (M n : ℕ) : ℕ := n / M

/-- A place is its depth's slices and its stack: the ring and its carry. -/
theorem place_of_depth_and_stack (M n : ℕ) : M * depth M n + stack M n = n :=
  Nat.div_add_mod n M

/-- **Two coprime rings weave one strand.** Places that agree on a ring of `w` and on a ring of `h`
coprime to it stand in one stack of the slice `w h`. -/
theorem coprime_rings_one_strand {w h : ℕ} (hc : Nat.Coprime w h) {m n : ℕ}
    (hw : m % w = n % w) (hh : m % h = n % h) : stack (w * h) m = stack (w * h) n :=
  (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨hw, hh⟩

/-- **Rings with a common factor weave several strands.** A place nearer than `w h` already repeats
the pair of remainders of place `0`. -/
theorem common_factor_several_strands {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (hd : 1 < Nat.gcd w h) :
    Nat.lcm w h % w = 0 ∧ Nat.lcm w h % h = 0 ∧ 0 < Nat.lcm w h ∧ Nat.lcm w h < w * h := by
  have hpos : 0 < Nat.lcm w h := Nat.lcm_pos hw hh
  have hmul : Nat.gcd w h * Nat.lcm w h = w * h := Nat.gcd_mul_lcm w h
  refine ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_lcm_left w h),
    Nat.mod_eq_zero_of_dvd (Nat.dvd_lcm_right w h), hpos, ?_⟩
  nlinarith

/-- **A dark stack holds at most one prime: its own common factor with the slice.** -/
theorem dark_stack_holds_its_gcd {M a p : ℕ} (hp : p.Prime) (hstack : stack M p = stack M a)
    (hdark : 1 < Nat.gcd M a) : p = Nat.gcd M a := by
  have h : Nat.gcd M p = Nat.gcd M a := by
    unfold stack at hstack
    rw [Nat.gcd_rec M p, Nat.gcd_rec M a, hstack]
  have hd : Nat.gcd M a ∣ p := by
    rw [← h]
    exact Nat.gcd_dvd_right M p
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · omega
  · exact h1.symm

/-- **A live stack holds a prime beyond every depth** (Dirichlet's theorem, as Mathlib proves it). -/
theorem live_stack_holds_primes_beyond_every_depth {M a : ℕ} (hM : M ≠ 0)
    (hlive : Nat.Coprime a M) (z : ℕ) :
    ∃ p, p.Prime ∧ stack M p = stack M a ∧ z < depth M p := by
  obtain ⟨p, hgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq ((z + 1) * M) hM hlive
  refine ⟨p, hp, hmod, ?_⟩
  have hle : z + 1 ≤ p / M :=
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hM)).2 (le_of_lt hgt)
  exact hle

/-- The slice of three by five, read by its two rings: the stack at `(2, 1)` is `11`. -/
theorem stack_two_one_three_by_five (n : ℕ) : (n % 3 = 2 ∧ n % 5 = 1) ↔ stack 15 n = 11 := by
  unfold stack; omega

/-- The slice of five by three, read by its two rings: the stack at `(2, 1)` is `7`. -/
theorem stack_two_one_five_by_three (n : ℕ) : (n % 5 = 2 ∧ n % 3 = 1) ↔ stack 15 n = 7 := by
  unfold stack; omega

/-- Read as a raster three wide, the place `(2, 1)` of the slice is `5`: a dark stack. -/
theorem raster_two_one_three_wide (n : ℕ) :
    (stack 15 n % 3 = 2 ∧ stack 15 n / 3 = 1) ↔ stack 15 n = 5 := by
  unfold stack; omega

/-- Read as a raster five wide, the place `(2, 1)` of the slice is `7`: a live stack. -/
theorem raster_two_one_five_wide (n : ℕ) :
    (stack 15 n % 5 = 2 ∧ stack 15 n / 5 = 1) ↔ stack 15 n = 7 := by
  unfold stack; omega

/-- Eight of the fifteen stacks are live. -/
theorem live_stacks_of_fifteen : Nat.totient 15 = 8 := by decide

/-- **A shape matched to its load.** `N` cells of resistance `r`, `s` in series by `p` side by side,
matched to a load `R` (`s r = p R`): the load picks the factorization, `s² r = N R`. -/
theorem matched_shape (s p N r R : ℚ) (hN : s * p = N) (hmatch : s * r = p * R) :
    s ^ 2 * r = N * R := by
  rw [← hN]
  calc s ^ 2 * r = s * (s * r) := by ring
    _ = s * (p * R) := by rw [hmatch]
    _ = s * p * R := by ring

/-- **One circle of turns across a ray.** With `k` directions across a ray, the turns among them are
`k (k − 1) / 2`, one circle exactly at `k = 2`: three dimensions of space. -/
theorem one_turn_across_a_ray (k : ℕ) : k * (k - 1) = 2 ↔ k = 2 := by
  constructor
  · intro h
    have hk : k ≤ 3 := by
      by_contra hc
      have h4 : 4 ≤ k := by omega
      have : 4 * 3 ≤ k * (k - 1) := Nat.mul_le_mul h4 (by omega)
      omega
    interval_cases k <;> simp_all
  · rintro rfl; rfl

/-- **Two hands each.** A wave of one index has `k` states across its ray and a wave of two symmetric
trace-free indices `k (k + 1) / 2 − 1`; the two counts agree exactly at `k = 2`. -/
theorem two_hands_each (k : ℕ) : k * (k + 1) = 2 * (k + 1) ↔ k = 2 := by
  constructor
  · intro h; exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos k) h
  · rintro rfl; rfl

/-- The rim of the cell dual to a line in `n` dimensions has `n − 2` dimensions: a circle exactly
in three. -/
theorem rim_is_a_circle (n : ℕ) : n - 2 = 1 ↔ n = 3 := by omega

/-- A closed strand of `p` dimensions and one of `q` link in `p + q + 1` dimensions. -/
def linkDimension (p q : ℕ) : ℕ := p + q + 1

/-- **Closed curves link closed curves in three dimensions, and strands of one kind link their own
kind in three dimensions only as curves.** -/
theorem curves_link_curves : linkDimension 1 1 = 3 ∧ ∀ p, linkDimension p p = 3 ↔ p = 1 := by
  refine ⟨rfl, fun p => ?_⟩
  unfold linkDimension; omega

end Holonics.Mathematics.ResidueStacks
