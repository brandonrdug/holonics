import HolonicsResearch.Foundation.EuclideanResidueTransport
import HolonicsResearch.Compression.FacesOnCycles
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-!
# A remainder convention is a gauge: the sections of `ℤ → ℤ/m` are one orbit, every one of them carries, and a sign is read whole only at an odd modulus

Sources: `Foundation/EuclideanResidueTransport` (the chart `ℤ ≃ ZMod m × ℤ` through the floor
remainder, and the truncated coordinates beside it), `Compression/FacesOnCycles` (atlas
`face.carry-bockstein`: the floor remainder's carry is a 2-cocycle and no integer coboundary),
`Geometry/PhaseCarry` (atlas `winding.carry-cocycle`), `Holonics/HNN/LatticeWord.carrier_ring_read`
and `HNN/SolvedChartBits.valMinAbs_intCast_eq` (a wrapped sum read at the balanced representative);
atlas `radix.release-quotient-or-section` and `radix.two-place-reconstruction`, which had no Lean
owner; the record of November 15 that states them; an outside reader's reply of November 19 (its
section "negativity, modularity, orientation": one family `div_rem` over the conventions floor,
ceiling, balanced and two's complement, with the change of convention moving a multiple of the
modulus between remainder and quotient).

What is proved.

1. **Sections and their charts** (`IsSection`, `winding`, `section_add_winding`, `sectionChart`):
   a section `s : ZMod m → ℤ` picks one integer in every residue class, and every section gives a
   chart `ℤ ≃ ZMod m × ℤ`, `x ↦ (x mod m, (x − s (x mod m))/m)`. Through the floor section it is the
   repository's `intEuclideanChart` (`sectionChart_floor`). The chart is a stack of residues
   (`pop_push`, `push_pop`): its inverse pushes a residue under an integer and the chart pops it,
   so a stack's depth is the integer's count of places.
2. **The conventions are one orbit, free and transitive** (`shift`, `isSection_shift`,
   `existsUnique_shift`, `winding_shift`): two sections differ by `m·δ` for exactly one
   `δ : ZMod m → ℤ`, every such shift of a section is a section, and the winding read through the
   shifted section is the old winding less `δ` at the residue. What a change of convention moves is
   a multiple of the modulus, from the remainder to the quotient.
3. **The interval family** (`intervalSection`, `isSection_interval`, `intervalSection_mem`,
   `intervalSection_reads`, `eq_intervalSection`): for every `a` the representatives in
   `[a, a + m)` are a section, it returns every integer of that interval from its residue, and a
   section whose values lie in the interval is that one. `floorSection` is the interval at `0`
   (`floorSection_eq_interval`); `twosSection j` on `ZMod 2^(j+1)` is the interval at `−2^j`
   (`twosSection_eq_interval`), it reads negative exactly when the residue's top place is set
   (`twosSection_neg_iff`), and it differs from the balanced section `ZMod.valMinAbs` at one
   residue, the half `2^j` (`twosSection_eq_balanced_sub`). The balanced section has the least
   magnitude among all lifts (`balancedSection_natAbs_le`). Under the floor convention the
   winding has the two fixed points `0` and `−1` (`winding_floor_fixed_iff`): `−1` pops the top
   residue and itself again; under the balanced convention, for `m ≥ 3`, only `0`
   (`winding_balanced_fixed_iff`).
4. **Truncation is outside the family** (`truncated_not_section`): the remainder of division
   truncated toward zero is not a function of the residue (`−3` and `5` share a residue modulo `8`
   and read `−3` and `5`), so it is no section: it reads the source's sign.
5. **A sign is read whole exactly at an odd modulus** (`exists_odd_section_iff`): a section that
   commutes with negation exists if and only if `m` is odd. At an even modulus the half is its own
   negative and no convention gives it a sign.
6. **Every section carries** (`carry`, `section_add`, `carry_shift`, `carry_floor`,
   `exists_carry_ne_zero`): `s r + s r' = s (r + r') + m·carry`, a change of convention changes
   the carry by the coboundary of `δ`, the floor section's carry is the repository's
   `FacesOnCycles.carry`, and for `m ≥ 2` no section has a carry that vanishes everywhere, from
   `FacesOnCycles.carry_not_coboundary`. No remainder convention is additive.
7. **A quotient commutes with the sum, a section does not** (`read_once_after_wrapped_sum`,
   `release`, `release_add`, `release_not_schedule_free`): a sum of residues is the residue of the
   integer sum, so one reading through the interval section after the sum returns the total
   whenever the total lies in the interval, whatever the partial sums did. The release of an
   integer through a section, `x − s (x mod m)`, fails additivity by `m` times the carry of the
   two residues, and a release after every add depends on the bracketing (`m = 2`, the terms
   `1, 1, 0`).

`[interpretation]` A remainder convention is a choice of gauge on the residue receiver: the
receiver's quotient is fixed, the representative is chosen, and the choice is paid for in the
winding. Floor, balanced and two's complement are three points of one orbit. What no choice
removes is the carry (item 6), and what no choice supplies at an even modulus is a sign for the
half (item 5): at `2^w` the half is the half-turn residue, the one place where two's complement
and the balanced reading part.

Limits: the fixed points of the winding are named, and that every integer's windings reach one
of them is not proved; the integers over one modulus only; no lattice or matrix modulus (the cokernel with no
section chosen is `Foundation/LatticeTransport`'s); the ceiling convention is the interval at
`1 − m` and is not named; nothing on rounding to a grain of the reals (the atlas row's `ρ_g` on
`ℝ`); the float side of `radix.release-quotient-or-section` (a float add releases at every step)
is not formalized; the counterexample of item 7 is one modulus and one triple.
Computational object: the helical pair interaction; touches the helix (a residue and its winding)
and faces and placement (which representative a face reads); the pair, the cell holonomy, the tube
and the tower thread stay attached.
Consumers: the atlas rows `radix.release-quotient-or-section`, `radix.two-place-reconstruction`
and `radix.section-gauge`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.SectionGauge

open Holonics.Foundation.EuclideanResidueTransport
open Holonics.Compression

variable {m : ℕ}

/-! ## 1. Sections and their charts -/

/-- [definition] A section of the residue receiver `ℤ → ZMod m`: one integer representative of
every residue. -/
def IsSection (m : ℕ) (s : ZMod m → ℤ) : Prop := ∀ r : ZMod m, ((s r : ℤ) : ZMod m) = r

/-- [definition] The winding of an integer read through a section: the quotient left when the
section's representative of its residue is taken off. -/
def winding (m : ℕ) (s : ZMod m → ℤ) (x : ℤ) : ℤ := (x - s (x : ZMod m)) / (m : ℤ)

/-- [proved-standard; formal-checked] An integer and the section's representative of its residue
differ by a multiple of the modulus. -/
theorem dvd_sub_section {s : ZMod m → ℤ} (hs : IsSection m s) (x : ℤ) :
    (m : ℤ) ∣ x - s (x : ZMod m) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hs]
  exact sub_self _

/-- [proved-standard; formal-checked] Division with remainder through any section:
`x = s (x mod m) + m · winding`. -/
theorem section_add_winding {s : ZMod m → ℤ} (hs : IsSection m s) (x : ℤ) :
    s (x : ZMod m) + (m : ℤ) * winding m s x = x := by
  unfold winding
  rw [Int.mul_ediv_cancel' (dvd_sub_section hs x)]
  ring

/-- [proved-derived; formal-checked] Every section gives a chart `ℤ ≃ ZMod m × ℤ`: the residue
and the winding through that section. -/
def sectionChart (m : ℕ) [NeZero m] (s : ZMod m → ℤ) (hs : IsSection m s) : ℤ ≃ ZMod m × ℤ where
  toFun x := ((x : ZMod m), winding m s x)
  invFun p := s p.1 + (m : ℤ) * p.2
  left_inv x := section_add_winding hs x
  right_inv p := by
    have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
    have hc : ((s p.1 + (m : ℤ) * p.2 : ℤ) : ZMod m) = p.1 := by
      push_cast
      rw [hs]
      simp
    apply Prod.ext
    · exact hc
    · change winding m s (s p.1 + (m : ℤ) * p.2) = p.2
      rw [winding, hc, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hm]

/-- [proved-derived; formal-checked] **The chart is a stack.** Pushing a residue under an integer,
`(r, q) ↦ s r + m·q`, and popping it, `x ↦ (x mod m, winding)`, undo each other: the pop of a
push returns the residue and the integer that was there. -/
theorem pop_push [NeZero m] {s : ZMod m → ℤ} (hs : IsSection m s) (r : ZMod m) (q : ℤ) :
    sectionChart m s hs (s r + (m : ℤ) * q) = (r, q) :=
  (sectionChart m s hs).apply_symm_apply (r, q)

/-- [proved-derived; formal-checked] The push of a pop returns the integer. -/
theorem push_pop [NeZero m] {s : ZMod m → ℤ} (hs : IsSection m s) (x : ℤ) :
    s (sectionChart m s hs x).1 + (m : ℤ) * (sectionChart m s hs x).2 = x :=
  (sectionChart m s hs).symm_apply_apply x

/-! ## 2. The conventions are one orbit -/

/-- [definition] A section moved by `δ`: at each residue the representative is shifted by `δ`
turns of the modulus. -/
def shift (m : ℕ) (s : ZMod m → ℤ) (δ : ZMod m → ℤ) : ZMod m → ℤ := fun r => s r + (m : ℤ) * δ r

/-- [proved-standard; formal-checked] A shifted section is a section. -/
theorem isSection_shift {s : ZMod m → ℤ} (hs : IsSection m s) (δ : ZMod m → ℤ) :
    IsSection m (shift m s δ) := by
  intro r
  unfold shift
  push_cast
  rw [hs]
  simp

/-- [proved-derived; formal-checked] **The conventions are one orbit, free and transitive**: any
two sections differ by `m·δ` for exactly one `δ`. -/
theorem existsUnique_shift [NeZero m] {s s' : ZMod m → ℤ} (hs : IsSection m s)
    (hs' : IsSection m s') : ∃! δ : ZMod m → ℤ, s' = shift m s δ := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h : ∀ r, ∃ c, s' r - s r = (m : ℤ) * c := by
    intro r
    have hd : (m : ℤ) ∣ s' r - s r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hs, hs']
      exact sub_self _
    exact hd
  choose δ hδ using h
  refine ⟨δ, funext fun r => ?_, ?_⟩
  · unfold shift
    linarith [hδ r]
  · intro δ' hδ'
    funext r
    have h1 := congrFun hδ' r
    unfold shift at h1
    have h2 : (m : ℤ) * δ' r = (m : ℤ) * δ r := by linarith [hδ r]
    exact mul_left_cancel₀ hm h2

/-- [proved-derived; formal-checked] **A change of convention moves turns of the modulus from the
remainder to the quotient**: the winding through the shifted section is the old winding less `δ`
at the residue. -/
theorem winding_shift [NeZero m] {s : ZMod m → ℤ} (hs : IsSection m s) (δ : ZMod m → ℤ)
    (x : ℤ) : winding m (shift m s δ) x = winding m s x - δ (x : ZMod m) := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h1 := section_add_winding hs x
  have h2 : x - shift m s δ (x : ZMod m) = (m : ℤ) * (winding m s x - δ (x : ZMod m)) := by
    unfold shift
    linear_combination (-1 : ℤ) * h1
  rw [winding, h2, Int.mul_ediv_cancel_left _ hm]

/-! ## 3. The interval family: floor, two's complement, balanced -/

/-- [definition] The section with representatives in `[a, a + m)`. -/
def intervalSection (m : ℕ) (a : ℤ) (r : ZMod m) : ℤ := a + ((r - (a : ZMod m)).val : ℤ)

/-- [proved-standard; formal-checked] The interval representatives are a section. -/
theorem isSection_interval [NeZero m] (a : ℤ) : IsSection m (intervalSection m a) := by
  intro r
  unfold intervalSection
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

/-- [proved-standard; formal-checked] The interval section's values lie in `[a, a + m)`. -/
theorem intervalSection_mem [NeZero m] (a : ℤ) (r : ZMod m) :
    a ≤ intervalSection m a r ∧ intervalSection m a r < a + m := by
  unfold intervalSection
  have h : ((r - (a : ZMod m)).val : ℤ) < m := by exact_mod_cast ZMod.val_lt (r - (a : ZMod m))
  have h0 : (0 : ℤ) ≤ ((r - (a : ZMod m)).val : ℤ) := Int.natCast_nonneg _
  constructor <;> linarith

/-- [proved-standard; formal-checked] **An integer of the interval is read whole from its
residue** (atlas `radix.two-place-reconstruction`: the low places and a declared interval give the
value). -/
theorem intervalSection_reads [NeZero m] (a x : ℤ) (h1 : a ≤ x) (h2 : x < a + m) :
    intervalSection m a (x : ZMod m) = x := by
  unfold intervalSection
  have hc : ((x : ZMod m) - (a : ZMod m)) = ((x - a : ℤ) : ZMod m) := by push_cast; ring
  rw [hc, ZMod.val_intCast, Int.emod_eq_of_lt (by linarith) (by linarith)]
  ring

/-- [proved-derived; formal-checked] A section whose values lie in `[a, a + m)` is the interval
section: the interval fixes the convention. -/
theorem eq_intervalSection [NeZero m] {s : ZMod m → ℤ} (hs : IsSection m s) (a : ℤ)
    (h : ∀ r, a ≤ s r ∧ s r < a + m) : s = intervalSection m a := by
  funext r
  have h1 := intervalSection_reads (m := m) a (s r) (h r).1 (h r).2
  rw [hs] at h1
  exact h1.symm

/-- [definition] The floor section: the representative in `[0, m)`. -/
def floorSection (m : ℕ) (r : ZMod m) : ℤ := (r.val : ℤ)

/-- [proved-standard; formal-checked] The floor representatives are a section. -/
theorem isSection_floor [NeZero m] : IsSection m (floorSection m) := by
  intro r
  unfold floorSection
  push_cast
  exact ZMod.natCast_zmod_val r

/-- [proved-standard; formal-checked] The floor section is the interval section at `0`. -/
theorem floorSection_eq_interval [NeZero m] : floorSection m = intervalSection m 0 := by
  apply eq_intervalSection isSection_floor
  intro r
  unfold floorSection
  have h : ((r.val : ℕ) : ℤ) < m := by exact_mod_cast ZMod.val_lt r
  have h0 : (0 : ℤ) ≤ ((r.val : ℕ) : ℤ) := Int.natCast_nonneg _
  constructor <;> linarith

/-- [proved-derived; formal-checked] Through the floor section the chart is the repository's
`intEuclideanChart`. -/
theorem sectionChart_floor [NeZero m] (x : ℤ) :
    sectionChart m (floorSection m) isSection_floor x = intEuclideanChart m x := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  apply Prod.ext
  · rfl
  · change winding m (floorSection m) x = x / (m : ℤ)
    have h : x - floorSection m (x : ZMod m) = (m : ℤ) * (x / (m : ℤ)) := by
      unfold floorSection
      rw [ZMod.val_intCast]
      have := Int.emod_add_mul_ediv x (m : ℤ)
      linarith
    rw [winding, h, Int.mul_ediv_cancel_left _ hm]

/-- [definition] The balanced section: Mathlib's representative of least magnitude, in
`(−m/2, m/2]`. -/
def balancedSection (m : ℕ) (r : ZMod m) : ℤ := r.valMinAbs

/-- [proved-standard; formal-checked] The balanced representatives are a section. -/
theorem isSection_balanced : IsSection m (balancedSection m) := fun r => ZMod.coe_valMinAbs r

/-- [proved-standard; formal-checked] The balanced representative has the least magnitude among
the integers of its residue. -/
theorem balancedSection_natAbs_le [NeZero m] (r : ZMod m) (y : ℤ) (hy : (y : ZMod m) = r) :
    (balancedSection m r).natAbs ≤ y.natAbs :=
  ZMod.natAbs_min_of_le_div_two m _ y (by rw [balancedSection, ZMod.coe_valMinAbs, hy])
    (ZMod.natAbs_valMinAbs_le r)

/-- [definition] The two's complement section at `j + 1` places: the residue's digits read as
they stand below the half `2^j`, and less `2^(j+1)` from the half up. -/
def twosSection (j : ℕ) (r : ZMod (2 ^ (j + 1))) : ℤ :=
  if r.val < 2 ^ j then (r.val : ℤ) else (r.val : ℤ) - (2 : ℤ) ^ (j + 1)

/-- [proved-standard; formal-checked] The two's complement values are a section, with values in
`[−2^j, 2^j)`. -/
theorem twosSection_spec (j : ℕ) (r : ZMod (2 ^ (j + 1))) :
    ((twosSection j r : ℤ) : ZMod (2 ^ (j + 1))) = r ∧
      -(2 : ℤ) ^ j ≤ twosSection j r ∧ twosSection j r < (2 : ℤ) ^ j := by
  have hlt : ((r.val : ℕ) : ℤ) < (2 : ℤ) ^ (j + 1) := by exact_mod_cast ZMod.val_lt r
  have h0 : (0 : ℤ) ≤ ((r.val : ℕ) : ℤ) := Int.natCast_nonneg _
  have hp : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by ring
  have hz : (((2 : ℤ) ^ (j + 1) : ℤ) : ZMod (2 ^ (j + 1))) = 0 := by
    have h := ZMod.natCast_self (2 ^ (j + 1))
    push_cast at h ⊢
    exact h
  unfold twosSection
  split_ifs with h
  · have hc : ((r.val : ℕ) : ℤ) < (2 : ℤ) ^ j := by exact_mod_cast h
    refine ⟨?_, by linarith, hc⟩
    push_cast
    exact ZMod.natCast_zmod_val r
  · have hc : (2 : ℤ) ^ j ≤ ((r.val : ℕ) : ℤ) := by exact_mod_cast not_lt.mp h
    refine ⟨?_, by linarith, by linarith⟩
    rw [Int.cast_sub, hz, sub_zero]
    push_cast
    exact ZMod.natCast_zmod_val r

/-- [proved-derived; formal-checked] Two's complement is the interval section at `−2^j`. -/
theorem twosSection_eq_interval (j : ℕ) :
    twosSection j = intervalSection (2 ^ (j + 1)) (-(2 : ℤ) ^ j) := by
  apply eq_intervalSection (fun r => (twosSection_spec j r).1)
  intro r
  have h := twosSection_spec j r
  have hp : (((2 ^ (j + 1) : ℕ) : ℤ)) = 2 * (2 : ℤ) ^ j := by push_cast; ring
  refine ⟨h.2.1, ?_⟩
  rw [hp]
  linarith [h.2.2]

/-- [proved-standard; formal-checked] Two's complement reads negative exactly when the residue's
top place is set. -/
theorem twosSection_neg_iff (j : ℕ) (r : ZMod (2 ^ (j + 1))) :
    twosSection j r < 0 ↔ 2 ^ j ≤ r.val := by
  have hlt : ((r.val : ℕ) : ℤ) < (2 : ℤ) ^ (j + 1) := by exact_mod_cast ZMod.val_lt r
  have h0 : (0 : ℤ) ≤ ((r.val : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold twosSection
  split_ifs with h
  · constructor
    · intro hneg
      linarith
    · intro hle
      exact absurd h (not_lt.mpr hle)
  · constructor
    · intro _
      exact not_lt.mp h
    · intro _
      linarith

/-- [proved-derived; formal-checked] **Two's complement and the balanced section part at one
residue**: they agree but at the half `2^j`, which two's complement reads as `−2^j` and the
balanced section as `+2^j`. -/
theorem twosSection_eq_balanced_sub (j : ℕ) (r : ZMod (2 ^ (j + 1))) :
    twosSection j r =
      balancedSection (2 ^ (j + 1)) r - (if r.val = 2 ^ j then (2 : ℤ) ^ (j + 1) else 0) := by
  have hhalf : 2 ^ (j + 1) / 2 = 2 ^ j := by
    rw [pow_succ]
    exact Nat.mul_div_cancel _ (by norm_num)
  have hc : (((2 ^ (j + 1) : ℕ) : ℤ)) = (2 : ℤ) ^ (j + 1) := by push_cast; rfl
  unfold twosSection balancedSection
  rw [ZMod.valMinAbs_def_pos, hhalf, hc]
  split_ifs <;> omega

/-- [proved-derived; formal-checked] **Under the floor convention the winding has two fixed
points, `0` and `−1`.** Popping `−1` returns the top residue `m − 1` and `−1` again: a negative
integer is a stack that bottoms out in the top digit, where a nonnegative one bottoms out in
zeros. -/
theorem winding_floor_fixed_iff [NeZero m] (hm2 : 2 ≤ m) (x : ℤ) :
    winding m (floorSection m) x = x ↔ x = 0 ∨ x = -1 := by
  have hm : (0 : ℤ) < (m : ℤ) := by exact_mod_cast NeZero.pos m
  have hm2' : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
  have hw : winding m (floorSection m) x = x / (m : ℤ) :=
    congrArg Prod.snd (sectionChart_floor (m := m) x)
  rw [hw]
  constructor
  · intro h
    have h1 := Int.emod_add_mul_ediv x (m : ℤ)
    have h2 := Int.emod_nonneg x hm.ne'
    have h3 := Int.emod_lt_of_pos x hm
    rw [h] at h1
    rcases lt_trichotomy x 0 with hx | hx | hx
    · right
      by_contra hne
      have hx2 : x ≤ -2 := by omega
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -2 - x) (by linarith : (0 : ℤ) ≤ (m : ℤ) - 1)]
    · left
      exact hx
    · exfalso
      nlinarith [mul_pos hx (by linarith : (0 : ℤ) < (m : ℤ) - 1)]
  · rintro (rfl | rfl)
    · simp
    · have h := (Int.ediv_emod_unique (a := -1) (r := (m : ℤ) - 1) (q := -1) hm).mpr
        ⟨by ring, by omega, by omega⟩
      exact h.1

/-- [proved-derived; formal-checked] **Under the balanced convention the winding's one fixed
point is `0`** (for `m ≥ 3`): every sign bottoms out in zeros, and no residue stands for it. -/
theorem winding_balanced_fixed_iff [NeZero m] (hm3 : 3 ≤ m) (x : ℤ) :
    winding m (balancedSection m) x = x ↔ x = 0 := by
  have hm3' : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm3
  constructor
  · intro h
    have h1 := section_add_winding (isSection_balanced (m := m)) x
    rw [h] at h1
    have h2 := ZMod.valMinAbs_mem_Ioc (x : ZMod m)
    rw [Set.mem_Ioc] at h2
    have h4 : balancedSection m (x : ZMod m) = (x : ZMod m).valMinAbs := rfl
    rw [h4] at h1
    rcases lt_trichotomy x 0 with hx | hx | hx
    · exfalso
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - x) (by linarith : (0 : ℤ) ≤ (m : ℤ) - 1)]
    · exact hx
    · exfalso
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ x - 1) (by linarith : (0 : ℤ) ≤ (m : ℤ) - 1)]
  · rintro rfl
    simp [winding, balancedSection]

/-! ## 4. Truncation is outside the family -/

/-- [counterexample; formal-checked] The remainder of division truncated toward zero is not a
function of the residue: `−3` and `5` share a residue modulo `8` and read `−3` and `5`. Truncation
reads the source's sign and is no section. -/
theorem truncated_not_section :
    ¬ ∃ s : ZMod 8 → ℤ, ∀ x : ℤ, (intTruncatedCoordinates 8 x).1 = s (x : ZMod 8) := by
  rintro ⟨s, hs⟩
  have h1 := hs (-3)
  have h2 := hs 5
  have e : (((-3 : ℤ)) : ZMod 8) = ((5 : ℤ) : ZMod 8) := by decide
  have v1 : (intTruncatedCoordinates 8 (-3)).1 = -3 := by decide
  have v2 : (intTruncatedCoordinates 8 5).1 = 5 := by decide
  rw [v1, e] at h1
  rw [v2] at h2
  omega

/-! ## 5. A sign is read whole exactly at an odd modulus -/

/-- [proved-derived; formal-checked] **A section that commutes with negation exists exactly when
the modulus is odd.** At an even modulus the half is its own negative and no convention gives it
a sign; at an odd modulus the balanced section does it. -/
theorem exists_odd_section_iff [NeZero m] :
    (∃ s : ZMod m → ℤ, IsSection m s ∧ ∀ r, s (-r) = -s r) ↔ Odd m := by
  constructor
  · rintro ⟨s, hs, hodd⟩
    by_contra hno
    obtain ⟨h, hh⟩ := Nat.not_odd_iff_even.mp hno
    have hpos : 0 < m := NeZero.pos m
    have hr : -(h : ZMod m) = (h : ZMod m) := by
      apply neg_eq_of_add_eq_zero_left
      rw [← Nat.cast_add, ← hh, ZMod.natCast_self]
    have h1 := hodd (h : ZMod m)
    rw [hr] at h1
    have h2 : s (h : ZMod m) = 0 := by linarith
    have h3 : (h : ZMod m) = 0 := by
      have h4 := hs (h : ZMod m)
      rw [h2] at h4
      simpa using h4.symm
    rw [ZMod.natCast_eq_zero_iff] at h3
    have h5 := Nat.le_of_dvd (by omega) h3
    omega
  · intro hodd
    refine ⟨balancedSection m, isSection_balanced, fun r => ?_⟩
    unfold balancedSection
    apply ZMod.valMinAbs_neg_of_ne_half
    intro h
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨r.val, by omega⟩

/-! ## 6. Every section carries -/

/-- [definition] The carry of a section: what its representatives owe the modulus under
addition. -/
def carry (m : ℕ) (s : ZMod m → ℤ) (r r' : ZMod m) : ℤ := (s r + s r' - s (r + r')) / (m : ℤ)

/-- [proved-standard; formal-checked] Addition through a section: the representatives add up to
the representative of the sum and `m` times the carry. -/
theorem section_add {s : ZMod m → ℤ} (hs : IsSection m s) (r r' : ZMod m) :
    s r + s r' = s (r + r') + (m : ℤ) * carry m s r r' := by
  have h : (m : ℤ) ∣ s r + s r' - s (r + r') := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hs, hs, hs]
    ring
  unfold carry
  rw [Int.mul_ediv_cancel' h]
  ring

/-- [proved-derived; formal-checked] **A change of convention changes the carry by a
coboundary**: `carry' = carry + δ r + δ r' − δ (r + r')`. -/
theorem carry_shift [NeZero m] {s : ZMod m → ℤ} (hs : IsSection m s) (δ : ZMod m → ℤ)
    (r r' : ZMod m) :
    carry m (shift m s δ) r r' = carry m s r r' + δ r + δ r' - δ (r + r') := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h1 := section_add (isSection_shift hs δ) r r'
  have h2 := section_add hs r r'
  have h3 : shift m s δ r + shift m s δ r' - shift m s δ (r + r') =
      s r + s r' - s (r + r') + (m : ℤ) * (δ r + δ r' - δ (r + r')) := by
    unfold shift
    ring
  have h4 : (m : ℤ) * carry m (shift m s δ) r r' =
      (m : ℤ) * (carry m s r r' + δ r + δ r' - δ (r + r')) := by
    linarith
  exact mul_left_cancel₀ hm h4

/-- [proved-derived; formal-checked] The floor section's carry is the repository's
`FacesOnCycles.carry`, `⌊(a + b)/m⌋` on the digits. -/
theorem carry_floor [NeZero m] (a b : ZMod m) :
    carry m (floorSection m) a b = FacesOnCycles.carry a b := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have h1 : ((a.val : ℕ) : ℤ) + ((b.val : ℕ) : ℤ) =
      (((a + b).val : ℕ) : ℤ) + (m : ℤ) * carry m (floorSection m) a b :=
    section_add isSection_floor a b
  have h2 := FacesOnCycles.val_add_add_carry a b
  have h3 : (m : ℤ) * carry m (floorSection m) a b = (m : ℤ) * FacesOnCycles.carry a b := by
    linarith
  exact mul_left_cancel₀ hm h3

/-- [proved-derived; formal-checked] **No remainder convention is additive**: for `m ≥ 2` every
section has a pair of residues whose carry is not zero. The floor carry is no integer coboundary
(`FacesOnCycles.carry_not_coboundary`), and every section's carry is the floor carry and a
coboundary. -/
theorem exists_carry_ne_zero [NeZero m] [Fact (1 < m)] {s : ZMod m → ℤ} (hs : IsSection m s) :
    ∃ r r', carry m s r r' ≠ 0 := by
  by_contra hcon
  have hzero : ∀ r r', carry m s r r' = 0 := fun r r' => by
    by_contra h
    exact hcon ⟨r, r', h⟩
  obtain ⟨δ, hδ, -⟩ := existsUnique_shift (isSection_floor (m := m)) hs
  apply FacesOnCycles.carry_not_coboundary (n := m)
  refine ⟨fun r => -δ r, fun a b => ?_⟩
  have h := carry_shift (isSection_floor (m := m)) δ a b
  rw [← hδ, hzero, carry_floor] at h
  unfold FacesOnCycles.delta
  linarith

/-! ## 7. A quotient commutes with the sum, a section does not -/

/-- [proved-derived; formal-checked] **One reading after a wrapped sum returns the total**: the
sum of the residues is the residue of the integer sum, so the interval section returns the total
whenever the total lies in the interval, whatever the partial sums did (atlas
`radix.release-quotient-or-section`, the quotient's side). -/
theorem read_once_after_wrapped_sum [NeZero m] {ι : Type*} (t : Finset ι) (x : ι → ℤ) (a : ℤ)
    (h1 : a ≤ ∑ i ∈ t, x i) (h2 : ∑ i ∈ t, x i < a + m) :
    intervalSection m a (∑ i ∈ t, (x i : ZMod m)) = ∑ i ∈ t, x i := by
  rw [← Int.cast_sum]
  exact intervalSection_reads a _ h1 h2

/-- [definition] The release of an integer at the modulus through a section: the integer less
the section's representative of its residue, a multiple of `m`. Through the floor section it is
rounding down to a multiple of `m`, through the balanced section rounding to the nearest. -/
def release (m : ℕ) (s : ZMod m → ℤ) (x : ℤ) : ℤ := x - s (x : ZMod m)

/-- [proved-standard; formal-checked] The release is `m` times the winding. -/
theorem release_eq_mul_winding {s : ZMod m → ℤ} (hs : IsSection m s) (x : ℤ) :
    release m s x = (m : ℤ) * winding m s x := by
  have h := section_add_winding hs x
  unfold release
  linarith

/-- [proved-derived; formal-checked] **A release through a section fails additivity by the
carry**: `release (x + y) = release x + release y + m · carry (x mod m) (y mod m)` (atlas
`radix.release-quotient-or-section`, the section's side). -/
theorem release_add {s : ZMod m → ℤ} (hs : IsSection m s) (x y : ℤ) :
    release m s (x + y) =
      release m s x + release m s y + (m : ℤ) * carry m s (x : ZMod m) (y : ZMod m) := by
  have h := section_add hs (x : ZMod m) (y : ZMod m)
  unfold release
  rw [Int.cast_add]
  linarith

/-- [counterexample; formal-checked] **A release after every add depends on the bracketing**:
rounding down to an even integer after each add, `(1 + 1) + 0` reads `2` and `1 + (1 + 0)`
reads `0`. -/
theorem release_not_schedule_free :
    release 2 (floorSection 2) (release 2 (floorSection 2) (1 + 1) + 0) = 2 ∧
      release 2 (floorSection 2) (1 + release 2 (floorSection 2) (1 + 0)) = 0 := by
  constructor <;> decide

end Holonics.Foundation.SectionGauge
