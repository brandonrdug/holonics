import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.List.Induction
import Mathlib.Tactic
import HolonicsResearch.Mathematics.RadixItinerary

/-!
# The strands' comparison chart: three strands under the rotor's laws hold `p_k − μᵏ(x + e y)`,
# which the ring of the result's length closes

The strands record of October 26
(`research/records/2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md`,
§2, "The comparison chart" and "The hand theorem", and §4, "Owed in #410"; atlas `hnn.tower-strands`) carries three
strands of residues and one sheet `o`, the dyad's orientation. A located digit `d` acts by the rotor's three laws,
`A` held (`r ← r`), `G` stepped (`r ← μ r`) and `H` turned (`r ← μ r + o·d`); every other byte acts by its located
key, a signed transfer between strands with the sheet kept, flipped or set. With the keys

```text
before the first numeral:   H ← 0,              o ← +1
between the numerals (∘):   A ← H,  H ← 0,      o ← e_∘
at the equals:              G ← H,  H ← −A,     o ← +1
```

the record derives the chart that `Mathematics/RadixItinerary.strand_digit` takes as its hypothesis. This file proves
it over any commutative ring, the base `μ` and the hand `e` free.

[proved-derived; formal-checked] What is proved.

1. **The rotor's laws on a numeral** (`read_eq`): reading the digits `ds` moves the strands to
   `(A, μⁿ G, μⁿ H + o · value ds, o)`, `n` the numeral's length and `value` its value in base `μ` read from the most
   significant end (`value_concat`, `value_natCast`).
2. **The chart** (`chart_eq`, `chart_comparison`): after `x ∘ y =` and the first `k` digits `zs` of the result,
   `A = x`, `G = μᵏ e y`, `H = p_k − μᵏ x` and the sheet is `+1`, so the comparison is
   `H − G = p_k − μᵏ (x + e y)`, from any opening strands. No strand ever holds `x + e y`: the sum stands only in the
   comparison of two strands.
3. **The comparison's step** (`comparison_digit`, `chart_concat`, `face_step`): a written digit turns the comparison
   by `c ↦ μ c + d`, so its conjugate `−c` moves by the base's expanding map `t ↦ μ t − d`; the written numeral is the
   conjugate face's itinerary.
4. **On the ring of the result's length** (`comparison_on_ring`, `chart_comparison_on_ring`, `pow_eq_one_on_ring`):
   where `μᴸ = 1` (on `ZMod q` with `q + 1 = bᴸ`) and `x + e y = p_k μ^(L−k) + s_k`, the comparison is `−μᵏ s_k`, the
   unwritten remainder turned to the top of the block.
5. **The ring closes** (`chart_closes`, `chart_closes_iff`): at `k = L` the comparison is `z − (x + e y)`, zero exactly
   where `z ≡ x + e y`.
6. **The chart feeds the release** (`chart_digit`): on `ZMod q`, `q + 1 = bᴸ`, for a result `S < q` with
   `x + e y ≡ S` and the written prefix `p_k = ⌊S / b^(L−k)⌋`, the `b`-th of the conjugate face is the next digit of
   `S` at every `k < L`, through `RadixItinerary.strand_digit`.
7. **One comparison serves both hands** (`face_comparison`, `face_comparison_coe`, `hands_differ`): the comparison's
   face on the ring is `face(H) · conj(face(G))`, and the two hands' comparisons differ by `2 μᵏ y`.
8. **The hand theorem** (`readL_eq`, `final_eq`, `hand_unread_without_sheet`): without the sheet, when a digit acts
   by a linear map `M` with `M h = μ • h` (`h` the turned strand) plus `d • h`, and the operator's and the equals'
   keys are any linear maps, the state after `x ∘ y =` is `K_=(Mⁿ(K_∘ s_x)) + value ys • K_= h`: `y`'s coefficient
   `K_= h` is the same for every operator, so the difference of two hands never sees `y`. The hand must then be
   read by a three-way product at the readout; the sheet lets the operator's key set the side `y` is read on.

The computational object is the helical pair interaction: each strand is a ring's phase, the turned strand winds
with the digit as its carry, and the comparison is the pair contact's product of two strands' faces. Of the winding
guide's six general objects this touches the helix (the rotor's laws), the pair (the comparison of two strands) and
faces and placement (the conjugate face read in tenths); the cell holonomy, the tube and the tower thread stay
attached.

Consumers: the atlas row `hnn.tower-strands`, `Mathematics/RadixItinerary.strand_digit` (whose hypothesis
`c ≡ −bᵏ s_k` `chart_digit` discharges), and the record's §2 and §4.

What stands beside it: the location of the keys (the record's §3, a measurement on the October machine), and the
measured census (1,496,496 calculations written digit by digit, §2), which the theorems here replace by the identity
for every `x`, `y` and hand.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.StrandsComparisonChart

open Complex

section Value

variable {R : Type*} [CommSemiring R]

/-- A numeral's value in base `μ`, its digits read from the most significant end. -/
def value (μ : R) (ds : List ℕ) : R := ds.foldl (fun (a : R) (d : ℕ) => μ * a + (d : R)) 0

@[simp] theorem value_nil (μ : R) : value μ [] = 0 := rfl

theorem value_concat (μ : R) (ds : List ℕ) (d : ℕ) :
    value μ (ds ++ [d]) = μ * value μ ds + d := by
  simp [value, List.foldl_append]

/-- The value read in `ℕ` and cast is the value read in the ring at the cast base. -/
theorem value_natCast (b : ℕ) (ds : List ℕ) : ((value b ds : ℕ) : R) = value (b : R) ds := by
  induction ds using List.reverseRecOn with
  | nil => simp
  | append_singleton ds d ih =>
    rw [value_concat, value_concat, ← ih]
    push_cast
    ring

end Value

section Ring

variable {R : Type*} [CommRing R]

/-- The three strands and the sheet: `A` held, `G` stepped, `H` turned, `o` the dyad's orientation. -/
structure Strands (R : Type*) where
  /-- The held strand. -/
  A : R
  /-- The stepped strand. -/
  G : R
  /-- The turned strand. -/
  H : R
  /-- The sheet. -/
  o : R

/-- A located digit `d`: `A` held, `G` stepped, `H` turned on the sheet. -/
def digit (μ : R) (s : Strands R) (d : ℕ) : Strands R :=
  ⟨s.A, μ * s.G, μ * s.H + s.o * d, s.o⟩

/-- A numeral read digit by digit. -/
def read (μ : R) (s : Strands R) (ds : List ℕ) : Strands R := ds.foldl (digit μ) s

theorem read_concat (μ : R) (s : Strands R) (ds : List ℕ) (d : ℕ) :
    read μ s (ds ++ [d]) = digit μ (read μ s ds) d := by
  simp [read, List.foldl_append]

/-- [proved-derived; formal-checked] **The rotor's laws on a numeral.** Reading `ds` keeps `A` and the sheet,
steps `G` by `μⁿ`, and turns `H` to `μⁿ H + o · value ds`. -/
theorem read_eq (μ : R) (s : Strands R) (ds : List ℕ) :
    read μ s ds = ⟨s.A, μ ^ ds.length * s.G, μ ^ ds.length * s.H + s.o * value μ ds, s.o⟩ := by
  induction ds using List.reverseRecOn with
  | nil => cases s; simp [read]
  | append_singleton ds d ih =>
    rw [read_concat, ih, value_concat]
    simp only [digit, List.length_append, List.length_singleton, pow_succ, Strands.mk.injEq]
    exact ⟨trivial, by ring, by ring, trivial⟩

/-- Before the first numeral: `H ← 0`, `o ← +1`. -/
def keyOpen (s : Strands R) : Strands R := ⟨s.A, s.G, 0, 1⟩

/-- Between the numerals, the operator of hand `e`: `A ← H`, `H ← 0`, `o ← e`. -/
def keyOp (e : R) (s : Strands R) : Strands R := ⟨s.H, s.G, 0, e⟩

/-- At the equals: `G ← H`, `H ← −A`, `o ← +1`. -/
def keyEq (s : Strands R) : Strands R := ⟨s.A, s.H, -s.A, 1⟩

/-- The chart: from any opening strands, `x ∘ y =` and the first digits `zs` of the result. -/
def chart (μ e : R) (s₀ : Strands R) (xs ys zs : List ℕ) : Strands R :=
  read μ (keyEq (read μ (keyOp e (read μ (keyOpen s₀) xs)) ys)) zs

/-- The comparison of the turned strand against the stepped one. -/
def comparison (s : Strands R) : R := s.H - s.G

/-- [proved-derived; formal-checked] **The chart.** After `x ∘ y =` and `k` digits of the result,
`A = x`, `G = μᵏ e y`, `H = p_k − μᵏ x` and the sheet is `+1`, from any opening strands. -/
theorem chart_eq (μ e : R) (s₀ : Strands R) (xs ys zs : List ℕ) :
    chart μ e s₀ xs ys zs =
      ⟨value μ xs, μ ^ zs.length * (e * value μ ys), value μ zs - μ ^ zs.length * value μ xs, 1⟩ := by
  simp only [chart, read_eq, keyOpen, keyOp, keyEq, Strands.mk.injEq]
  exact ⟨by ring, by ring, by ring, trivial⟩

/-- [proved-derived; formal-checked] **The comparison** `H − G = p_k − μᵏ (x + e y)`. -/
theorem chart_comparison (μ e : R) (s₀ : Strands R) (xs ys zs : List ℕ) :
    comparison (chart μ e s₀ xs ys zs) =
      value μ zs - μ ^ zs.length * (value μ xs + e * value μ ys) := by
  rw [comparison, chart_eq]
  ring

/-- **The comparison's step**: a digit turns the comparison by `c ↦ μ c + o d`. -/
theorem comparison_digit (μ : R) (s : Strands R) (d : ℕ) :
    comparison (digit μ s d) = μ * comparison s + s.o * d := by
  simp only [comparison, digit]
  ring

/-- The chart's next digit is one more turn of the strands. -/
theorem chart_concat (μ e : R) (s₀ : Strands R) (xs ys zs : List ℕ) (d : ℕ) :
    chart μ e s₀ xs ys (zs ++ [d]) = digit μ (chart μ e s₀ xs ys zs) d := by
  simp only [chart, read_concat]

/-- [proved-derived; formal-checked] **The conjugate face moves by the base's expanding map** `t ↦ μ t − d`
as the result's digits are written. -/
theorem face_step (μ e : R) (s₀ : Strands R) (xs ys zs : List ℕ) (d : ℕ) :
    -comparison (chart μ e s₀ xs ys (zs ++ [d])) = μ * -comparison (chart μ e s₀ xs ys zs) - d := by
  rw [chart_concat, comparison_digit]
  have : (chart μ e s₀ xs ys zs).o = 1 := by rw [chart_eq]
  rw [this]
  ring

/-- [proved-derived; formal-checked] **On the ring of the result's length** (`μᴸ = 1`), with
`S = p μ^(L−k) + s`, the comparison `p − μᵏ S` is `−μᵏ s`. -/
theorem comparison_on_ring {μ p s S : R} {L k : ℕ} (hμ : μ ^ L = 1) (hk : k ≤ L)
    (hS : S = p * μ ^ (L - k) + s) : p - μ ^ k * S = -(μ ^ k * s) := by
  subst hS
  have h : μ ^ k * μ ^ (L - k) = 1 := by rw [← pow_add, Nat.add_sub_cancel' hk, hμ]
  linear_combination (-p) * h

/-- The chart on the ring of the result's length: its comparison is the unwritten remainder turned to the top,
`−μᵏ s_k`. -/
theorem chart_comparison_on_ring {μ e s : R} {L : ℕ} (s₀ : Strands R) (xs ys zs : List ℕ) (hμ : μ ^ L = 1)
    (hk : zs.length ≤ L)
    (hS : value μ xs + e * value μ ys = value μ zs * μ ^ (L - zs.length) + s) :
    comparison (chart μ e s₀ xs ys zs) = -(μ ^ zs.length * s) := by
  rw [chart_comparison]
  exact comparison_on_ring hμ hk hS

/-- [proved-derived; formal-checked] **The ring closes**: once `L` digits are written on the ring where
`μᴸ = 1`, the comparison is `z − (x + e y)`. -/
theorem chart_closes {μ e : R} (s₀ : Strands R) (xs ys zs : List ℕ) (hμ : μ ^ zs.length = 1) :
    comparison (chart μ e s₀ xs ys zs) = value μ zs - (value μ xs + e * value μ ys) := by
  rw [chart_comparison, hμ, one_mul]

/-- The ring closes at zero exactly where the written result is `x + e y` on it. -/
theorem chart_closes_iff {μ e : R} (s₀ : Strands R) (xs ys zs : List ℕ) (hμ : μ ^ zs.length = 1) :
    comparison (chart μ e s₀ xs ys zs) = 0 ↔ value μ zs = value μ xs + e * value μ ys := by
  rw [chart_closes s₀ xs ys zs hμ, sub_eq_zero]

/-- [proved-derived; formal-checked] **The two hands' comparisons differ by `2 μᵏ y`.** One comparison reads both
hands, the sheet carrying the operator's sign onto `y`. -/
theorem hands_differ (μ : R) (s₀ : Strands R) (xs ys zs : List ℕ) :
    comparison (chart μ (-1) s₀ xs ys zs) - comparison (chart μ 1 s₀ xs ys zs) =
      2 * μ ^ zs.length * value μ ys := by
  rw [chart_comparison, chart_comparison]
  ring

end Ring

/-! ## On the ring `q = bᴸ − 1` -/

/-- On `ZMod q` with `q + 1 = bᴸ`, the base's `L`-th power is one. -/
theorem pow_eq_one_on_ring {b q L : ℕ} (hq : q + 1 = b ^ L) : (b : ZMod q) ^ L = 1 := by
  have h := congrArg (Nat.cast : ℕ → ZMod q) hq
  push_cast at h
  rw [ZMod.natCast_self, zero_add] at h
  exact h.symm

/-- [proved-derived; formal-checked] **The chart feeds the release.** On `ZMod q`, `q + 1 = bᴸ`, for a result
`S < q` with `x + e y ≡ S` and `k < L` digits written, their value the prefix `⌊S / b^(L−k)⌋`, the `b`-th of the
conjugate face of the strands' comparison is the next digit of `S`. -/
theorem chart_digit {b q L : ℕ} (hb : 1 < b) (hq : q + 1 = b ^ L) {S : ℕ} (hS : S < q) (e : ZMod q)
    (s₀ : Strands (ZMod q)) (xs ys zs : List ℕ) (hk : zs.length < L)
    (hsum : value (b : ZMod q) xs + e * value (b : ZMod q) ys = (S : ZMod q))
    (hz : value (b : ZMod q) zs = ((S / b ^ (L - zs.length) : ℕ) : ZMod q)) :
    b * (-comparison (chart (b : ZMod q) e s₀ xs ys zs)).val / q = S / b ^ (L - zs.length - 1) % b := by
  apply Mathematics.RadixItinerary.strand_digit hb hq hk hS
  have hS' : value (b : ZMod q) xs + e * value (b : ZMod q) ys =
      value (b : ZMod q) zs * (b : ZMod q) ^ (L - zs.length) + ((S % b ^ (L - zs.length) : ℕ) : ZMod q) := by
    rw [hsum, hz]
    conv_lhs => rw [← Nat.div_add_mod' S (b ^ (L - zs.length))]
    push_cast
    ring
  rw [chart_comparison_on_ring s₀ xs ys zs (pow_eq_one_on_ring hq) hk.le hS']
  push_cast
  ring

/-- [proved-derived; formal-checked] **One comparison is one product of faces**: on the ring, the comparison's face
is the turned strand's face times the inverse (the conjugate) of the stepped strand's. -/
theorem face_comparison {q : ℕ} [NeZero q] (s : Strands (ZMod q)) :
    ZMod.toCircle (comparison s) = ZMod.toCircle s.H * (ZMod.toCircle s.G)⁻¹ := by
  rw [comparison, AddChar.map_sub_eq_div, div_eq_mul_inv]

theorem face_comparison_coe {q : ℕ} [NeZero q] (s : Strands (ZMod q)) :
    (ZMod.toCircle (comparison s) : ℂ) = ZMod.toCircle s.H * (starRingEnd ℂ) (ZMod.toCircle s.G) := by
  rw [face_comparison, Circle.coe_mul, Circle.coe_inv_eq_conj]

/-! ## The hand theorem: without the sheet, `y`'s coefficient is the same for every operator -/

section Hand

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A numeral read with no sheet: each digit moves the strands by `M` and adds `d • h` on the turned strand. -/
def readL (M : Module.End R V) (h : V) (s : V) (ds : List ℕ) : V :=
  ds.foldl (fun (s : V) (d : ℕ) => M s + (d : R) • h) s

/-- [proved-derived; formal-checked] Where the turned strand is an eigenvector, `M h = μ • h`, a numeral moves the
strands to `Mⁿ s + value ds • h`. -/
theorem readL_eq {μ : R} (M : Module.End R V) {h : V} (hM : M h = μ • h) (s : V) (ds : List ℕ) :
    readL M h s ds = (M ^ ds.length) s + value μ ds • h := by
  induction ds using List.reverseRecOn with
  | nil => simp [readL]
  | append_singleton ds d ih =>
    have hc : readL M h s (ds ++ [d]) = M (readL M h s ds) + (d : R) • h := by
      simp [readL, List.foldl_append]
    rw [hc, ih, value_concat, List.length_append, List.length_singleton, pow_succ', Module.End.mul_apply,
      map_add, map_smul, hM, smul_smul, add_smul, add_assoc, mul_comm μ]

/-- The state after `x ∘ y =`: the operator's key `K`, the numeral `y`, then the equals' key `K_=`. -/
def final (M : Module.End R V) (h : V) (K Keq : Module.End R V) (sx : V) (ys : List ℕ) : V :=
  Keq (readL M h (K sx) ys)

theorem final_eq {μ : R} (M : Module.End R V) {h : V} (hM : M h = μ • h) (K Keq : Module.End R V) (sx : V)
    (ys : List ℕ) :
    final M h K Keq sx ys = Keq ((M ^ ys.length) (K sx)) + value μ ys • Keq h := by
  rw [final, readL_eq M hM, map_add, map_smul]

/-- [proved-derived; formal-checked] **The hand theorem.** Without the sheet, two operators' keys `K₁`, `K₂`
(any linear maps, signed transfers among them) and a shared equals' key leave `y`'s coefficient `K_= h` the
same, so the difference of the two hands' states is the same for every `y` of a given length: no reading linear in
the strands separates the hands by `y`. -/
theorem hand_unread_without_sheet {μ : R} (M : Module.End R V) {h : V} (hM : M h = μ • h)
    (K₁ K₂ Keq : Module.End R V) (sx : V) (ys ys' : List ℕ) (hlen : ys.length = ys'.length) :
    final M h K₁ Keq sx ys - final M h K₂ Keq sx ys = final M h K₁ Keq sx ys' - final M h K₂ Keq sx ys' := by
  rw [final_eq M hM, final_eq M hM, final_eq M hM, final_eq M hM, hlen]
  abel

end Hand

end Holonics.HNN.StrandsComparisonChart
