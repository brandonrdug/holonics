import Mathlib

/-!
# Four contexts on a cycle: one table bounds the reading by two, a path always glues, and geometry bounds the defect

[proved-standard] The source is the record of November 11
(`research/records/2026-11-11_EINSTEINS_FIELD_PROGRAM_ON_THE_COMPLEX_THE_UNIFIED_FIELD_IS_A_TWO_WAY_FLOW_A_GRAIN_GIVES_THE_MASS_AND_A_PROBABILITY_IS_ITS_FLAT_PART.md`,
§6.3 and §11). Two settings on each of two sides give four contexts `(a, b)`, `(a, b′)`, `(a′, b)`, `(a′, b′)`, which
form a cycle of four. Write `S = E(a, b) + E(a, b′) + E(a′, b) − E(a′, b′)`.

What is proved.

1. **One table bounds `S` by two.** Each assignment of a value in `[−1, 1]` to every setting reads `|S| ≤ 2`
   (`assignment_bound`), and `S` is linear, so every table of all four settings does (`table_bound`).
2. **A path of contexts always glues.** The three contexts on the path `b′ − a − b − a′`, with the marginals they share
   equal, glue to the table `p(a, b′) p(a, b) p(a′, b)/(p(a) p(b))`, which returns all three (`glued_returns_middle`,
   `glued_returns_first`, `glued_returns_last`). This is the path's case of Vorob'ev's theorem; the theorem for every
   complex of contexts without a cycle is the literature's.
3. **The closing edge carries the whole defect.** For two-valued readings with even marginals the glued table reads the
   closing context at the product of the three readings along the path (`glued_closing_reading`): `48/125` for the
   readings `4/5, 4/5, 3/5` (`glued_closing_ruler`), where the faces `(1, 0)`, `(0, 1)`, `(4/5, ±3/5)` read `−3/5`
   and `S = 14/5` (`faces_ruler`). No table of all four settings returns those four readings (`faces_have_no_table`).
4. **Geometry bounds the defect.** For faces that are unit vectors of a real inner product space `S² ≤ 8`
   (`gram_bound`; Tsirelson's bound in its vector form), the bound is reached (`gram_bound_reached`), and four settings
   at sixths of a turn read `S = 5/2` (`sixths_ruler`).

Limits. Statement 2 is the path of three contexts; the general acyclic complex is not formalized here. Statement 4 is the
bound for readings that are inner products of unit vectors; that the readings of a pair of two-valued observables on a
state are such inner products is the literature's and is not formalized. Nothing here says which readings nature gives.

The computational object is the helical pair interaction: a context is a pair contact of two settings and its reading the
contact's face. Of the winding guide's six general objects this touches cell holonomy (the cycle of four contexts, whose
closing edge carries the defect) and faces and placement (the readings); the helix, pair, tube and tower thread stay
attached.

Consumers: #410's box "Four contexts on a cycle"; the objects' gluing clause (unique, plural or obstructed), of which
this is the smallest obstructed instance.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.ContextCycle

open Finset

/-! ## 1. One table -/

/-- The cycle's reading on four values: `ab + ab′ + a′b − a′b′`. -/
def cycleReading (a a' b b' : ℝ) : ℝ := a * b + a * b' + a' * b - a' * b'

/-- [proved-standard] **Each assignment reads at most two**: values in `[−1, 1]` on the four settings give
`|ab + ab′ + a′b − a′b′| ≤ 2`. The sixteen assignments of `±1` are its corners. -/
theorem assignment_bound {a a' b b' : ℝ} (ha : |a| ≤ 1) (ha' : |a'| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    |cycleReading a a' b b'| ≤ 2 := by
  have h1 : |a * (b + b')| ≤ |b + b'| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (b + b'), abs_nonneg a]
  have h2 : |a' * (b - b')| ≤ |b - b'| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (b - b'), abs_nonneg a']
  have h3 : |b + b'| + |b - b'| ≤ 2 := by
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    obtain ⟨hb1', hb2'⟩ := abs_le.mp hb'
    rcases abs_cases (b + b') with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases abs_cases (b - b') with ⟨h', _⟩ | ⟨h', _⟩ <;>
      rw [h, h'] <;> linarith
  have hS : cycleReading a a' b b' = a * (b + b') + a' * (b - b') := by
    unfold cycleReading
    ring
  rw [hS]
  calc |a * (b + b') + a' * (b - b')| ≤ |a * (b + b')| + |a' * (b - b')| := abs_add_le _ _
    _ ≤ |b + b'| + |b - b'| := add_le_add h1 h2
    _ ≤ 2 := h3

variable {Λ : Type*} [Fintype Λ]

/-- A table's reading of a context: the mean of the product of the two settings' values under the weights `p`. -/
def reading (p : Λ → ℝ) (X Y : Λ → ℝ) : ℝ := ∑ l, p l * (X l * Y l)

/-- [proved-standard] **One table bounds the cycle by two**: for nonnegative weights of sum one on any finite set of
assignments, with every setting's value in `[−1, 1]`, `|E(a, b) + E(a, b′) + E(a′, b) − E(a′, b′)| ≤ 2`. -/
theorem table_bound (p : Λ → ℝ) (hp : ∀ l, 0 ≤ p l) (hsum : ∑ l, p l = 1) (A A' B B' : Λ → ℝ)
    (hA : ∀ l, |A l| ≤ 1) (hA' : ∀ l, |A' l| ≤ 1) (hB : ∀ l, |B l| ≤ 1) (hB' : ∀ l, |B' l| ≤ 1) :
    |reading p A B + reading p A B' + reading p A' B - reading p A' B'| ≤ 2 := by
  have hlin : reading p A B + reading p A B' + reading p A' B - reading p A' B' =
      ∑ l, p l * cycleReading (A l) (A' l) (B l) (B' l) := by
    unfold reading cycleReading
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hlin]
  calc |∑ l, p l * cycleReading (A l) (A' l) (B l) (B' l)|
      ≤ ∑ l, |p l * cycleReading (A l) (A' l) (B l) (B' l)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, p l * 2 := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hp l)]
        exact mul_le_mul_of_nonneg_left (assignment_bound (hA l) (hA' l) (hB l) (hB' l)) (hp l)
    _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]

/-! ## 2. A path of contexts glues -/

section Glue

variable {X X' Y Y' : Type*} [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']

/-- The path's glued table: `p(a, b′) p(a, b) p(a′, b)/(p(a) p(b))`, the marginals read from the middle context. -/
noncomputable def glued (p1 : X → Y' → ℝ) (p2 : X → Y → ℝ) (p3 : X' → Y → ℝ) (x : X) (x' : X') (y : Y) (y' : Y') :
    ℝ :=
  p1 x y' * p2 x y * p3 x' y / ((∑ v, p2 x v) * (∑ u, p2 u y))

omit [Fintype X] [Fintype X'] [Fintype Y'] in
private theorem middle_zero_of_row {p2 : X → Y → ℝ} (h2 : ∀ x y, 0 ≤ p2 x y) {x : X} (h : ∑ v, p2 x v = 0) (y : Y) :
    p2 x y = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun v _ => h2 x v).mp h y (Finset.mem_univ y)

omit [Fintype X'] [Fintype Y] [Fintype Y'] in
private theorem middle_zero_of_col {p2 : X → Y → ℝ} (h2 : ∀ x y, 0 ≤ p2 x y) {y : Y} (h : ∑ u, p2 u y = 0) (x : X) :
    p2 x y = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun u _ => h2 u y).mp h x (Finset.mem_univ x)

private theorem sum_mul_div {ι : Type*} [Fintype ι] (f : ι → ℝ) (c D : ℝ) :
    ∑ i, f i * c / D = (∑ i, f i) * c / D := by
  rw [Finset.sum_mul, Finset.sum_div]

/-- [proved-standard] **The glued table returns the middle context** `(a, b)`. -/
theorem glued_returns_middle (p1 : X → Y' → ℝ) (p2 : X → Y → ℝ) (p3 : X' → Y → ℝ)
    (h2 : ∀ x y, 0 ≤ p2 x y)
    (ha : ∀ x, ∑ y', p1 x y' = ∑ y, p2 x y) (hb : ∀ y, ∑ x', p3 x' y = ∑ x, p2 x y) (x : X) (y : Y) :
    ∑ x', ∑ y', glued p1 p2 p3 x x' y y' = p2 x y := by
  have hinner : ∀ x', ∑ y', glued p1 p2 p3 x x' y y' =
      p3 x' y * ((∑ y', p1 x y') * p2 x y) / ((∑ v, p2 x v) * (∑ u, p2 u y)) := by
    intro x'
    have hterm : ∀ y', glued p1 p2 p3 x x' y y' =
        p1 x y' * (p2 x y * p3 x' y) / ((∑ v, p2 x v) * (∑ u, p2 u y)) := by
      intro y'
      unfold glued
      ring
    rw [Finset.sum_congr rfl fun y' _ => hterm y', sum_mul_div]
    ring
  rw [Finset.sum_congr rfl fun x' _ => hinner x', sum_mul_div, ha, hb]
  by_cases hx : ∑ v, p2 x v = 0
  · rw [middle_zero_of_row h2 hx y]
    simp
  by_cases hy : ∑ u, p2 u y = 0
  · rw [middle_zero_of_col h2 hy x]
    simp
  field_simp

/-- [proved-standard] **The glued table returns the first context** `(a, b′)`. -/
theorem glued_returns_first (p1 : X → Y' → ℝ) (p2 : X → Y → ℝ) (p3 : X' → Y → ℝ)
    (h1 : ∀ x y', 0 ≤ p1 x y') (h2 : ∀ x y, 0 ≤ p2 x y)
    (ha : ∀ x, ∑ y', p1 x y' = ∑ y, p2 x y) (hb : ∀ y, ∑ x', p3 x' y = ∑ x, p2 x y) (x : X) (y' : Y') :
    ∑ x', ∑ y, glued p1 p2 p3 x x' y y' = p1 x y' := by
  have hinner : ∀ y, ∑ x', glued p1 p2 p3 x x' y y' = p2 x y * p1 x y' / (∑ v, p2 x v) := by
    intro y
    have hterm : ∀ x', glued p1 p2 p3 x x' y y' =
        p3 x' y * (p1 x y' * p2 x y) / ((∑ v, p2 x v) * (∑ u, p2 u y)) := by
      intro x'
      unfold glued
      ring
    rw [Finset.sum_congr rfl fun x' _ => hterm x', sum_mul_div, hb]
    by_cases hy : ∑ u, p2 u y = 0
    · rw [middle_zero_of_col h2 hy x]
      simp
    by_cases hx : ∑ v, p2 x v = 0
    · rw [middle_zero_of_row h2 hx y]
      simp
    field_simp
  rw [Finset.sum_comm, Finset.sum_congr rfl fun y _ => hinner y, sum_mul_div]
  by_cases hx : ∑ v, p2 x v = 0
  · have hx1 : ∑ v, p1 x v = 0 := by rw [ha, hx]
    have hz : p1 x y' = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun v _ => h1 x v).mp hx1 y' (Finset.mem_univ y')
    rw [hz]
    simp
  field_simp

/-- [proved-standard] **The glued table returns the last context** `(a′, b)`. -/
theorem glued_returns_last (p1 : X → Y' → ℝ) (p2 : X → Y → ℝ) (p3 : X' → Y → ℝ)
    (h2 : ∀ x y, 0 ≤ p2 x y) (h3 : ∀ x' y, 0 ≤ p3 x' y)
    (ha : ∀ x, ∑ y', p1 x y' = ∑ y, p2 x y) (hb : ∀ y, ∑ x', p3 x' y = ∑ x, p2 x y) (x' : X') (y : Y) :
    ∑ x, ∑ y', glued p1 p2 p3 x x' y y' = p3 x' y := by
  have hinner : ∀ x, ∑ y', glued p1 p2 p3 x x' y y' = p2 x y * p3 x' y / (∑ u, p2 u y) := by
    intro x
    have hterm : ∀ y', glued p1 p2 p3 x x' y y' =
        p1 x y' * (p2 x y * p3 x' y) / ((∑ v, p2 x v) * (∑ u, p2 u y)) := by
      intro y'
      unfold glued
      ring
    rw [Finset.sum_congr rfl fun y' _ => hterm y', sum_mul_div, ha]
    by_cases hx : ∑ v, p2 x v = 0
    · rw [middle_zero_of_row h2 hx y]
      simp
    by_cases hy : ∑ u, p2 u y = 0
    · rw [middle_zero_of_col h2 hy x]
      simp
    field_simp
  rw [Finset.sum_congr rfl fun x _ => hinner x, sum_mul_div]
  by_cases hy : ∑ u, p2 u y = 0
  · have hy3 : ∑ u, p3 u y = 0 := by rw [hb, hy]
    have hz : p3 x' y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun u _ => h3 u y).mp hy3 x' (Finset.mem_univ x')
    rw [hz]
    simp
  field_simp

end Glue

/-! ## 3. The closing edge -/

/-- A two-valued reading's sign: `true ↦ 1`, `false ↦ −1`. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

/-- The table of two two-valued settings with even marginals and reading `E`: `(1 + E s t)/4`. -/
noncomputable def pairTable (E : ℝ) (s t : Bool) : ℝ := (1 + E * sgn s * sgn t) / 4

/-- [proved-standard] The pair table reads `E`. -/
theorem pairTable_reading (E : ℝ) : ∑ s, ∑ t, pairTable E s t * (sgn s * sgn t) = E := by
  simp [pairTable, sgn]
  ring

/-- [proved-standard] The pair table's marginals are even. -/
theorem pairTable_marginal (E : ℝ) (s : Bool) : ∑ t, pairTable E s t = 1 / 2 := by
  cases s <;> simp [pairTable, sgn] <;> ring

/-- [proved-standard] **The glued table reads the closing context at the product of the path's three readings.** -/
theorem glued_closing_reading (E1 E2 E3 : ℝ) :
    ∑ x, ∑ x', ∑ y, ∑ y', glued (pairTable E1) (pairTable E2) (fun x' y => pairTable E3 x' y) x x' y y' *
      (sgn x' * sgn y') = E1 * E2 * E3 := by
  have hrow : ∀ x : Bool, ∑ v, pairTable E2 x v = 1 / 2 := pairTable_marginal E2
  have hcol : ∀ y : Bool, ∑ u, pairTable E2 u y = 1 / 2 := by
    intro y
    cases y <;> simp [pairTable, sgn] <;> ring
  simp only [glued, hrow, hcol]
  simp [pairTable, sgn]
  ring

/-- [proved-standard] **The ruler's glued reading**: the path's readings `4/5, 4/5, 3/5` glue to `48/125` on the closing
context. -/
theorem glued_closing_ruler :
    ∑ x, ∑ x', ∑ y, ∑ y', glued (pairTable (4 / 5)) (pairTable (4 / 5)) (fun x' y => pairTable (3 / 5) x' y) x x' y y' *
      (sgn x' * sgn y') = 48 / 125 := by
  rw [glued_closing_reading]
  norm_num

/-- The plane's pairing of two faces. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- [proved-standard] **The faces' ruler**: the unit faces `(1, 0)`, `(0, 1)`, `(4/5, 3/5)`, `(4/5, −3/5)` read
`4/5, 4/5, 3/5, −3/5` and `S = 14/5`, above two and within the Gram bound. -/
theorem faces_ruler :
    dot (1, 0) (4 / 5, 3 / 5) = 4 / 5 ∧ dot (1, 0) (4 / 5, -3 / 5) = 4 / 5 ∧
      dot (0, 1) (4 / 5, 3 / 5) = 3 / 5 ∧ dot (0, 1) (4 / 5, -3 / 5) = -3 / 5 ∧
      dot (4 / 5, 3 / 5) (4 / 5, 3 / 5) = 1 ∧ dot (4 / 5, -3 / 5) (4 / 5, -3 / 5) = 1 ∧
      (4 / 5 + 4 / 5 + 3 / 5 - (-3 / 5) : ℝ) = 14 / 5 ∧ (2 : ℝ) < 14 / 5 ∧ ((14 : ℝ) / 5) ^ 2 ≤ 8 := by
  unfold dot
  norm_num

/-- [proved-standard] **The closing edge carries the whole defect**: the faces read the closing context at `−3/5` and
the glued table at `48/125`, and they differ. -/
theorem closing_defect : (48 : ℝ) / 125 - (-3 / 5) = 123 / 125 := by norm_num

/-- [proved-standard] **The faces' four readings are sections of no table**: no nonnegative weights of sum one on a
finite set of assignments with values in `[−1, 1]` return `4/5, 4/5, 3/5, −3/5` on the four contexts. -/
theorem faces_have_no_table (p : Λ → ℝ) (hp : ∀ l, 0 ≤ p l) (hsum : ∑ l, p l = 1) (A A' B B' : Λ → ℝ)
    (hA : ∀ l, |A l| ≤ 1) (hA' : ∀ l, |A' l| ≤ 1) (hB : ∀ l, |B l| ≤ 1) (hB' : ∀ l, |B' l| ≤ 1) :
    ¬ (reading p A B = 4 / 5 ∧ reading p A B' = 4 / 5 ∧ reading p A' B = 3 / 5 ∧ reading p A' B' = -3 / 5) := by
  rintro ⟨h1, h2, h3, h4⟩
  have h := table_bound p hp hsum A A' B B' hA hA' hB hB'
  rw [h1, h2, h3, h4] at h
  norm_num at h

/-! ## 4. The Gram bound -/

section Gram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open scoped RealInnerProductSpace

/-- [proved-standard] **The Gram bound** (Tsirelson's bound in its vector form): for unit vectors `a, a′, b, b′` of a
real inner product space, `(⟨a, b⟩ + ⟨a, b′⟩ + ⟨a′, b⟩ − ⟨a′, b′⟩)² ≤ 8`. -/
theorem gram_bound (a a' b b' : V) (ha : ‖a‖ = 1) (ha' : ‖a'‖ = 1) (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1) :
    (⟪a, b⟫ + ⟪a, b'⟫ + ⟪a', b⟫ - ⟪a', b'⟫) ^ 2 ≤ 8 := by
  have hS : ⟪a, b⟫ + ⟪a, b'⟫ + ⟪a', b⟫ - ⟪a', b'⟫ = ⟪a, b + b'⟫ + ⟪a', b - b'⟫ := by
    rw [inner_add_right, inner_sub_right]
    ring
  have h1 : |⟪a, b + b'⟫| ≤ ‖b + b'‖ := by
    have := abs_real_inner_le_norm a (b + b')
    rwa [ha, one_mul] at this
  have h2 : |⟪a', b - b'⟫| ≤ ‖b - b'‖ := by
    have := abs_real_inner_le_norm a' (b - b')
    rwa [ha', one_mul] at this
  have hpar := parallelogram_law_with_norm ℝ b b'
  rw [hb, hb'] at hpar
  have habs : |⟪a, b + b'⟫ + ⟪a', b - b'⟫| ≤ ‖b + b'‖ + ‖b - b'‖ :=
    (abs_add_le _ _).trans (add_le_add h1 h2)
  rw [hS, ← sq_abs]
  have hn1 := norm_nonneg (b + b')
  have hn2 := norm_nonneg (b - b')
  have hsq : |⟪a, b + b'⟫ + ⟪a', b - b'⟫| ^ 2 ≤ (‖b + b'‖ + ‖b - b'‖) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) habs 2
  nlinarith [sq_nonneg (‖b + b'‖ - ‖b - b'‖)]

end Gram

/-- [proved-standard] **The Gram bound is reached**: the faces `(1, 0)`, `(0, 1)`, `(1/√2, 1/√2)`, `(1/√2, −1/√2)` read
`S² = 8`. -/
theorem gram_bound_reached :
    (dot (1, 0) (1 / √2, 1 / √2) + dot (1, 0) (1 / √2, -(1 / √2)) + dot (0, 1) (1 / √2, 1 / √2) -
      dot (0, 1) (1 / √2, -(1 / √2))) ^ 2 = 8 := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : (√2 : ℝ) ≠ 0 := by positivity
  unfold dot
  field_simp
  nlinarith [h2]

/-- [proved-standard] **Four settings at sixths of a turn read `S = 5/2`** with every reading in `{1, ½, −½, −1}`: the
faces `(1, 0)`, `(−1/2, √3/2)` on one side and `(1/2, √3/2)`, `(1/2, −√3/2)` on the other. -/
theorem sixths_ruler :
    dot (1, 0) (1 / 2, √3 / 2) = 1 / 2 ∧ dot (1, 0) (1 / 2, -(√3 / 2)) = 1 / 2 ∧
      dot (-(1 / 2), √3 / 2) (1 / 2, √3 / 2) = 1 / 2 ∧ dot (-(1 / 2), √3 / 2) (1 / 2, -(√3 / 2)) = -1 ∧
      (1 / 2 + 1 / 2 + 1 / 2 - (-1) : ℝ) = 5 / 2 := by
  have h3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  unfold dot
  refine ⟨by ring, by ring, ?_, ?_, by norm_num⟩
  · nlinarith [h3]
  · nlinarith [h3]

end Holonics.Physics.ContextCycle
