import Holonics.HNN.ReceivingPrior

/-!
# HNN.PriorCarry: the receiving prior carried and moved per field

[proved-derived; formal-checked] The native form of the per-field receiving prior (#62, comment
5973559786 item 4: "carry `a` and `V` beside the Gram, and move `s` by the Newton point as
readings arrive"). The record
`research/records/2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE.md`
§4 states the law and §6 declares campaign 1's prior `2 I` by hand. `HNN/ReceivingPrior` proves the
law's second order. This file proves what carrying and moving it require.

```text
carried     (a, C) ← (a + w⟨g, Δ⟩ , C + 2|w| ((119/80) Var_p(Δ_Re) + ¼|Δ_Im|²))   per reading, no tape
held face   Δ ↦ ψ Δ                                     ⇒   (a, C) ↦ (ψ a, ψ² C) ,  ψ · Newton′ = Newton
at the map  q(φ) = −(φ − 1) a + ½ (φ − 1)² V ;  (a, V) ↦ (ψ (a − (ψ − 1) V), ψ² V)
            q(ψ χ) = q(ψ) + q′(χ) ,  ψ (1 + a′/V′) = 1 + a/V
dyadic      q(x) ≤ q(2x)  ⇔  2 (V + a) ≤ 3 x V ;  x best on the grid  ⇐  3x/4 ≤ 1 + a/V ≤ 3x/2
```

1. **The carry is the certificate's own sum, continued** (`Reading`, `Carry.read`, `carried`,
   `carried_append`, `carried_eq_sum`). A reading contributes exactly the terms
   `receiving_fisher_face` sums: the alignment `w ⟨g, Δ⟩` (the covector paired with the whole move,
   real and phase parts) and twice the curvature `|w| ((119/80) Var_p(Δ_Re) + ¼ |Δ_Im|²)`. Carried
   across windows, the pair after both is read from the pair after the first and the second
   window's readings alone: the law needs no tape. The certificate reads `Δ_t = D f_t`, the
   window's own deposit. The prior's law reads `Δ_t = W_t z_t`, the map in force before the
   reading's deposit (record §4). The fold is the same; only the move each reading presents
   differs.
2. **On a held face the pair rebases exactly** (`Reading.alignment_scale`,
   `Reading.curvature_scale`, `carried_scale`, `certified_newton_rebase`,
   `certified_bound_rebase`). Raising the prior to `s/ψ` where the map is `1/s` times its unit
   scales every reading's move by `ψ`. With the covector and masses held (the certified form,
   anchored at the face as `HNN/ReceivingPrior.prequential_code_le` is), the carried pair moves to
   `(ψ a, ψ² C)` (`variance_smul`). The certified bound read from the moved member is the same
   function of the total scale, and its Newton point `a/C` moves by `1/ψ`, so the located prior
   is the same from either member.
3. **At the map the pair rebases at second order** (`model`, `rebaseAt`, `model_rebase`,
   `rebaseAt_one`, `rebaseAt_mul`, `newton_rebaseAt`, `rebase_into_cell`). Record §4's at-map
   alignment pairs each reading with the covector at the map in force, which moves with the map:
   along `φ` its alignment falls by the curvature. In the record's quadratic
   `q(φ) = −(φ − 1) a + ½ (φ − 1)² V`, a prior move by `ψ` takes the carried pair to
   `(ψ (a − (ψ − 1) V), ψ² V)`, and the quadratic read from the moved member is the original one
   less its value there, exactly: `q(ψ χ) = q(ψ) + q′(χ)`. The rebase is an action of the scales
   (`rebaseAt_one`, `rebaseAt_mul`), and the located scale `1 + a/V` is the same from every
   member. A move into a member's cell leaves the rebased Newton point in the unit's cell, so the
   moved prior stays until new readings move it. Beyond the quadratic the curvature itself moves;
   that is the third order, which the record's model drops.
4. **The dyadic move** (`model_sub`, `neighbour_le_iff`, `grid_member_best`,
   `grid_member_best_zpow`, `cell_prior_iff`, `campaign_one_cell`, `campaign_one_open_cell`). The
   prior is held on `2^k` (record §6). On the quadratic two members compare exactly:
   `q(x) − q(y) = ½ (x − y) ((x + y − 2) V − 2a)`, so `x` codes at most `2x` iff
   `2 (V + a) ≤ 3 x V`: the Newton point at most the arithmetic midpoint `3x/2` in the map's scale.
   A member whose cell `[3x/4, 3x/2]` holds the Newton point codes least on the whole grid. In the
   prior's own scale (`σ = s/φ`) the cell of `σ_m` is `[2σ_m/3, 4σ_m/3]`, the harmonic midpoints
   of its neighbours. [agent-inferred] The move is by this comparison, because it is the code the
   law minimizes; record §6 read the Newton points against `(σ_m/√2, σ_m √2)`, the members' cells
   in the exponent. The two readings differ in general. On campaign 1 they agree: every at-map
   Newton point the record reports lies in `[4/3, 8/3]`, the cell of `2 I` (`campaign_one_cell`),
   and the opening's located priors lie in `[8/3, 16/3]`, the cell of `2² I`
   (`campaign_one_open_cell`), which the at-map read refines (record §5).

What the Rust carries, read against these statements (#62 holds the rest): `receiving_fisher_face`
computes item 1's terms on the window's own deposit and returns them for the window's certified
step; no pair is carried across deposits, no reading's move through the map before its deposit is
paired with its covector, and `ReceiverDeclaration::receiving_scale` founds `k` once
(`NormalLaw::with_scaled_prior`, `SolvedChart::founded`) and nothing moves it.
-/

namespace Holonics.HNN.PriorCarry

open Holonics.HNN.ReceivingPrior (variance variance_smul)

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
variable {ι : Type*} [Fintype ι]

/-- One reading as `receiving_fisher_face` reads it: its weight `w`, its covector `g = q − p̃` in
its real and phase parts, its masses `p̃`, and the move `Δ` it presents, in its real and phase
parts. -/
structure Reading (ι L : Type*) where
  weight : L
  covRe : ι → L
  covIm : ι → L
  masses : ι → L
  moveRe : ι → L
  moveIm : ι → L

namespace Reading

/-- The reading's alignment `w ⟨g, Δ⟩`, the covector paired with the whole move. -/
def alignment (r : Reading ι L) : L :=
  r.weight * (∑ c, r.covRe c * r.moveRe c + ∑ c, r.covIm c * r.moveIm c)

/-- The reading's curvature `|w| ((119/80) Var_p(Δ_Re) + ¼ |Δ_Im|²)`. -/
def curvature (r : Reading ι L) : L :=
  |r.weight| * (119 / 80 * variance r.masses r.moveRe + (∑ c, r.moveIm c ^ 2) / 4)

/-- The reading with its move scaled by `ψ`, its covector and masses held. -/
def scale (ψ : L) (r : Reading ι L) : Reading ι L :=
  { r with moveRe := fun c => ψ * r.moveRe c, moveIm := fun c => ψ * r.moveIm c }

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] A move scaled by `ψ` has `ψ` times the alignment. -/
theorem alignment_scale (ψ : L) (r : Reading ι L) : (r.scale ψ).alignment = ψ * r.alignment := by
  have h1 : ∑ c, r.covRe c * (ψ * r.moveRe c) = ψ * ∑ c, r.covRe c * r.moveRe c := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∑ c, r.covIm c * (ψ * r.moveIm c) = ψ * ∑ c, r.covIm c * r.moveIm c := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  simp only [alignment, scale, h1, h2]
  ring

/-- [proved-derived; formal-checked] A move scaled by `ψ` has `ψ²` times the curvature
(`variance_smul`). -/
theorem curvature_scale (ψ : L) (r : Reading ι L) : (r.scale ψ).curvature = ψ ^ 2 * r.curvature := by
  have h : ∑ c, (ψ * r.moveIm c) ^ 2 = ψ ^ 2 * ∑ c, r.moveIm c ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  simp only [curvature, scale, h, variance_smul]
  ring

end Reading

/-- The carried pair: the alignment `a` and the certificate's curvature `C`
(`receiving_fisher_face` returns `2 Σ curvature` as its `C`). -/
@[ext]
structure Carry (L : Type*) where
  alignment : L
  curvature : L

/-- One reading arrives: the pair adds its alignment and twice its curvature. -/
def Carry.read (c : Carry L) (r : Reading ι L) : Carry L :=
  ⟨c.alignment + r.alignment, c.curvature + 2 * r.curvature⟩

/-- The pair carried from `c` over the readings in their order of arrival. -/
def carried (c : Carry L) (rs : List (Reading ι L)) : Carry L :=
  rs.foldl Carry.read c

omit [IsStrictOrderedRing L] in
theorem carried_cons (c : Carry L) (r : Reading ι L) (rs : List (Reading ι L)) :
    carried c (r :: rs) = carried (c.read r) rs := rfl

omit [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The carry needs no tape.** The pair carried over two runs of
readings is the pair carried over the second from the pair carried over the first. -/
theorem carried_append (c : Carry L) (xs ys : List (Reading ι L)) :
    carried c (xs ++ ys) = carried (carried c xs) ys :=
  List.foldl_append

omit [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The carry is the certificate's sum.** Carried from `c`, the
pair is `c` plus the readings' summed alignment and twice their summed curvature: over one window's
samples from zero, the fold `receiving_fisher_face` computes. -/
theorem carried_eq_sum (c : Carry L) (rs : List (Reading ι L)) :
    carried c rs = ⟨c.alignment + (rs.map Reading.alignment).sum,
      c.curvature + 2 * (rs.map Reading.curvature).sum⟩ := by
  induction rs generalizing c with
  | nil => ext <;> simp [carried]
  | cons r rs ih =>
    rw [carried_cons, ih]
    ext <;> simp only [Carry.read, List.map_cons, List.sum_cons] <;> ring

/-- [proved-derived; formal-checked] **On a held face the carried pair rebases exactly.** Scaling
every reading's move by `ψ` takes the carried pair `(a, C)` to `(ψ a, ψ² C)`. -/
theorem carried_scale (ψ a C : L) (rs : List (Reading ι L)) :
    carried ⟨ψ * a, ψ ^ 2 * C⟩ (rs.map (Reading.scale ψ)) =
      ⟨ψ * (carried ⟨a, C⟩ rs).alignment, ψ ^ 2 * (carried ⟨a, C⟩ rs).curvature⟩ := by
  induction rs generalizing a C with
  | nil => rfl
  | cons r rs ih =>
    have e : Carry.read ⟨ψ * a, ψ ^ 2 * C⟩ (r.scale ψ) =
        ⟨ψ * (a + r.alignment), ψ ^ 2 * (C + 2 * r.curvature)⟩ := by
      ext <;> simp only [Carry.read, Reading.alignment_scale, Reading.curvature_scale] <;> ring
    rw [List.map_cons, carried_cons, carried_cons, e]
    exact ih _ _

/-- [proved-derived; formal-checked] **The certified bound read from the moved member.** The bound
`L₀ − φ a + φ² C/2` read with the rebased pair `(ψ a, ψ² C)` at `χ` is the original bound at the
total scale `ψ χ`. -/
theorem certified_bound_rebase (L0 a C ψ χ : L) :
    L0 - χ * (ψ * a) + χ ^ 2 * (ψ ^ 2 * C) / 2 = L0 - (ψ * χ) * a + (ψ * χ) ^ 2 * C / 2 := by
  ring

omit [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The certified Newton point locates one prior from every
member.** The rebased pair's Newton point `ψ a/(ψ² C)`, times `ψ`, is the original `a/C`. -/
theorem certified_newton_rebase (a C ψ : L) (hψ : ψ ≠ 0) :
    ψ * ((ψ * a) / (ψ ^ 2 * C)) = a / C := by
  by_cases hC : C = 0
  · simp [hC]
  · field_simp

section AtMap

/-- Record §4's quadratic: the prequential code's change, to second order, when the map in force is
scaled by `φ`, with `a` the at-map alignment and `V` its curvature. -/
def model (a V φ : L) : L := -(φ - 1) * a + (φ - 1) ^ 2 * V / 2

/-- The at-map pair after the prior moves by `ψ` (`s ↦ s/ψ`): `(ψ (a − (ψ − 1) V), ψ² V)`. -/
def rebaseAt (ψ : L) (p : L × L) : L × L :=
  (ψ * (p.1 - (ψ - 1) * p.2), ψ ^ 2 * p.2)

/-- [proved-derived; formal-checked] **The rebased pair reads the same quadratic.** Read from the
member `ψ`, the quadratic of the rebased pair is the original one less its value at `ψ`:
`q(ψ χ) = q(ψ) + q′(χ)`. -/
theorem model_rebase (a V ψ χ : L) :
    model a V (ψ * χ) = model a V ψ + model (rebaseAt ψ (a, V)).1 (rebaseAt ψ (a, V)).2 χ := by
  simp only [model, rebaseAt]
  ring

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] The unit move leaves the pair. -/
theorem rebaseAt_one (p : L × L) : rebaseAt 1 p = p := by
  ext <;> simp [rebaseAt]

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **Moves compose.** Two moves of the prior rebase the pair as
their product does. -/
theorem rebaseAt_mul (ψ₁ ψ₂ : L) (p : L × L) :
    rebaseAt ψ₂ (rebaseAt ψ₁ p) = rebaseAt (ψ₁ * ψ₂) p := by
  ext <;> simp only [rebaseAt] <;> ring

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The located scale is the same from every member.** The
rebased pair's Newton point `1 + a′/V′`, times `ψ`, is the original `1 + a/V`. -/
theorem newton_rebaseAt (a V ψ : L) (hψ : ψ ≠ 0) (hV : V ≠ 0) :
    ψ * (1 + (rebaseAt ψ (a, V)).1 / (rebaseAt ψ (a, V)).2) = 1 + a / V := by
  simp only [rebaseAt]
  field_simp
  ring

/-- [proved-derived; formal-checked] **A move into a member's cell stays there.** If the Newton
point lies in the cell `[3x/4, 3x/2]` of the member `x`, the pair rebased to `x` has its Newton
point in the unit's cell `[3/4, 3/2]`: the moved prior is the rebased pair's own best member. -/
theorem rebase_into_cell (a V x : L) (hx : 0 < x) (hV : V ≠ 0)
    (hlo : 3 * x ≤ 4 * (1 + a / V)) (hhi : 2 * (1 + a / V) ≤ 3 * x) :
    3 ≤ 4 * (1 + (rebaseAt x (a, V)).1 / (rebaseAt x (a, V)).2) ∧
      2 * (1 + (rebaseAt x (a, V)).1 / (rebaseAt x (a, V)).2) ≤ 3 := by
  have e := newton_rebaseAt a V x hx.ne' hV
  set ν := 1 + (rebaseAt x (a, V)).1 / (rebaseAt x (a, V)).2
  rw [← e] at hlo hhi
  constructor
  · nlinarith
  · nlinarith

/-- [proved-derived; formal-checked] Two members compare by the arithmetic midpoint:
`q(x) − q(y) = ½ (x − y) ((x + y − 2) V − 2a)`. -/
theorem model_sub (a V x y : L) :
    model a V x - model a V y = (x - y) * ((x + y - 2) * V - 2 * a) / 2 := by
  simp only [model]
  ring

/-- [proved-derived; formal-checked] **Neighbouring powers of two.** For `x > 0`, `x` codes at most
`2x` exactly when `2 (V + a) ≤ 3 x V`: for `V > 0`, the Newton point `1 + a/V` at most `3x/2`. -/
theorem neighbour_le_iff (a V x : L) (hx : 0 < x) :
    model a V x ≤ model a V (2 * x) ↔ 2 * (V + a) ≤ 3 * x * V := by
  have e : model a V x - model a V (2 * x) = -(x * (3 * x * V - 2 * (V + a))) / 2 := by
    rw [model_sub]; ring
  rw [← sub_nonpos, e]
  constructor
  · intro h
    by_contra hc
    have hc' := not_le.mp hc
    nlinarith
  · intro h
    have : 0 ≤ x * (3 * x * V - 2 * (V + a)) := mul_nonneg hx.le (by linarith)
    linarith

/-- [proved-derived; formal-checked] **The best member of the grid.** For `V > 0`, if
`3 x V ≤ 4 (V + a)` and `2 (V + a) ≤ 3 x V` (the Newton point in `[3x/4, 3x/2]`), then `x` codes
at most every `y ≥ 2x` and every `y ≤ x/2`. -/
theorem grid_member_best (a V x y : L) (hV : 0 < V) (hlo : 3 * x * V ≤ 4 * (V + a))
    (hhi : 2 * (V + a) ≤ 3 * x * V) (hy : 2 * x ≤ y ∨ y ≤ x / 2) :
    model a V x ≤ model a V y := by
  have hx : 0 ≤ x := by nlinarith
  rw [← sub_nonneg, model_sub]
  apply div_nonneg _ zero_le_two
  rcases hy with hy | hy
  · have h1 : 0 ≤ y - x := by linarith
    have h2 : 0 ≤ (y + x - 2) * V - 2 * a := by nlinarith
    exact mul_nonneg h1 h2
  · have h1 : y - x ≤ 0 := by linarith
    have h2 : (y + x - 2) * V - 2 * a ≤ 0 := by nlinarith
    nlinarith [mul_nonneg (neg_nonneg.2 h1) (neg_nonneg.2 h2)]

/-- [proved-derived; formal-checked] **The dyadic grid.** Under the same cell condition, `x` codes
at most every member `2^j x`. -/
theorem grid_member_best_zpow (a V x : L) (hV : 0 < V) (hlo : 3 * x * V ≤ 4 * (V + a))
    (hhi : 2 * (V + a) ≤ 3 * x * V) (j : ℤ) :
    model a V x ≤ model a V ((2 : L) ^ j * x) := by
  have hx : 0 ≤ x := by nlinarith
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · apply grid_member_best a V x _ hV hlo hhi
    right
    have h : (2 : L) ^ j ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ one_le_two (by omega)
    have h' : (2 : L) ^ (-1 : ℤ) = 1 / 2 := by simp
    rw [h'] at h
    nlinarith
  · simp
  · apply grid_member_best a V x _ hV hlo hhi
    left
    have h : (2 : L) ^ (1 : ℤ) ≤ 2 ^ j := zpow_le_zpow_right₀ one_le_two (by omega)
    rw [zpow_one] at h
    nlinarith

/-- [proved-derived; formal-checked] **The cell in the prior's scale.** With the map's scale
`φ = s/σ` for a prior `σ` read from the member `s`, the Newton point `s/σ*` lies in the cell
`[3x/4, 3x/2]` of the member `x = s/σ_m` exactly when the located prior lies in
`[2σ_m/3, 4σ_m/3]`. -/
theorem cell_prior_iff (s σm σ : L) (hs : 0 < s) (hm : 0 < σm) (hσ : 0 < σ) :
    (3 * (s / σm) ≤ 4 * (s / σ) ∧ 2 * (s / σ) ≤ 3 * (s / σm)) ↔
      (2 * σm ≤ 3 * σ ∧ 3 * σ ≤ 4 * σm) := by
  rw [show 3 * (s / σm) = (3 * s) / σm by ring, show 4 * (s / σ) = (4 * s) / σ by ring,
    show 2 * (s / σ) = (2 * s) / σ by ring, div_le_div_iff₀ hm hσ, div_le_div_iff₀ hσ hm]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- [proved-derived; formal-checked] **Campaign 1's at-map Newton points lie in the cell of `2 I`.**
Record §5 and §6: over the 3,400 readings, read from `I` (`12055433/2^23`) and from `2 I`
(`16109515/2^23`); over the first 2,192, read from `I` (`14350156/2^23`), from `2 I`
(`9137823/2^22`) and from `2² I` (`10741668/2^22`). Each lies in `[4/3, 8/3]`. -/
theorem campaign_one_cell :
    ∀ σ ∈ ({12055433 / 2 ^ 23, 16109515 / 2 ^ 23, 14350156 / 2 ^ 23, 9137823 / 2 ^ 22,
      10741668 / 2 ^ 22} : Finset ℚ), 2 * 2 ≤ 3 * σ ∧ 3 * σ ≤ 4 * 2 := by
  intro σ hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- [proved-derived; formal-checked] **The opening's located priors lie in the cell of `2² I`.**
Record §5: `s_open` is `13773580/2^22` over 2,192 readings and `14757253/2^22` over 3,400, each in
`[8/3, 16/3]`; the at-map read refines it into the cell of `2 I` (`campaign_one_cell`). -/
theorem campaign_one_open_cell :
    ∀ σ ∈ ({13773580 / 2 ^ 22, 14757253 / 2 ^ 22} : Finset ℚ),
      2 * 4 ≤ 3 * σ ∧ 3 * σ ≤ 4 * 4 := by
  intro σ hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl <;> norm_num

end AtMap

/-! ### Audit -/

#print axioms carried_append
#print axioms carried_eq_sum
#print axioms carried_scale
#print axioms certified_newton_rebase
#print axioms model_rebase
#print axioms rebaseAt_mul
#print axioms newton_rebaseAt
#print axioms rebase_into_cell
#print axioms neighbour_le_iff
#print axioms grid_member_best_zpow
#print axioms cell_prior_iff
#print axioms campaign_one_cell
#print axioms campaign_one_open_cell

end Holonics.HNN.PriorCarry
