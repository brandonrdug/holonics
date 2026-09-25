import Holonics.Holarchy.View
import Holonics.Geometry.AffineSwing

/-!
# Fluid.Cells: reflect a square and a cube with the Swing, then join them

[definition] Battle test 1 of rebuild step 6, K3 (#74; restructure plan §3.5 at `13f8c734`). The
cells of a fluid control volume are **cubical cells** of the grid chart `ℚⁿ`: a cell is a base
corner `v` and a set `S` of directions, the box `v + [0,1]^S` (`Cell`). Its oriented boundary is
the cubical formula

```text
∂(v, S) = Σ_{i ∈ S} (−1)^{pos(S,i)} [ (v + eᵢ, S∖i) − (v, S∖i) ]      pos(S,i) = #{j ∈ S | j < i}
```

(`faces`, extended linearly to integer chains: `boundary`). The **Swing** about an anchor `b`
(`Geometry/AffineSwing.swing`, `x ↦ b + b − x`) sends the cell `(v, S)` to the cell whose base is
the Swing of its far corner, `(swing b (v + 1_S), S)` (`swingCell`), and it reverses every one of
the cell's `|S|` directions, so it carries the cell's orientation with the **hand** `(−1)^|S|`
(`swingChain`).

[proved-derived; formal-checked]

* **`∂² = 0`** on the whole grid chart, in every dimension (`boundary_boundary`): the two ways of
  removing directions `i ≠ j` meet the same codimension-two cell with opposite signs
  (`sgn_erase_antisymm`).
* **The Swing is a chain map with its hand**: `∂ ∘ swing_* = swing_* ∘ ∂` with the sign
  `(−1)^k` on `k`-cells (`boundary_swingChain`). The point Swing preserves the orientation of a
  square (`(−1)² = 1`) and reverses that of a cube (`(−1)³ = −1`).
* **Reflect across a face.** The Swing about the centre of the face `x_i = 1` of the unit cube
  `(0, univ)` sends it to its neighbour `(eᵢ, univ)` (`swingCell_cube`) and fixes that face
  (`swingCell_sharedFace`); the pushed chain is the neighbour with the hand `(−1)ⁿ`
  (`swingChain_cube`).
* **Join.** The shared face enters the cube's boundary with the sign `sgn` and the neighbour's
  with `−sgn` (`faces_cube_sharedFace`, `faces_neighbour_sharedFace`), so it cancels in the joined
  boundary (`join_cancels`): the cube joined to its Swing push corrected by the hand `(−1)ⁿ` is the
  cube joined to its neighbour (`handed_push_cancels`). The finite complex of the joined cells (`gridComplex`, the three top
  grades as a Holarchy `CellComplex`, with `∂² = 0` inherited from the grid: `incidence_dd`)
  carries the join as a two-block grain, and `Holarchy/View.shared_face_cancels` gives the
  cancellation there (`joined_shared_face_cancels`): **the shared face cancels exactly once**,
  with unit coefficients of opposite sign in the two blocks.

[counterexample; formal-checked] **The hand is load-bearing.** Joining the cube to its raw Swing
image (the pushed chain, hand not corrected) leaves the shared face with coefficient
`sgn · (1 − (−1)ⁿ)` in the whole's boundary (`rawPush_sharedFace`): zero for the square
(`square_rawPush_cancels`) and `2·sgn ≠ 0` for the cube (`cube_rawPush_uncancelled`), which is
the `sharedFaceUncancelled` defect of `Holarchy/Join`.

[open] The cubical cells are unit boxes of the grid chart; a general polyhedral cell, a declared
metric other than the grid's and connection-valued incidence on these cells are not treated here.
-/

noncomputable section

namespace Holonics.Physics.Fluid.Cells

open Finsupp
open Holonics.Geometry.AffineSwing
open Matrix

variable {n : ℕ}

/-! ## 1. Cubical cells and their oriented boundary -/

/-- [definition] A point of the grid chart `ℚⁿ`. -/
abbrev Point (n : ℕ) := Fin n → ℚ

/-- [definition] **A cubical cell**: its base corner `v` and its set of directions `S`, the box
`v + [0,1]^S`. -/
abbrev Cell (n : ℕ) := Point n × Finset (Fin n)

/-- [definition] Integer chains of cubical cells. -/
abbrev Chain (n : ℕ) := Cell n →₀ ℤ

/-- [definition] The far-corner offset of a direction set, `1_S`. -/
def ind (S : Finset (Fin n)) : Point n := fun i => if i ∈ S then 1 else 0

/-- [definition] The unit step `eᵢ`. -/
def unit (i : Fin n) : Point n := Pi.single i 1

/-- [definition] How many directions of `S` precede `i`. -/
def pos (S : Finset (Fin n)) (i : Fin n) : ℕ := (S.filter (· < i)).card

/-- [definition] The orientation sign `(−1)^pos(S,i)` of removing direction `i` from `S`. -/
def sgn (S : Finset (Fin n)) (i : Fin n) : ℤ := (-1) ^ pos S i

/-- [definition] The chain of one cell with coefficient `1`. -/
def cell (c : Cell n) : Chain n := Finsupp.single c 1

/-- [definition] **The oriented faces of a cell**: `Σ_{i∈S} (−1)^pos(S,i) [(v + eᵢ, S∖i) − (v, S∖i)]`. -/
def faces (c : Cell n) : Chain n :=
  ∑ i ∈ c.2, sgn c.2 i • (cell (c.1 + unit i, c.2.erase i) - cell (c.1, c.2.erase i))

/-- [definition] **The boundary** of an integer chain: `faces`, extended linearly. -/
def boundary : Chain n →ₗ[ℤ] Chain n := Finsupp.linearCombination ℤ faces

theorem boundary_cell (c : Cell n) : boundary (cell c) = faces c := by
  simp [boundary, cell]

theorem single_eq_smul_cell (c : Cell n) (k : ℤ) : Finsupp.single c k = k • cell c := by
  simp [cell]

theorem ind_erase_add_unit {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) :
    ind (S.erase i) + unit i = ind S := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [ind, unit, hi]
  · simp [ind, unit, hji, Finset.mem_erase]

theorem unit_ne_zero (i : Fin n) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit] at this

/-- Removing `i` lowers the position of every later direction by one. -/
theorem pos_erase_of_lt {S : Finset (Fin n)} {i j : Fin n} (hi : i ∈ S) (hij : i < j) :
    pos (S.erase i) j + 1 = pos S j := by
  unfold pos
  rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hi, hij⟩)]
  have : 0 < (S.filter (· < j)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩
  omega

/-- Removing `i` keeps the position of every earlier direction. -/
theorem pos_erase_of_not_lt {S : Finset (Fin n)} {i j : Fin n} (hij : ¬ i < j) :
    pos (S.erase i) j = pos S j := by
  unfold pos
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp [hij]

theorem sgn_erase_of_lt {S : Finset (Fin n)} {i j : Fin n} (hi : i ∈ S) (hij : i < j) :
    sgn (S.erase i) j = -sgn S j := by
  unfold sgn
  rw [← pos_erase_of_lt hi hij, pow_succ]
  ring

theorem sgn_erase_of_not_lt {S : Finset (Fin n)} {i j : Fin n} (hij : ¬ i < j) :
    sgn (S.erase i) j = sgn S j := by
  unfold sgn
  rw [pos_erase_of_not_lt hij]

/-- [proved-derived; formal-checked] **The two removal orders carry opposite signs**: for distinct
directions `i, j` of `S`, `sgn(S,i)·sgn(S∖i,j) = −sgn(S,j)·sgn(S∖j,i)`. This is the whole of
`∂² = 0`. -/
theorem sgn_erase_antisymm {S : Finset (Fin n)} {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    sgn S i * sgn (S.erase i) j = -(sgn S j * sgn (S.erase j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [sgn_erase_of_lt hi h, sgn_erase_of_not_lt (not_lt.mpr h.le)]
    ring
  · rw [sgn_erase_of_not_lt (not_lt.mpr h.le), sgn_erase_of_lt hj h]
    ring

/-- The four codimension-two corners met by removing `i` and then `j`. -/
def corner (c : Cell n) (i j : Fin n) : Chain n :=
  cell (c.1 + unit i + unit j, (c.2.erase i).erase j) - cell (c.1 + unit i, (c.2.erase i).erase j)
    - cell (c.1 + unit j, (c.2.erase i).erase j) + cell (c.1, (c.2.erase i).erase j)

theorem corner_symm (c : Cell n) (i j : Fin n) : corner c i j = corner c j i := by
  unfold corner
  rw [Finset.erase_right_comm, add_right_comm c.1 (unit i) (unit j)]
  abel

theorem boundary_faces_eq (c : Cell n) :
    boundary (faces c) =
      ∑ i ∈ c.2, ∑ j ∈ c.2.erase i, (sgn c.2 i * sgn (c.2.erase i) j) • corner c i j := by
  unfold faces
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_sub, boundary_cell, boundary_cell]
  unfold faces
  simp only
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul, ← smul_sub]
  congr 2
  unfold corner
  abel

/-- [proved-derived; formal-checked] **`∂² = 0` on the grid chart, in every dimension.** -/
theorem boundary_faces (c : Cell n) : boundary (faces c) = 0 := by
  rw [boundary_faces_eq, Finset.sum_sigma']
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_erase] at hp
    obtain ⟨hi, hji, hj⟩ := hp
    simp only
    rw [sgn_erase_antisymm hi hj (Ne.symm hji), corner_symm c j i, neg_smul, neg_add_cancel]
  · rintro ⟨i, j⟩ hp _ heq
    simp only [Finset.mem_sigma, Finset.mem_erase] at hp
    simp only [Sigma.mk.injEq] at heq
    exact hp.2.1 heq.1
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_erase] at hp ⊢
    exact ⟨hp.2.2, Ne.symm hp.2.1, hp.1⟩
  · rintro ⟨i, j⟩ _
    rfl

/-- [proved-derived; formal-checked] **`∂ ∘ ∂ = 0`** on every integer chain. -/
theorem boundary_boundary : (boundary : Chain n →ₗ[ℤ] Chain n) ∘ₗ boundary = 0 := by
  refine Finsupp.lhom_ext fun c k => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, single_eq_smul_cell, map_zsmul,
    boundary_cell, boundary_faces, smul_zero]

theorem boundary_boundary_apply (x : Chain n) : boundary (boundary x) = 0 :=
  LinearMap.congr_fun boundary_boundary x

/-! ## 2. The Swing on cells, with its hand -/

/-- [definition] **The Swing of a cell** about the anchor `b`: the box whose base is the Swing of
the cell's far corner, `(swing b (v + 1_S), S)`. -/
def swingCell (b : Point n) (c : Cell n) : Cell n := (swing b (c.1 + ind c.2), c.2)

/-- [definition] **The Swing on chains**: each cell goes to its Swing with the hand `(−1)^|S|`,
since the half-turn reverses each of the cell's directions. -/
def swingChain (b : Point n) : Chain n →ₗ[ℤ] Chain n :=
  Finsupp.linearCombination ℤ fun c => ((-1 : ℤ) ^ c.2.card) • cell (swingCell b c)

theorem swingChain_cell (b : Point n) (c : Cell n) :
    swingChain b (cell c) = ((-1 : ℤ) ^ c.2.card) • cell (swingCell b c) := by
  simp [swingChain, cell]

theorem swing_far_corner (b v : Point n) {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) :
    swing b (v + unit i + ind (S.erase i)) = swing b (v + ind S) := by
  rw [← ind_erase_add_unit hi]; congr 1; abel

theorem swing_near_corner (b v : Point n) {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) :
    swing b (v + ind (S.erase i)) = swing b (v + ind S) + unit i := by
  rw [← ind_erase_add_unit hi]; simp only [swing]; abel

theorem neg_one_pow_card_erase {S : Finset (Fin n)} {i : Fin n} (hi : i ∈ S) :
    (-1 : ℤ) ^ (S.erase i).card = -(-1 : ℤ) ^ S.card := by
  rw [Finset.card_erase_of_mem hi]
  have : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
  conv_rhs => rw [show S.card = (S.card - 1) + 1 by omega, pow_succ]
  ring

/-- [proved-derived; formal-checked] **The Swing is a chain map with its hand**:
`∂ (swing_* c) = swing_* (∂ c)` for every chain, with `(−1)^k` on `k`-cells. -/
theorem boundary_swingChain (b : Point n) :
    (boundary : Chain n →ₗ[ℤ] Chain n) ∘ₗ swingChain b = swingChain b ∘ₗ boundary := by
  refine Finsupp.lhom_ext fun c k => ?_
  simp only [LinearMap.comp_apply, single_eq_smul_cell, map_zsmul]
  congr 1
  rw [swingChain_cell, map_zsmul, boundary_cell, boundary_cell]
  unfold faces swingCell
  simp only
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_zsmul, map_sub, swingChain_cell, swingChain_cell]
  simp only [swingCell]
  rw [swing_far_corner b c.1 hi, swing_near_corner b c.1 hi, neg_one_pow_card_erase hi,
    smul_comm ((-1 : ℤ) ^ c.2.card) (sgn c.2 i)]
  congr 1
  rw [neg_smul, neg_smul, smul_sub]
  abel

theorem boundary_swingChain_apply (b : Point n) (x : Chain n) :
    boundary (swingChain b x) = swingChain b (boundary x) :=
  LinearMap.congr_fun (boundary_swingChain b) x

/-! ## 3. Reflect the unit cube across a face and join -/

/-- [definition] The unit cube `[0,1]ⁿ`. -/
def cube : Cell n := (0, Finset.univ)

/-- [definition] Its neighbour across the face `x_i = 1`. -/
def neighbour (i : Fin n) : Cell n := (unit i, Finset.univ)

/-- [definition] The shared face `x_i = 1`. -/
def sharedFace (i : Fin n) : Cell n := (unit i, Finset.univ.erase i)

/-- [definition] The centre of the shared face, the Swing's anchor. -/
def faceCentre (i : Fin n) : Point n := unit i + (1 / 2 : ℚ) • ind (Finset.univ.erase i)

theorem faceCentre_double (i : Fin n) :
    faceCentre i + faceCentre i = unit i + ind Finset.univ := by
  rw [← ind_erase_add_unit (Finset.mem_univ i)]
  funext j
  simp only [faceCentre, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **The Swing about the face centre carries the cube to its
neighbour.** -/
theorem swingCell_cube (i : Fin n) : swingCell (faceCentre i) cube = neighbour i := by
  simp only [swingCell, cube, neighbour, swing, zero_add, faceCentre_double, add_sub_cancel_right]

/-- [proved-derived; formal-checked] **The Swing fixes the shared face** (its anchor is the face's
centre). -/
theorem swingCell_sharedFace (i : Fin n) : swingCell (faceCentre i) (sharedFace i) = sharedFace i := by
  simp only [swingCell, sharedFace, swing, faceCentre_double, Prod.mk.injEq, and_true]
  rw [← ind_erase_add_unit (Finset.mem_univ i)]
  abel

/-- [proved-derived; formal-checked] The pushed chain of the cube is its neighbour with the hand
`(−1)ⁿ`. -/
theorem swingChain_cube (i : Fin n) :
    swingChain (faceCentre i) (cell cube) = ((-1 : ℤ) ^ n) • cell (neighbour i) := by
  rw [swingChain_cell, swingCell_cube]
  simp [cube]

theorem cell_apply_sharedFace_step (i j : Fin n) (v : Point n) :
    cell (v + unit j, Finset.univ.erase j) (sharedFace i) =
      if v + unit j = unit i ∧ j = i then 1 else 0 := by
  unfold cell sharedFace
  rw [Finsupp.single_apply]
  by_cases h : v + unit j = unit i ∧ j = i
  · obtain ⟨h1, rfl⟩ := h
    simp [h1]
  · rw [if_neg h, if_neg]
    rintro heq
    simp only [Prod.mk.injEq] at heq
    refine h ⟨heq.1, ?_⟩
    by_contra hji
    have := congrArg (fun s : Finset (Fin n) => j ∈ s) heq.2
    simp [hji] at this

theorem cell_apply_sharedFace_base (i j : Fin n) (v : Point n) :
    cell (v, Finset.univ.erase j) (sharedFace i) = if v = unit i ∧ j = i then 1 else 0 := by
  unfold cell sharedFace
  rw [Finsupp.single_apply]
  by_cases h : v = unit i ∧ j = i
  · obtain ⟨h1, rfl⟩ := h
    simp [h1]
  · rw [if_neg h, if_neg]
    rintro heq
    simp only [Prod.mk.injEq] at heq
    refine h ⟨heq.1, ?_⟩
    by_contra hji
    have := congrArg (fun s : Finset (Fin n) => j ∈ s) heq.2
    simp [hji] at this

/-- [proved-derived; formal-checked] **The shared face in the cube's oriented boundary**: it enters
with the sign `sgn(univ, i)`. -/
theorem faces_cube_sharedFace (i : Fin n) : faces cube (sharedFace i) = sgn Finset.univ i := by
  unfold faces cube
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [cell_apply_sharedFace_step, cell_apply_sharedFace_base]
    have h0 : (0 : Point n) ≠ unit i := (unit_ne_zero i).symm
    simp [h0]
  · intro j _ hji
    rw [cell_apply_sharedFace_step, cell_apply_sharedFace_base]
    simp [hji]
  · simp

/-- [proved-derived; formal-checked] **The shared face in the neighbour's oriented boundary**: it
enters with the opposite sign `−sgn(univ, i)`. -/
theorem faces_neighbour_sharedFace (i : Fin n) :
    faces (neighbour i) (sharedFace i) = -sgn Finset.univ i := by
  unfold faces neighbour
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [cell_apply_sharedFace_step, cell_apply_sharedFace_base]
    have : unit i + unit i ≠ unit i := by
      intro h; exact unit_ne_zero i (by simpa using h)
    simp [this]
  · intro j _ hji
    rw [cell_apply_sharedFace_step, cell_apply_sharedFace_base]
    have : unit i + unit j ≠ unit i := by
      intro h; exact unit_ne_zero j (by simpa using h)
    simp [hji, this]
  · simp

/-- [proved-derived; formal-checked] **The join cancels the shared face**: in the boundary of the
cube plus its neighbour (each with its own positive orientation) the shared face has coefficient
zero. -/
theorem join_cancels (i : Fin n) :
    boundary (cell cube + cell (neighbour i)) (sharedFace i) = 0 := by
  rw [map_add, boundary_cell, boundary_cell, Finsupp.add_apply, faces_cube_sharedFace,
    faces_neighbour_sharedFace, add_neg_cancel]

/-- [proved-derived; formal-checked] **The hand-corrected Swing push joins**: the cube plus
`(−1)ⁿ` times its pushed chain is the cube plus its neighbour, which cancels the shared face. -/
theorem handed_push_cancels (i : Fin n) :
    boundary (cell cube + ((-1 : ℤ) ^ n) • swingChain (faceCentre i) (cell cube)) (sharedFace i)
      = 0 := by
  rw [swingChain_cube, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  exact join_cancels i

/-- [counterexample; formal-checked] **The raw push leaves `sgn·(1 − (−1)ⁿ)`** on the shared
face: the cube joined to its uncorrected Swing image. -/
theorem rawPush_sharedFace (i : Fin n) :
    boundary (cell cube + swingChain (faceCentre i) (cell cube)) (sharedFace i) =
      sgn Finset.univ i * (1 - (-1) ^ n) := by
  rw [swingChain_cube, map_add, map_zsmul, boundary_cell, boundary_cell, Finsupp.add_apply,
    Finsupp.smul_apply, faces_cube_sharedFace, faces_neighbour_sharedFace, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **The square**: the point Swing preserves a square's
hand, so the raw push already cancels the shared edge. -/
theorem square_rawPush_cancels (i : Fin 2) :
    boundary (cell cube + swingChain (faceCentre i) (cell cube)) (sharedFace i) = 0 := by
  rw [rawPush_sharedFace]; norm_num

/-- [counterexample; formal-checked] **The cube**: the point Swing reverses a cube's hand, so the
raw push leaves the shared face with coefficient `±2`, uncancelled. -/
theorem cube_rawPush_uncancelled (i : Fin 3) :
    boundary (cell cube + swingChain (faceCentre i) (cell cube)) (sharedFace i) =
      2 * sgn Finset.univ i ∧
    boundary (cell cube + swingChain (faceCentre i) (cell cube)) (sharedFace i) ≠ 0 := by
  rw [rawPush_sharedFace]
  refine ⟨by norm_num; ring, ?_⟩
  have : sgn (Finset.univ : Finset (Fin 3)) i ≠ 0 := by unfold sgn; exact pow_ne_zero _ (by norm_num)
  norm_num
  exact this

/-! ## 4. The finite complex of joined cells, and the Holarchy join -/

/-- [definition] The faces met by a set of top cells. -/
def facesOf (tops : Finset (Cell n)) : Finset (Cell n) := tops.biUnion fun c => (faces c).support

/-- [definition] The ridges met by those faces. -/
def ridgesOf (tops : Finset (Cell n)) : Finset (Cell n) :=
  (facesOf tops).biUnion fun f => (faces f).support

/-- A chain's boundary read through any finite set of cells containing its support. -/
theorem boundary_apply_eq_sum (x : Chain n) {F : Finset (Cell n)} (hF : x.support ⊆ F)
    (r : Cell n) : boundary x r = ∑ f ∈ F, x f * faces f r := by
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_subset hF fun f _ hf => ?_
  rw [Finsupp.notMem_support_iff.mp hf, zero_mul]

/-- [definition] The ridge-by-face incidence of a set of top cells, read from the grid. -/
def ridgeIncidence (tops : Finset (Cell n)) : Matrix (ridgesOf tops) (facesOf tops) ℚ :=
  fun r f => ((faces f.1 r.1 : ℤ) : ℚ)

/-- [definition] The face-by-region incidence of a set of top cells, read from the grid. -/
def faceIncidence (tops : Finset (Cell n)) : Matrix (facesOf tops) tops ℚ :=
  fun f c => ((faces c.1 f.1 : ℤ) : ℚ)

/-- [proved-derived; formal-checked] **`∂² = 0` on the finite complex of any set of top cells**,
inherited from the grid (`boundary_faces`): the faces met by the top cells contain the support of
their boundaries, so the matrix product reads `∂∂` of each top cell. -/
theorem incidence_dd (tops : Finset (Cell n)) : ridgeIncidence tops * faceIncidence tops = 0 := by
  funext r c
  simp only [Matrix.zero_apply]
  have hsub : (faces c.1).support ⊆ facesOf tops :=
    Finset.subset_biUnion_of_mem (fun c => (faces c).support) c.2
  have h := boundary_apply_eq_sum (faces c.1) hsub r.1
  rw [boundary_faces] at h
  have h' : ((∑ f ∈ facesOf tops, faces c.1 f * faces f r.1 : ℤ) : ℚ) = 0 := by
    rw [← h]; simp
  push_cast at h'
  rw [← h', ← Finset.sum_coe_sort (facesOf tops)]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [ridgeIncidence, faceIncidence]
  ring

/-- [definition] **The finite complex of a set of top cells**: its regions are the top cells, its
faces and ridges the cells their boundaries meet, and its incidences the grid's
(`Holarchy/Join.CellComplex`). -/
def gridComplex (tops : Finset (Cell n)) : HolarchyCore.CellComplex ℚ where
  C₀ := ridgesOf tops
  C₁ := facesOf tops
  C₂ := tops
  d₁ := ridgeIncidence tops
  d₂ := faceIncidence tops
  dd := incidence_dd tops

/-- [definition] The joined cells: the cube and its neighbour across face `i`. -/
def joined (i : Fin n) : Finset (Cell n) := {cube, neighbour i}

theorem cube_ne_neighbour (i : Fin n) : (cube : Cell n) ≠ neighbour i := by
  intro h
  have := congrArg Prod.fst h
  exact unit_ne_zero i this.symm

theorem cube_mem_joined (i : Fin n) : (cube : Cell n) ∈ joined i := by simp [joined]

theorem neighbour_mem_joined (i : Fin n) : neighbour i ∈ joined i := by simp [joined]

theorem sgn_ne_zero (S : Finset (Fin n)) (i : Fin n) : sgn S i ≠ 0 := by
  unfold sgn; exact pow_ne_zero _ (by norm_num)

theorem sharedFace_mem_facesOf (i : Fin n) : sharedFace i ∈ facesOf (joined i) := by
  refine Finset.mem_biUnion.mpr ⟨cube, cube_mem_joined i, ?_⟩
  rw [Finsupp.mem_support_iff, faces_cube_sharedFace]
  exact sgn_ne_zero _ _

/-- [definition] The cube as a region of the joined complex. -/
def cubeRegion (i : Fin n) : (gridComplex (joined i)).C₂ := ⟨cube, cube_mem_joined i⟩

/-- [definition] The neighbour as a region of the joined complex. -/
def neighbourRegion (i : Fin n) : (gridComplex (joined i)).C₂ :=
  ⟨neighbour i, neighbour_mem_joined i⟩

/-- [definition] The shared face as a face of the joined complex. -/
def sharedFaceCell (i : Fin n) : (gridComplex (joined i)).C₁ :=
  ⟨sharedFace i, sharedFace_mem_facesOf i⟩

/-- [definition] The grain of the join: each region is its own block (the two constituents). -/
def joinGrain (i : Fin n) :
    HolarchyCore.Grain (gridComplex (joined i)).C₂ (gridComplex (joined i)).C₂ :=
  ⟨fun c => {c}⟩

theorem regions_cases (i : Fin n) (c : (gridComplex (joined i)).C₂) :
    c = cubeRegion i ∨ c = neighbourRegion i := by
  obtain ⟨c, hc⟩ := c
  simp only [joined, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem cubeRegion_ne (i : Fin n) : cubeRegion i ≠ neighbourRegion i := by
  intro h
  exact cube_ne_neighbour i (congrArg Subtype.val h)

/-- The whole's boundary coefficient on a face, for a declared orientation of the two regions. -/
theorem whole_coefficient (i : Fin n) (orient : (gridComplex (joined i)).C₂ → ℚ)
    (f : (gridComplex (joined i)).C₁) :
    ((gridComplex (joined i)).d₂ *ᵥ orient) f =
      (faces cube f.1 : ℚ) * orient (cubeRegion i) +
        (faces (neighbour i) f.1 : ℚ) * orient (neighbourRegion i) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  have huniv : (Finset.univ : Finset (gridComplex (joined i)).C₂) =
      {cubeRegion i, neighbourRegion i} := by
    ext c; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact regions_cases i c
  rw [huniv, Finset.sum_pair (cubeRegion_ne i)]
  rfl

/-- [proved-derived; formal-checked] **The shared face cancels exactly once in the Holarchy
join.** On the joined complex, with each region its own block and both positively oriented,
`Holarchy/View.shared_face_cancels` applies: the shared face enters the cube's block boundary with
the coefficient `sgn(univ, i) ≠ 0` and the neighbour's with its negative. -/
theorem joined_shared_face_cancels (i : Fin n) :
    ((gridComplex (joined i)).d₂ *ᵥ
        HolarchyCore.blockChain (gridComplex (joined i)) 1 (joinGrain i) (cubeRegion i))
        (sharedFaceCell i) =
      -((gridComplex (joined i)).d₂ *ᵥ
        HolarchyCore.blockChain (gridComplex (joined i)) 1 (joinGrain i) (neighbourRegion i))
        (sharedFaceCell i) ∧
    ((gridComplex (joined i)).d₂ *ᵥ
        HolarchyCore.blockChain (gridComplex (joined i)) 1 (joinGrain i) (cubeRegion i))
        (sharedFaceCell i) = (sgn Finset.univ i : ℚ) := by
  classical
  refine ⟨HolarchyCore.shared_face_cancels (g := joinGrain i) ?_ ?_ 1 (sharedFaceCell i) ?_
    (cubeRegion_ne i) ?_, ?_⟩
  · intro c; exact ⟨c, Finset.mem_singleton_self c⟩
  · intro b b' hbb'
    simp only [joinGrain, Finset.disjoint_singleton]
    exact hbb'
  · rw [whole_coefficient]
    simp only [Pi.one_apply, mul_one]
    have := join_cancels i
    rw [map_add, boundary_cell, boundary_cell, Finsupp.add_apply] at this
    exact_mod_cast this
  · intro b'' h1 h2
    rcases regions_cases i b'' with h | h
    · exact absurd h h1
    · exact absurd h h2
  · have hchain : HolarchyCore.blockChain (gridComplex (joined i)) 1 (joinGrain i) (cubeRegion i) =
        fun c => if c = cubeRegion i then 1 else 0 := by
      funext c
      simp [HolarchyCore.blockChain, joinGrain]
    rw [hchain, whole_coefficient]
    simp only [if_true, mul_one, if_neg (cubeRegion_ne i).symm, mul_zero, add_zero]
    change ((faces cube (sharedFace i) : ℤ) : ℚ) = _
    rw [faces_cube_sharedFace]

section Audit

#print axioms boundary_boundary
#print axioms boundary_swingChain
#print axioms join_cancels
#print axioms handed_push_cancels
#print axioms square_rawPush_cancels
#print axioms cube_rawPush_uncancelled
#print axioms incidence_dd
#print axioms joined_shared_face_cancels

end Audit

end Holonics.Physics.Fluid.Cells
