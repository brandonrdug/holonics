import HolonicsResearch.Landmarks.IharaBass

/-!
# The Ihara identity in two frames: a map's source graph and its face dual share their contacts, swap cells for
# faces, and pair their cycle ranks to the contact count

The October receiver topology (`geometry::receiver_topology::two_frame_ihara_reading`, retired with the October crate;
atlas `trace.ihara-two-frames`) reads one construction in two frames: the graph a receiver's diagram presents, and its
face dual, whose cells are the diagram's faces and whose contacts are the diagram's contacts, each joining the faces on
its two sides. It asserts Ihara's theorem in each frame, reads each frame's first Betti number as
`edges − vertices + 1`, and checks that the two cycle ranks sum to the shared contact count (Euler's formula, which
the construction itself demands: it refuses a diagram whose face count is not `edges + 2 − vertices`). The face dual
is dual to the diagram graph, not the source: an apparent crossing adds a diagram node and splits two source
segments.

This file states that reading on a combinatorial map, darts with a rotation `σ` at the cells and a fixed-point-free
involution `α` pairing the two darts of a contact, and joins both frames to `Landmarks/IharaBass.ihara_bass`.

[proved-derived; formal-checked] What is proved.

1. **The face dual** (`dual_σ`, `dual_α`, `dual_φ`, `dual_dual`): the dual map `(σα, α)` has the faces as its cells,
   the same contacts, and the cells as its faces (`σαα = σ`); the dual of the dual is the map.
2. **The two frames' counts** (`cellCount_dual`, `edgeCount_dual`, `faceCount_dual`, `euler_dual`): `V* = F`, `E* = E`,
   `F* = V`, and `V − E + F` is the same in both frames.
3. **The darts are the frame graph's darts** (`dartOf`, `dartOf_bijective`, `dartEquiv`, `card_darts`, `src_frame`,
   `tgt_frame`, `dartOf_swap`): with each contact's two darts `e.out`, `α e.out`, the frame graph's oriented contacts
   `E ⊕ E` are the map's darts, the reversal is `α`, a dart leaves the cell it lies in and enters its reverse's, and
   there are `2E` darts.
4. **Ihara in two frames** (`face_frame_eq_dual_frame`, `two_frames_ihara_bass`): the face-dual frame's graph is the
   dual map's own source frame, and the identity `(1 − u²)^|cells| det(1 − uB) = det(1 − uA + u²(D − 1)) (1 − u²)^|E|`
   holds in both frames, the contacts' power shared and the cells' power `|V|` in one and `|F|` in the other.
5. **The cycle ranks pair** (`cycleRank_dual`, `cycleRank_add_dual`, `cycleRank_eq`, `dual_cycleRank_eq`,
   `iharaExponent_sub_dual`): under Euler's relation `V − E + F = 2`, `b₁ + b₁* = E`, `b₁ = F − 1`, `b₁* = V − 1`, and
   the two frames' Ihara exponents `E − V` and `E − F` differ by `F − V`.
6. **The dual pairs with the diagram, not the source** (`split_edges`, `diagram_cycleRank`,
   `source_pairs_with_dual_iff`): `c` apparent crossings, each on two source segments, give the diagram `V_s + c` cells
   and `E_s + 2c` contacts, so its cycle rank is the source's plus `c`, and the source's cycle rank pairs with the
   face dual's to the diagram's contact count exactly when no crossing split a segment.

The cycle rank `E − V + 1` is the first Betti number of a connected frame, which the October owner required (it refused
a disconnected graph); on a map with `c` components it reads `E − V + c`, and nothing here uses connectivity except as
the reading of that name.

The computational object is the helical pair interaction read on its contacts: a dart is a contact's oriented half,
its reverse the pair's other side, and the two frames read one contact graph at two receivers. Of the winding guide's
six general objects this touches the cell holonomy (the cycle rank counts independent circuits, the primitive cycles
Ihara's product runs over) and the pair (each contact's two darts); the helix, faces and placement, the tube and the
tower thread stay attached.

Consumers: the atlas rows `trace.ihara-two-frames` and `trace.ihara-zeta`, and `Landmarks/IharaBass.ihara_bass`, which
item 4 reads in both frames.

What stands beside it: the planar embedding itself (recovering the faces from a projected diagram and its Euler check,
which this file takes as the hypothesis `V − E + F = 2`), and the Euler product over primitive closed walks
(`Landmarks/IharaEulerProduct`), which the October owner compared to the determinant in each frame.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Landmarks.IharaTwoFrames

open Holonics.Landmarks.IharaBass

/-- [definition] **A combinatorial map**: darts, the rotation `σ` at the cells, and the involution `α` pairing the two
darts of a contact, with no fixed dart. -/
structure CombMap (D : Type*) where
  /-- The rotation at the cells. -/
  σ : Equiv.Perm D
  /-- The pairing of a contact's two darts. -/
  α : Equiv.Perm D
  α_α : ∀ d, α (α d) = d
  α_ne : ∀ d, α d ≠ d

namespace CombMap

variable {D : Type*} (M : CombMap D)

/-- [definition] The face permutation `φ = σα`. -/
def φ : Equiv.Perm D := M.σ * M.α

theorem α_mul_α : M.α * M.α = 1 := Equiv.ext fun d => M.α_α d

/-- [definition] **The face dual** `(σα, α)`. -/
def dual : CombMap D := ⟨M.φ, M.α, M.α_α, M.α_ne⟩

/-- [proved-derived; formal-checked] The dual's cells are the faces. -/
@[simp] theorem dual_σ : M.dual.σ = M.φ := rfl

/-- [proved-derived; formal-checked] The dual's contacts are the map's. -/
@[simp] theorem dual_α : M.dual.α = M.α := rfl

/-- [proved-derived; formal-checked] The dual's faces are the cells: `σαα = σ`. -/
theorem dual_φ : M.dual.φ = M.σ := by
  simp only [φ, dual, mul_assoc, α_mul_α, mul_one]

/-- [proved-derived; formal-checked] The dual of the dual is the map. -/
theorem dual_dual : M.dual.dual = M := by
  have h : M.dual.dual.σ = M.σ := M.dual_φ
  cases M
  simp only [dual, CombMap.mk.injEq] at h ⊢
  exact ⟨h, trivial⟩

/-! ## Cells, contacts and faces -/

/-- [definition] The orbits of a permutation. -/
abbrev Cells (π : Equiv.Perm D) := MulAction.orbitRel.Quotient (Subgroup.zpowers π) D

/-- [definition] The orbit of a dart. -/
def cellOf (π : Equiv.Perm D) (d : D) : Cells π := Quotient.mk (MulAction.orbitRel (Subgroup.zpowers π) D) d

/-- [definition] The count of cells `V`, contacts `E` and faces `F`. -/
noncomputable def cellCount : ℕ := Nat.card (Cells M.σ)
/-- The count of contacts. -/
noncomputable def edgeCount : ℕ := Nat.card (Cells M.α)
/-- The count of faces. -/
noncomputable def faceCount : ℕ := Nat.card (Cells M.φ)

/-- [proved-derived; formal-checked] `V* = F`. -/
theorem cellCount_dual : M.dual.cellCount = M.faceCount := rfl

/-- [proved-derived; formal-checked] `E* = E`. -/
theorem edgeCount_dual : M.dual.edgeCount = M.edgeCount := rfl

/-- [proved-derived; formal-checked] `F* = V`. -/
theorem faceCount_dual : M.dual.faceCount = M.cellCount := by
  simp only [faceCount, cellCount, dual_φ]

/-- [proved-derived; formal-checked] Euler's characteristic `V − E + F` is the same in both frames. -/
theorem euler_dual :
    (M.dual.cellCount : ℤ) - M.dual.edgeCount + M.dual.faceCount =
      (M.cellCount : ℤ) - M.edgeCount + M.faceCount := by
  rw [cellCount_dual, edgeCount_dual, faceCount_dual]
  ring

/-! ## The darts are the frame graph's darts -/

/-- A dart and its reverse lie in one contact. -/
theorem cellOf_α (d : D) : cellOf M.α (M.α d) = cellOf M.α d := by
  apply Quotient.sound
  exact ⟨⟨M.α, Subgroup.mem_zpowers _⟩, rfl⟩

/-- Every power of `α` sends a dart to itself or its reverse. -/
theorem zpow_apply (d : D) (k : ℤ) : (M.α ^ k) d = d ∨ (M.α ^ k) d = M.α d := by
  have hstep : ∀ x : D, x = d ∨ x = M.α d → M.α x = d ∨ M.α x = M.α d := by
    rintro x (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (M.α_α _)
  have hinv : (M.α)⁻¹ = M.α := inv_eq_of_mul_eq_one_right M.α_mul_α
  induction k using Int.induction_on with
  | zero => exact Or.inl (by simp)
  | succ n ih =>
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    exact hstep _ ih
  | pred n ih =>
    rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, hinv, Equiv.Perm.mul_apply]
    exact hstep _ ih

/-- The orbit of a dart under `α` is the dart and its reverse. -/
theorem eq_or_eq_α_of_cellOf {d d' : D} (h : cellOf M.α d' = cellOf M.α d) : d' = d ∨ d' = M.α d := by
  obtain ⟨⟨g, hg⟩, hgd⟩ := Quotient.exact h
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hgd' : (M.α ^ k) d = d' := hgd
  rw [← hgd']
  exact M.zpow_apply d k

/-- [definition] The ends of a contact `e` in the frame of `π`: the cells of its two darts `e.out` and `α e.out`. -/
noncomputable def endA (π : Equiv.Perm D) (e : Cells M.α) : Cells π := cellOf π e.out

/-- The other end. -/
noncomputable def endB (π : Equiv.Perm D) (e : Cells M.α) : Cells π := cellOf π (M.α e.out)

/-- [definition] The frame graph's oriented contacts as darts: `inl e` is `e.out`, `inr e` is `α e.out`. -/
noncomputable def dartOf : Cells M.α ⊕ Cells M.α → D := Sum.elim (fun e => e.out) (fun e => M.α e.out)

theorem cellOf_out (e : Cells M.α) : cellOf M.α e.out = e := Quotient.out_eq e

/-- [proved-derived; formal-checked] **The frame graph's darts are the map's darts.** -/
theorem dartOf_bijective : Function.Bijective M.dartOf := by
  constructor
  · have hne : ∀ e e' : Cells M.α, e.out ≠ M.α e'.out := by
      intro e e' h
      have he : e = e' := by
        rw [← M.cellOf_out e, ← M.cellOf_out e', h, M.cellOf_α]
      subst he
      exact M.α_ne _ h.symm
    rintro (e | e) (e' | e') h <;> simp only [dartOf, Sum.elim_inl, Sum.elim_inr] at h
    · rw [← M.cellOf_out e, ← M.cellOf_out e', h]
    · exact absurd h (hne e e')
    · exact absurd h.symm (hne e' e)
    · rw [← M.cellOf_out e, ← M.cellOf_out e', M.α.injective h]
  · intro d
    rcases M.eq_or_eq_α_of_cellOf (M.cellOf_out (cellOf M.α d)) with h | h
    · exact ⟨Sum.inl (cellOf M.α d), h⟩
    · refine ⟨Sum.inr (cellOf M.α d), ?_⟩
      simp only [dartOf, Sum.elim_inr, h, M.α_α]

/-- [definition] The darts as the frame graph's oriented contacts. -/
noncomputable def dartEquiv : Cells M.α ⊕ Cells M.α ≃ D := Equiv.ofBijective _ M.dartOf_bijective

/-- [proved-derived; formal-checked] **There are `2E` darts.** -/
theorem card_darts [Finite D] : Nat.card D = 2 * M.edgeCount := by
  have : Finite (Cells M.α) := Quotient.finite _
  rw [← Nat.card_congr M.dartEquiv, Nat.card_sum, edgeCount, two_mul]

/-- [proved-derived; formal-checked] A dart leaves the cell it lies in. -/
theorem src_frame (π : Equiv.Perm D) (x : Cells M.α ⊕ Cells M.α) :
    src (M.endA π) (M.endB π) x = cellOf π (M.dartOf x) := by
  rcases x with e | e <;> rfl

/-- [proved-derived; formal-checked] A dart enters the cell its reverse lies in. -/
theorem tgt_frame (π : Equiv.Perm D) (x : Cells M.α ⊕ Cells M.α) :
    tgt (M.endA π) (M.endB π) x = cellOf π (M.α (M.dartOf x)) := by
  rcases x with e | e
  · rfl
  · simp only [tgt, Sum.elim_inr, endA, dartOf, M.α_α]

/-- [proved-derived; formal-checked] The frame graph's reversal is `α`. -/
theorem dartOf_swap (x : Cells M.α ⊕ Cells M.α) : M.dartOf x.swap = M.α (M.dartOf x) := by
  rcases x with e | e
  · rfl
  · simp only [Sum.swap_inr, dartOf, Sum.elim_inl, Sum.elim_inr, M.α_α]

/-! ## Ihara in two frames -/

/-- [proved-derived; formal-checked] **The face-dual frame is the dual map's source frame**: same contacts, the faces
as cells, each contact joining the faces of its two darts. -/
theorem face_frame_eq_dual_frame :
    M.dual.endA M.dual.σ = M.endA M.φ ∧ M.dual.endB M.dual.σ = M.endB M.φ := ⟨rfl, rfl⟩

noncomputable instance (π : Equiv.Perm D) [Finite D] : Fintype (Cells π) :=
  have : Finite (Cells π) := Quotient.finite _
  Fintype.ofFinite _

noncomputable instance (π : Equiv.Perm D) : DecidableEq (Cells π) := Classical.decEq _

/-- [proved-derived; formal-checked] **The Ihara identity in two frames.** For every `u` in every commutative ring, the
source frame (cells `V`) and the face-dual frame (cells `F`) each satisfy
`(1 − u²)^|cells| det(1 − uB) = det(1 − uA + u²(D − 1)) (1 − u²)^|E|`, over the same contacts. -/
theorem two_frames_ihara_bass [Finite D] (R : Type*) [CommRing R] (u : R) :
    ((1 - u ^ 2) ^ Fintype.card (Cells M.σ) * (1 - u • hashimoto R (M.endA M.σ) (M.endB M.σ)).det =
      (1 - u • adjacency R (M.endA M.σ) (M.endB M.σ) +
        u ^ 2 • (degree R (M.endA M.σ) (M.endB M.σ) - 1)).det * (1 - u ^ 2) ^ Fintype.card (Cells M.α)) ∧
    ((1 - u ^ 2) ^ Fintype.card (Cells M.φ) * (1 - u • hashimoto R (M.endA M.φ) (M.endB M.φ)).det =
      (1 - u • adjacency R (M.endA M.φ) (M.endB M.φ) +
        u ^ 2 • (degree R (M.endA M.φ) (M.endB M.φ) - 1)).det * (1 - u ^ 2) ^ Fintype.card (Cells M.α)) :=
  ⟨ihara_bass R (M.endA M.σ) (M.endB M.σ) u, ihara_bass R (M.endA M.φ) (M.endB M.φ) u⟩

/-- The cells' power in a frame is its cell count. -/
theorem card_cells_eq [Finite D] (π : Equiv.Perm D) : Fintype.card (Cells π) = Nat.card (Cells π) :=
  (Nat.card_eq_fintype_card).symm

/-! ## The cycle ranks pair -/

/-- [definition] A frame's cycle rank `E − V + 1`, its first Betti number when it is connected. -/
noncomputable def cycleRank : ℤ := (M.edgeCount : ℤ) - M.cellCount + 1

/-- [definition] A frame's Ihara exponent `E − V`, the power of `1 − u²` in the classical form. -/
noncomputable def iharaExponent : ℤ := (M.edgeCount : ℤ) - M.cellCount

/-- [proved-derived; formal-checked] The dual's cycle rank is `E − F + 1`. -/
theorem cycleRank_dual : M.dual.cycleRank = (M.edgeCount : ℤ) - M.faceCount + 1 := by
  rw [cycleRank, cellCount_dual, edgeCount_dual]

/-- [proved-derived; formal-checked] **The cycle ranks sum to the contact count** under Euler's relation. -/
theorem cycleRank_add_dual (h : (M.cellCount : ℤ) - M.edgeCount + M.faceCount = 2) :
    M.cycleRank + M.dual.cycleRank = M.edgeCount := by
  rw [cycleRank_dual, cycleRank]
  linear_combination -h

/-- [proved-derived; formal-checked] Under Euler's relation the source frame's cycle rank is `F − 1`. -/
theorem cycleRank_eq (h : (M.cellCount : ℤ) - M.edgeCount + M.faceCount = 2) :
    M.cycleRank = (M.faceCount : ℤ) - 1 := by
  rw [cycleRank]
  linear_combination -h

/-- [proved-derived; formal-checked] Under Euler's relation the dual frame's cycle rank is `V − 1`. -/
theorem dual_cycleRank_eq (h : (M.cellCount : ℤ) - M.edgeCount + M.faceCount = 2) :
    M.dual.cycleRank = (M.cellCount : ℤ) - 1 := by
  rw [cycleRank_dual]
  linear_combination -h

/-- [proved-derived; formal-checked] **The two frames' Ihara exponents differ by `F − V`.** -/
theorem iharaExponent_sub_dual :
    M.iharaExponent - M.dual.iharaExponent = (M.faceCount : ℤ) - M.cellCount := by
  rw [iharaExponent, iharaExponent, cellCount_dual, edgeCount_dual]
  ring

end CombMap

/-! ## The dual pairs with the diagram, not the source -/

/-- [proved-derived; formal-checked] **Splitting segments at crossings**: segments `s` carrying `k_s` crossings each
become `k_s + 1` diagram contacts; with every crossing on two segments, `Σ k_s = 2c`, the diagram has `E_s + 2c`. -/
theorem split_edges {ι : Type*} (S : Finset ι) (k : ι → ℕ) {c : ℕ} (hk : ∑ s ∈ S, k s = 2 * c) :
    ∑ s ∈ S, (k s + 1) = S.card + 2 * c := by
  rw [Finset.sum_add_distrib, hk, Finset.sum_const, smul_eq_mul, mul_one, add_comm]

/-- [proved-derived; formal-checked] **The diagram's cycle rank is the source's plus the crossings**: `V_s + c` cells
and `E_s + 2c` contacts. -/
theorem diagram_cycleRank (Vs Es c : ℕ) :
    ((Es + 2 * c : ℕ) : ℤ) - ((Vs + c : ℕ) : ℤ) + 1 = ((Es : ℤ) - Vs + 1) + c := by
  push_cast
  ring

/-- [proved-derived; formal-checked] **The face dual pairs with the diagram, not the source.** For a diagram of
`V_s + c` cells, `E_s + 2c` contacts and `F` faces with `V − E + F = 2`, the face dual's cycle rank `E − F + 1` and the
source's `E_s − V_s + 1` sum to the diagram's contact count exactly when no crossing split a segment (`c = 0`); the
diagram's own cycle rank always does. -/
theorem source_pairs_with_dual_iff (Vs Es c F : ℕ)
    (heuler : ((Vs + c : ℕ) : ℤ) - ((Es + 2 * c : ℕ) : ℤ) + F = 2) :
    (((Es + 2 * c : ℕ) : ℤ) - ((Vs + c : ℕ) : ℤ) + 1) + (((Es + 2 * c : ℕ) : ℤ) - F + 1) = ((Es + 2 * c : ℕ) : ℤ) ∧
    (((Es : ℤ) - Vs + 1) + (((Es + 2 * c : ℕ) : ℤ) - F + 1) = ((Es + 2 * c : ℕ) : ℤ) ↔ c = 0) := by
  push_cast at heuler ⊢
  constructor
  · linear_combination -heuler
  · constructor
    · intro h
      have : (c : ℤ) = 0 := by linear_combination -h - heuler
      exact_mod_cast this
    · rintro rfl
      push_cast at heuler ⊢
      linear_combination -heuler

end Holonics.Landmarks.IharaTwoFrames
