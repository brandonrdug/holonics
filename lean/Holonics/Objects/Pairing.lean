import Holonics.Geometry.ExteriorBoundary
import Holonics.Foundation.Holon
import Holonics.Transport.CellHolonomy
import Holonics.Transport.JunctionLaw
import Holonics.Transport.EditRigidity

/-!
# Object 1: the Holon and its coholon, and the one pairing between them

[definition] `docs/ELEMENTARY_OBJECTS.md` §1. A **Holon** is a continuing object on the complex:
here a `Foundation/Holon.lean::BoundaryHolon`, whose returned current has an additive boundary
realizing `target − source`. A **coholon** is its dual: an element of `Module.Dual R Chain`, a
potential or receiver, whose coboundary is `LinearMap.dualMap` of the boundary
(`Geometry/ExteriorBoundary.lean`). Their pairing is the **face**. No new complex, dual or
coboundary is founded here; every statement composes the named owners.

[proved-derived; formal-checked] What is proved.

1. **Face = potential drop.** `face_is_potential_drop`:
   `φ(∂(receive o)) = φ(target o) − φ(source o)`; with a linear boundary, `coboundary_face` is
   Stokes (`ExteriorBoundary.stokes_pairing`) composed with `BoundaryHolon.returnsBoundary`, and
   `coboundary_total_face` is its finite-population form through
   `BoundaryHolon.boundary_totalCurrent`: the interior ports cancel.
2. **Orientation lives only in the pairing.** A signed reorientation of cells acts on chains and,
   dually, on coholons. The face is unchanged when both sides are reoriented
   (`face_unchanged_by_joint_reorientation`, and `stokes_face_independent_of_orientation` for the
   reoriented boundary); reorienting only one side negates the reoriented cell's contribution
   (`one_side_reorientation_negates_the_cell`). Conversely, a sign assignment preserving every
   face is exactly a unit sign (`face_invariance_forces_unit_signs`), which is the hypothesis under
   which `JunctionLaw.walkHolonomy_telescopes` holds; so such a reorientation has trivial holonomy
   on every closed walk (`pairing_preserving_reorientation_has_trivial_closed_holonomy`). The
   obstruction is the product of a `±1` joint relation around a cycle: product `−1` admits no
   unit sign assignment (`no_orientation_of_reversing_cycle`), product `+1` admits one
   (`orientation_of_preserving_cycle`); 3-cycle and Möbius-seam witnesses in
   `three_cycle_orientation_witness`. (This replaces a use of the
   retired JunctionLaw reversing-loop statement (`Orientation.junction_statement_from_cycle`), whose hypothesis
   `s () * s () = −1` is unsatisfiable in `ℤ`, so it carries no content.)
3. **The class pairing descends.** `⟨ω + dη, z⟩ = ⟨ω, z⟩` for a cycle, `⟨ω, z + ∂c⟩ = ⟨ω, z⟩`
   for a cocycle (`pairing_add_coboundary`, `pairing_add_boundary`, over any `Module.Dual`), hence
   one bilinear pairing `classPairing` on cohomology × homology, stated over the submodule quotients
   in the cell-coordinate chart (the chart `HodgeReceiver.harmonicEquivCohomology` uses; Mathlib's
   instance path does not currently form a quotient of a submodule of a `Module.Dual`). On a `HodgeReceiver.WeightedComplex` a cycle reads a cocycle only through
   its unique harmonic (dormant) representative (`cycle_reads_the_harmonic_representative`).
4. **Kernel/cokernel is the two-term case.** A coholon annihilating `range T` is exactly a cocycle
   of the two-term complex (`annihilates_range_iff_cocycle`), and the Fredholm alternative
   `EditRigidity.mem_range_iff_annihilators_vanish` restated in coholons is
   `mem_range_iff_coholon_cocycles_vanish`.

Witnesses: a two-edge path Holon with an explicit potential (`pathHolon`); a two-cell signed
reorientation (`reorientation_witness`); a square with one filled triangle, one hollow triangle,
a cocycle that is not a coboundary and a cycle that is not a boundary, pairing to `1`
(`square_class_pairing_is_one`); a `2 × 1` matrix with an obstructed and a reached target.

[open] Not proved here: the smooth Stokes theorem on a manifold with boundary; the torsion part of
integral homology (the pairing is over a commutative ring and the witnesses over `ℚ`); the claim
that a coholon orients a Holon only over a relatively complete region (object 7), which is owed in
#62 and not asserted.
-/

noncomputable section

namespace Holonics.Objects.Pairing

open Holonics
open Holonics.Geometry.ExteriorBoundary
open Matrix

/-! ## 1. Coholon and face -/

/-- [definition] A **coholon** on a chain module: a potential/receiver, the dual of the Holon's
chain module. It is `Module.Dual`, not a new type. -/
abbrev Coholon (R Chain : Type*) [CommRing R] [AddCommGroup Chain] [Module R Chain] :=
  Module.Dual R Chain

section Face

variable {R C₀ C₁ : Type*} [CommRing R] [AddCommGroup C₀] [Module R C₀]
  [AddCommGroup C₁] [Module R C₁]

/-- [proved-derived; formal-checked] **The face is the potential drop.** A coholon read on the
boundary of a Holon's returned current is its outgoing value minus its incoming value. -/
theorem face_is_potential_drop {Cur : Type*} [AddCommMonoid Cur]
    (H : BoundaryHolon C₀ Cur) (φ : Coholon R C₀) (o : H.Occurrence) :
    φ (H.boundary (H.receive o)) = φ (H.target o) - φ (H.source o) := by
  rw [H.returnsBoundary, map_sub]

/-- [proved-derived; formal-checked] **Stokes for coholons.** When the Holon's boundary is a
linear map `∂`, the coboundary `dφ = ∂.dualMap φ` read on the returned current is the drop of `φ`
across the occurrence: `ExteriorBoundary.stokes_pairing` composed with `returnsBoundary`. -/
theorem coboundary_face (H : BoundaryHolon C₀ C₁) (bd : C₁ →ₗ[R] C₀)
    (hb : ∀ c, H.boundary c = bd c) (φ : Coholon R C₀) (o : H.Occurrence) :
    bd.dualMap φ (H.receive o) = φ (H.target o) - φ (H.source o) := by
  rw [stokes_pairing, ← hb, face_is_potential_drop]

/-- [proved-derived; formal-checked] **The global face of a finite occurrence population.** The
coboundary read on the total current is the drop between the total outgoing and total incoming
faces; every joined interior port cancels (`BoundaryHolon.boundary_totalCurrent`). -/
theorem coboundary_total_face (H : BoundaryHolon C₀ C₁) [Fintype H.Occurrence]
    (bd : C₁ →ₗ[R] C₀) (hb : ∀ c, H.boundary c = bd c) (φ : Coholon R C₀) :
    bd.dualMap φ H.totalCurrent = φ H.totalTarget - φ H.totalSource := by
  rw [stokes_pairing, ← hb, H.boundary_totalCurrent, map_sub]

/-- [proved-derived; formal-checked] An exact coholon is silent on a closed population: when the
total outgoing face equals the total incoming face, `⟨dφ, H⟩ = 0` for every potential `φ`. -/
theorem exact_coholon_silent_on_closed (H : BoundaryHolon C₀ C₁) [Fintype H.Occurrence]
    (bd : C₁ →ₗ[R] C₀) (hb : ∀ c, H.boundary c = bd c)
    (closed : H.totalTarget = H.totalSource) (φ : Coholon R C₀) :
    bd.dualMap φ H.totalCurrent = 0 := by
  rw [coboundary_total_face H bd hb, closed, sub_self]

end Face

/-! ### Witness: a two-edge path `0 → 1 → 2` -/

/-- [definition] The node × edge incidence of the path `0 → 1 → 2`: edge `e` leaves node `e` and
enters node `e + 1`. -/
def pathIncidence : Matrix (Fin 3) (Fin 2) ℚ := !![-1, 0; 1, -1; 0, 1]

/-- [definition] The path as a `BoundaryHolon`: one occurrence per edge, carrying one unit of
current on it; the boundary is the incidence. -/
def pathHolon : BoundaryHolon (Fin 3 → ℚ) (Fin 2 → ℚ) where
  Occurrence := Fin 2
  source o := Pi.single (Fin.castSucc o) 1
  target o := Pi.single o.succ 1
  receive o := Pi.single o 1
  boundary := (Matrix.mulVecLin pathIncidence).toAddMonoidHom
  returnsBoundary := by
    intro o
    funext i
    fin_cases o <;> fin_cases i <;>
      simp [pathIncidence, Matrix.mulVec, dotProduct, Pi.single_apply]

instance : Fintype pathHolon.Occurrence := inferInstanceAs (Fintype (Fin 2))

/-- [definition] A concrete potential `φ = (0, 2, 5)` as a coholon. -/
def pathPotential : Coholon ℚ (Fin 3 → ℚ) :=
  (2 : ℚ) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) 1 +
    (5 : ℚ) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) 2

theorem pathPotential_apply (x : Fin 3 → ℚ) : pathPotential x = 2 * x 1 + 5 * x 2 := by
  simp [pathPotential]

/-- [proved-derived; formal-checked] **Witness.** On the path, the coboundary of `φ = (0,2,5)`
reads `3` on the second edge (its drop), and `5 = φ(2) − φ(0)` on the whole population: the
interior node `1` cancels. -/
theorem path_faces :
    (Matrix.mulVecLin pathIncidence).dualMap pathPotential
        (pathHolon.receive (show pathHolon.Occurrence from (1 : Fin 2))) = 3 ∧
      (Matrix.mulVecLin pathIncidence).dualMap pathPotential pathHolon.totalCurrent = 5 := by
  have hb : ∀ c, pathHolon.boundary c = Matrix.mulVecLin pathIncidence c := fun _ => rfl
  refine ⟨?_, ?_⟩
  · rw [coboundary_face pathHolon _ hb]
    change pathPotential (Pi.single (2 : Fin 3) 1) - pathPotential (Pi.single (1 : Fin 3) 1) = 3
    rw [pathPotential_apply, pathPotential_apply]
    simp [Fin.ext_iff]
    norm_num
  · rw [coboundary_total_face pathHolon _ hb]
    change pathPotential (∑ o : Fin 2, Pi.single o.succ 1) -
      pathPotential (∑ o : Fin 2, Pi.single (Fin.castSucc o) 1) = 5
    simp only [Fin.sum_univ_two]
    rw [pathPotential_apply, pathPotential_apply]
    simp [Fin.ext_iff]

/-! ## 2. Orientation exists only in the pairing -/

section Orientation

variable {R : Type*} [CommRing R] {ι : Type*}

/-- [definition] A signed reorientation of cells acting on chains: cell `i` is multiplied by the
sign `s i`. -/
def reorient (s : ι → ℤ) : (ι → R) →ₗ[R] (ι → R) where
  toFun z i := (s i : R) * z i
  map_add' z w := by funext i; simp [mul_add]
  map_smul' c z := by funext i; simp; ring

@[simp] theorem reorient_apply (s : ι → ℤ) (z : ι → R) (i : ι) :
    reorient (R := R) s z i = (s i : R) * z i := rfl

/-- [definition] The same reorientation acting on coholons: the dual map, which negates the
coholon's coordinate at every reversed cell. -/
def reorientCoholon (s : ι → ℤ) (ω : Coholon R (ι → R)) : Coholon R (ι → R) :=
  (reorient s).dualMap ω

/-- [proved-derived; formal-checked] A unit sign assignment is an involution on chains. -/
theorem reorient_reorient (s : ι → ℤ) (unit : ∀ i, s i * s i = 1) (z : ι → R) :
    reorient s (reorient s z) = z := by
  funext i
  have h : ((s i : R) * (s i : R)) = 1 := by
    have := congrArg (Int.cast : ℤ → R) (unit i)
    push_cast at this
    exact this
  simp only [reorient_apply]
  rw [← mul_assoc, h, one_mul]

/-- [proved-derived; formal-checked] **Reorienting both sides leaves every face unchanged.** -/
theorem face_unchanged_by_joint_reorientation (s : ι → ℤ) (unit : ∀ i, s i * s i = 1)
    (ω : Coholon R (ι → R)) (z : ι → R) :
    reorientCoholon s ω (reorient s z) = ω z := by
  rw [reorientCoholon, LinearMap.dualMap_apply, reorient_reorient s unit]

/-- [proved-derived; formal-checked] **Stokes does not see the orientation.** Reorient the cells
of `C₁`, carry the chain along (`z ↦ s z`) and replace the boundary by `∂ ∘ s`; the coboundary of
any potential read on the reoriented chain is the original face. -/
theorem stokes_face_independent_of_orientation {C₀ : Type*} [AddCommGroup C₀] [Module R C₀]
    (s : ι → ℤ) (unit : ∀ i, s i * s i = 1) (bd : (ι → R) →ₗ[R] C₀) (φ : Coholon R C₀)
    (z : ι → R) :
    (bd.comp (reorient s)).dualMap φ (reorient s z) = bd.dualMap φ z := by
  rw [stokes_pairing, stokes_pairing, LinearMap.comp_apply, reorient_reorient s unit]

variable [DecidableEq ι]

/-- [proved-derived; formal-checked] **Reorienting only one side negates the reversed cell.** -/
theorem one_side_reorientation_negates_the_cell (s : ι → ℤ) (c : ι) (hc : s c = -1)
    (ω : Coholon R (ι → R)) (r : R) :
    ω (reorient s (Pi.single c r)) = -ω (Pi.single c r) ∧
      reorientCoholon s ω (Pi.single c r) = -ω (Pi.single c r) := by
  have hz : reorient (R := R) s (Pi.single c r) = -(Pi.single c r) := by
    funext i
    by_cases hi : i = c
    · subst hi; simp [hc]
    · simp [hi]
  refine ⟨?_, ?_⟩
  · rw [hz, map_neg]
  · rw [reorientCoholon, LinearMap.dualMap_apply, hz, map_neg]

/-- [proved-derived; formal-checked] **Only unit signs preserve every face.** If a sign assignment
preserves the pairing of every coholon with every chain, each sign squares to one. -/
theorem face_invariance_forces_unit_signs [CharZero R] (s : ι → ℤ)
    (preserves : ∀ (ω : Coholon R (ι → R)) (z : ι → R),
      reorientCoholon s ω (reorient s z) = ω z) :
    ∀ i, s i * s i = 1 := by
  intro i
  have h := preserves (LinearMap.proj i) (Pi.single i 1)
  simp [reorientCoholon, LinearMap.dualMap_apply] at h
  exact_mod_cast h

/-- [proved-derived; formal-checked] **A pairing-preserving reorientation has trivial holonomy on
every closed dual walk.** This is `JunctionLaw.closed_walk_holonomy_one`, whose unit hypothesis is
supplied by `face_invariance_forces_unit_signs`. -/
theorem pairing_preserving_reorientation_has_trivial_closed_holonomy [CharZero R]
    (s : ι → ℤ)
    (preserves : ∀ (ω : Coholon R (ι → R)) (z : ι → R),
      reorientCoholon s ω (reorient s z) = ω z)
    (first : ι) (rest : List ι)
    (closed : (first :: rest).getLast (List.cons_ne_nil first rest) = first) :
    Transport.JunctionLaw.walkHolonomy s (first :: rest) = 1 :=
  Transport.JunctionLaw.closed_walk_holonomy_one s
    (face_invariance_forces_unit_signs s preserves) first rest closed

end Orientation

/-! ### The orientation obstruction is the product of a sign relation around a cycle

The cells `0, 1, …, k` of a closed walk are joined consecutively, the last back to the first
(`i ↦ i + 1` in `Fin (k+1)`). Each joint requires a relation `r i ∈ {±1}` between the unit signs
of the two cells it joins: `s i · s (i+1) = r i`. The product of `r` around the walk is the
obstruction: `−1` admits no sign assignment, `+1` admits one. For `k = 0` this is a single cell
glued to itself with `r = −1`, the Möbius seam, and the hypothesis `∏ r = −1` is satisfiable. -/

/-- [proved-derived; formal-checked] **A reversing cycle admits no orientation.** If the relation
multiplies to `−1` around the cycle, no unit sign assignment satisfies it on every joint: the
product of `s i · s (i+1)` over the cycle is `∏ s i² = 1`, because the shift `i ↦ i + 1`
permutes the cells. -/
theorem no_orientation_of_reversing_cycle {k : ℕ} (r : Fin (k + 1) → ℤ)
    (reversing : ∏ i, r i = -1) :
    ¬ ∃ s : Fin (k + 1) → ℤ, (∀ i, s i * s i = 1) ∧ ∀ i, s i * s (i + 1) = r i := by
  rintro ⟨s, unit, rel⟩
  have hshift : ∏ i, s (i + 1) = ∏ i, s i :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  have hone : ∏ i, r i = 1 := by
    calc ∏ i, r i = ∏ i, (s i * s (i + 1)) := Finset.prod_congr rfl fun i _ => (rel i).symm
      _ = (∏ i, s i) * ∏ i, s (i + 1) := Finset.prod_mul_distrib
      _ = ∏ i, (s i * s i) := by rw [hshift, Finset.prod_mul_distrib]
      _ = 1 := Finset.prod_eq_one fun i _ => unit i
  rw [hone] at reversing
  exact absurd reversing (by decide)

/-- [definition] The relation on a cycle extended by `1` past its last joint. -/
def cycleRelation {k : ℕ} (r : Fin (k + 1) → ℤ) (j : ℕ) : ℤ :=
  if h : j < k + 1 then r ⟨j, h⟩ else 1

/-- [definition] The sign transported from cell `0` along the first `m` joints. -/
def cycleSign {k : ℕ} (r : Fin (k + 1) → ℤ) (m : ℕ) : ℤ :=
  ∏ j ∈ Finset.range m, cycleRelation r j

theorem cycleSign_succ {k : ℕ} (r : Fin (k + 1) → ℤ) (m : ℕ) :
    cycleSign r (m + 1) = cycleSign r m * cycleRelation r m :=
  Finset.prod_range_succ _ _

theorem cycleSign_zero {k : ℕ} (r : Fin (k + 1) → ℤ) : cycleSign r 0 = 1 :=
  Finset.prod_range_zero _

/-- [proved-derived; formal-checked] **A preserving cycle admits an orientation.** If every joint
relation is a unit sign and the product around the cycle is `+1`, transporting the sign of cell
`0` along the joints closes consistently. -/
theorem orientation_of_preserving_cycle {k : ℕ} (r : Fin (k + 1) → ℤ)
    (unitR : ∀ i, r i * r i = 1) (preserving : ∏ i, r i = 1) :
    ∃ s : Fin (k + 1) → ℤ, (∀ i, s i * s i = 1) ∧ ∀ i, s i * s (i + 1) = r i := by
  have unitN : ∀ j, cycleRelation r j * cycleRelation r j = 1 := by
    intro j
    by_cases h : j < k + 1 <;> simp [cycleRelation, h, unitR]
  have unitP : ∀ m, cycleSign r m * cycleSign r m = 1 := by
    intro m
    rw [cycleSign, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => unitN j
  have hrel : ∀ i : Fin (k + 1), cycleRelation r i.val = r i := by
    intro i
    simp [cycleRelation, i.isLt]
  have total : cycleSign r (k + 1) = 1 := by
    rw [cycleSign, Finset.prod_range, ← preserving]
    exact Finset.prod_congr rfl fun i _ => hrel i
  refine ⟨fun i => cycleSign r i.val, fun i => unitP _, ?_⟩
  intro i
  by_cases hi : i.val < k
  · have hlt : i < Fin.last k := by rw [Fin.lt_def, Fin.val_last]; exact hi
    have hv : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt hlt
    change cycleSign r i.val * cycleSign r (i + 1).val = r i
    rw [hv, cycleSign_succ, ← mul_assoc, unitP, one_mul, hrel]
  · have hlast : i = Fin.last k := Fin.ext (by have := i.isLt; simp; omega)
    subst hlast
    change cycleSign r k * cycleSign r (Fin.last k + 1).val = r (Fin.last k)
    rw [Fin.last_add_one, Fin.val_zero, cycleSign_zero, mul_one]
    have hk : cycleSign r k * r (Fin.last k) = 1 := by
      rw [← total, cycleSign_succ, ← hrel (Fin.last k), Fin.val_last]
    have hr := unitR (Fin.last k)
    calc cycleSign r k = cycleSign r k * (r (Fin.last k) * r (Fin.last k)) := by
          rw [hr, mul_one]
      _ = (cycleSign r k * r (Fin.last k)) * r (Fin.last k) := by ring
      _ = r (Fin.last k) := by rw [hk, one_mul]

/-- [proved-derived; formal-checked] **Witness on a 3-cycle.** The relation `(1, 1, −1)` multiplies
to `−1` and admits no orientation; `(−1, −1, 1)` multiplies to `+1` and is oriented by
`s = (1, −1, 1)`. The Möbius seam `k = 0`, `r = (−1)` also admits none. -/
theorem three_cycle_orientation_witness :
    (¬ ∃ s : Fin 3 → ℤ, (∀ i, s i * s i = 1) ∧ ∀ i, s i * s (i + 1) = ![1, 1, -1] i) ∧
      ((∀ i, (![1, -1, 1] : Fin 3 → ℤ) i * ![1, -1, 1] i = 1) ∧
        ∀ i : Fin 3, (![1, -1, 1] : Fin 3 → ℤ) i * ![1, -1, 1] (i + 1) = ![-1, -1, 1] i) ∧
      (¬ ∃ s : Fin 1 → ℤ, (∀ i, s i * s i = 1) ∧ ∀ i, s i * s (i + 1) = ![-1] i) := by
  refine ⟨no_orientation_of_reversing_cycle _ (by simp [Fin.prod_univ_three]), ⟨by decide, by decide⟩,
    no_orientation_of_reversing_cycle _ (by simp)⟩

/-- [definition] A witness coholon on two cells: `ω(z) = z₀ + 3 z₁`. -/
def twoCellCoholon : Coholon ℚ (Fin 2 → ℚ) :=
  LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 0 +
    (3 : ℚ) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 1

/-- [proved-derived; formal-checked] **Witness.** Reverse cell `1` (`s = (1, −1)`) and read
`z = (2, 5)`. Reorienting both sides returns `17` again; reorienting only the chain returns `−13`,
so the orientation is visible only when the two sides disagree. -/
theorem reorientation_witness :
    reorientCoholon ![1, -1] twoCellCoholon (reorient ![1, -1] ![2, 5]) = 17 ∧
      twoCellCoholon ![2, 5] = 17 ∧
      twoCellCoholon (reorient ![1, -1] ![(2 : ℚ), 5]) = -13 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [reorientCoholon, twoCellCoholon, LinearMap.dualMap_apply] <;> norm_num

/-! ## 3. The class pairing descends to homology × cohomology -/

section Classes

variable {R C₀ C₁ C₂ : Type*} [CommRing R] [AddCommGroup C₀] [Module R C₀]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]

/-- [proved-derived; formal-checked] **A coboundary is invisible to a cycle.**
`⟨ω + dη, z⟩ = ⟨ω, z⟩` whenever `∂z = 0` (Stokes). -/
theorem pairing_add_coboundary (bd₁ : C₁ →ₗ[R] C₀) (ω : Coholon R C₁) (η : Coholon R C₀)
    {z : C₁} (hz : bd₁ z = 0) : (ω + bd₁.dualMap η) z = ω z := by
  rw [LinearMap.add_apply, stokes_pairing, hz, map_zero, add_zero]

/-- [proved-derived; formal-checked] **A boundary is invisible to a cocycle.**
`⟨ω, z + ∂c⟩ = ⟨ω, z⟩` whenever `dω = 0`. -/
theorem pairing_add_boundary (bd₂ : C₂ →ₗ[R] C₁) {ω : Coholon R C₁}
    (hω : bd₂.dualMap ω = 0) (z : C₁) (c : C₂) : ω (z + bd₂ c) = ω z := by
  have h : ω (bd₂ c) = 0 := by rw [← stokes_pairing, hω, LinearMap.zero_apply]
  rw [map_add, h, add_zero]

/-- [proved-derived; formal-checked] **A cocycle that pairs nonzero with some cycle is not a
coboundary, and that cycle is not a boundary.** -/
theorem nonzero_pairing_certifies (bd₁ : C₁ →ₗ[R] C₀) (bd₂ : C₂ →ₗ[R] C₁)
    {ω : Coholon R C₁} (hω : bd₂.dualMap ω = 0) {z : C₁} (hz : bd₁ z = 0) (h : ω z ≠ 0) :
    ω ∉ LinearMap.range bd₁.dualMap ∧ z ∉ LinearMap.range bd₂ := by
  constructor
  · rintro ⟨η, hη⟩
    apply h
    have := pairing_add_coboundary bd₁ 0 η hz
    rw [zero_add, LinearMap.zero_apply] at this
    rw [← hη, this]
  · rintro ⟨c, hc⟩
    apply h
    have := pairing_add_boundary bd₂ hω 0 c
    rw [zero_add, map_zero] at this
    rw [← hc, this]

end Classes

/-! ### The class pairing on quotients, in the cell-coordinate chart

A coholon on a finite cell population is read through its coordinate vector
(`EditRigidity.dual_is_dotProduct`), and the coboundary is the transpose of the boundary matrix.
The quotients are taken there, as `HodgeReceiver.harmonicEquivCohomology` takes them. -/

section ClassQuotient

variable {R : Type*} [CommRing R] {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
variable (B₁ : Matrix V E R) (B₂ : Matrix E F R)

/-- [proved-derived; formal-checked] Stokes in the coordinate chart: `⟨Bᵀη, z⟩ = ⟨η, Bz⟩`. -/
theorem coordinate_stokes {X Y : Type*} [Fintype X] [Fintype Y] (B : Matrix X Y R)
    (η : X → R) (z : Y → R) : (Bᵀ *ᵥ η) ⬝ᵥ z = η ⬝ᵥ (B *ᵥ z) := by
  rw [mulVec_transpose, ← dotProduct_mulVec]

/-- [definition] The cycles `ker ∂₁`. -/
abbrev cycles : Submodule R (E → R) := LinearMap.ker (Matrix.mulVecLin B₁)

/-- [definition] The boundaries `im ∂₂` inside the cycles. -/
abbrev boundariesIn : Submodule R (cycles B₁) :=
  (LinearMap.range (Matrix.mulVecLin B₂)).comap (cycles B₁).subtype

/-- [definition] The cocycles `ker d₁ = ker ∂₂ᵀ`. -/
abbrev cocycles : Submodule R (E → R) := LinearMap.ker (Matrix.mulVecLin B₂ᵀ)

/-- [definition] The coboundaries `im d₀ = im ∂₁ᵀ` inside the cocycles. -/
abbrev coboundariesIn : Submodule R (cocycles B₂) :=
  (LinearMap.range (Matrix.mulVecLin B₁ᵀ)).comap (cocycles B₂).subtype

/-- [definition] Homology `ker ∂₁ / im ∂₂`. -/
abbrev Homology := cycles B₁ ⧸ boundariesIn B₁ B₂

/-- [definition] Cohomology `ker d₁ / im d₀`. -/
abbrev Cohomology := cocycles B₂ ⧸ coboundariesIn B₁ B₂

/-- [definition] The cycle/cocycle pairing, with the cycle first. -/
def cyclePairing : cycles B₁ →ₗ[R] cocycles B₂ →ₗ[R] R :=
  LinearMap.mk₂ R (fun z ω => (ω : E → R) ⬝ᵥ (z : E → R))
    (fun z z' ω => by simp [dotProduct_add])
    (fun c z ω => by simp [dotProduct_smul])
    (fun z ω ω' => by simp [add_dotProduct])
    (fun c z ω => by simp [smul_dotProduct])

/-- The pairing descended over boundaries (uses only that `ω` is a cocycle). -/
def homologyPairing : Homology B₁ B₂ →ₗ[R] cocycles B₂ →ₗ[R] R :=
  (boundariesIn B₁ B₂).liftQ (cyclePairing B₁ B₂) (by
    rintro ⟨z, hz⟩ ⟨c, hc⟩
    rw [LinearMap.mem_ker]
    ext ⟨ω, hω⟩
    change ω ⬝ᵥ z = 0
    have hω' : B₂ᵀ *ᵥ ω = 0 := hω
    have hc' : B₂ *ᵥ c = z := hc
    rw [← hc', dotProduct_mulVec, ← mulVec_transpose, hω', zero_dotProduct])

/-- [definition] **The class pairing** `H¹ × H₁ → R`, descended in both arguments. -/
def classPairing : Cohomology B₁ B₂ →ₗ[R] Homology B₁ B₂ →ₗ[R] R :=
  (coboundariesIn B₁ B₂).liftQ (homologyPairing B₁ B₂).flip (by
    rintro ⟨ω, hω⟩ ⟨η, hη⟩
    rw [LinearMap.mem_ker]
    apply Submodule.linearMap_qext
    ext ⟨z, hz⟩
    change ω ⬝ᵥ z = 0
    have hz' : B₁ *ᵥ z = 0 := hz
    have hη' : B₁ᵀ *ᵥ η = ω := hη
    rw [← hη', coordinate_stokes, hz', dotProduct_zero])

/-- [proved-derived; formal-checked] **The class pairing reads any representatives.** -/
theorem classPairing_mk (ω : cocycles B₂) (z : cycles B₁) :
    classPairing B₁ B₂ (Submodule.Quotient.mk ω) (Submodule.Quotient.mk z) =
      (ω : E → R) ⬝ᵥ (z : E → R) := rfl

/-- [proved-derived; formal-checked] **Representatives may be moved by a coboundary and a
boundary.** `⟨ω + ∂₁ᵀη, z + ∂₂c⟩ = ⟨ω, z⟩` for a cocycle `ω` and a cycle `z` when `∂₁∂₂ = 0`. -/
theorem classPairing_representatives (hB : B₁ * B₂ = 0) (ω z : E → R) (hω : B₂ᵀ *ᵥ ω = 0) (hz : B₁ *ᵥ z = 0)
    (η : V → R) (c : F → R) :
    (ω + B₁ᵀ *ᵥ η) ⬝ᵥ (z + B₂ *ᵥ c) = ω ⬝ᵥ z := by
  have h1 : (B₁ᵀ *ᵥ η) ⬝ᵥ z = 0 := by rw [coordinate_stokes, hz, dotProduct_zero]
  have h2 : ω ⬝ᵥ (B₂ *ᵥ c) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hω, zero_dotProduct]
  have h3 : (B₁ᵀ *ᵥ η) ⬝ᵥ (B₂ *ᵥ c) = 0 := by
    rw [coordinate_stokes, mulVec_mulVec, hB, zero_mulVec, dotProduct_zero]
  rw [add_dotProduct, dotProduct_add, dotProduct_add, h1, h2, h3]
  ring

end ClassQuotient

/-! ### Witness: a square with one filled and one hollow triangle

Nodes `0,1,2,3`; edges `e₀: 0→1`, `e₁: 1→2`, `e₂: 2→3`, `e₃: 3→0`, `e₄: 0→2`; one filled face
`f = e₀ + e₁ − e₄`. The triangle `0,2,3` is hollow. -/

/-- [definition] Node × edge incidence. -/
def squareBd₁ : Matrix (Fin 4) (Fin 5) ℚ :=
  !![-1, 0, 0, 1, -1;
      1, -1, 0, 0, 0;
      0, 1, -1, 0, 1;
      0, 0, 1, -1, 0]

/-- [definition] Edge × face incidence of the one filled triangle. -/
def squareBd₂ : Matrix (Fin 5) (Fin 1) ℚ := !![1; 1; 0; 0; -1]

/-- [definition] The coholon reading edge `e₃`, in coordinates. -/
def squareCocycle : Fin 5 → ℚ := ![0, 0, 0, 1, 0]

/-- [definition] The hollow cycle `e₂ + e₃ + e₄`. -/
def squareCycle : Fin 5 → ℚ := ![0, 0, 1, 1, 1]

theorem square_boundary_squared : squareBd₁ * squareBd₂ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [squareBd₁, squareBd₂, Matrix.mul_apply, Fin.sum_univ_five]

theorem squareCocycle_mem : squareCocycle ∈ cocycles squareBd₂ := by
  rw [LinearMap.mem_ker]
  funext i
  fin_cases i
  simp [squareCocycle, squareBd₂]

theorem squareCycle_mem : squareCycle ∈ cycles squareBd₁ := by
  rw [LinearMap.mem_ker]
  funext i
  fin_cases i <;> simp [squareBd₁, squareCycle, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

/-- [proved-derived; formal-checked] **Witness.** `∂₁∂₂ = 0` on the square; the class pairing of
`[e₃*]` with the hollow cycle is `1`, so (by `nonzero_pairing_certifies`, read through the
coordinate coholon) the cocycle is not a coboundary and the hollow cycle is not a boundary, while
the filled triangle's boundary pairs to `0`. -/
theorem square_class_pairing_is_one :
    classPairing squareBd₁ squareBd₂
        (Submodule.Quotient.mk ⟨squareCocycle, squareCocycle_mem⟩)
        (Submodule.Quotient.mk ⟨squareCycle, squareCycle_mem⟩) = 1 ∧
      (¬ ∃ η, squareBd₁ᵀ *ᵥ η = squareCocycle) ∧
      (¬ ∃ c, squareBd₂ *ᵥ c = squareCycle) ∧
      squareCocycle ⬝ᵥ (squareBd₂ *ᵥ ![1]) = 0 := by
  have hpair : squareCocycle ⬝ᵥ squareCycle = 1 := by
    simp [squareCocycle, squareCycle, dotProduct, Fin.sum_univ_five]
  have hω : squareBd₂ᵀ *ᵥ squareCocycle = 0 := squareCocycle_mem
  have hz : squareBd₁ *ᵥ squareCycle = 0 := squareCycle_mem
  refine ⟨by rw [classPairing_mk]; exact hpair, ?_, ?_, ?_⟩
  · rintro ⟨η, hη⟩
    have := classPairing_representatives squareBd₁ squareBd₂ square_boundary_squared
      0 squareCycle (mulVec_zero _) hz η 0
    rw [zero_add, hη, mulVec_zero, add_zero, zero_dotProduct, hpair] at this
    exact one_ne_zero this
  · rintro ⟨c, hc⟩
    have := classPairing_representatives squareBd₁ squareBd₂ square_boundary_squared
      squareCocycle 0 hω (mulVec_zero _) 0 c
    rw [zero_add, hc, mulVec_zero, add_zero, dotProduct_zero, hpair] at this
    exact one_ne_zero this
  · simp [squareCocycle, squareBd₂, Matrix.mulVec, dotProduct, Fin.sum_univ_five]


/-! ### The cycle reads the dormant harmonic representative -/

section Hodge

open Holonics.Foundation.HodgeReceiver

variable {p q r : ℕ} (C : WeightedComplex p q r)

/-- [proved-derived; formal-checked] **A cycle reads a cocycle's class only through its harmonic
representative.** For a chain `z` with `∂z = d₀ᵀ z = 0` and a cocycle `ω`, there is exactly one
harmonic `h` with `ω − h` exact (`CellHolonomy.closed_field_retains_unique_harmonic_mode`), and
`⟨ω, z⟩ = ⟨h, z⟩`: the exact part is invisible to the cycle (Stokes). -/
theorem cycle_reads_the_harmonic_representative {ω : Fin q → ℚ} (hω : ω ∈ C.cocycles)
    {z : Fin q → ℚ} (hz : C.d₀ᵀ *ᵥ z = 0) :
    ∃! h, (h ∈ C.harmonic ∧ ω - h ∈ C.exactPart) ∧ ω ⬝ᵥ z = h ⬝ᵥ z := by
  obtain ⟨h, ⟨hh, hd⟩, huniq⟩ :=
    Transport.CellHolonomy.closed_field_retains_unique_harmonic_mode C hω
  refine ⟨h, ⟨⟨hh, hd⟩, ?_⟩, fun h' hh' => huniq h' hh'.1⟩
  obtain ⟨a, ha⟩ := (C.mem_exactPart_iff _).mp hd
  have hzero : (ω - h) ⬝ᵥ z = 0 := by
    rw [← ha, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hz, zero_dotProduct]
  rw [sub_dotProduct, sub_eq_zero] at hzero
  exact hzero

end Hodge

/-! ## 4. Kernel and cokernel: the two-term complex -/

section TwoTerm

variable {R C₀ C₁ : Type*} [CommRing R] [AddCommGroup C₀] [Module R C₀]
  [AddCommGroup C₁] [Module R C₁]

/-- [proved-derived; formal-checked] **A coholon annihilating `range T` is exactly a cocycle of the
two-term complex `C₁ →T C₀`**, i.e. `dω = T* ω = 0`; equivalently a member of Mathlib's
`dualAnnihilator` of the range. -/
theorem annihilates_range_iff_cocycle (T : C₁ →ₗ[R] C₀) (ω : Coholon R C₀) :
    (∀ y ∈ LinearMap.range T, ω y = 0) ↔ T.dualMap ω = 0 := by
  constructor
  · intro h
    ext x
    rw [stokes_pairing, LinearMap.zero_apply]
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    rw [← stokes_pairing, h, LinearMap.zero_apply]

theorem annihilates_range_iff_mem_dualAnnihilator (T : C₁ →ₗ[R] C₀) (ω : Coholon R C₀) :
    ω ∈ (LinearMap.range T).dualAnnihilator ↔ T.dualMap ω = 0 := by
  rw [Submodule.mem_dualAnnihilator, ← annihilates_range_iff_cocycle]

end TwoTerm

/-- [proved-derived; formal-checked] **The Fredholm alternative in coholons.** A target is reached
by an exact rational map exactly when every cocycle of the two-term complex vanishes on it. This is
`EditRigidity.mem_range_iff_annihilators_vanish`, whose left-null vectors are the coordinate
charts of these coholons (`EditRigidity.dual_is_dotProduct`). -/
theorem mem_range_iff_coholon_cocycles_vanish {μ ι : Type*} [Fintype μ] [DecidableEq μ]
    [Fintype ι] [DecidableEq ι] (M : Matrix μ ι ℚ) (y : μ → ℚ) :
    (∃ x, M *ᵥ x = y) ↔
      ∀ ω : Coholon ℚ (μ → ℚ), (Matrix.mulVecLin M).dualMap ω = 0 → ω y = 0 := by
  rw [Transport.EditRigidity.mem_range_iff_annihilators_vanish]
  constructor
  · intro h ω hω
    rw [Transport.EditRigidity.dual_is_dotProduct ω y, dotProduct_comm]
    apply h
    funext j
    have hj := LinearMap.congr_fun hω (Pi.single j 1)
    rw [stokes_pairing, LinearMap.zero_apply, Transport.EditRigidity.dual_is_dotProduct,
      Matrix.mulVecLin_apply, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose] at hj
    simpa [dotProduct_single] using hj
  · intro h w hw
    let ω : Coholon ℚ (μ → ℚ) := (Matrix.mulVecLin (Matrix.of fun (_ : Unit) i => w i)) |>
      fun L => (LinearMap.proj ()).comp L
    have hωapply : ∀ u, ω u = w ⬝ᵥ u := fun u => by simp [ω, Matrix.mulVec, dotProduct]
    have hcocycle : (Matrix.mulVecLin M).dualMap ω = 0 := by
      apply LinearMap.ext
      intro x
      rw [stokes_pairing, LinearMap.zero_apply, hωapply, Matrix.mulVecLin_apply,
        dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]
    have := h ω hcocycle
    rwa [hωapply] at this

/-- [definition] A `2 × 1` map `x ↦ (x, x)`. -/
def diagonalMap : Matrix (Fin 2) (Fin 1) ℚ := !![1; 1]

/-- [proved-derived; formal-checked] **Witness.** `(1, −1)` is not reached: the cocycle
`ω(u) = u₀ − u₁` vanishes on the range and reads `2` on it. `(2, 2)` is reached. -/
theorem diagonalMap_obstruction_and_reach :
    ¬ (∃ x, diagonalMap *ᵥ x = ![1, -1]) ∧ (∃ x, diagonalMap *ᵥ x = ![2, 2]) := by
  refine ⟨?_, ⟨![2], ?_⟩⟩
  · rw [mem_range_iff_coholon_cocycles_vanish]
    intro h
    let ω : Coholon ℚ (Fin 2 → ℚ) := LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 0 -
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 1
    have hω : (Matrix.mulVecLin diagonalMap).dualMap ω = 0 := by
      ext x
      simp [ω, diagonalMap]
    have := h ω hω
    norm_num [ω] at this
  · funext i
    fin_cases i <;> simp [diagonalMap, Matrix.mulVec, dotProduct]

end Holonics.Objects.Pairing

section Audit
open Holonics.Objects.Pairing
#print axioms face_is_potential_drop
#print axioms coboundary_face
#print axioms coboundary_total_face
#print axioms exact_coholon_silent_on_closed
#print axioms path_faces
#print axioms face_unchanged_by_joint_reorientation
#print axioms stokes_face_independent_of_orientation
#print axioms one_side_reorientation_negates_the_cell
#print axioms face_invariance_forces_unit_signs
#print axioms pairing_preserving_reorientation_has_trivial_closed_holonomy
#print axioms no_orientation_of_reversing_cycle
#print axioms orientation_of_preserving_cycle
#print axioms three_cycle_orientation_witness
#print axioms reorientation_witness
#print axioms pairing_add_coboundary
#print axioms pairing_add_boundary
#print axioms classPairing_mk
#print axioms classPairing_representatives
#print axioms nonzero_pairing_certifies
#print axioms square_class_pairing_is_one
#print axioms cycle_reads_the_harmonic_representative
#print axioms annihilates_range_iff_cocycle
#print axioms mem_range_iff_coholon_cocycles_vanish
#print axioms diagonalMap_obstruction_and_reach
end Audit
