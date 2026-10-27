import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.AddCircle.Real
import HolonicsResearch.Geometry.TorusBraid

/-!
# A torus map has `|det(M − 1)|` fixed points: the determinant is the count

`Geometry/TorusBraid` proves `|det(A^(k+1) − 1)| = L_(2k+2) − 2` for the cat map `A = [[2,1],[1,1]]`
and owes to #410 the index law that turns the determinant into a count: an integer matrix `M`
acting on the torus `ℝⁿ/ℤⁿ` with `det(M − 1) ≠ 0` has exactly `|det(M − 1)|` fixed points (the
record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`,
§13(e)). This file proves it.

[proved-standard; formal-checked] What is proved.

1. **The torus map** (`act`, `act_proj`): an integer matrix `N` moves a point of the torus
   `UnitAddTorus n = n → ℝ/ℤ` by `x ↦ N x`, and on a real lift `v` it is the lift of `N v`.
2. **Its kernel is the lattice read back through `N`** (`lift`, `lift_eq_zero_iff`,
   `act_eq_zero_iff`): for `det N ≠ 0` the points with `N x = 0` are exactly the images of `N⁻¹ w`
   for `w ∈ ℤⁿ`, and `w` lands on `0` exactly when `w ∈ N ℤⁿ`. The map `w ↦ N⁻¹ w mod ℤⁿ` therefore
   identifies the kernel with `ℤⁿ / N ℤⁿ`.
3. **The index law** (`latticeMap`, `det_latticeMap`, `card_ker_act`): `#{x : N x = 0} = |det N|`,
   through Mathlib's `Submodule.natAbs_det_equiv` (the index of a full sublattice `N ℤⁿ` is the
   absolute determinant of `N` on the lattice).
4. **The fixed points** (`act_sub_one`, `card_fixed`): `#{x : M x = x} = |det(M − 1)|` whenever
   `det(M − 1) ≠ 0`.
5. **The three kinds on the two-torus** (`card_fixed_two`, `turn_fixed_point`,
   `quarter_turn_fixed_points`, `half_turn_fixed_points`, `cat_fixed_points`): for `det M = 1` and
   `tr M ≠ 2` the count is `|2 − tr M|`. The turns count by their trace: the order-six turn `T L`
   (trace 1) fixes one point, the quarter turn `T L T` (trace 0) two, the half turn `−1` (trace −2)
   the four half-periods. The boost `A^(k+1)`, the cat map's power, fixes `L_(2k+2) − 2` points,
   with `L_(2k+2) = F_(2k+1) + F_(2k+3)`: 1, 5, 16, 45, 121 for `k = 0, …, 4`. A shear (trace 2) has
   `det(M − 1) = 0` and falls outside the law: it fixes whole circles, and the identity fixes the
   whole torus.

The computational object is the helical pair interaction read on the torus: a move's fixed points
are the places where the body and its image coincide, and the lattice `ℤⁿ` is the winding the
pairing forgets. Of the winding guide's six general objects this touches the cell holonomy (the
lattice index is the count of closed returns); the helix, the pair, faces and placement, the tube
and the tower thread stay attached.

Consumers: the atlas row `motion.torus-twists-every-kind` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Geometry.TorusIndex

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. The torus map -/

/-- [definition] The torus map of an integer matrix, `(N x)_i = Σ_j N_ij x_j` on `ℝⁿ/ℤⁿ`. -/
def act (N : Matrix n n ℤ) (x : UnitAddTorus n) : UnitAddTorus n := fun i => ∑ j, N i j • x j

/-- [definition] The torus point of a real lift. -/
def proj (v : n → ℝ) : UnitAddTorus n := fun i => (v i : UnitAddCircle)

/-- [definition] An integer vector read as a real one. -/
def castVec (w : n → ℤ) : n → ℝ := fun i => (w i : ℝ)

/-- [definition] An integer matrix read as a real one. -/
abbrev toReal (N : Matrix n n ℤ) : Matrix n n ℝ := N.map fun x => (x : ℝ)

theorem proj_add (u v : n → ℝ) : proj (u + v) = proj u + proj v := funext fun _ => rfl

theorem proj_sub (u v : n → ℝ) : proj (u - v) = proj u - proj v := funext fun _ => rfl

/-- [proved-standard; formal-checked] Every torus point has a real lift. -/
theorem proj_surjective : Function.Surjective (proj (n := n)) := by
  intro x
  choose v hv using fun i => QuotientAddGroup.mk_surjective (x i)
  exact ⟨v, funext hv⟩

theorem castVec_add (a b : n → ℤ) : castVec (a + b) = castVec a + castVec b := by
  funext i
  simp [castVec]

theorem castVec_injective : Function.Injective (castVec (n := n)) :=
  fun a b h => funext fun i => Int.cast_injective (congrFun h i)

/-- [proved-standard; formal-checked] A lattice point is the torus's zero. -/
theorem proj_castVec (w : n → ℤ) : proj (castVec w) = 0 := by
  funext i
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨w i, by simp [castVec]⟩

/-- [proved-standard; formal-checked] A real lift reads the torus's zero exactly on the lattice. -/
theorem proj_eq_zero_iff (v : n → ℝ) : proj v = 0 ↔ ∃ z : n → ℤ, castVec z = v := by
  constructor
  · intro h
    have hi : ∀ i, ∃ m : ℤ, m • (1 : ℝ) = v i := fun i =>
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (congrFun h i)
    choose z hz using hi
    exact ⟨z, funext fun i => by simpa [castVec] using hz i⟩
  · rintro ⟨z, rfl⟩
    exact proj_castVec z

theorem det_toReal (N : Matrix n n ℤ) : (toReal N).det = (N.det : ℝ) := (Int.cast_det N).symm

theorem isUnit_det_toReal {N : Matrix n n ℤ} (hN : N.det ≠ 0) : IsUnit (toReal N).det := by
  rw [det_toReal]
  exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)

theorem toReal_mulVec_inv {N : Matrix n n ℤ} (hN : N.det ≠ 0) (v : n → ℝ) :
    toReal N *ᵥ ((toReal N)⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_toReal hN), one_mulVec]

theorem inv_mulVec_toReal {N : Matrix n n ℤ} (hN : N.det ≠ 0) (v : n → ℝ) :
    (toReal N)⁻¹ *ᵥ (toReal N *ᵥ v) = v := by
  rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_toReal hN), one_mulVec]

theorem toReal_mulVec_castVec (N : Matrix n n ℤ) (w : n → ℤ) :
    toReal N *ᵥ castVec w = castVec (N *ᵥ w) := by
  funext i
  simp [toReal, castVec, mulVec, dotProduct]

/-- [proved-standard; formal-checked] **The torus map on a lift is the lift of `N v`.** -/
theorem act_proj (N : Matrix n n ℤ) (v : n → ℝ) : act N (proj v) = proj (toReal N *ᵥ v) := by
  funext i
  simp only [act, proj, toReal, mulVec, dotProduct, Matrix.map_apply]
  rw [QuotientAddGroup.mk_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← zsmul_eq_mul, QuotientAddGroup.mk_zsmul]

/-! ## 2. The kernel is the lattice read back through `N` -/

/-- [definition] The lattice read back through `N`: `w ↦ N⁻¹ w mod ℤⁿ`. -/
def lift (N : Matrix n n ℤ) : (n → ℤ) →+ UnitAddTorus n :=
  AddMonoidHom.mk' (fun w => proj ((toReal N)⁻¹ *ᵥ castVec w)) fun a b => by
    simp only [castVec_add, mulVec_add, proj_add]

theorem lift_apply (N : Matrix n n ℤ) (w : n → ℤ) :
    lift N w = proj ((toReal N)⁻¹ *ᵥ castVec w) := rfl

/-- [proved-standard; formal-checked] **`w` lands on zero exactly when `w ∈ N ℤⁿ`.** -/
theorem lift_eq_zero_iff {N : Matrix n n ℤ} (hN : N.det ≠ 0) (w : n → ℤ) :
    lift N w = 0 ↔ ∃ z, N *ᵥ z = w := by
  rw [lift_apply, proj_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, castVec_injective ?_⟩
    rw [← toReal_mulVec_castVec, hz, toReal_mulVec_inv hN]
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [← toReal_mulVec_castVec, inv_mulVec_toReal hN]⟩

/-- [proved-standard; formal-checked] **The kernel of the torus map is the image of the lattice
read back through `N`.** -/
theorem act_eq_zero_iff {N : Matrix n n ℤ} (hN : N.det ≠ 0) (x : UnitAddTorus n) :
    act N x = 0 ↔ ∃ w, lift N w = x := by
  obtain ⟨v, rfl⟩ := proj_surjective x
  rw [act_proj, proj_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [lift_apply, hz, inv_mulVec_toReal hN]
  · rintro ⟨w, hw⟩
    rw [lift_apply] at hw
    have h0 : proj (v - (toReal N)⁻¹ *ᵥ castVec w) = 0 := by
      rw [proj_sub]
      exact sub_eq_zero.mpr hw.symm
    obtain ⟨z, hz⟩ := (proj_eq_zero_iff _).mp h0
    refine ⟨N *ᵥ z + w, ?_⟩
    rw [castVec_add, ← toReal_mulVec_castVec, hz, mulVec_sub, toReal_mulVec_inv hN,
      sub_add_cancel]

/-- [definition] `N` acting on the lattice `ℤⁿ`, `w ↦ N w`. -/
def latticeMap (N : Matrix n n ℤ) : (n → ℤ) →+ (n → ℤ) :=
  AddMonoidHom.mk' (fun w => N *ᵥ w) fun a b => mulVec_add N a b

theorem latticeMap_apply (N : Matrix n n ℤ) (w : n → ℤ) : latticeMap N w = N *ᵥ w := rfl

/-- [proved-standard; formal-checked] An integer matrix of nonzero determinant is injective on the
lattice. -/
theorem latticeMap_injective {N : Matrix n n ℤ} (hN : N.det ≠ 0) :
    Function.Injective (latticeMap N).toIntLinearMap := by
  intro a b h
  have h₀ : N *ᵥ a = N *ᵥ b := h
  apply castVec_injective
  have h' := congrArg (fun w => (toReal N)⁻¹ *ᵥ castVec w) h₀
  simp only [← toReal_mulVec_castVec, inv_mulVec_toReal hN] at h'
  exact h'

/-- [proved-standard; formal-checked] The lattice map's determinant is the matrix's. -/
theorem det_latticeMap (N : Matrix n n ℤ) :
    LinearMap.det (latticeMap N).toIntLinearMap = N.det := by
  rw [← LinearMap.det_toLin' N]
  first
    | rfl
    | exact congrArg LinearMap.det (LinearMap.ext fun w => rfl)

/-! ## 3. The index law -/

/-- [proved-standard; formal-checked] **The index law**: for `det N ≠ 0` the torus map `x ↦ N x`
has exactly `|det N|` points in its kernel. -/
theorem card_ker_act (N : Matrix n n ℤ) (hN : N.det ≠ 0) :
    Nat.card {x : UnitAddTorus n // act N x = 0} = N.det.natAbs := by
  have inj := latticeMap_injective hN
  have hker : LinearMap.ker (lift N).toIntLinearMap =
      LinearMap.range (latticeMap N).toIntLinearMap := by
    ext w
    exact LinearMap.mem_ker.trans ((lift_eq_zero_iff hN w).trans LinearMap.mem_range.symm)
  have key := Submodule.natAbs_det_equiv (LinearMap.range (latticeMap N).toIntLinearMap)
    (LinearEquiv.ofInjective (latticeMap N).toIntLinearMap inj)
  calc Nat.card {x : UnitAddTorus n // act N x = 0}
      = Nat.card (LinearMap.range (lift N).toIntLinearMap) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x =>
          (act_eq_zero_iff hN x).trans LinearMap.mem_range.symm)
    _ = Nat.card ((n → ℤ) ⧸ LinearMap.ker (lift N).toIntLinearMap) :=
        Nat.card_congr (lift N).toIntLinearMap.quotKerEquivRange.toEquiv.symm
    _ = Nat.card ((n → ℤ) ⧸ LinearMap.range (latticeMap N).toIntLinearMap) :=
        Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv
    _ = N.det.natAbs := by
        refine key.symm.trans (congrArg Int.natAbs ?_)
        refine Eq.trans ?_ (det_latticeMap N)
        exact congrArg LinearMap.det (LinearMap.ext fun w => by first | rfl | simp)

/-! ## 4. The fixed points -/

/-- [proved-standard; formal-checked] `(M − 1) x = M x − x` on the torus. -/
theorem act_sub_one (M : Matrix n n ℤ) (x : UnitAddTorus n) : act (M - 1) x = act M x - x := by
  funext i
  simp only [act, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply,
    Pi.sub_apply]
  congr 1
  simp [ite_smul]

/-- [proved-standard; formal-checked] **The fixed points**: for `det(M − 1) ≠ 0` the torus map of
`M` has exactly `|det(M − 1)|` fixed points. -/
theorem card_fixed (M : Matrix n n ℤ) (hM : (M - 1).det ≠ 0) :
    Nat.card {x : UnitAddTorus n // act M x = x} = (M - 1).det.natAbs := by
  rw [← card_ker_act (M - 1) hM]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [act_sub_one, sub_eq_zero])

/-! ## 5. The three kinds on the two-torus -/

/-- [proved-standard; formal-checked] On the two-torus, a move of determinant 1 and trace other
than 2 has exactly `|2 − tr M|` fixed points. -/
theorem card_fixed_two (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (htr : M.trace ≠ 2) :
    Nat.card {x : UnitAddTorus (Fin 2) // act M x = x} = (2 - M.trace).natAbs := by
  have h : (M - 1).det = 2 - M.trace := by
    rw [TorusBraid.det_sub_one_fin_two, hdet]
    ring
  rw [card_fixed M (by rw [h]; exact sub_ne_zero.mpr (Ne.symm htr)), h]

/-- [proved-standard; formal-checked] **The order-six turn `T L` fixes one point.** -/
theorem turn_fixed_point :
    Nat.card {x : UnitAddTorus (Fin 2) // act (TorusBraid.T * TorusBraid.L) x = x} = 1 := by
  have hdet : (TorusBraid.T * TorusBraid.L).det = 1 := by
    norm_num [TorusBraid.turn_eq, Matrix.det_fin_two_of]
  have h := card_fixed_two _ hdet (by rw [TorusBraid.trace_turn]; norm_num)
  rw [TorusBraid.trace_turn] at h
  exact h.trans (by first | rfl | decide | norm_num)

/-- [proved-standard; formal-checked] **The quarter turn `T L T` fixes two points**, `0` and
`(½, ½)`. -/
theorem quarter_turn_fixed_points :
    Nat.card {x : UnitAddTorus (Fin 2) //
      act (TorusBraid.T * TorusBraid.L * TorusBraid.T) x = x} = 2 := by
  have hdet : (TorusBraid.T * TorusBraid.L * TorusBraid.T).det = 1 := by
    norm_num [TorusBraid.quarter_turn, Matrix.det_fin_two_of]
  have htr : (TorusBraid.T * TorusBraid.L * TorusBraid.T).trace = 0 := by
    norm_num [TorusBraid.quarter_turn, Matrix.trace_fin_two_of]
  have h := card_fixed_two _ hdet (by rw [htr]; norm_num)
  rw [htr] at h
  exact h.trans (by first | rfl | decide | norm_num)

/-- [proved-standard; formal-checked] **The half turn `−1 = (T L T)²` fixes the four
half-periods.** -/
theorem half_turn_fixed_points :
    Nat.card {x : UnitAddTorus (Fin 2) // act (-1 : Matrix (Fin 2) (Fin 2) ℤ) x = x} = 4 := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    norm_num [Matrix.det_fin_two]
  have htr : (-1 : Matrix (Fin 2) (Fin 2) ℤ).trace = -2 := by
    norm_num [Matrix.trace_fin_two]
  have h := card_fixed_two _ hdet (by rw [htr]; norm_num)
  rw [htr] at h
  exact h.trans (by first | rfl | decide | norm_num)

/-- [proved-standard; formal-checked] **The cat map's power `A^(k+1)` fixes `L_(2k+2) − 2`
points**, with `L_(2k+2) = F_(2k+1) + F_(2k+3)`: 1, 5, 16, 45, 121 for `k = 0, …, 4`
(`TorusBraid.cat_counts`). -/
theorem cat_fixed_points (k : ℕ) :
    Nat.card {x : UnitAddTorus (Fin 2) // act (TorusBraid.A ^ (k + 1)) x = x} =
      Nat.fib (2 * k + 1) + Nat.fib (2 * k + 3) - 2 := by
  have habs := TorusBraid.abs_det_cat_pow_sub_one k
  have h3 : 2 ≤ Nat.fib (2 * k + 3) := by
    have hmono : Nat.fib 3 ≤ Nat.fib (2 * k + 3) := Nat.fib_mono (by omega)
    have h : Nat.fib 3 = 2 := rfl
    omega
  have h1 : 1 ≤ Nat.fib (2 * k + 1) := Nat.fib_pos.mpr (by omega)
  have hne : (TorusBraid.A ^ (k + 1) - 1).det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    omega
  rw [card_fixed _ hne]
  have key : (((TorusBraid.A ^ (k + 1) - 1).det.natAbs : ℕ) : ℤ) =
      ((Nat.fib (2 * k + 1) : ℤ) + Nat.fib (2 * k + 3)) - 2 := by
    rw [Int.natCast_natAbs, habs]
  omega

end Holonics.Geometry.TorusIndex
