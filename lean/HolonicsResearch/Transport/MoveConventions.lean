import Holonics.Transport.CellHolonomy
import Holonics.Transport.SerialScrewChain
import Holonics.Geometry.Motion

/-!
# Move-composition conventions: left to right is the opposite group, the cochain is the holonomy's
first order, and a based point closes where the frame need not

A cell realization composes its edges' moves in a declared order, reads its holonomy in a declared
chart, and tests closure on a declared object. This file states each of the three conventions on
the owners that hold the moves (`Geometry/Motion.move`, `Transport/SerialScrewChain.AffineMap3`)
and the cell (`Transport/CellHolonomy.triangleHolonomy`), and reads each pair of conventions apart
by a witness.

Sources: #410's box "Move-composition conventions for cell realization: left-to-right affine
composition versus the opposite group; multiplicative holonomy versus additive cochain; point closure
versus whole-frame closure (`Geometry/Motion`, `Transport/CellHolonomy`)"; the winding guide §4
(`docs/WINDING_CARRY_AND_PLACEMENT.md`: "closure of a based point is `(R−I)x+t=0`; closure of the
whole frame is `R=I, t=0`. Translation alone is not the test. The `followed_by` convention … applies
maps left to right, whereas standard column matrices/permutations multiply right to left. Its formal
realization uses the opposite group or reverses the represented word; a noncommuting triangle checks
the convention. … Multiplicative nonabelian holonomy and the additive Hodge complex require their
declared representation/linearization before their fields can be identified"); the open paragraph of
`Transport/CellHolonomy` ("Scope: group identities on one triangular cell … Continuum connections,
curvature forms and characteristic classes are outside this module") and of
`Transport/SerialScrewChain` ("composition is ordered and acts on points … No finite chart is
silently identified with an exponential of an infinitesimal screw"); the records
`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md` and
`research/records/2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md`;
atlas rows `holonomy.composition-convention` (graded `definition`, no Lean owner before this file),
`holonomy.cell-face`, `winding.burgers-step`, `chain.affine-composition`, `motion.affine-move-pivot`,
`motion.commutator-carry`, `screw.burgers-loop-carry` and `cell.connection-route-return`.

[definition] [proved-standard; formal-checked] [proved-derived; formal-checked] What is proved.

1. **Left-to-right composition is the opposite group.** In a monoid whose product composes right to
   left, "`f`, then `g`" is `followedBy f g = g * f` (`followedBy`), the product `op f * op g` of the
   opposite monoid (`op_followedBy`); a word composed left to right (`followedByWord`) is the
   right-to-left product of the reversed word (`followedByWord_eq_prod_reverse`) and, in the opposite
   monoid, the product of its letters in word order (`op_followedByWord`). The maps of a type under
   "then" (`ThenEnd`) are isomorphic as a monoid to `(Function.End α)ᵐᵒᵖ` by `f ↦ op f`
   (`thenEndEquivOp`, `thenEnd_mul_apply`); `Equiv.trans` is "then" in the permutation group
   (`perm_trans_eq_followedBy`). The serial owner's charts form a monoid under its ordered
   composition (`chart_mul_def`, `chart_one_def`); application is an injective monoid map into
   `(Function.End Vec)ᵐᵒᵖ` (`apply_compose_eq_followedBy`, `applyHom`, `apply_injective`,
   `applyHom_injective`) and an isomorphism onto its range (`applyEquivRange`). The homogeneous
   column matrix `[[L, t], [0, 1]]` acts on `(x, 1)` as the chart (`homogeneous`,
   `homogeneous_mulVec`) and multiplies right to left: `H(f, then g) = H g · H f`
   (`homogeneous_compose`, `homogeneous_identity`), an injective monoid map into the opposite of the
   column matrices (`homogeneousHom`, `homogeneous_injective`). The owner's `configuration` is the
   chart product of its word (`configuration_eq_prod`), whose homogeneous matrix is the column product
   of the reversed word (`homogeneous_configuration`), while the owner's `serialConfiguration` is the
   column product of its word as written (`homogeneous_serialConfiguration`). On a cell: the owner's
   regauge `kᵢ⁻¹ g kⱼ` makes `gᵢⱼ` carry the frame at `j` to the frame at `i`, so its word
   `g₀₁ g₁₂ g₂₀` is written along the boundary `0 → 1 → 2 → 0` and acts right to left, `g₂₀` first.
   The triangle holonomy in the opposite group is the holonomy of the reversed word
   (`triangleHolonomy_op`), and regauging there exchanges the vertices and inverts the frames
   (`regauge_op`).
2. **The noncommuting triangle.** With the translations `e₁`, `e₂` and the quarter turn about `e₃`
   (`shiftX`, `shiftY`, `quarterTurn`), the triangle read left to right is the quarter turn with the
   carry `2e₂` (`leftToRight_triangle`) and read right to left the quarter turn with no carry
   (`rightToLeft_triangle`); the two values differ as charts and as column-matrix products
   (`triangle_readings_differ`, `homogeneous_triangle_orders_differ`), so the convention is read from
   the holonomy's value. The right-to-left reading closes the origin and no frame
   (`rightToLeft_triangle_closes_origin_not_frame`); the left-to-right reading leaves the origin open
   and closes `(−1, 1, 0)` (`leftToRight_triangle_pivot`): one turn about two axes, the order's
   torsion of `motion.commutator-carry`.
3. **Multiplicative holonomy against the additive cochain.** In a commutative carrier written
   additively the triangle holonomy is the sum of the edge values (`additive_triangleHolonomy`),
   regauging adds the coboundary `kⱼ − kᵢ` (`additive_regauge`), and the cochain sum is gauge-free
   and vanishes on a pure gauge (`additive_holonomy_gauge_free`, `additive_pure_gauge`, read from
   `CellHolonomy.abelian_holonomy_is_gauge_free` and `CellHolonomy.pure_gauge_has_trivial_holonomy`).
   Along `gₑ(t) = exp(t aₑ)` in a Banach algebra over `ℝ` the derivative at `t = 0` of
   `g₀₁ g₁₂ g₂₀` is the cochain sum `a₀₁ + a₁₂ + a₂₀` (`holonomy_first_order`, and for real matrices
   `matrix_holonomy_first_order`), while the second derivatives of `exp(ta) exp(tb) exp(tc)` and
   `exp(t(a + b + c))` at `0` differ by `[a, b] + [a, c] + [b, c]` (`holonomy_second_order`). An
   element with `x³ = 0` has `exp x = 1 + x + x²/2` (`exp_of_cube_eq_zero`, `exp_of_sq_eq_zero`).
4. **Point closure against whole-frame closure** for `x ↦ M x + t` on a module over a ring. A based
   point closes iff `(M − 1) x + t = 0` (`point_closes_iff`); the frame closes iff `M = 1` and `t = 0`
   (`frame_closes_iff`), and then every point closes (`frame_closure_closes_every_point`). A turn
   about a point closes that point and no frame (`turn_closes_pivot_not_frame`). For `M ≠ 1` the
   translation is not the test: a zero translation leaves the frame open and a nonzero translation
   closes some point (`translation_is_not_the_test`). For `M = 1` the translation decides: a point
   closes iff `t = 0`, so all points close or none (`flat_point_closes_iff`,
   `flat_closes_all_or_none`, with `Motion.translation_has_no_pivot`). When `M − 1` is a unit one
   and only one point closes (`unique_closing_point`, with `Motion.pivot_unique`). The serial
   owner's chart is the Motion owner's move of its matrix (`apply_eq_move`), closes a based point iff
   `(L − 1) x + t = 0` (`chart_point_closes_iff`) and closes the frame iff it is the identity chart
   (`chart_frame_closes_iff`).

[counterexample; formal-checked] The witnesses.

- **The triangle**, item 2.
- **Two noncommuting steps.** For `a = E₀₁`, `b = E₁₀` of the two-by-two real matrices,
  `exp a · exp b ≠ exp(a + b)` (`raise2`, `lower2`, `exp_raise_mul_exp_lower_ne`). Here `a + b` is
  not nilpotent (it squares to `1`), so the series of `exp(a + b)` does not end; the witness reads
  that `exp(a + b)` commutes with `a + b` while `(1 + a)(1 + b)` does not.
- **The Heisenberg steps**, where every exponential is a polynomial. For `a = E₀₁`, `b = E₁₂` of the
  three-by-three real matrices (`step01`, `step12`): `exp a · exp b = exp(a + b + [a, b]/2)`, the
  Baker–Campbell–Hausdorff series ending at its commutator term (`heisenberg_exp_mul_exp`), and
  `exp a · exp b ≠ exp(a + b)` (`heisenberg_exp_mul_exp_ne`). The cell with edges `a`, `b`, `−(a + b)`
  has cochain sum `0` and holonomy `1 + [a, b]/2` (`heisenberg_cell_holonomy`), which is not `1`
  (`heisenberg_cell_holonomy_ne_one`): the additive cochain reads a flat cell where the
  multiplicative holonomy carries the commutator.

What is not claimed. No logarithm of a holonomy is constructed and no general
Baker–Campbell–Hausdorff series is stated: the second order is read as a difference of derivatives
at `t = 0` and as one nilpotent instance. The linearization that would identify the fields of a
multiplicative nonabelian holonomy with the cochains of `Foundation/HodgeReceiver`'s weighted complex
is not built; this file states where the two charts agree (a commutative carrier, and the first order
at the identity) and where they part (the commutator at second order). The rigid reading of a closed
or open holonomy (Chasles, `Geometry/Motion.chasles`), the base-point dependence of a carry
(`move_basepoint` of `Geometry/ScrewTorsion`) and the retired Rust `followed_by` itself are cited, not restated: the
left-to-right convention is read from the guide's sentence and from the serial owner's `compose`.

The computational object is the helical pair interaction: each edge of a cell is a pair contact
whose transport over one tick is a move (a turn, a boost or a fall), the cell's face is the composite
of its contacts' moves, and a realization that multiplies the contacts in the other order reads the
same contacts at a moved pivot; the pair's torsion, the commutator of two moves, is the term the
additive chart misses at second order, and a based point's closure is the pivot of the composite move.
Of the winding guide's six general objects this touches the cell holonomy (all four items), the tube
(the serial chain's ordered transfer between charts and its column-matrix realization) and the helix
(the one-parameter family `exp(t a)`, a turn with its carry, and the flat carry `t` of item 4); the
pair, the faces and placement, and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

open scoped Matrix
open Matrix MulOpposite

namespace Holonics.Transport.MoveConventions

open Holonics.Transport.CellHolonomy
open Holonics.Transport.SerialScrewChain
open Holonics.Geometry.ScrewGeometry (Vec)

/-! ## 1. Left-to-right composition is the opposite monoid -/

section Generic

variable {M : Type*} [Monoid M]

/-- [definition] **"`f`, then `g`"** in a monoid whose product composes right to left
(`Function.End`, `Equiv.Perm`, `Module.End`, column matrices): `followedBy f g = g * f`. -/
def followedBy (f g : M) : M := g * f

/-- [definition] A word composed left to right: its first letter acts first. -/
def followedByWord : List M → M
  | [] => 1
  | f :: fs => followedBy f (followedByWord fs)

/-- [proved-standard; formal-checked] In the opposite monoid, "`f`, then `g`" is the product `op f * op g`. -/
theorem op_followedBy (f g : M) : op (followedBy f g) = op f * op g :=
  op_mul g f

/-- [proved-standard; formal-checked] A word composed left to right is the right-to-left product of the
reversed word. -/
theorem followedByWord_eq_prod_reverse (fs : List M) : followedByWord fs = fs.reverse.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [followedByWord, followedBy, ih]

/-- [proved-standard; formal-checked] In the opposite monoid a left-to-right word is the product of its
letters in word order. -/
theorem op_followedByWord (fs : List M) : op (followedByWord fs) = (fs.map op).prod := by
  rw [followedByWord_eq_prod_reverse, op_list_prod, List.map_reverse, List.reverse_reverse]

end Generic

section Maps

variable (α : Type*)

/-- [definition] The maps of `α` under left-to-right composition, the retired `followed_by`:
`f * g` applies `f`, then `g`. -/
def ThenEnd : Type _ := α → α

/-- [definition] The monoid of `ThenEnd`: the identity, and `f * g = g ∘ f`. -/
instance : Monoid (ThenEnd α) where
  one := (id : α → α)
  mul f g := ((g : α → α) ∘ (f : α → α) : α → α)
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

variable {α}

/-- [proved-standard; formal-checked] In `ThenEnd`, `f * g` applies `f` first. -/
theorem thenEnd_mul_apply (f g : ThenEnd α) (x : α) :
    (show α → α from f * g) x = (show α → α from g) ((show α → α from f) x) := rfl

variable (α)

/-- [proved-standard; formal-checked] **Left-to-right composition is the opposite of composition:**
`f ↦ op f` is a monoid isomorphism from `(maps, then)` to `(maps, ∘)ᵐᵒᵖ`. -/
def thenEndEquivOp : ThenEnd α ≃* (Function.End α)ᵐᵒᵖ where
  toFun f := op (show Function.End α from f)
  invFun f := (show ThenEnd α from unop f)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Maps

/-- [proved-standard; formal-checked] `Equiv.trans` is left-to-right: `f.trans g` is "`f`, then `g`" in the
permutation group, whose product composes right to left. -/
theorem perm_trans_eq_followedBy {α : Type*} (f g : Equiv.Perm α) : f.trans g = followedBy f g :=
  (Equiv.Perm.mul_def g f).symm

/-! ### The serial owner's charts -/

/-- [definition] The serial owner's charts under their ordered composition: `f * g = f.compose g`
applies `f`, then `g` (`SerialScrewChain.AffineMap3.compose`). -/
instance : Monoid AffineMap3 where
  mul := AffineMap3.compose
  one := AffineMap3.identity
  mul_assoc := AffineMap3.compose_assoc
  one_mul := AffineMap3.identity_compose
  mul_one := AffineMap3.compose_identity

/-- [proved-derived; formal-checked] The chart product is the owner's ordered composition. -/
theorem chart_mul_def (f g : AffineMap3) : f * g = f.compose g := rfl

/-- [proved-derived; formal-checked] The unit chart is the owner's identity. -/
theorem chart_one_def : (1 : AffineMap3) = AffineMap3.identity := rfl

/-- [proved-derived; formal-checked] Applying a composed chart is the composite of the applications,
"`f`, then `g`". -/
theorem apply_compose_eq_followedBy (f g : AffineMap3) :
    ((f.compose g).apply : Function.End Vec) = followedBy (M := Function.End Vec) f.apply g.apply :=
  funext (AffineMap3.compose_apply f g)

/-- [proved-derived; formal-checked] Application is a monoid map from the charts under "then" to the
opposite of the maps of `Vec` under composition. -/
def applyHom : AffineMap3 →* (Function.End Vec)ᵐᵒᵖ where
  toFun f := op (f.apply : Function.End Vec)
  map_one' := congrArg op (funext AffineMap3.identity_apply)
  map_mul' f g := congrArg op (funext (AffineMap3.compose_apply f g))

/-- [proved-derived; formal-checked] A chart is determined by its action on points. -/
theorem apply_injective : Function.Injective AffineMap3.apply := by
  intro f g h
  have ht : f.translation = g.translation := by
    simpa [AffineMap3.apply] using congrFun h 0
  have hl : f.linear = g.linear := by
    apply Matrix.mulVec_injective
    funext x
    have hx := congrFun h x
    simp only [AffineMap3.apply, ht] at hx
    exact add_right_cancel hx
  cases f; cases g
  simp_all

/-- [proved-derived; formal-checked] Application is an injective monoid map into the opposite. -/
theorem applyHom_injective : Function.Injective applyHom :=
  fun _ _ h => apply_injective (op_injective h)

/-- [proved-derived; formal-checked] **The charts under "then" are isomorphic to the affine maps of
`Vec` inside `(maps, ∘)ᵐᵒᵖ`.** -/
noncomputable def applyEquivRange : AffineMap3 ≃* MonoidHom.mrange applyHom :=
  MulEquiv.ofBijective applyHom.mrangeRestrict
    ⟨fun _ _ h => applyHom_injective (congrArg Subtype.val h), applyHom.mrangeRestrict_surjective⟩

/-- [definition] The homogeneous column matrix of a chart: `[[L, t], [0, 1]]`, acting on `(x, 1)`. -/
def homogeneous (f : AffineMap3) : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℚ :=
  fromBlocks f.linear (replicateCol Unit f.translation) 0 1

/-- [proved-standard; formal-checked] The homogeneous matrix acts on the column `(x, 1)` as the chart. -/
theorem homogeneous_mulVec (f : AffineMap3) (x : Vec) :
    homogeneous f *ᵥ Sum.elim x (fun _ => 1) = Sum.elim (f.apply x) (fun _ => 1) := by
  rw [homogeneous, fromBlocks_mulVec]
  congr 1
  · funext i
    simp [AffineMap3.apply, mulVec, dotProduct, replicateCol_apply]
  · funext i
    simp

/-- [proved-standard; formal-checked] **Column matrices multiply right to left:** the homogeneous
matrix of "`f`, then `g`" is `H g * H f`. -/
theorem homogeneous_compose (f g : AffineMap3) :
    homogeneous (f.compose g) = homogeneous g * homogeneous f := by
  rw [homogeneous, homogeneous, homogeneous, fromBlocks_multiply]
  simp only [AffineMap3.compose, Matrix.mul_zero, add_zero, Matrix.zero_mul, Matrix.mul_one, zero_add]
  congr 1

/-- [proved-standard; formal-checked] The identity chart has the identity homogeneous matrix. -/
theorem homogeneous_identity : homogeneous AffineMap3.identity = 1 := by
  rw [homogeneous]
  simp [AffineMap3.identity, fromBlocks_one]

/-- [proved-derived; formal-checked] The homogeneous matrix is a monoid map from the charts under
"then" to the opposite of the column matrices. -/
def homogeneousHom : AffineMap3 →* (Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℚ)ᵐᵒᵖ where
  toFun f := op (homogeneous f)
  map_one' := congrArg op homogeneous_identity
  map_mul' f g := by
    rw [chart_mul_def, homogeneous_compose, op_mul]

/-- [proved-derived; formal-checked] The homogeneous matrix determines the chart. -/
theorem homogeneous_injective : Function.Injective homogeneous := by
  intro f g h
  rw [homogeneous, homogeneous, fromBlocks_inj] at h
  obtain ⟨hl, ht, -, -⟩ := h
  cases f; cases g
  simp only at hl ht
  rw [hl, replicateCol_injective ht]

/-- [proved-derived; formal-checked] The owner's application-order configuration is the chart product of
the word. -/
theorem configuration_eq_prod (fs : List AffineMap3) : configuration fs = fs.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [configuration, ih, List.prod_cons, chart_mul_def]

/-- [proved-derived; formal-checked] **The reversed word:** the homogeneous matrix of a word composed left
to right is the right-to-left matrix product of the reversed word. -/
theorem homogeneous_configuration (fs : List AffineMap3) :
    homogeneous (configuration fs) = (fs.map homogeneous).reverse.prod := by
  have h := congrArg unop (map_list_prod homogeneousHom fs)
  rw [← configuration_eq_prod] at h
  rw [unop_list_prod, List.map_map] at h
  exact h

/-- [proved-derived; formal-checked] The owner's native serial configuration is the column-matrix
product of its word as written. -/
theorem homogeneous_serialConfiguration (fs : List AffineMap3) :
    homogeneous (serialConfiguration fs) = (fs.map homogeneous).prod := by
  rw [serialConfiguration, homogeneous_configuration, List.map_reverse, List.reverse_reverse]

/-! ### The cell holonomy in the opposite group -/

section OppositeCell

variable {G : Type*} [Group G]

/-- [proved-standard; formal-checked] The triangle holonomy computed in the opposite group is the
holonomy of the reversed word. -/
theorem triangleHolonomy_op (g01 g12 g20 : G) :
    triangleHolonomy (op g01) (op g12) (op g20) = op (triangleHolonomy g20 g12 g01) := by
  simp only [triangleHolonomy, op_mul, mul_assoc]

/-- [proved-standard; formal-checked] Regauging in the opposite group is regauging by the inverse
frames with the vertices exchanged. -/
theorem regauge_op (ki kj g : G) :
    regauge (op ki) (op kj) (op g) = op (regauge kj⁻¹ ki⁻¹ g) := by
  simp only [regauge, op_mul, op_inv, inv_inv, mul_assoc]

end OppositeCell

/-! ### A noncommuting triangle reads the convention -/

/-- [definition] Translation by `e₁`. -/
def shiftX : AffineMap3 := translationChart ![1, 0, 0]

/-- [definition] Translation by `e₂`. -/
def shiftY : AffineMap3 := translationChart ![0, 1, 0]

/-- [definition] The quarter turn about the `e₃` axis through the origin. -/
def quarterTurn : AffineMap3 where
  linear := !![0, -1, 0; 1, 0, 0; 0, 0, 1]
  translation := 0

/-- [proved-derived; formal-checked] Read left to right, the triangle `e₁`, quarter turn, `e₂` is the
quarter turn followed by the carry `2e₂`. -/
theorem leftToRight_triangle :
    configuration [shiftX, quarterTurn, shiftY] = ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], ![0, 2, 0]⟩ := by
  simp only [configuration, AffineMap3.compose_identity]
  simp only [AffineMap3.compose, shiftX, shiftY, quarterTurn, translationChart]
  congr 1
  · simp
  · ext i; fin_cases i <;> norm_num

/-- [proved-derived; formal-checked] Read right to left (the reversed word in application order), the
same triangle is the quarter turn with no carry. -/
theorem rightToLeft_triangle :
    configuration [shiftY, quarterTurn, shiftX] = ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], 0⟩ := by
  simp only [configuration, AffineMap3.compose_identity]
  simp only [AffineMap3.compose, shiftX, shiftY, quarterTurn, translationChart]
  congr 1
  · simp
  · ext i; fin_cases i <;> simp

/-- [counterexample; formal-checked] **The two readings of the triangle differ**, so the convention is
read from the holonomy's value. -/
theorem triangle_readings_differ :
    configuration [shiftX, quarterTurn, shiftY] ≠ configuration [shiftY, quarterTurn, shiftX] := by
  rw [leftToRight_triangle, rightToLeft_triangle]
  intro h
  have := congrFun (congrArg AffineMap3.translation h) 1
  simp at this

/-- [counterexample; formal-checked] The column-matrix products of the triangle in its two orders
differ. -/
theorem homogeneous_triangle_orders_differ :
    homogeneous shiftY * homogeneous quarterTurn * homogeneous shiftX
      ≠ homogeneous shiftX * homogeneous quarterTurn * homogeneous shiftY := by
  intro h
  apply triangle_readings_differ
  apply homogeneous_injective
  rw [homogeneous_configuration, homogeneous_configuration]
  simpa [List.prod_cons, mul_assoc] using h

/-! ## 2. Multiplicative holonomy against the additive cochain -/

section Additive

variable {A : Type*} [AddCommGroup A]

/-- [proved-standard; formal-checked] In a commutative carrier written additively, the triangle holonomy
is the sum of the edge values. -/
theorem additive_triangleHolonomy (a01 a12 a20 : A) :
    (triangleHolonomy (Multiplicative.ofAdd a01) (Multiplicative.ofAdd a12)
      (Multiplicative.ofAdd a20)).toAdd = a01 + a12 + a20 := rfl

/-- [proved-standard; formal-checked] Additively, regauging adds the coboundary `kⱼ − kᵢ` of the vertex
potential to the edge value. -/
theorem additive_regauge (ki kj a : A) :
    (regauge (Multiplicative.ofAdd ki) (Multiplicative.ofAdd kj) (Multiplicative.ofAdd a)).toAdd
      = a + (kj - ki) := by
  simp only [regauge, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

/-- [proved-derived; formal-checked] **The additive cochain sum is gauge-free:** the coboundary of a
vertex potential sums to zero around the cell (`CellHolonomy.abelian_holonomy_is_gauge_free`). -/
theorem additive_holonomy_gauge_free (k0 k1 k2 a01 a12 a20 : A) :
    (a01 + (k1 - k0)) + (a12 + (k2 - k1)) + (a20 + (k0 - k2)) = a01 + a12 + a20 := by
  have h := congrArg Multiplicative.toAdd
    (abelian_holonomy_is_gauge_free (Multiplicative.ofAdd k0) (Multiplicative.ofAdd k1)
      (Multiplicative.ofAdd k2) (Multiplicative.ofAdd a01) (Multiplicative.ofAdd a12)
      (Multiplicative.ofAdd a20))
  rwa [triangleHolonomy, triangleHolonomy, toAdd_mul, toAdd_mul, toAdd_mul, toAdd_mul,
    additive_regauge, additive_regauge, additive_regauge, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd] at h

/-- [proved-derived; formal-checked] Additively, a pure gauge sums to zero around the cell
(`CellHolonomy.pure_gauge_has_trivial_holonomy`). -/
theorem additive_pure_gauge (k0 k1 k2 : A) : (k1 - k0) + (k2 - k1) + (k0 - k2) = 0 := by
  have h := congrArg Multiplicative.toAdd
    (pure_gauge_has_trivial_holonomy (Multiplicative.ofAdd k0) (Multiplicative.ofAdd k1)
      (Multiplicative.ofAdd k2))
  rw [← ofAdd_zero] at h
  rw [triangleHolonomy, toAdd_mul, toAdd_mul, additive_regauge, additive_regauge, additive_regauge,
    toAdd_ofAdd] at h
  simpa only [zero_add] using h

end Additive

section FirstOrder

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- [proved-standard; formal-checked] **At first order the holonomy is the additive cochain:** along
`gₑ(t) = exp(t aₑ)` the derivative at `t = 0` of `g₀₁ g₁₂ g₂₀` is `a₀₁ + a₁₂ + a₂₀`. -/
theorem holonomy_first_order (a01 a12 a20 : 𝔸) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a01) * NormedSpace.exp (t • a12)
      * NormedSpace.exp (t • a20)) (a01 + a12 + a20) 0 := by
  have h := ((hasDerivAt_exp_smul_const a01 (0 : ℝ)).fun_mul
    (hasDerivAt_exp_smul_const a12 (0 : ℝ))).fun_mul (hasDerivAt_exp_smul_const a20 (0 : ℝ))
  convert h using 1
  simp

/-- [proved-standard; formal-checked] **At second order the commutators enter:** the second derivatives
at `t = 0` of `exp(ta) exp(tb) exp(tc)` and of `exp(t(a + b + c))` differ by
`[a, b] + [a, c] + [b, c]`. -/
theorem holonomy_second_order (a b c : 𝔸) :
    iteratedDeriv 2 (fun t : ℝ => NormedSpace.exp (t • a) * NormedSpace.exp (t • b)
        * NormedSpace.exp (t • c)) 0
      - iteratedDeriv 2 (fun t : ℝ => NormedSpace.exp (t • (a + b + c))) 0
      = (a * b - b * a) + (a * c - c * a) + (b * c - c * b) := by
  set E : 𝔸 → ℝ → 𝔸 := fun x t => NormedSpace.exp (t • x) with hE
  have hd : ∀ (x : 𝔸) (t : ℝ), HasDerivAt (E x) (x * E x t) t :=
    fun x t => hasDerivAt_exp_smul_const' x t
  have hE0 : ∀ x : 𝔸, E x 0 = 1 := fun x => by simp [hE]
  have hP : deriv (fun t : ℝ => E a t * E b t * E c t)
      = fun t => a * E a t * E b t * E c t + E a t * b * E b t * E c t
          + E a t * E b t * c * E c t := by
    funext t
    refine (((hd a t).fun_mul (hd b t)).fun_mul (hd c t)).deriv.trans ?_
    noncomm_ring
  have hQ : deriv (E (a + b + c)) = fun t => (a + b + c) * E (a + b + c) t :=
    funext fun t => (hd (a + b + c) t).deriv
  have hP' : HasDerivAt (fun t => a * E a t * E b t * E c t + E a t * b * E b t * E c t
      + E a t * E b t * c * E c t)
      (a * a + a * b + a * c + (a * b + b * b + b * c) + (a * c + b * c + c * c)) 0 := by
    have h1 := ((((hd a 0).const_mul a).fun_mul (hd b 0)).fun_mul (hd c 0))
    have h2 := ((((hd a 0).mul_const b).fun_mul (hd b 0)).fun_mul (hd c 0))
    have h3 := ((((hd a 0).fun_mul (hd b 0)).mul_const c).fun_mul (hd c 0))
    refine ((h1.fun_add h2).fun_add h3).congr_deriv ?_
    simp only [hE0, mul_one, one_mul]
    noncomm_ring
  have hQ' : HasDerivAt (fun t => (a + b + c) * E (a + b + c) t) ((a + b + c) * (a + b + c)) 0 := by
    refine ((hd (a + b + c) 0).const_mul (a + b + c)).congr_deriv ?_
    rw [hE0, mul_one]
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
  change deriv (deriv (fun t : ℝ => E a t * E b t * E c t)) 0 - deriv (deriv (E (a + b + c))) 0 = _
  rw [hP, hQ, hP'.deriv, hQ'.deriv]
  noncomm_ring

end FirstOrder

section MatrixFirstOrder

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] The first-order reading for real matrix transports, under a
submultiplicative operator norm (every norm on the matrices gives the same derivative). -/
theorem matrix_holonomy_first_order {n : Type*} [Fintype n] [DecidableEq n]
    (a01 a12 a20 : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • a01) * NormedSpace.exp (t • a12)
      * NormedSpace.exp (t • a20)) (a01 + a12 + a20) 0 :=
  holonomy_first_order a01 a12 a20

end MatrixFirstOrder

section Witnesses

/-- [proved-standard; formal-checked] In a topological `ℝ`-algebra, an element whose cube is zero has
`exp x = 1 + x + x²/2`. -/
theorem exp_of_cube_eq_zero {𝔹 : Type*} [Ring 𝔹] [Algebra ℝ 𝔹] [TopologicalSpace 𝔹]
    [IsTopologicalRing 𝔹] {x : 𝔹} (hx : x ^ 3 = 0) :
    NormedSpace.exp x = 1 + x + (2⁻¹ : ℝ) • x ^ 2 := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, Nat.factorial]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, hx, zero_mul, smul_zero]

/-- [proved-standard; formal-checked] An element whose square is zero has `exp x = 1 + x`. -/
theorem exp_of_sq_eq_zero {𝔹 : Type*} [Ring 𝔹] [Algebra ℝ 𝔹] [TopologicalSpace 𝔹]
    [IsTopologicalRing 𝔹] {x : 𝔹} (hx : x ^ 2 = 0) : NormedSpace.exp x = 1 + x := by
  rw [exp_of_cube_eq_zero (by rw [pow_succ, hx, zero_mul]), hx, smul_zero, add_zero]

/-- [definition] The raising step `E₀₁` of the two-by-two matrices. -/
def raise2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- [definition] The lowering step `E₁₀` of the two-by-two matrices. -/
def lower2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- [counterexample; formal-checked] **Two noncommuting steps:** `exp a · exp b ≠ exp(a + b)` for
`a = E₀₁`, `b = E₁₀`. -/
theorem exp_raise_mul_exp_lower_ne :
    NormedSpace.exp raise2 * NormedSpace.exp lower2 ≠ NormedSpace.exp (raise2 + lower2) := by
  intro h
  have hc : Commute (raise2 + lower2) (NormedSpace.exp (raise2 + lower2)) := (Commute.refl _).exp_right
  have ha : raise2 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [raise2, pow_two]
  have hb : lower2 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lower2, pow_two]
  rw [← h, exp_of_sq_eq_zero ha, exp_of_sq_eq_zero hb] at hc
  have := congrFun (congrFun hc.eq 0) 1
  simp [raise2, lower2, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- [definition] `E₀₁` of the three-by-three matrices. -/
def step01 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- [definition] `E₁₂` of the three-by-three matrices. -/
def step12 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 1; 0, 0, 0]

/-- [proved-standard; formal-checked] **The second-order term is the commutator** (Baker–Campbell–Hausdorff
on the Heisenberg steps, where it ends): `exp a · exp b = exp(a + b + [a, b]/2)`. -/
theorem heisenberg_exp_mul_exp :
    NormedSpace.exp step01 * NormedSpace.exp step12
      = NormedSpace.exp (step01 + step12 + (2⁻¹ : ℝ) • (step01 * step12 - step12 * step01)) := by
  have h01 : step01 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [step01, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have h12 : step12 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [step12, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have hs : (step01 + step12 + (2⁻¹ : ℝ) • (step01 * step12 - step12 * step01)) ^ 3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [step01, step12, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  rw [exp_of_sq_eq_zero h01, exp_of_sq_eq_zero h12, exp_of_cube_eq_zero hs]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [step01, step12, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  norm_num

/-- [counterexample; formal-checked] On the Heisenberg steps `exp a · exp b ≠ exp(a + b)`. -/
theorem heisenberg_exp_mul_exp_ne :
    NormedSpace.exp step01 * NormedSpace.exp step12 ≠ NormedSpace.exp (step01 + step12) := by
  have h01 : step01 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [step01, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have h12 : step12 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [step12, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have hs : (step01 + step12) ^ 3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [step01, step12, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  rw [exp_of_sq_eq_zero h01, exp_of_sq_eq_zero h12, exp_of_cube_eq_zero hs]
  intro h
  have := congrFun (congrFun h 0) 2
  simp [step01, step12, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] at this

/-- [proved-derived; formal-checked] **A cell whose additive cochain sums to zero carries the commutator
as its holonomy:** with edges `a`, `b`, `−(a + b)` the cochain sum is `0`, and
`exp a · exp b · exp(−(a + b)) = 1 + [a, b]/2`. -/
theorem heisenberg_cell_holonomy :
    step01 + step12 + -(step01 + step12) = 0 ∧
      NormedSpace.exp step01 * NormedSpace.exp step12 * NormedSpace.exp (-(step01 + step12))
        = 1 + (2⁻¹ : ℝ) • (step01 * step12 - step12 * step01) := by
  refine ⟨add_neg_cancel _, ?_⟩
  have h01 : step01 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [step01, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have h12 : step12 ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [step12, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  have hs : (-(step01 + step12)) ^ 3 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [step01, step12, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  rw [exp_of_sq_eq_zero h01, exp_of_sq_eq_zero h12, exp_of_cube_eq_zero hs]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [step01, step12, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

/-- [counterexample; formal-checked] That holonomy is not the identity, so the additive cochain does not
read the nonabelian face. -/
theorem heisenberg_cell_holonomy_ne_one :
    NormedSpace.exp step01 * NormedSpace.exp step12 * NormedSpace.exp (-(step01 + step12)) ≠ 1 := by
  rw [heisenberg_cell_holonomy.2]
  intro h
  have := congrFun (congrFun h 0) 2
  simp [step01, step12] at this

end Witnesses

/-! ## 3. Point closure against whole-frame closure -/

section Closure

open Holonics.Geometry.Motion (move move_fixes_iff_pivot pivot_unique translation_has_no_pivot)

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- [proved-standard; formal-checked] **A based point closes** under `x ↦ M x + t` iff
`(M − 1) x + t = 0`. -/
theorem point_closes_iff (M : Module.End R V) (t x : V) :
    move M t x = x ↔ (M - 1) x + t = 0 := by
  rw [move, LinearMap.sub_apply, Module.End.one_apply,
    show M x - x + t = M x + t - x by abel, sub_eq_zero]

/-- [proved-standard; formal-checked] **The whole frame closes** iff `M = 1` and `t = 0`. -/
theorem frame_closes_iff (M : Module.End R V) (t : V) :
    move M t = id ↔ M = 1 ∧ t = 0 := by
  constructor
  · intro h
    have ht : t = 0 := by simpa [move] using congrFun h 0
    refine ⟨LinearMap.ext fun x => ?_, ht⟩
    simpa [move, ht] using congrFun h x
  · rintro ⟨rfl, rfl⟩
    funext x
    simp [move]

/-- [proved-standard; formal-checked] Whole-frame closure closes every based point. -/
theorem frame_closure_closes_every_point {M : Module.End R V} {t : V} (h : move M t = id) (x : V) :
    move M t x = x :=
  congrFun h x

/-- [counterexample; formal-checked] **A turn about a point closes that point and no frame:** for
`M ≠ 1` and `t = (1 − M) x₀`. -/
theorem turn_closes_pivot_not_frame {M : Module.End R V} (hM : M ≠ 1) (x₀ : V) :
    move M ((1 - M) x₀) x₀ = x₀ ∧ move M ((1 - M) x₀) ≠ id :=
  ⟨(move_fixes_iff_pivot M _ x₀).2 rfl, fun h => hM ((frame_closes_iff M _).1 h).1⟩

/-- [counterexample; formal-checked] **Translation alone is not the test** when `M ≠ 1`: a zero
translation leaves the frame open, and a nonzero translation closes some point. -/
theorem translation_is_not_the_test {M : Module.End R V} (hM : M ≠ 1) :
    move M 0 ≠ id ∧ ∃ t x : V, t ≠ 0 ∧ move M t x = x := by
  refine ⟨fun h => hM ((frame_closes_iff M 0).1 h).1, ?_⟩
  have hx : ∃ x, M x ≠ x := by
    by_contra hall
    push Not at hall
    exact hM (LinearMap.ext hall)
  obtain ⟨x, hx⟩ := hx
  refine ⟨(1 - M) x, x, ?_, (move_fixes_iff_pivot M _ x).2 rfl⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_ne_zero]
  exact hx.symm

/-- [proved-standard; formal-checked] With `M = 1` the translation decides: a based point closes iff
`t = 0`. -/
theorem flat_point_closes_iff (t x : V) : move (1 : Module.End R V) t x = x ↔ t = 0 := by
  rw [point_closes_iff, sub_self, LinearMap.zero_apply, zero_add]

/-- [proved-standard; formal-checked] **A flat holonomy closes every point or none:** with `M = 1`,
either `t = 0` and all points close, or `t ≠ 0` and none does (`Motion.translation_has_no_pivot`). -/
theorem flat_closes_all_or_none (t : V) :
    (t = 0 ∧ ∀ x, move (1 : Module.End R V) t x = x) ∨
      (t ≠ 0 ∧ ∀ x, move (1 : Module.End R V) t x ≠ x) := by
  by_cases ht : t = 0
  · exact Or.inl ⟨ht, fun x => (flat_point_closes_iff t x).2 ht⟩
  · exact Or.inr ⟨ht, translation_has_no_pivot ht⟩

/-- [proved-standard; formal-checked] **When `M − 1` is a unit one and only one point closes**, the
pivot (`Motion.pivot_unique`). -/
theorem unique_closing_point {M : Module.End R V} (h : IsUnit (M - 1)) (t : V) :
    ∃! x, move M t x = x := by
  have hu : IsUnit (1 - M) := by
    rw [← neg_sub]
    exact h.neg
  have hb := (Module.End.isUnit_iff _).1 hu
  obtain ⟨x, hx⟩ := hb.2 t
  exact ⟨x, (move_fixes_iff_pivot M t x).2 hx,
    fun y hy => pivot_unique hb.1 ((move_fixes_iff_pivot M t y).1 hy) hx⟩

end Closure

/-! ### Closure of the serial owner's charts -/

/-- [proved-derived; formal-checked] A chart's application is the Motion owner's move of its matrix and
translation. -/
theorem apply_eq_move (f : AffineMap3) :
    f.apply = Holonics.Geometry.Motion.move (Matrix.mulVecLin f.linear) f.translation := by
  funext x
  rfl

/-- [proved-derived; formal-checked] A chart closes a based point iff `(L − 1) x + t = 0`. -/
theorem chart_point_closes_iff (f : AffineMap3) (x : Vec) :
    f.apply x = x ↔ (f.linear - 1) *ᵥ x + f.translation = 0 := by
  rw [apply_eq_move, point_closes_iff, LinearMap.sub_apply, Module.End.one_apply,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]

/-- [proved-derived; formal-checked] A chart closes the whole frame iff it is the identity chart. -/
theorem chart_frame_closes_iff (f : AffineMap3) : f.apply = id ↔ f = AffineMap3.identity := by
  constructor
  · intro h
    apply apply_injective
    rw [h]
    funext x
    exact (AffineMap3.identity_apply x).symm
  · rintro rfl
    funext x
    exact AffineMap3.identity_apply x

/-- [proved-derived; formal-checked] The right-to-left reading of the triangle closes the origin and no
frame: it is the quarter turn about the `e₃` axis. -/
theorem rightToLeft_triangle_closes_origin_not_frame :
    (configuration [shiftY, quarterTurn, shiftX]).apply 0 = 0 ∧
      (configuration [shiftY, quarterTurn, shiftX]).apply ≠ id := by
  rw [rightToLeft_triangle]
  refine ⟨by simp [AffineMap3.apply], fun h => ?_⟩
  have := congrFun (congrArg AffineMap3.linear ((chart_frame_closes_iff _).1 h)) 0
  have := congrFun this 1
  simp [AffineMap3.identity] at this

/-- [proved-derived; formal-checked] The left-to-right reading of the triangle leaves the origin open and
closes `(−1, 1, 0)`: the same quarter turn about a moved axis. -/
theorem leftToRight_triangle_pivot :
    (configuration [shiftX, quarterTurn, shiftY]).apply 0 ≠ 0 ∧
      (configuration [shiftX, quarterTurn, shiftY]).apply ![-1, 1, 0] = ![-1, 1, 0] := by
  rw [leftToRight_triangle]
  constructor
  · intro h
    have := congrFun h 1
    simp [AffineMap3.apply] at this
  · ext i
    fin_cases i <;> simp [AffineMap3.apply]
    norm_num

end Holonics.Transport.MoveConventions
