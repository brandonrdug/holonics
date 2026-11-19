import Holonics.Fluid.NavierStokesCurvedTransport
import Mathlib.Geometry.Euclidean.Triangle

/-!
# The Regge deficit: a triangle's corners from its edge lengths, the deficit at a hinge, and Gauss–Bonnet

[definition] One box of #410: "Einstein: the continuum realization (Lorentzian metric, connection, a
fluid-plus-thermal constitution solving `G + Λg = κT`), the weak-field limit `R₀₀ = ∇²Φ`, and the Regge
construction (`Physics/Spacetime/Einstein`)", part done in #1032, #1034 and #1041, whose note ends "left:
perturbations, the Bianchi identity in general, the Regge construction, and homogeneity". The owner's `[open]`
paragraph reads: "The Regge construction of the discrete Einstein side, that `G` is the boundary of the moment of
rotation `F` of a simplicial metric's deficit angles (Misner–Thorne–Wheeler §15.4), is owed (#410): here the field
`F` is supplied, not built from a metric." This module starts that construction where it is elementary: a
simplicial metric's deficit angles, built from its edge lengths. Sources: the record of August 10 in
`research/records/`, `2026-08-10_THE_MANIFOLD_IS_THE_INVARIANT_OF_THE_CURRENTS_…_THE_RUNG_IS_THE_HINGE_DEFICIT`,
§8 (every simplex is flat and curvature stands on the codimension-two hinges, `deficit(h) = 2π − Σ_(t ⊇ h) θ_h(t)`,
`Σθ = π` per planar triangle is Regge's founding hypothesis, and the combinatorial charge `6 − |link(v)|` is the
shadow of the metric deficit); the null-cone record of September 24, §2 (curvature is holonomy round a cell, and the
contracted Bianchi identity is `∂² = 0` one level up, the moments of rotation of a 3-cell's faces cancelling); atlas
`ns.polygon-gauss-bonnet` (the ledger consumed below), `gr.discrete-bianchi`, `gr.route-curvature` and
`holonomy.cell-face`; Mathlib's `EuclideanGeometry.law_cos` and `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`.

**How it joins the owner.** `Physics/Spacetime/Einstein` takes the discrete Einstein side as `G = ∂₂F` with the
field `F` supplied, and nothing of it is consumed here; the module imports `Fluid/NavierStokesCurvedTransport`,
which `Einstein` imports, and Mathlib's triangle geometry. That owner's `TriangulatedGaussBonnetLedger` takes its
corner angles, each face's angle budget `π` and the Euler incidence `2χ = 2V + B − F` as supplied fields. Here the
corner angles are built from edge lengths, the budget is proved from Mathlib's angle sum and the incidence from the
surface's closure; the ledger is then built with no boundary vertex (`SimplicialMetric.toLedger`), its
`bulkCurvature` is the deficit, and Gauss–Bonnet is the ledger's own `gaussBonnet`.

[proved-standard; formal-checked] What is proved. Everything is over ℝ.

1. **A triangle's corners from its edge lengths** (`IsTriangle`, `IsTriangle.pos`, `IsTriangle.rotate`,
   `cornerAngle`, `cornerAngle_comm`, `cornerAngle_pos`, `cornerAngle_lt_pi`, `angle_eq_cornerAngle`,
   `triangle_exists`, `cornerAngle_add`, `cornerAngle_equilateral`). For `a, b, c` with the three strict triangle
   inequalities (which force `a, b, c > 0`), the corner opposite `a` is `arccos((b² + c² − a²)/(2bc))`, in `(0, π)`.
   In any Euclidean affine space it is the angle of every triangle with those sides (the law of cosines); such a
   triangle stands in the plane `ℂ`; so the three corners sum to `π` (Mathlib's angle sum). The equilateral
   triangle's corners are `π/3`.
2. **The deficit and discrete Gauss–Bonnet** (`sideOf`, `ClosedSurface`, `ClosedSurface.edges`,
   `ClosedSurface.eulerChar`, `ClosedSurface.two_mul_card_edges`, `SimplicialMetric`, `SimplicialMetric.angleAt`,
   `SimplicialMetric.angleAt_sum`, `SimplicialMetric.sum_angleAt`, `SimplicialMetric.deficit`,
   `SimplicialMetric.reggeAction`, `SimplicialMetric.gauss_bonnet`, `regge_action_two_invariant`). A closed
   triangulated surface is a finite set of triangles, each with three distinct ordered corners, the side opposite a
   corner the unordered pair of the other two, and every side met by exactly two (triangle, corner) slots; its edges
   are the sides, and `2E = 3F`. A simplicial metric is a length on each edge with the triangle inequalities in each
   triangle. The deficit at a vertex is `ε_v = 2π − Σ` of the corners at `v`. Then the corners sum to `πF` and
   `Σ_v ε_v = 2π(V − E + F)`, so the two-dimensional Regge action `Σ_v ε_v` is the same for every length assignment
   on one surface: the discrete form of the two-dimensional Einstein tensor vanishing identically.
   [proved-derived; formal-checked] The join: the built corners, budget and incidence are the owner's ledger
   (`SimplicialMetric.toLedger`), whose bulk curvature is the deficit (`SimplicialMetric.deficit_eq_bulkCurvature`).
3. **Witnesses** (`unitMetric`, `unitMetric_angleAt`, `ClosedSurface.degree`, `unitMetric_deficit`,
   `sum_six_sub_degree`, `tetraCorner`, `tetrahedron`, `tetrahedron_eulerChar`, `tetrahedron_deficit`,
   `tetrahedron_total`, `octaCorner`, `octahedron`, `octahedron_eulerChar`, `octahedron_deficit`, `octahedron_total`,
   `one_lt_sqrt_two`, `sqrt_two_lt_two`, `cubeCorner`, `cornerAngle_sqrt_two_one_one`, `cornerAngle_one_one_sqrt_two`,
   `cubeCorner_deficit_zero`, `cubeCorner_deficit_base`, `cubeCorner_witness`). With every length equal the deficit
   is `(π/3)(6 − deg v)`, `deg v` the count of corners at `v`: the record's combinatorial charge `6 − |link(v)|`
   times `π/3`, where the link is one cycle, and `Σ_v (6 − deg v) = 6χ`. The boundary
   of the tetrahedron at unit lengths has every deficit `π` and total `4π = 2π·2`; the octahedron has every deficit
   `2π/3` and total `4π = 2π·2`. The cube's corner, the tetrahedron with unit edges at the apex `0` and `√2` on the
   opposite triangle, has deficit `π/2` at the apex and `7π/6` at the other three vertices, and total `4π`, the unit
   tetrahedron's.
4. **The three-dimensional hinge** (`linkAngle`, `dihedralAngle`, `dihedralAngle_regular`, `hingeSlot`,
   `TetraComplex`, `TetraComplex.hingeOf`, `TetraComplex.hinges`, `TetraComplex.dihedralAt`,
   `TetraComplex.hingeDeficit`, `TetraComplex.reggeAction`, `regularTetra`, `regularTetra_dihedralAt`,
   `regularTetra_hingeDeficit`, `regularTetra_reggeAction`). In three dimensions the hinges are edges. [definition]
   The dihedral angle of a tetrahedron at its edge `ij` is read on the link of `i` by the spherical law of cosines,
   `arccos((cos θ₃ − cos θ₁ cos θ₂)/(sin θ₁ sin θ₂))`, with `θ₁`, `θ₂` the corners at `i` of the faces `ijk`, `ijl`
   and `θ₃` that of `ikl`, each built from the lengths; the deficit at an edge is `ε_e = 2π − Σ_σ θ_σ(e)` over the
   tetrahedra `σ` at `e`, and the Regge action is `Σ_e ℓ_e ε_e`. [proved-standard; formal-checked] The regular
   tetrahedron of any edge `a > 0` has dihedral angle `arccos(1/3)` at every edge; one regular tetrahedron alone has
   deficit `2π − arccos(1/3)` at each of its six hinges and action `6a(2π − arccos(1/3))`.

What is not claimed. The moment of rotation of the deficits and `G` as its boundary in four dimensions
(Misner–Thorne–Wheeler §15.4) are not built, so the owner's sentence "here the field `F` is supplied, not built
from a metric" stands. Schläfli's identity (`Σ_e ℓ_e dθ_σ(e) = 0` over one tetrahedron) and Regge's field equations
`∂S/∂ℓ_e = ε_e` that follow from it are not stated. That `dihedralAngle` is the angle between the two faces of a
realized Euclidean tetrahedron, that it reads the same on the link of `j`, and when six lengths are realizable (the
Cayley–Menger conditions) are not proved; `TetraComplex` asks no realizability and no condition on its hinges'
links. `ClosedSurface` asks each side to be met by two slots; that each vertex's link is one cycle, and
orientability, are not asked, and Gauss–Bonnet does not use them. The reading of a deficit as the holonomy of its
hinge's star is a reading, not proved here. The continuum limit (deficits converging to a curvature density),
Lorentzian signature, and the box's perturbations, general Bianchi identity and homogeneity are not touched.

The computational object is the helical pair interaction, read on the triangulated surface. An edge is a pair
contact: the closure `two_sided` meets each side from exactly two triangles, so the `3F` corner slots are paired
two by two through their sides (a fixed-point-free pairing, as in the helical code; the involution itself is not
built here), and `2E = 3F` is that pairing's count. A corner angle is the turn taken at one corner, and the deficit
is the turn left over when the corners round a vertex are composed, read as the holonomy of the vertex's star
(`gr.route-curvature`, `holonomy.cell-face`); its total `2πχ` is fixed by the incidence alone. Of the winding guide's
six general objects it touches the pair (the edge as the two-triangle contact), faces and placement (each corner
placed at its vertex, the sums regrouped by the fibres of the corner map, the ledger's face budget) and cell holonomy
(the deficit at a hinge, `Σ_v ε_v = 2πχ`); the helix (the total `2πχ` is `χ` whole turns), the tube and the tower
thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

open Real EuclideanGeometry Finset

namespace Holonics.Physics.Spacetime.ReggeDeficit

/-! ## 1. A triangle's corners from its edge lengths -/

/-- [definition] **The strict triangle inequalities** on three lengths. -/
def IsTriangle (a b c : ℝ) : Prop := a < b + c ∧ b < c + a ∧ c < a + b

namespace IsTriangle

variable {a b c : ℝ}

/-- [proved-standard; formal-checked] The triangle inequalities force a positive length. -/
theorem pos (h : IsTriangle a b c) : 0 < a := by linarith [h.2.1, h.2.2]

/-- [proved-standard; formal-checked] The triangle inequalities are cyclic. -/
theorem rotate (h : IsTriangle a b c) : IsTriangle b c a := ⟨h.2.1, h.2.2, h.1⟩

end IsTriangle

/-- [definition] **The corner opposite the side `a`** of a triangle with sides `a, b, c`, from its lengths alone. -/
def cornerAngle (a b c : ℝ) : ℝ := arccos ((b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c))

/-- [proved-standard; formal-checked] The corner does not depend on the order of its two adjacent sides. -/
theorem cornerAngle_comm (a b c : ℝ) : cornerAngle a b c = cornerAngle a c b := by
  unfold cornerAngle; ring_nf

/-- [proved-standard; formal-checked] A corner of a nondegenerate triangle is positive. -/
theorem cornerAngle_pos {a b c : ℝ} (h : IsTriangle a b c) : 0 < cornerAngle a b c := by
  have hb := h.rotate.pos
  have hc := h.rotate.rotate.pos
  rw [cornerAngle, arccos_pos, div_lt_one (by positivity)]
  nlinarith [mul_pos (sub_pos.2 h.2.1) (sub_pos.2 h.2.2)]

/-- [proved-standard; formal-checked] A corner of a nondegenerate triangle is less than `π`. -/
theorem cornerAngle_lt_pi {a b c : ℝ} (h : IsTriangle a b c) : cornerAngle a b c < π := by
  have ha := h.pos
  have hb := h.rotate.pos
  have hc := h.rotate.rotate.pos
  rw [cornerAngle, arccos_lt_pi, lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos (sub_pos.2 h.1) (add_pos (add_pos ha hb) hc)]

/-- [proved-standard; formal-checked] **The law of cosines**: in any Euclidean affine space the angle at `p₂` is the
corner built from the three distances. -/
theorem angle_eq_cornerAngle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {p₁ p₂ p₃ : P} (h₁ : p₁ ≠ p₂) (h₃ : p₃ ≠ p₂) :
    ∠ p₁ p₂ p₃ = cornerAngle (dist p₁ p₃) (dist p₁ p₂) (dist p₃ p₂) := by
  have hlaw := law_cos p₁ p₂ p₃
  have hb : 0 < dist p₁ p₂ := dist_pos.2 h₁
  have hc : 0 < dist p₃ p₂ := dist_pos.2 h₃
  refine (arccos_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _)).symm.trans ?_
  rw [cornerAngle]
  congr 1
  rw [eq_div_iff (by positivity)]
  linear_combination hlaw

/-- [proved-standard; formal-checked] **A triangle with given sides stands in the plane**: three points of `ℂ` at
the distances `a, b, c`. -/
theorem triangle_exists {a b c : ℝ} (h : IsTriangle a b c) :
    ∃ p₁ p₂ p₃ : ℂ, dist p₂ p₃ = a ∧ dist p₁ p₃ = b ∧ dist p₁ p₂ = c := by
  have ha := h.pos
  have hb := h.rotate.pos
  have hc := h.rotate.rotate.pos
  set x := (b ^ 2 + c ^ 2 - a ^ 2) / (2 * c) with hx
  have hx1 : x < b := by
    rw [hx, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.2 h.2.1) (sub_pos.2 h.2.2)]
  have hx2 : -b < x := by
    rw [hx, lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.2 h.1) (add_pos (add_pos ha hb) hc)]
  have hy : (√(b ^ 2 - x ^ 2)) ^ 2 = b ^ 2 - x ^ 2 := sq_sqrt (by nlinarith)
  refine ⟨0, c, ⟨x, √(b ^ 2 - x ^ 2)⟩, ?_, ?_, ?_⟩
  · rw [Complex.dist_eq_re_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [show (c - x) ^ 2 + (0 - √(b ^ 2 - x ^ 2)) ^ 2 = a ^ 2 by
      rw [show (0 - √(b ^ 2 - x ^ 2)) ^ 2 = √(b ^ 2 - x ^ 2) ^ 2 by ring, hy, hx]
      field_simp
      ring]
    exact sqrt_sq ha.le
  · rw [Complex.dist_eq_re_im]
    simp only [Complex.zero_re, Complex.zero_im]
    rw [show (0 - x) ^ 2 + (0 - √(b ^ 2 - x ^ 2)) ^ 2 = b ^ 2 by
      rw [show (0 - √(b ^ 2 - x ^ 2)) ^ 2 = √(b ^ 2 - x ^ 2) ^ 2 by ring, hy]
      ring]
    exact sqrt_sq hb.le
  · rw [Complex.dist_eq_re_im]
    simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [show (0 - c) ^ 2 + (0 - 0) ^ 2 = c ^ 2 by ring]
    exact sqrt_sq hc.le

/-- [proved-standard; formal-checked] **The corners built from the lengths sum to `π`**, through a realized
triangle and Mathlib's angle sum. -/
theorem cornerAngle_add {a b c : ℝ} (h : IsTriangle a b c) :
    cornerAngle a b c + cornerAngle b c a + cornerAngle c a b = π := by
  obtain ⟨p₁, p₂, p₃, hA, hB, hC⟩ := triangle_exists h
  have ha := h.pos
  have hb := h.rotate.pos
  have hc := h.rotate.rotate.pos
  have h21 : p₂ ≠ p₁ := fun e => by rw [e, dist_self] at hC; linarith
  have h31 : p₃ ≠ p₁ := fun e => by rw [e, dist_self] at hB; linarith
  have h32 : p₃ ≠ p₂ := fun e => by rw [e, dist_self] at hA; linarith
  have hsum := angle_add_angle_add_angle_eq_pi p₃ h21
  rw [angle_eq_cornerAngle h21.symm h32, angle_eq_cornerAngle h32.symm h31.symm,
    angle_eq_cornerAngle h31 h21] at hsum
  rw [dist_comm p₃ p₂, dist_comm p₂ p₁, dist_comm p₃ p₁, hA, hB, hC] at hsum
  linarith

/-- [proved-standard; formal-checked] **The equilateral triangle's corners are `π/3`.** -/
theorem cornerAngle_equilateral {a : ℝ} (ha : 0 < a) : cornerAngle a a a = π / 3 := by
  rw [cornerAngle, show (a ^ 2 + a ^ 2 - a ^ 2) / (2 * a * a) = 1 / 2 by field_simp; ring,
    ← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

/-! ## 2. The deficit at a vertex and discrete Gauss–Bonnet -/

section Surface

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F]

/-- [definition] **The side opposite a corner**: the unordered pair of the triangle's other two corners. -/
def sideOf (corner : F → Fin 3 → V) (p : F × Fin 3) : Sym2 V :=
  s(corner p.1 (p.2 + 1), corner p.1 (p.2 + 2))

/-- [definition] **A closed triangulated surface**: triangles with three distinct ordered corners, every side met
by exactly two (triangle, corner) slots. -/
structure ClosedSurface (V F : Type*) [Fintype V] [DecidableEq V] [Fintype F] where
  /-- The corners of each triangle. -/
  corner : F → Fin 3 → V
  /-- A triangle's three corners are distinct. -/
  corner_injective : ∀ t, Function.Injective (corner t)
  /-- Every side is shared by exactly two triangle slots: the surface is closed. -/
  two_sided : ∀ p : F × Fin 3, #{q | sideOf corner q = sideOf corner p} = 2

namespace ClosedSurface

variable (S : ClosedSurface V F)

/-- [definition] The edges: the sides of the triangles. -/
def edges : Finset (Sym2 V) := univ.image (sideOf S.corner)

/-- [definition] The Euler characteristic `V − E + F`. -/
def eulerChar : ℤ := Fintype.card V - #S.edges + Fintype.card F

/-- [definition] The degree of a vertex: the count of corners standing at it. -/
def degree (v : V) : ℕ := #{p : F × Fin 3 | S.corner p.1 p.2 = v}

/-- [proved-standard; formal-checked] **`2E = 3F`**: each edge is two of the `3F` corner slots' sides. -/
theorem two_mul_card_edges : 2 * #S.edges = 3 * Fintype.card F := by
  have h := card_eq_sum_card_image (sideOf S.corner) (univ : Finset (F × Fin 3))
  rw [sum_congr rfl (g := fun _ => 2) (fun e he => by
    obtain ⟨p, -, rfl⟩ := mem_image.1 he
    exact S.two_sided p)] at h
  rw [sum_const, smul_eq_mul, card_univ, Fintype.card_prod, Fintype.card_fin] at h
  rw [edges]; linarith

end ClosedSurface

/-- [definition] **A simplicial metric**: a length on each edge, with the triangle inequalities in each
triangle. -/
structure SimplicialMetric (S : ClosedSurface V F) where
  /-- The length of each edge. -/
  length : Sym2 V → ℝ
  /-- Each triangle satisfies the strict triangle inequalities. -/
  triangle : ∀ t, IsTriangle (length (sideOf S.corner (t, 0))) (length (sideOf S.corner (t, 1)))
    (length (sideOf S.corner (t, 2)))

namespace SimplicialMetric

variable {S : ClosedSurface V F} (m : SimplicialMetric S)

/-- [definition] **The corner angle at a slot**, opposite the slot's side, built from the triangle's lengths. -/
def angleAt (p : F × Fin 3) : ℝ :=
  cornerAngle (m.length (sideOf S.corner p)) (m.length (sideOf S.corner (p.1, p.2 + 1)))
    (m.length (sideOf S.corner (p.1, p.2 + 2)))

/-- [proved-standard; formal-checked] **Each triangle's corners sum to `π`.** -/
theorem angleAt_sum (t : F) : ∑ i, m.angleAt (t, i) = π := by
  have h := cornerAngle_add (m.triangle t)
  simp only [Fin.sum_univ_three, angleAt]
  simpa using h

/-- [proved-standard; formal-checked] **All the corners sum to `πF`.** -/
theorem sum_angleAt : ∑ p, m.angleAt p = π * Fintype.card F := by
  rw [Fintype.sum_prod_type]
  simp only [m.angleAt_sum, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- [definition] **The deficit at a vertex**: `ε_v = 2π − Σ` of the corners standing at `v`. -/
def deficit (v : V) : ℝ := 2 * π - ∑ p with S.corner p.1 p.2 = v, m.angleAt p

/-- [definition] **The two-dimensional Regge action** `Σ_v ε_v`: a hinge is a vertex, of unit content. -/
def reggeAction : ℝ := ∑ v, m.deficit v

open Holonics.Fluid.NavierStokesCurvedTransport in
/-- [definition] **The owner's Gauss–Bonnet ledger, built**: corners from the lengths, no boundary vertex, the
face budget from the angle sum and the Euler incidence from `2E = 3F`. -/
def toLedger : TriangulatedGaussBonnetLedger V Empty F where
  cornerAngle := Sum.elim (fun v t => ∑ i with S.corner t i = v, m.angleAt (t, i)) (fun b => b.elim)
  eulerCharacteristic := S.eulerChar
  faceAngleBudget t := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, univ_eq_empty, sum_empty, add_zero]
    rw [sum_fiberwise univ (S.corner t) (fun i => m.angleAt (t, i))]
    exact m.angleAt_sum t
  combinatorialCount := by
    have h := S.two_mul_card_edges
    simp only [ClosedSurface.eulerChar, Fintype.card_empty, Nat.cast_zero, add_zero]
    push_cast
    have h' : (2 : ℝ) * #S.edges = 3 * Fintype.card F := by exact_mod_cast h
    linarith

open Holonics.Fluid.NavierStokesCurvedTransport in
/-- [proved-derived; formal-checked] **The deficit is the built ledger's bulk curvature.** -/
theorem deficit_eq_bulkCurvature (v : V) : m.deficit v = m.toLedger.bulkCurvature v := by
  simp only [deficit, TriangulatedGaussBonnetLedger.bulkCurvature, toLedger, Sum.elim_inl, sum_filter,
    Fintype.sum_prod_type]

/-- [proved-standard; formal-checked] **Discrete Gauss–Bonnet**: `Σ_v ε_v = 2π(V − E + F)`, through the owner's
`gaussBonnet`. -/
theorem gauss_bonnet : ∑ v, m.deficit v = 2 * π * S.eulerChar := by
  have h := m.toLedger.gaussBonnet
  simp only [univ_eq_empty, sum_empty, add_zero] at h
  simp only [deficit_eq_bulkCurvature]
  exact h

end SimplicialMetric

/-- [proved-standard; formal-checked] **The two-dimensional Regge action does not depend on the lengths**: any
two simplicial metrics on one surface have the same total deficit. -/
theorem regge_action_two_invariant {S : ClosedSurface V F} (m m' : SimplicialMetric S) :
    m.reggeAction = m'.reggeAction := by
  rw [SimplicialMetric.reggeAction, SimplicialMetric.reggeAction, m.gauss_bonnet, m'.gauss_bonnet]

/-! ## 3. Witnesses -/

/-- [definition] Every edge of length `1`. -/
def unitMetric (S : ClosedSurface V F) : SimplicialMetric S where
  length _ := 1
  triangle _ := ⟨by norm_num, by norm_num, by norm_num⟩

/-- [proved-standard; formal-checked] At unit lengths every corner is `π/3`. -/
theorem unitMetric_angleAt (S : ClosedSurface V F) (p : F × Fin 3) : (unitMetric S).angleAt p = π / 3 :=
  cornerAngle_equilateral one_pos

/-- [proved-standard; formal-checked] **At unit lengths the deficit is the combinatorial charge**:
`ε_v = (π/3)(6 − deg v)`. -/
theorem unitMetric_deficit (S : ClosedSurface V F) (v : V) :
    (unitMetric S).deficit v = π / 3 * (6 - S.degree v) := by
  rw [SimplicialMetric.deficit]
  simp only [unitMetric_angleAt, sum_const, nsmul_eq_mul]
  rw [ClosedSurface.degree]
  ring

/-- [proved-standard; formal-checked] **The combinatorial charge totals `6χ`**: `Σ_v (6 − deg v) = 6(V − E + F)`,
Gauss–Bonnet at unit lengths. -/
theorem sum_six_sub_degree (S : ClosedSurface V F) : ∑ v, (6 - (S.degree v : ℤ)) = 6 * S.eulerChar := by
  have h := (unitMetric S).gauss_bonnet
  simp only [unitMetric_deficit, ← mul_sum] at h
  have h' : ∑ v, (6 - (S.degree v : ℝ)) = 6 * S.eulerChar := by
    have hπ : π ≠ 0 := pi_ne_zero
    have h3 : π / 3 * ∑ v, (6 - (S.degree v : ℝ)) = π / 3 * (6 * S.eulerChar) := by rw [h]; ring
    exact mul_left_cancel₀ (div_ne_zero hπ three_ne_zero) h3
  exact_mod_cast h'

end Surface

section Witnesses

/-- [definition] The tetrahedron's triangles: triangle `t` has the corners other than `t`. -/
def tetraCorner : Fin 4 → Fin 3 → Fin 4 := ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

/-- [definition] **The boundary of the tetrahedron** as a closed surface. -/
def tetrahedron : ClosedSurface (Fin 4) (Fin 4) where
  corner := tetraCorner
  corner_injective := by decide
  two_sided := by decide

/-- [proved-standard; formal-checked] The tetrahedron has `χ = 4 − 6 + 4 = 2`. -/
theorem tetrahedron_eulerChar : tetrahedron.eulerChar = 2 := by
  have h : #tetrahedron.edges = 6 := by decide
  simp [ClosedSurface.eulerChar, h]

/-- [proved-standard; formal-checked] **At unit lengths every deficit of the tetrahedron is `π`.** -/
theorem tetrahedron_deficit (v : Fin 4) : (unitMetric tetrahedron).deficit v = π := by
  have h : ∀ v : Fin 4, tetrahedron.degree v = 3 := by decide
  rw [unitMetric_deficit, h]
  ring

/-- [proved-standard; formal-checked] **The unit tetrahedron's total deficit is `4π = 2π·χ`.** -/
theorem tetrahedron_total :
    ∑ v, (unitMetric tetrahedron).deficit v = 4 * π ∧
      ∑ v, (unitMetric tetrahedron).deficit v = 2 * π * tetrahedron.eulerChar := by
  refine ⟨?_, SimplicialMetric.gauss_bonnet _⟩
  simp only [tetrahedron_deficit, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- [definition] The octahedron's triangles: one of `{0, 1}`, `{2, 3}`, `{4, 5}` each (the poles `±x`, `±y`,
`±z`). -/
def octaCorner : Fin 8 → Fin 3 → Fin 6 :=
  ![![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5]]

/-- [definition] **The boundary of the octahedron** as a closed surface. -/
def octahedron : ClosedSurface (Fin 6) (Fin 8) where
  corner := octaCorner
  corner_injective := by decide
  two_sided := by decide

/-- [proved-standard; formal-checked] The octahedron has `χ = 6 − 12 + 8 = 2`. -/
theorem octahedron_eulerChar : octahedron.eulerChar = 2 := by
  have h : #octahedron.edges = 12 := by decide
  simp [ClosedSurface.eulerChar, h]

/-- [proved-standard; formal-checked] **At unit lengths every deficit of the octahedron is `2π/3`.** -/
theorem octahedron_deficit (v : Fin 6) : (unitMetric octahedron).deficit v = 2 * π / 3 := by
  have h : ∀ v : Fin 6, octahedron.degree v = 4 := by decide
  rw [unitMetric_deficit, h]
  ring

/-- [proved-standard; formal-checked] **The unit octahedron's total deficit is `4π = 2π·χ`.** -/
theorem octahedron_total :
    ∑ v, (unitMetric octahedron).deficit v = 4 * π ∧
      ∑ v, (unitMetric octahedron).deficit v = 2 * π * octahedron.eulerChar := by
  refine ⟨?_, SimplicialMetric.gauss_bonnet _⟩
  simp only [octahedron_deficit, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- [proved-standard; formal-checked] `1 < √2`. -/
theorem one_lt_sqrt_two : 1 < √2 := by
  rw [show (1 : ℝ) = √1 by simp]; exact sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- [proved-standard; formal-checked] `√2 < 2`. -/
theorem sqrt_two_lt_two : √2 < 2 := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
  exact sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- [definition] **The cube's corner**: the tetrahedron with unit edges at the apex `0` and `√2` on the opposite
triangle. -/
def cubeCorner : SimplicialMetric tetrahedron where
  length e := if (0 : Fin 4) ∈ e then 1 else √2
  triangle t := by
    have h1 := one_lt_sqrt_two
    have h2 := sqrt_two_lt_two
    fin_cases t <;> simp [sideOf, tetrahedron, tetraCorner, IsTriangle] <;> linarith

/-- [proved-standard; formal-checked] The right corner of the isosceles right triangle: `π/2`. -/
theorem cornerAngle_sqrt_two_one_one : cornerAngle (√2) 1 1 = π / 2 := by
  rw [cornerAngle, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- [proved-standard; formal-checked] A base corner of the isosceles right triangle: `π/4`. -/
theorem cornerAngle_one_one_sqrt_two : cornerAngle 1 1 (√2) = π / 4 := by
  have hs : (0 : ℝ) < √2 := by positivity
  rw [cornerAngle, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    show ((1 : ℝ) ^ 2 + 2 - 1 ^ 2) / (2 * 1 * √2) = √2 / 2 by
      field_simp; rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring,
    ← cos_pi_div_four, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- [proved-standard; formal-checked] The cube corner's apex has deficit `2π − 3·π/2 = π/2`. -/
theorem cubeCorner_deficit_zero : cubeCorner.deficit 0 = π / 2 := by
  rw [SimplicialMetric.deficit, sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_four, Fin.sum_univ_three, tetrahedron, tetraCorner, SimplicialMetric.angleAt, sideOf,
    cubeCorner, cornerAngle_sqrt_two_one_one]
  ring

/-- [proved-standard; formal-checked] The cube corner's other vertices have deficit `2π − (π/3 + 2·π/4) = 7π/6`. -/
theorem cubeCorner_deficit_base {v : Fin 4} (hv : v ≠ 0) : cubeCorner.deficit v = 7 * π / 6 := by
  have hs : (0 : ℝ) < √2 := by positivity
  rw [SimplicialMetric.deficit, sum_filter, Fintype.sum_prod_type]
  fin_cases v
  · exact absurd rfl hv
  all_goals
    simp [Fin.sum_univ_four, Fin.sum_univ_three, tetrahedron, tetraCorner, SimplicialMetric.angleAt, sideOf,
      cubeCorner, cornerAngle_equilateral hs, cornerAngle_one_one_sqrt_two, cornerAngle_comm 1 (√2) 1]
    ring

/-- [proved-standard; formal-checked] **The deficits move, their total does not**: the cube corner's deficits are
`π/2` and `7π/6`, unequal, and they total `4π`, the unit tetrahedron's Regge action. -/
theorem cubeCorner_witness :
    cubeCorner.deficit 0 = π / 2 ∧ (∀ v, v ≠ 0 → cubeCorner.deficit v = 7 * π / 6) ∧
      cubeCorner.deficit 0 ≠ cubeCorner.deficit 1 ∧ cubeCorner.reggeAction = 4 * π ∧
      cubeCorner.reggeAction = (unitMetric tetrahedron).reggeAction := by
  refine ⟨cubeCorner_deficit_zero, fun v hv => cubeCorner_deficit_base hv, ?_, ?_,
    regge_action_two_invariant _ _⟩
  · rw [cubeCorner_deficit_zero, cubeCorner_deficit_base (by decide)]
    intro h; linarith [pi_pos]
  · rw [SimplicialMetric.reggeAction, SimplicialMetric.gauss_bonnet, tetrahedron_eulerChar]
    push_cast; ring

end Witnesses

/-! ## 4. The three-dimensional hinge -/

section Hinge

/-- [definition] **The angle of a spherical triangle** at the vertex where the sides `θ₁`, `θ₂` meet, with `θ₃`
opposite (the spherical law of cosines). -/
def linkAngle (θ₁ θ₂ θ₃ : ℝ) : ℝ := arccos ((cos θ₃ - cos θ₁ * cos θ₂) / (sin θ₁ * sin θ₂))

/-- [definition] **The dihedral angle of a tetrahedron at its edge `ij`**, read on the link of `i` (`k`, `l` the
other two vertices), with every corner built from the lengths `L`. -/
def dihedralAngle (L : Fin 4 → Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  linkAngle (cornerAngle (L j k) (L i j) (L i k)) (cornerAngle (L j l) (L i j) (L i l))
    (cornerAngle (L k l) (L i k) (L i l))

/-- [proved-standard; formal-checked] **The regular tetrahedron's dihedral angle is `arccos(1/3)`** at every
edge, for every edge length `a > 0`. -/
theorem dihedralAngle_regular {a : ℝ} (ha : 0 < a) (i j k l : Fin 4) :
    dihedralAngle (fun _ _ => a) i j k l = arccos (1 / 3) := by
  rw [dihedralAngle, linkAngle, cornerAngle_equilateral ha, cos_pi_div_three, sin_pi_div_three]
  congr 1
  have h3 : √3 * √3 = 3 := mul_self_sqrt (by norm_num)
  rw [show √3 / 2 * (√3 / 2) = 3 / 4 by rw [div_mul_div_comm, h3]; norm_num]
  norm_num

/-- [definition] The six edges of a tetrahedron, each as `(i, j, k, l)`: the edge `ij` and the other two
vertices. -/
def hingeSlot : Fin 6 → Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
  ![(0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2), (1, 2, 0, 3), (1, 3, 0, 2), (2, 3, 0, 1)]

/-- [definition] **A three-dimensional simplicial complex**: tetrahedra with four distinct ordered vertices. -/
structure TetraComplex (V T : Type*) [Fintype V] [DecidableEq V] [Fintype T] where
  /-- The vertices of each tetrahedron. -/
  vertex : T → Fin 4 → V
  /-- A tetrahedron's four vertices are distinct. -/
  vertex_injective : ∀ σ, Function.Injective (vertex σ)

namespace TetraComplex

variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T] (K : TetraComplex V T)

/-- [definition] The hinge of a (tetrahedron, edge) slot: the edge as an unordered pair of vertices. -/
def hingeOf (p : T × Fin 6) : Sym2 V :=
  s(K.vertex p.1 (hingeSlot p.2).1, K.vertex p.1 (hingeSlot p.2).2.1)

/-- [definition] The hinges: the edges of the tetrahedra. -/
def hinges : Finset (Sym2 V) := univ.image K.hingeOf

/-- [definition] The dihedral angle at a slot, from the lengths of its tetrahedron's edges. -/
def dihedralAt (length : Sym2 V → ℝ) (p : T × Fin 6) : ℝ :=
  dihedralAngle (fun a b => length s(K.vertex p.1 a, K.vertex p.1 b)) (hingeSlot p.2).1
    (hingeSlot p.2).2.1 (hingeSlot p.2).2.2.1 (hingeSlot p.2).2.2.2

/-- [definition] **The deficit at a hinge**: `ε_e = 2π − Σ_σ θ_σ(e)` over the tetrahedra at `e`. -/
def hingeDeficit (length : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  2 * π - ∑ p with K.hingeOf p = e, K.dihedralAt length p

/-- [definition] **The three-dimensional Regge action** `Σ_e ℓ_e ε_e`. -/
def reggeAction (length : Sym2 V → ℝ) : ℝ := ∑ e ∈ K.hinges, length e * K.hingeDeficit length e

end TetraComplex

/-- [definition] One tetrahedron alone. -/
def regularTetra : TetraComplex (Fin 4) (Fin 1) where
  vertex _ := id
  vertex_injective _ := Function.injective_id

/-- [proved-standard; formal-checked] At edge length `a > 0` every dihedral angle of the tetrahedron is
`arccos(1/3)`. -/
theorem regularTetra_dihedralAt {a : ℝ} (ha : 0 < a) (p : Fin 1 × Fin 6) :
    regularTetra.dihedralAt (fun _ => a) p = arccos (1 / 3) :=
  dihedralAngle_regular ha _ _ _ _

/-- [proved-standard; formal-checked] **One regular tetrahedron has deficit `2π − arccos(1/3)` at each hinge.** -/
theorem regularTetra_hingeDeficit {a : ℝ} (ha : 0 < a) {e : Sym2 (Fin 4)} (he : e ∈ regularTetra.hinges) :
    regularTetra.hingeDeficit (fun _ => a) e = 2 * π - arccos (1 / 3) := by
  have hone : ∀ p : Fin 1 × Fin 6, #{q | regularTetra.hingeOf q = regularTetra.hingeOf p} = 1 := by decide
  obtain ⟨p, -, rfl⟩ := mem_image.1 he
  rw [TetraComplex.hingeDeficit]
  simp only [regularTetra_dihedralAt ha, sum_const, nsmul_eq_mul, hone]
  ring

/-- [proved-standard; formal-checked] **Its Regge action is `6a(2π − arccos(1/3))`.** -/
theorem regularTetra_reggeAction {a : ℝ} (ha : 0 < a) :
    regularTetra.reggeAction (fun _ => a) = 6 * a * (2 * π - arccos (1 / 3)) := by
  have h6 : #regularTetra.hinges = 6 := by decide
  rw [TetraComplex.reggeAction, sum_congr rfl (fun e he => by rw [regularTetra_hingeDeficit ha he]),
    sum_const, h6, nsmul_eq_mul]
  ring

end Hinge

end Holonics.Physics.Spacetime.ReggeDeficit
