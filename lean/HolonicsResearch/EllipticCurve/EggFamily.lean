import Mathlib
import HolonicsResearch.EllipticCurve.EggSource
import HolonicsResearch.Geometry.CompleteEllipticSeries

/-!
# The egg as an elliptic family: Hügelschäffer's cubic is a twisted Legendre curve

Source: #410's box "The egg as an elliptic family" (the egg cubic equals the twisted Legendre form with
`λ = ((a − w)/(a + w))² = k⁻⁴`; its real components and degenerate fibres at `β = 0, 1`; rational eggs as elliptic
curves over `ℚ`; null monodromy and logarithmic period at the neck), from
`research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md` §§1–3 and its
"Obligations", with the scope correction of
`research/records/2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md` §4.
Atlas rows: `egg.legendre-j`, `egg.arithmetic-two-torsion`, `egg.actual-point-descent`,
`egg.affine-inverse-and-infinity-carriers`, `egg.period-coefficients`. Owners consumed: `Geometry/EggModular`
(`legendreJ`, `eggLambda`; its `egg_to_fullTwoTorsion` is the rational transport), `EllipticCurve/EggSource`
(`eggPoint`, `secondInfinityCarrier`, `rootA`, `rootB`), `EllipticCurve/GeneralFace` (`E`) and
`Geometry/CompleteEllipticSeries` (`ellipticK`).

[definition] The egg, for radii `a, b` and displacement `w`, is `(a² + w² + 2wx) y² = b²(a² − x²)` (`eggEq`). With
`u = 2wx + a² + w²` (`eggU`), `A = (a − w)²`, `B = (a + w)²` (`branchA`, `branchB`) and `Y = u y` it is carried onto
`Y² = −(b²/4w²) u (u − A)(u − B)` (`twistEq`, `eggTwist`, `legendreCubic`).

[proved-derived; formal-checked] What is proved. The classical inputs (the cubic's discriminant, Euler's relation,
the real topology, `K`'s logarithmic asymptotic) are tagged `[proved-standard; formal-checked]` at their theorems.

1. **The identity** (§1). In any field, `4w² (u y)² + b² u (u − A)(u − B) = 4w² u (u y² − b²(a² − x²))`
   (`egg_twist_polynomial_identity`, `eggTwist_mul_legendreCubic`). So for `w ≠ 0` (and `2 ≠ 0`) the egg lands on
   the twisted Legendre curve (`twistEq_of_eggEq`), and for `u ≠ 0` the two equations are equivalent
   (`eggEq_iff_twistEq`); on the asymptote `u = 0` the image `(0, 0)` lies on the twisted curve for every `y`
   (`eggEq_on_asymptote`). `x ↦ u` is inverted by `u ↦ (u − a² − w²)/(2w)` (`eggU_inverse`), and the transport is a
   bijection between the two curves' points off `u = 0` (`eggTwistEquiv`).
2. **The twist** (§1). `Y² = d u (u − A)(u − B)` is the monic cubic with roots `0, dA, dB` read at `(du, dY)`
   (`twistEq_iff_scaled`). The egg's `d = −b²/(4w²)` is `−(b/(2w))²` (`eggTwist_eq_neg_sq`), so over the base field
   `(u, Y) ↦ (−u, (2w/b) Y)` carries the egg's twist to the twist by `−1`, `V² = X (X + A)(X + B)`
   (`eggTwist_iff_minusOne`).
3. **The modulus** (§1). `λ = A/B = ((a − w)/(a + w))² = ((1 − β)/(1 + β))²` with `β = w/a` (`branch_ratio`,
   `branch_ratio_beta`), `= k⁻⁴` with `k² = (1 + β)/(1 − β)` (`lambda_eq_inv_kSq_sq`; on `ℝ` with
   `k = √((1 + β)/(1 − β))` and `λ = EggModular.eggLambda β`, `branch_ratio_eq_inv_k_pow_four`), and
   `1 − λ = 4aw/(a + w)²` (`one_sub_branch_ratio`). In the rapidity chart `β = tanh χ`: `k² = e^(2χ)` (`kSq_tanh`),
   `k = e^χ`, `λ = e^(−4χ)` and `log(1/λ) = 4χ` (`rapidity_chart`).
4. **The discriminant and the degenerate fibres** (§2). The cubic `u³ − (A + B) u² + AB u` (`legendreCubicPoly`,
   `legendreCubicPoly_eval`) has discriminant `A² B² (A − B)²` (`legendreCubicPoly_discr`), which is
   `(a − w)⁴ (a + w)⁴ (4aw)²` (`egg_discr`): `w²` times a cofactor `16 a¹⁰ ≠ 0` at `w = 0`, and `(a − w)⁴` times a
   cofactor `256 a⁸ ≠ 0` at `w = a` (`egg_discr_orders`); in `0 ≤ w ≤ a` it vanishes only there
   (`egg_discr_eq_zero_iff`). At `w = 0`,
   `A = B` (`λ = 1`) and the egg is the ellipse `x²/a² + y²/b² = 1` (`ellipse_fibre`); at `w = a`, `A = 0` (`λ = 0`)
   and the egg is the line `x = −a` with the conic `2a y² + b²(x − a) = 0` (`neck_fibre`; projectively
   `neck_homogeneous_factor`), singular exactly at their crossings `(−a, ±b)` (`neck_singular_points`).
5. **Smoothness** (§2). For `a, b ≠ 0` and `a ≠ ±w` no affine point has both partials zero (`egg_smooth`; the
   partials are the derivatives over `ℝ`, `hasDerivAt_egg_x`, `hasDerivAt_egg_y`); for `b, w ≠ 0` the two points at
   infinity `[1 : 0 : 0]` and `[0 : 1 : 0]` are smooth (`egg_smooth_at_infinity`, with Euler's relation
   `eggHom_euler`).
6. **The real picture for `0 < w < a`** (§2). The roots satisfy `0 < A < B` (`branch_order`) and the asymptote
   `x = −(a² + w²)/(2w)` lies left of `−a` (`asymptote_lt_neg`, `eggU_neg_iff`). Every real point has `x ∈ [−a, a]`
   or lies left of the asymptote (`real_points_split`), and a real point sits over `x` exactly when `x` is in one of
   those two sets (`exists_point_iff`). The part over `[−a, a]` is compact (`egg_oval_isCompact`) and connected
   (`egg_oval_isConnected`): the oval. The other part is unbounded (`branch_unbounded`).
7. **Rational eggs are elliptic curves over `ℚ`** (§3). The model is `GeneralFace.E (−A) (−B)`,
   `V² = X (X + A)(X + B)` (`eggCurve`, `eggCurve_equation_iff`), which the chain of 1 and 2 reaches at
   `EggSource.eggPoint`'s coordinates (`egg_to_eggCurve`, `eggPoint_eq`). Its discriminant is
   `Δ = 16 A² B² (A − B)² = 256 a² w² (a² − w²)⁴` and `c₄ = 16 (a⁴ + 14 a² w² + w⁴)`, which is `16 a⁴` at `w = 0` and
   `256 a⁴` at `w = a` (`eggCurve_Δ`, `eggCurve_c₄`). It is elliptic for `a, w ≠ 0`, `a ≠ ±w`
   (`eggCurve_isElliptic`, `eggCurve_isElliptic_of_lt`), with `j = EggModular.legendreJ λ` (`eggCurve_j`, through
   `legendreJ_ratio`), and it depends on `β = w/a` alone (`eggCurve_scale`). The egg's rational vertices `(±a, 0)`
   map to `(−(a ± w)², 0)`, which with `(0, 0)` and the origin are the four points of `E[2](ℚ)`
   (`vertices_two_torsion`). The egg `a = 2, b = 1, w = 1` is `V² = X³ + 10 X² + 9 X` with `Δ = 2¹⁰ · 3⁴`,
   `c₄ = 2⁴ · 73` and `j = 2² · 73³/3⁴` (`egg_211`).
8. **The logarithmic period at the neck** (§4). `K(√(1 − λ)) − ½ log(16/λ) → 0` as `λ → 0⁺` (`ellipticK_neck`): the
   integrand splits into `sin θ (cos²θ + λ sin²θ)^(−1/2)`, integrated in closed form (`integral_g`), and a remainder
   that tends to `log 2` by dominated convergence (`tendsto_integral_h`, `integral_limit`). For the record's closed
   form of the period, `(2/(b(a + w))) K(√(1 − λ)) − (1/(2ab)) log(1/λ) → 2 log 2/(ab)` as `w → a⁻`
   (`egg_period_neck`): the record's `(1/(2ab)) log(1/λ) + O(1)`, with its constant.

Two readings of the record are sharpened here. Its "exactly" for the transport holds off the asymptote `u = 0`, which
the transport sends whole to `(0, 0)`; the egg has no affine point there for `0 < w < a`, `b ≠ 0`, and `(0, 0)` is the
image of its vertical point at infinity. Its `Δ = 256 a² w² (a² − w²)⁴` is the Weierstrass (LMFDB) normalization of
the Legendre model, sixteen times the cubic's discriminant `(a − w)⁴ (a + w)⁴ (4aw)²`, and it is also the discriminant
of the rational model (the twist by `−1`); the monic model of the twist by `d` itself has `d⁶ Δ`.

What is not claimed. The identity `∫_egg ω = (2/(b(a + w))) K(√(1 − λ))` (the substitution on the oval) is not
proved: `egg_period_neck` is about the record's closed form. The monodromies `[[1, 4], [0, 1]]` at the neck and
`[[1, 2], [0, 1]]` at the ellipse, Kodaira's types `I₄` and `I₂`, the resolution of the total surface and the Legendre
fibre `I₂*` at `∞` are out of scope; only the discriminant's orders 2 and 4 with `c₄ ≠ 0` are proved. The group
`E(ℝ) ≅ S¹ × ℤ/2` and the exchange of the two real parts by translation are not proved, and the unbounded part is not
shown connected (affinely its arcs `y > 0` and `y < 0` meet only through the points at infinity). Nothing is claimed
on ranks or Mordell–Weil groups of rational eggs beyond the four two-torsion points (`EggSource` holds a rank bound
for `a = 3, b = 2, w = 1`), and the projective group equivalence between the egg and `eggCurve` stays as `EggSource`
left it. Reading `β` as a velocity, `k` as a Doppler factor, `w = 0` as a rest frame and `w = a` as a lightlike limit
is an assigned image (the September 26 scope correction): here `β`, `k` and `χ` carry their algebraic relations only.

The computational object is the helical pair interaction: de La Hire's two circles in relative motion, the inner one
displaced by `w`, whose face is the egg. The displacement enters the curve only through the modulus `λ = k⁻⁴`, the
inverse Doppler ratio's fourth power, and the period round the oval grows toward the neck as
`log(1/λ)/(2ab) = 2χ/(ab)`. Of the winding guide's six general objects this touches faces and placement (the Legendre
face, its twist by a square class, and the placement `0 < A < B` of the branch points that splits the real locus)
and the cell holonomy (the degenerate fibres at `w = 0` and `w = a`, where the cycle the family's monodromy moves
pinches, and the period that grows there); the helix, the pair, the tube and the tower thread stay attached.

Consumers: the #410 box "The egg as an elliptic family" and the atlas rows above.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.EllipticCurve.EggFamily

/-! ## §1 The egg cubic is the twisted Legendre form -/

section Field

variable {K : Type*} [Field K]

/-- [definition] **Hügelschäffer's egg** `(a² + w² + 2wx) y² = b²(a² − x²)`. -/
def eggEq (a b w x y : K) : Prop :=
  (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2)

/-- [definition] The Legendre abscissa `u = 2wx + a² + w²`. -/
def eggU (a w x : K) : K := 2 * w * x + a ^ 2 + w ^ 2

/-- [definition] The first finite branch point `A = (a − w)²`. -/
def branchA (a w : K) : K := (a - w) ^ 2

/-- [definition] The second finite branch point `B = (a + w)²`. -/
def branchB (a w : K) : K := (a + w) ^ 2

/-- [definition] The Legendre cubic `u (u − A)(u − B)`. -/
def legendreCubic (A B u : K) : K := u * (u - A) * (u - B)

/-- [definition] The twisted Legendre equation `Y² = d · u (u − A)(u − B)`. -/
def twistEq (d A B u Y : K) : Prop := Y ^ 2 = d * legendreCubic A B u

/-- [definition] The egg's twist `d = −b²/(4w²)`. -/
def eggTwist (b w : K) : K := -(b ^ 2 / (4 * w ^ 2))

/-- [proved-derived; formal-checked] `u − A = 2w(x + a)`. -/
theorem eggU_sub_branchA (a w x : K) : eggU a w x - branchA a w = 2 * w * (x + a) := by
  unfold eggU branchA; ring

/-- [proved-derived; formal-checked] `u − B = 2w(x − a)`. -/
theorem eggU_sub_branchB (a w x : K) : eggU a w x - branchB a w = 2 * w * (x - a) := by
  unfold eggU branchB; ring

/-- [proved-derived; formal-checked] The Legendre cubic at the egg's abscissa is `−4w² u (a² − x²)`. -/
theorem legendreCubic_eggU (a w x : K) :
    legendreCubic (branchA a w) (branchB a w) (eggU a w x) =
      -(4 * w ^ 2) * eggU a w x * (a ^ 2 - x ^ 2) := by
  unfold legendreCubic eggU branchA branchB; ring

/-- [proved-derived; formal-checked] **The polynomial identity behind the transport**, in any field and with no
division: `4w² (u y)² + b² u (u − A)(u − B) = 4w² u (u y² − b²(a² − x²))`. -/
theorem egg_twist_polynomial_identity (a b w x y : K) :
    4 * w ^ 2 * (eggU a w x * y) ^ 2 + b ^ 2 * legendreCubic (branchA a w) (branchB a w) (eggU a w x) =
      4 * w ^ 2 * eggU a w x * (eggU a w x * y ^ 2 - b ^ 2 * (a ^ 2 - x ^ 2)) := by
  rw [legendreCubic_eggU]; ring

/-- [proved-derived; formal-checked] The twist factor times the Legendre cubic at the egg's abscissa is
`b² u (a² − x²)`. -/
theorem eggTwist_mul_legendreCubic (a b w x : K) (h2 : (2 : K) ≠ 0) (hw : w ≠ 0) :
    eggTwist b w * legendreCubic (branchA a w) (branchB a w) (eggU a w x) =
      eggU a w x * (b ^ 2 * (a ^ 2 - x ^ 2)) := by
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [legendreCubic_eggU]
  unfold eggTwist
  field_simp

/-- [proved-derived; formal-checked] **The egg lands on the twisted Legendre curve.** For `w ≠ 0` (and `2 ≠ 0`) every
point of the egg is carried by `(x, y) ↦ (u, u y)` onto `Y² = −(b²/4w²) u (u − A)(u − B)`. -/
theorem twistEq_of_eggEq {a b w x y : K} (h2 : (2 : K) ≠ 0) (hw : w ≠ 0) (h : eggEq a b w x y) :
    twistEq (eggTwist b w) (branchA a w) (branchB a w) (eggU a w x) (eggU a w x * y) := by
  unfold twistEq
  rw [eggTwist_mul_legendreCubic a b w x h2 hw]
  unfold eggEq at h
  unfold eggU
  linear_combination (2 * w * x + a ^ 2 + w ^ 2) * h

/-- [proved-derived; formal-checked] **The identity, off the asymptote.** For `w ≠ 0` and `u ≠ 0`, `(x, y)` is on the
egg exactly when `(u, u y)` is on the twisted Legendre curve. -/
theorem eggEq_iff_twistEq {a b w x y : K} (h2 : (2 : K) ≠ 0) (hw : w ≠ 0) (hu : eggU a w x ≠ 0) :
    eggEq a b w x y ↔
      twistEq (eggTwist b w) (branchA a w) (branchB a w) (eggU a w x) (eggU a w x * y) := by
  refine ⟨twistEq_of_eggEq h2 hw, fun h => ?_⟩
  unfold twistEq at h
  rw [eggTwist_mul_legendreCubic a b w x h2 hw] at h
  unfold eggEq
  have h' : eggU a w x * (eggU a w x * y ^ 2) = eggU a w x * (b ^ 2 * (a ^ 2 - x ^ 2)) := by
    linear_combination h
  have h'' := mul_left_cancel₀ hu h'
  unfold eggU at h''
  linear_combination h''

/-- [proved-derived; formal-checked] **On the asymptote the transport forgets the egg.** Where `u = 0` the image
`(0, 0)` is on the twisted curve whatever `y` is, while the egg's equation reads `b²(a² − x²) = 0`. -/
theorem eggEq_on_asymptote {a b w x y : K} (hu : eggU a w x = 0) :
    twistEq (eggTwist b w) (branchA a w) (branchB a w) (eggU a w x) (eggU a w x * y) ∧
      (eggEq a b w x y ↔ b ^ 2 * (a ^ 2 - x ^ 2) = 0) := by
  have hu' : a ^ 2 + w ^ 2 + 2 * w * x = 0 := by unfold eggU at hu; linear_combination hu
  refine ⟨?_, ?_⟩
  · unfold twistEq legendreCubic
    rw [hu]; ring
  · unfold eggEq
    rw [hu', zero_mul]
    exact eq_comm

/-- [proved-derived; formal-checked] The abscissa returns: `u ↦ (u − a² − w²)/(2w)` inverts `x ↦ u`. -/
theorem eggU_inverse {a w : K} (h2 : (2 : K) ≠ 0) (hw : w ≠ 0) (u : K) :
    eggU a w ((u - a ^ 2 - w ^ 2) / (2 * w)) = u := by
  unfold eggU
  field_simp
  ring

/-- [proved-derived; formal-checked] **The transport is a bijection off the asymptote**: the egg's points with
`u ≠ 0` and the twisted Legendre curve's points with `u ≠ 0` correspond under `(x, y) ↦ (u, u y)`, with inverse
`(u, Y) ↦ ((u − a² − w²)/(2w), Y/u)`. -/
def eggTwistEquiv (a b w : K) (h2 : (2 : K) ≠ 0) (hw : w ≠ 0) :
    {p : K × K // eggEq a b w p.1 p.2 ∧ eggU a w p.1 ≠ 0} ≃
      {q : K × K // twistEq (eggTwist b w) (branchA a w) (branchB a w) q.1 q.2 ∧ q.1 ≠ 0} where
  toFun p := ⟨(eggU a w p.1.1, eggU a w p.1.1 * p.1.2), twistEq_of_eggEq h2 hw p.2.1, p.2.2⟩
  invFun q := ⟨((q.1.1 - a ^ 2 - w ^ 2) / (2 * w), q.1.2 / q.1.1), by
    have hu : eggU a w ((q.1.1 - a ^ 2 - w ^ 2) / (2 * w)) = q.1.1 := eggU_inverse h2 hw q.1.1
    refine ⟨?_, by rw [hu]; exact q.2.2⟩
    rw [eggEq_iff_twistEq h2 hw (by rw [hu]; exact q.2.2), hu, mul_div_cancel₀ _ q.2.2]
    exact q.2.1⟩
  left_inv p := by
    obtain ⟨⟨x, y⟩, _, hu⟩ := p
    have hu' : (2 * w * x + a ^ 2 + w ^ 2) ≠ 0 := hu
    ext
    · simp only
      unfold eggU
      field_simp
      ring
    · simp only
      field_simp
  right_inv q := by
    obtain ⟨⟨u, Y⟩, _, hu⟩ := q
    ext
    · exact eggU_inverse h2 hw u
    · simp only
      rw [eggU_inverse h2 hw u]
      field_simp

/-- [proved-standard; formal-checked] **The twist is a scaling of the Legendre model.** `Y² = d u (u − A)(u − B)`
exactly when `(d u, d Y)` lies on the monic cubic with roots `0, dA, dB`, for `d ≠ 0`. -/
theorem twistEq_iff_scaled {d A B u Y : K} (hd : d ≠ 0) :
    twistEq d A B u Y ↔ (d * Y) ^ 2 = legendreCubic (d * A) (d * B) (d * u) := by
  unfold twistEq legendreCubic
  constructor
  · intro h
    linear_combination d ^ 2 * h
  · intro h
    have h' : d ^ 2 * Y ^ 2 = d ^ 2 * (d * (u * (u - A) * (u - B))) := by linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 2 hd) h'

/-- [proved-derived; formal-checked] The egg's twist is minus a square, `−b²/(4w²) = −(b/(2w))²`. -/
theorem eggTwist_eq_neg_sq (b w : K) : eggTwist b w = -(b / (2 * w)) ^ 2 := by
  unfold eggTwist
  rw [div_pow, mul_pow]
  norm_num

/-- [proved-derived; formal-checked] **The egg's twist is the twist by `−1` over the base field.** Since the twist
`−(b/(2w))²` is `−1` times a square, `(u, Y) ↦ (−u, (2w/b) Y)` carries `Y² = −(b²/4w²) u (u − A)(u − B)` onto
`V² = X (X + A)(X + B)`, and back. -/
theorem eggTwist_iff_minusOne {b w A B u Y : K} (hb : b ≠ 0) (hw : w ≠ 0) (h2 : (2 : K) ≠ 0) :
    twistEq (eggTwist b w) A B u Y ↔ (2 * w / b * Y) ^ 2 = legendreCubic (-A) (-B) (-u) := by
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hk : 4 * w ^ 2 / b ^ 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hw)) (pow_ne_zero 2 hb)
  have key : (2 * w / b * Y) ^ 2 - legendreCubic (-A) (-B) (-u) =
      4 * w ^ 2 / b ^ 2 * (Y ^ 2 - eggTwist b w * legendreCubic A B u) := by
    unfold legendreCubic eggTwist
    field_simp
    ring
  unfold twistEq
  rw [← sub_eq_zero, ← sub_eq_zero (a := (2 * w / b * Y) ^ 2), key, mul_eq_zero, or_iff_right hk]

/-! ### The modulus -/

/-- [proved-derived; formal-checked] `λ = A/B = ((a − w)/(a + w))²`. -/
theorem branch_ratio (a w : K) : branchA a w / branchB a w = ((a - w) / (a + w)) ^ 2 := by
  unfold branchA branchB
  rw [div_pow]

/-- [proved-derived; formal-checked] `λ = ((1 − β)/(1 + β))²` with `β = w/a`. -/
theorem branch_ratio_beta {a w : K} (ha : a ≠ 0) :
    branchA a w / branchB a w = ((1 - w / a) / (1 + w / a)) ^ 2 := by
  rw [branch_ratio]
  congr 1
  rw [one_sub_div ha, one_add_div ha, div_div_div_cancel_right₀ ha]

/-- [proved-derived; formal-checked] `λ = k⁻⁴` with `k² = (1 + β)/(1 − β)`. -/
theorem lambda_eq_inv_kSq_sq (β : K) :
    ((1 - β) / (1 + β)) ^ 2 = (((1 + β) / (1 - β)) ^ 2)⁻¹ := by
  rw [← inv_pow, inv_div]

/-- [proved-derived; formal-checked] The complementary modulus `1 − λ = 4aw/(a + w)²`; `λ − 1` has a simple zero at
`w = 0` and `λ` a double zero at `w = a`. -/
theorem one_sub_branch_ratio {a w : K} (hp : a + w ≠ 0) :
    1 - branchA a w / branchB a w = 4 * a * w / (a + w) ^ 2 := by
  unfold branchA branchB
  field_simp
  ring

end Field

/-! ### The modulus on the real line: the factor `k` and the rapidity chart -/

section Real

open Real

/-- [proved-derived; formal-checked] **`λ = k⁻⁴` on the real line**, with `k = √((1 + β)/(1 − β))` and `β = w/a`;
`λ` is `EggModular.eggLambda (w/a)`. -/
theorem branch_ratio_eq_inv_k_pow_four {a w : ℝ} (ha : a ≠ 0) (hβ0 : 0 ≤ w / a) (hβ1 : w / a < 1) :
    branchA a w / branchB a w = Geometry.EggModular.eggLambda (w / a) ∧
      branchA a w / branchB a w = (Real.sqrt ((1 + w / a) / (1 - w / a)) ^ 4)⁻¹ := by
  have hnn : 0 ≤ (1 + w / a) / (1 - w / a) := div_nonneg (by linarith) (by linarith)
  refine ⟨branch_ratio_beta ha, ?_⟩
  rw [branch_ratio_beta ha, lambda_eq_inv_kSq_sq, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    Real.sq_sqrt hnn]

/-- [proved-standard; formal-checked] With `β = tanh χ`, `k² = (1 + β)/(1 − β) = e^(2χ)`. -/
theorem kSq_tanh (χ : ℝ) : (1 + tanh χ) / (1 - tanh χ) = exp χ ^ 2 := by
  have hc := cosh_pos χ
  rw [tanh_eq_sinh_div_cosh]
  have e1 : 1 + sinh χ / cosh χ = exp χ / cosh χ := by
    rw [← cosh_add_sinh]; field_simp
  have e2 : 1 - sinh χ / cosh χ = exp (-χ) / cosh χ := by
    rw [← cosh_sub_sinh]; field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hc.ne', exp_neg]
  field_simp

/-- [proved-derived; formal-checked] **The rapidity chart.** At `β = tanh χ`, `k = √((1 + β)/(1 − β)) = e^χ`, the
modulus is `λ = e^(−4χ)`, and `log(1/λ) = 4χ`, so the record's leading period term `(1/(2ab)) log(1/λ)` is
`2χ/(ab)`. -/
theorem rapidity_chart (χ : ℝ) :
    Real.sqrt ((1 + tanh χ) / (1 - tanh χ)) = exp χ ∧
      Geometry.EggModular.eggLambda (tanh χ) = exp (-(4 * χ)) ∧
      Real.log (Geometry.EggModular.eggLambda (tanh χ))⁻¹ = 4 * χ := by
  have hl : Geometry.EggModular.eggLambda (tanh χ) = exp (-(4 * χ)) := by
    unfold Geometry.EggModular.eggLambda
    rw [lambda_eq_inv_kSq_sq, kSq_tanh, ← pow_mul, ← exp_nat_mul, ← exp_neg]
    norm_num
  refine ⟨?_, hl, ?_⟩
  · rw [kSq_tanh, Real.sqrt_sq (exp_pos χ).le]
  · rw [hl, ← exp_neg, neg_neg, log_exp]

end Real

/-! ## §2 The discriminant, the degenerate fibres and the real picture -/

section Discriminant

variable {K : Type*} [Field K]

/-- [definition] The Legendre cubic as a `Cubic`: `u³ − (A + B) u² + A B u`. -/
def legendreCubicPoly (A B : K) : Cubic K := ⟨1, -(A + B), A * B, 0⟩

/-- [proved-standard; formal-checked] The `Cubic` evaluates to `u (u − A)(u − B)`. -/
theorem legendreCubicPoly_eval (A B u : K) :
    (legendreCubicPoly A B).toPoly.eval u = legendreCubic A B u := by
  simp only [legendreCubicPoly, Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, legendreCubic]
  ring

/-- [proved-standard; formal-checked] **The discriminant of the cubic with roots `0, A, B`** is `A² B² (A − B)²`. -/
theorem legendreCubicPoly_discr (A B : K) :
    (legendreCubicPoly A B).discr = A ^ 2 * B ^ 2 * (A - B) ^ 2 := by
  simp only [legendreCubicPoly, Cubic.discr]
  ring

/-- [proved-derived; formal-checked] **The egg's cubic discriminant** is `(a − w)⁴ (a + w)⁴ (4aw)²`. -/
theorem egg_discr (a w : K) :
    (legendreCubicPoly (branchA a w) (branchB a w)).discr = (a - w) ^ 4 * (a + w) ^ 4 * (4 * a * w) ^ 2 := by
  rw [legendreCubicPoly_discr]
  unfold branchA branchB
  ring

/-- [proved-derived; formal-checked] **The orders of the degenerations**: the discriminant is `w²` times a cofactor
that is `16 a¹⁰ ≠ 0` at `w = 0`, and `(a − w)⁴` times a cofactor that is `256 a⁸ ≠ 0` at `w = a`. -/
theorem egg_discr_orders {a : K} (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) :
    (∀ w : K, (legendreCubicPoly (branchA a w) (branchB a w)).discr =
        w ^ 2 * (16 * a ^ 2 * (a ^ 2 - w ^ 2) ^ 4)) ∧
      16 * a ^ 2 * (a ^ 2 - 0 ^ 2) ^ 4 = 16 * a ^ 10 ∧ 16 * a ^ 10 ≠ 0 ∧
      (∀ w : K, (legendreCubicPoly (branchA a w) (branchB a w)).discr =
        (a - w) ^ 4 * (16 * a ^ 2 * w ^ 2 * (a + w) ^ 4)) ∧
      16 * a ^ 2 * a ^ 2 * (a + a) ^ 4 = 256 * a ^ 8 ∧ 256 * a ^ 8 ≠ 0 := by
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num]; exact pow_ne_zero 4 h2
  have h256 : (256 : K) ≠ 0 := by
    rw [show (256 : K) = 2 ^ 8 by norm_num]; exact pow_ne_zero 8 h2
  refine ⟨fun w => by rw [egg_discr]; ring, by ring, mul_ne_zero h16 (pow_ne_zero 10 ha),
    fun w => by rw [egg_discr]; ring, by ring, mul_ne_zero h256 (pow_ne_zero 8 ha)⟩

/-- [proved-derived; formal-checked] **The rest frame `w = 0`**: `A = B` (so `λ = 1`), and the egg is the ellipse
`x²/a² + y²/b² = 1`. -/
theorem ellipse_fibre {a b x y : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    branchA a 0 = branchB a 0 ∧ (eggEq a b 0 x y ↔ x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1) := by
  refine ⟨by unfold branchA branchB; ring, ?_⟩
  unfold eggEq
  rw [div_add_div _ _ (pow_ne_zero 2 ha) (pow_ne_zero 2 hb), div_eq_one_iff_eq
    (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb))]
  constructor <;> intro h <;> linear_combination h

/-- [proved-derived; formal-checked] **The neck `w = a`**: `A = 0` (so `λ = 0`), and the egg is the line `x = −a`
together with the conic `2a y² + b²(x − a) = 0`. -/
theorem neck_fibre {a b x y : K} :
    branchA a a = 0 ∧ (eggEq a b a x y ↔ x + a = 0 ∨ 2 * a * y ^ 2 + b ^ 2 * (x - a) = 0) := by
  refine ⟨by unfold branchA; ring, ?_⟩
  unfold eggEq
  rw [← mul_eq_zero, ← sub_eq_zero]
  constructor <;> intro h <;> linear_combination h

/-- [proved-derived; formal-checked] The neck's projective fibre factors as a line times a conic:
`((a² + a²) Z + 2aX) Y² − b² Z (a² Z² − X²) = (X + aZ)(2aY² + b² Z (X − aZ))`. -/
theorem neck_homogeneous_factor (a b X Y Z : K) :
    ((a ^ 2 + a ^ 2) * Z + 2 * a * X) * Y ^ 2 - b ^ 2 * Z * (a ^ 2 * Z ^ 2 - X ^ 2) =
      (X + a * Z) * (2 * a * Y ^ 2 + b ^ 2 * Z * (X - a * Z)) := by
  ring

/-- [definition] The partial derivative `∂F/∂x = 2w y² + 2b² x` of `F = (a² + w² + 2wx) y² − b²(a² − x²)`. -/
def eggFx (b w x y : K) : K := 2 * w * y ^ 2 + 2 * b ^ 2 * x

/-- [definition] The partial derivative `∂F/∂y = 2(a² + w² + 2wx) y`. -/
def eggFy (a w x y : K) : K := 2 * (a ^ 2 + w ^ 2 + 2 * w * x) * y

/-- [proved-derived; formal-checked] **The affine egg is smooth** for `a, b ≠ 0`, `a ≠ ±w` (and `2 ≠ 0`): no point of
it has both partial derivatives zero. -/
theorem egg_smooth {a b w x y : K} (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hm : a - w ≠ 0)
    (hp : a + w ≠ 0) (h : eggEq a b w x y) : eggFx b w x y ≠ 0 ∨ eggFy a w x y ≠ 0 := by
  by_contra hc
  simp only [not_or, not_not] at hc
  obtain ⟨hx, hy⟩ := hc
  unfold eggFx at hx
  unfold eggFy at hy
  unfold eggEq at h
  rcases mul_eq_zero.mp hy with hu | hy0
  · have hu' : a ^ 2 + w ^ 2 + 2 * w * x = 0 := (mul_eq_zero.mp hu).resolve_left h2
    rw [hu', zero_mul] at h
    have hx2 : (x - a) * (x + a) = 0 := by
      have := (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hb)
      linear_combination -this
    rcases mul_eq_zero.mp hx2 with h1 | h1
    · have : x = a := sub_eq_zero.mp h1
      subst this
      exact pow_ne_zero 2 hp (by linear_combination hu')
    · have : x = -a := eq_neg_of_add_eq_zero_left h1
      subst this
      exact pow_ne_zero 2 hm (by linear_combination hu')
  · subst hy0
    have hx0 : x = 0 := by
      have h' : 2 * b ^ 2 * x = 0 := by linear_combination hx
      exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero h2 (pow_ne_zero 2 hb))
    subst hx0
    have : b ^ 2 * a ^ 2 = 0 := by linear_combination -h
    exact mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 ha) this

/-- [proved-derived; formal-checked] **The neck's singular points.** At `w = a` the affine egg is singular exactly at
the two crossings `(−a, ±b)` of its line and its conic. -/
theorem neck_singular_points {a b x y : K} (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (eggEq a b a x y ∧ eggFx b a x y = 0 ∧ eggFy a a x y = 0) ↔ x = -a ∧ (y = b ∨ y = -b) := by
  unfold eggEq eggFx eggFy
  constructor
  · rintro ⟨h, hx, hy⟩
    have hy' : (x + a) * y = 0 := by
      have : 2 * (2 * a) * ((x + a) * y) = 0 := by linear_combination hy
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 (mul_ne_zero h2 ha))
    rcases mul_eq_zero.mp hy' with h1 | h1
    · have hxa : x = -a := eq_neg_of_add_eq_zero_left h1
      subst hxa
      refine ⟨rfl, ?_⟩
      have : y ^ 2 = b ^ 2 := by
        have h' : 2 * a * (y ^ 2 - b ^ 2) = 0 := by linear_combination hx
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (mul_ne_zero h2 ha))
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    · subst h1
      exfalso
      have hx0 : x = 0 := by
        have h' : 2 * b ^ 2 * x = 0 := by linear_combination hx
        exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero h2 (pow_ne_zero 2 hb))
      subst hx0
      exact mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 ha) (by linear_combination -h)
  · rintro ⟨rfl, hy | hy⟩ <;> subst hy <;> refine ⟨by ring, by ring, by ring⟩

/-- [definition] The homogeneous egg `F(X, Y, Z) = ((a² + w²) Z + 2wX) Y² − b² Z (a² Z² − X²)`. -/
def eggHom (a b w X Y Z : K) : K :=
  ((a ^ 2 + w ^ 2) * Z + 2 * w * X) * Y ^ 2 - b ^ 2 * Z * (a ^ 2 * Z ^ 2 - X ^ 2)

/-- [definition] `∂F/∂X = 2w Y² + 2b² Z X`. -/
def eggHomX (b w X Y Z : K) : K := 2 * w * Y ^ 2 + 2 * b ^ 2 * Z * X

/-- [definition] `∂F/∂Y = 2((a² + w²) Z + 2wX) Y`. -/
def eggHomY (a w X Y Z : K) : K := 2 * ((a ^ 2 + w ^ 2) * Z + 2 * w * X) * Y

/-- [definition] `∂F/∂Z = (a² + w²) Y² − b² (3a² Z² − X²)`. -/
def eggHomZ (a b w X Y Z : K) : K := (a ^ 2 + w ^ 2) * Y ^ 2 - b ^ 2 * (3 * a ^ 2 * Z ^ 2 - X ^ 2)

/-- [proved-standard; formal-checked] Euler's relation `X F_X + Y F_Y + Z F_Z = 3F` for the cubic form, and the
affine chart `Z = 1` returns the affine partials. -/
theorem eggHom_euler (a b w X Y Z : K) :
    X * eggHomX b w X Y Z + Y * eggHomY a w X Y Z + Z * eggHomZ a b w X Y Z = 3 * eggHom a b w X Y Z ∧
      eggHomX b w X Y 1 = eggFx b w X Y ∧ eggHomY a w X Y 1 = eggFy a w X Y := by
  unfold eggHomX eggHomY eggHomZ eggHom eggFx eggFy
  refine ⟨by ring, by ring, by ring⟩

/-- [proved-derived; formal-checked] **No singular point at infinity** for `w, b ≠ 0`: the points at infinity are
`[1 : 0 : 0]` and `[0 : 1 : 0]`, where `∂F/∂Z = b² X²` and `∂F/∂X = 2w Y²` are nonzero. -/
theorem egg_smooth_at_infinity {a b w X Y : K} (h2 : (2 : K) ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0)
    (hXY : X ≠ 0 ∨ Y ≠ 0) (h : eggHom a b w X Y 0 = 0) :
    (X = 0 ∧ eggHomX b w X Y 0 ≠ 0) ∨ (Y = 0 ∧ eggHomZ a b w X Y 0 ≠ 0) := by
  unfold eggHom at h
  have h' : 2 * w * X * Y ^ 2 = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · have hX : X = 0 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero h2 hw)
    have hY : Y ≠ 0 := hXY.resolve_left (not_not.mpr hX)
    left
    refine ⟨hX, ?_⟩
    unfold eggHomX
    rw [hX]
    simpa using mul_ne_zero (mul_ne_zero h2 hw) (pow_ne_zero 2 hY)
  · have hY : Y = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    have hX : X ≠ 0 := hXY.resolve_right (not_not.mpr hY)
    right
    refine ⟨hY, ?_⟩
    unfold eggHomZ
    rw [hY]
    simpa using mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hX)

end Discriminant

/-! ### The real picture for `0 < w < a` -/

section RealPicture

variable {a b w : ℝ}

/-- [proved-standard; formal-checked] **Three distinct real roots** `0 < A < B` for `0 < w < a`. -/
theorem branch_order (hw : 0 < w) (hwa : w < a) : 0 < branchA a w ∧ branchA a w < branchB a w := by
  unfold branchA branchB
  have hm : 0 < a - w := sub_pos.mpr hwa
  exact ⟨by positivity, by nlinarith⟩

/-- [proved-derived; formal-checked] **The degenerations in `0 ≤ w ≤ a`**: the discriminant vanishes exactly at
`w = 0` and `w = a`. -/
theorem egg_discr_eq_zero_iff (ha : 0 < a) (hw : 0 ≤ w) (hwa : w ≤ a) :
    (legendreCubicPoly (branchA a w) (branchB a w)).discr = 0 ↔ w = 0 ∨ w = a := by
  rw [egg_discr]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · right
        have := (pow_eq_zero_iff (n := 4) (by norm_num)).mp h2
        linarith
      · exfalso
        have := (pow_eq_zero_iff (n := 4) (by norm_num)).mp h2
        linarith
    · left
      have h3 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exfalso
        linarith
      · exact h4
  · rintro (rfl | rfl) <;> ring

/-- [proved-standard; formal-checked] The asymptote `x = −(a² + w²)/(2w)` lies left of `x = −a`. -/
theorem asymptote_lt_neg (hw : 0 < w) (hwa : w < a) : -(a ^ 2 + w ^ 2) / (2 * w) < -a := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hwa)]

/-- [proved-derived; formal-checked] `u < 0` exactly left of the asymptote. -/
theorem eggU_neg_iff (hw : 0 < w) (x : ℝ) : eggU a w x < 0 ↔ x < -(a ^ 2 + w ^ 2) / (2 * w) := by
  rw [lt_div_iff₀ (by positivity)]
  unfold eggU
  constructor <;> intro h <;> linarith

/-- [proved-standard; formal-checked] **Every real point lies on the oval or on the branch**: `x ∈ [−a, a]`, or `x`
is left of the asymptote. -/
theorem real_points_split (hb : b ≠ 0) (hw : 0 < w) (hwa : w < a) {x y : ℝ} (h : eggEq a b w x y) :
    (-a ≤ x ∧ x ≤ a) ∨ x < -(a ^ 2 + w ^ 2) / (2 * w) := by
  have hb2 : 0 < b ^ 2 := by positivity
  rcases lt_trichotomy (eggU a w x) 0 with hu | hu | hu
  · exact Or.inr ((eggU_neg_iff hw x).mp hu)
  · exfalso
    have h0 := (eggEq_on_asymptote (b := b) (y := y) hu).2.mp h
    have hx2 : x ^ 2 - a ^ 2 = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left hb2.ne'
      linear_combination -this
    unfold eggU at hu
    have e : (a ^ 2 - w ^ 2) ^ 2 = 0 := by
      linear_combination (a ^ 2 + w ^ 2 - 2 * w * x) * hu + 4 * w ^ 2 * hx2
    have e' : a ^ 2 - w ^ 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp e
    nlinarith
  · left
    unfold eggEq at h
    have hnn : 0 ≤ b ^ 2 * (a ^ 2 - x ^ 2) := by
      rw [← h]
      unfold eggU at hu
      exact mul_nonneg (by linarith) (sq_nonneg y)
    have hx : x ^ 2 ≤ a ^ 2 := by
      have := (mul_nonneg_iff_of_pos_left hb2).mp hnn
      linarith
    exact abs_le_of_sq_le_sq' hx (by linarith)

/-- [proved-standard; formal-checked] **The real abscissae**: a real point of the egg sits over `x` exactly when
`x ∈ [−a, a]` or `x < −(a² + w²)/(2w)`; so both parts are nonempty, and the gap between them is
`(−(a² + w²)/(2w), −a)`. -/
theorem exists_point_iff (hb : b ≠ 0) (hw : 0 < w) (hwa : w < a) (x : ℝ) :
    (∃ y, eggEq a b w x y) ↔ (-a ≤ x ∧ x ≤ a) ∨ x < -(a ^ 2 + w ^ 2) / (2 * w) := by
  refine ⟨fun ⟨y, h⟩ => real_points_split hb hw hwa h, fun hx => ?_⟩
  have key : ∀ u : ℝ, u = a ^ 2 + w ^ 2 + 2 * w * x → u ≠ 0 → 0 ≤ b ^ 2 * (a ^ 2 - x ^ 2) / u →
      ∃ y, eggEq a b w x y := by
    intro u hu hu0 hnn
    refine ⟨Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) / u), ?_⟩
    unfold eggEq
    rw [Real.sq_sqrt hnn, ← hu]
    field_simp
  rcases hx with ⟨h1, h2⟩ | h1
  · have hu : 0 < a ^ 2 + w ^ 2 + 2 * w * x := by nlinarith [sq_pos_of_pos (sub_pos.mpr hwa)]
    have hx2 : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith
    exact key _ rfl hu.ne' (div_nonneg (mul_nonneg (sq_nonneg b) hx2) hu.le)
  · have hu : a ^ 2 + w ^ 2 + 2 * w * x < 0 := by
      have := (eggU_neg_iff (a := a) hw x).mpr h1
      unfold eggU at this
      linarith
    have hxa : x < -a := lt_trans h1 (asymptote_lt_neg hw hwa)
    have hx2 : a ^ 2 - x ^ 2 ≤ 0 := by nlinarith
    exact key _ rfl hu.ne (div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hx2) hu.le)

/-- [proved-standard; formal-checked] **The branch is unbounded**: it has points left of any abscissa `M`. -/
theorem branch_unbounded (hb : b ≠ 0) (hw : 0 < w) (hwa : w < a) (M : ℝ) :
    ∃ x y, eggEq a b w x y ∧ x < -(a ^ 2 + w ^ 2) / (2 * w) ∧ x < M := by
  have h1 := min_le_left (-(a ^ 2 + w ^ 2) / (2 * w)) M
  have h2 := min_le_right (-(a ^ 2 + w ^ 2) / (2 * w)) M
  obtain ⟨y, hy⟩ := (exists_point_iff hb hw hwa (min (-(a ^ 2 + w ^ 2) / (2 * w)) M - 1)).mpr
    (Or.inr (by linarith))
  exact ⟨_, y, hy, by linarith, by linarith⟩

/-- [proved-standard; formal-checked] **The egg is a compact oval**: its points over `[−a, a]` form a compact set,
inside `[−a, a] × [−M, M]` with `M = √(b² a²/(a − w)²)`. -/
theorem egg_oval_isCompact (hw : 0 < w) (hwa : w < a) :
    IsCompact {p : ℝ × ℝ | eggEq a b w p.1 p.2 ∧ -a ≤ p.1 ∧ p.1 ≤ a} := by
  have hm : 0 < a - w := sub_pos.mpr hwa
  apply (isCompact_Icc.prod (isCompact_Icc (a := -Real.sqrt (b ^ 2 * a ^ 2 / (a - w) ^ 2))
    (b := Real.sqrt (b ^ 2 * a ^ 2 / (a - w) ^ 2)))).of_isClosed_subset
  · simp only [eggEq, Set.ofPred_and]
    exact (isClosed_eq (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop)))
  · rintro ⟨x, y⟩ ⟨h, h1, h2⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    have hu : (a - w) ^ 2 ≤ a ^ 2 + w ^ 2 + 2 * w * x := by nlinarith
    have hy : y ^ 2 ≤ b ^ 2 * a ^ 2 / (a - w) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      unfold eggEq at h
      nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg y), sq_nonneg (b * x)]
    exact abs_le.mp (Real.abs_le_sqrt hy)

/-- [proved-standard; formal-checked] **The egg is connected**: the upper arc `y = f(x)` and the lower arc `y = −f(x)`
over `[−a, a]`, `f = √(b²(a² − x²)/u)`, are its points, and they meet at `(±a, 0)`. -/
theorem egg_oval_isConnected (hw : 0 < w) (hwa : w < a) :
    IsConnected {p : ℝ × ℝ | eggEq a b w p.1 p.2 ∧ -a ≤ p.1 ∧ p.1 ≤ a} := by
  have hm : 0 < a - w := sub_pos.mpr hwa
  have ha : 0 < a := by linarith
  have hu : ∀ x ∈ Set.Icc (-a) a, 0 < a ^ 2 + w ^ 2 + 2 * w * x := fun x hx => by
    nlinarith [hx.1, sq_pos_of_pos hm]
  have hf : ContinuousOn (fun x => Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x)))
      (Set.Icc (-a) a) :=
    Real.continuous_sqrt.comp_continuousOn
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hu x hx).ne')
  have hI : IsConnected (Set.Icc (-a) a) := isConnected_Icc (by linarith)
  have hU := hI.image (fun x => (x, Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x))))
    (continuousOn_id.prodMk hf)
  have hL := hI.image (fun x => (x, -Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x))))
    (continuousOn_id.prodMk hf.neg)
  have hfa : Real.sqrt (b ^ 2 * (a ^ 2 - a ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * a)) = 0 := by simp
  have hmeet : (Set.image (fun x => (x, Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x))))
      (Set.Icc (-a) a) ∩ Set.image (fun x => (x, -Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) /
        (a ^ 2 + w ^ 2 + 2 * w * x)))) (Set.Icc (-a) a)).Nonempty :=
    ⟨(a, 0), ⟨a, ⟨by linarith, le_rfl⟩, by simp only [hfa]⟩, ⟨a, ⟨by linarith, le_rfl⟩, by simp only [hfa, neg_zero]⟩⟩
  convert hU.union hmeet hL using 1
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨h, h1, h2⟩
    have hux := hu x ⟨h1, h2⟩
    have hy2 : y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x) := by
      unfold eggEq at h
      rw [eq_div_iff hux.ne']
      linear_combination h
    have hs : |y| = Real.sqrt (b ^ 2 * (a ^ 2 - x ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x)) := by
      rw [← hy2, Real.sqrt_sq_eq_abs]
    rcases abs_choice y with hy | hy
    · exact Or.inl ⟨x, ⟨h1, h2⟩, rfl, by rw [← hs, hy]⟩
    · exact Or.inr ⟨x, ⟨h1, h2⟩, rfl, by rw [← hs, hy, neg_neg]⟩
  · rintro (⟨x', ⟨h1, h2⟩, rfl, rfl⟩ | ⟨x', ⟨h1, h2⟩, rfl, rfl⟩) <;> refine ⟨?_, h1, h2⟩ <;>
    · have hux := hu x' ⟨h1, h2⟩
      have hnn : 0 ≤ b ^ 2 * (a ^ 2 - x' ^ 2) / (a ^ 2 + w ^ 2 + 2 * w * x') :=
        div_nonneg (mul_nonneg (sq_nonneg b) (by nlinarith)) hux.le
      unfold eggEq
      simp only [neg_sq, Real.sq_sqrt hnn]
      exact mul_div_cancel₀ _ hux.ne'

end RealPicture

/-- [proved-standard; formal-checked] `eggFx` is the derivative of the egg's polynomial in `x`, over `ℝ`. -/
theorem hasDerivAt_egg_x (a b w x y : ℝ) :
    HasDerivAt (fun x => (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 - b ^ 2 * (a ^ 2 - x ^ 2)) (eggFx b w x y) x := by
  have h := ((((hasDerivAt_id x).const_mul (2 * w)).const_add (a ^ 2 + w ^ 2)).mul_const (y ^ 2)).sub
    (((hasDerivAt_pow 2 x).const_sub (a ^ 2)).const_mul (b ^ 2))
  refine h.congr_deriv ?_
  unfold eggFx
  norm_num
  ring

/-- [proved-standard; formal-checked] `eggFy` is the derivative of the egg's polynomial in `y`, over `ℝ`. -/
theorem hasDerivAt_egg_y (a b w x y : ℝ) :
    HasDerivAt (fun y => (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 - b ^ 2 * (a ^ 2 - x ^ 2)) (eggFy a w x y) y := by
  have h := ((hasDerivAt_pow 2 y).const_mul (a ^ 2 + w ^ 2 + 2 * w * x)).sub_const (b ^ 2 * (a ^ 2 - x ^ 2))
  refine h.congr_deriv ?_
  unfold eggFy
  norm_num
  ring

/-! ## §3 Rational eggs are elliptic curves over `ℚ` -/

section Rational

open WeierstrassCurve WeierstrassCurve.Affine
open Holonics.EllipticCurve.GeneralFace Holonics.EllipticCurve.EggSource

/-- [proved-derived; formal-checked] `j` of the Legendre parameter `A/B`, cleared of its nested fractions:
`j(A/B) = 256 (A² − AB + B²)³ / (A² B² (A − B)²)`. -/
theorem legendreJ_ratio {K : Type*} [Field K] {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A - B ≠ 0) :
    Geometry.EggModular.legendreJ (A / B) = 256 * (A ^ 2 - A * B + B ^ 2) ^ 3 / (A ^ 2 * B ^ 2 * (A - B) ^ 2) := by
  have hBA : B - A ≠ 0 := fun h => hAB (by linear_combination -h)
  have h1 : 1 - A / B = (B - A) / B := by field_simp
  unfold Geometry.EggModular.legendreJ
  rw [h1]
  field_simp
  ring

/-- [definition] **The rational egg's Weierstrass model** `V² = X (X + (a − w)²)(X + (a + w)²)`: the existing
full-two-torsion curve `GeneralFace.E (−(a − w)²) (−(a + w)²)` that `EggSource.eggPoint` lands in. It does not
depend on `b`. -/
abbrev eggCurve (a w : ℚ) : WeierstrassCurve.Affine ℚ := GeneralFace.E (rootA a w) (rootB a w)

/-- [proved-derived; formal-checked] The model's equation is the `−1` twist of the Legendre form,
`V² = X (X + A)(X + B)`. -/
theorem eggCurve_equation_iff (a w X V : ℚ) :
    (eggCurve a w).Equation X V ↔ V ^ 2 = legendreCubic (-branchA a w) (-branchB a w) X := by
  rw [equation_iff]
  simp only [GeneralFace.E, rootA, rootB, legendreCubic, branchA, branchB]
  constructor <;> intro h <;> linear_combination h

/-- [proved-derived; formal-checked] **The chain closes on the rational model.** The record's transport
`(x, y) ↦ (u, u y)` onto the twisted Legendre form, followed by the square-class rescaling
`(u, Y) ↦ (−u, (2w/b) Y)`, lands on `eggCurve a w`; these are the coordinates of `EggModular.egg_to_fullTwoTorsion`
and `EggSource.eggPoint`. -/
theorem egg_to_eggCurve {a b w x y : ℚ} (hb : b ≠ 0) (hw : w ≠ 0) (h : eggEq a b w x y) :
    (eggCurve a w).Equation (-eggU a w x) (2 * w / b * (eggU a w x * y)) := by
  rw [eggCurve_equation_iff]
  exact (eggTwist_iff_minusOne hb hw two_ne_zero).mp (twistEq_of_eggEq two_ne_zero hw h)

/-- [proved-derived; formal-checked] **The discriminant** of the rational model is the Legendre discriminant,
`Δ = 16 A² B² (A − B)² = 256 a² w² (a² − w²)⁴`, sixteen times the cubic's. -/
theorem eggCurve_Δ (a w : ℚ) :
    (eggCurve a w).Δ = 256 * a ^ 2 * w ^ 2 * (a ^ 2 - w ^ 2) ^ 4 ∧
      (eggCurve a w).Δ = 16 * (legendreCubicPoly (branchA a w) (branchB a w)).discr := by
  have h : (eggCurve a w).Δ = 256 * a ^ 2 * w ^ 2 * (a ^ 2 - w ^ 2) ^ 4 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, GeneralFace.E, rootA, rootB]
    ring
  refine ⟨h, ?_⟩
  rw [h, egg_discr]
  ring

/-- [proved-derived; formal-checked] `c₄ = 16 (a⁴ + 14 a² w² + w⁴)`, which is `16 a⁴` at `w = 0` and `256 a⁴` at
`w = a`: both degenerations are multiplicative. -/
theorem eggCurve_c₄ (a w : ℚ) :
    (eggCurve a w).c₄ = 16 * (a ^ 4 + 14 * a ^ 2 * w ^ 2 + w ^ 4) ∧
      (eggCurve a 0).c₄ = 16 * a ^ 4 ∧ (eggCurve a a).c₄ = 256 * a ^ 4 := by
  have h : ∀ w : ℚ, (eggCurve a w).c₄ = 16 * (a ^ 4 + 14 * a ^ 2 * w ^ 2 + w ^ 4) := fun w => by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, GeneralFace.E, rootA, rootB]
    ring
  exact ⟨h w, by rw [h]; ring, by rw [h]; ring⟩

/-- [proved-derived; formal-checked] **A rational egg is an elliptic curve over `ℚ`** when `a, w ≠ 0` and
`a ≠ ±w`. -/
theorem eggCurve_isElliptic {a w : ℚ} (ha : a ≠ 0) (hw : w ≠ 0) (hm : a - w ≠ 0) (hp : a + w ≠ 0) :
    (eggCurve a w).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, (eggCurve_Δ a w).1]
  have hd : a ^ 2 - w ^ 2 ≠ 0 := by
    rw [show a ^ 2 - w ^ 2 = (a - w) * (a + w) by ring]; exact mul_ne_zero hm hp
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) (pow_ne_zero 2 hw))
    (pow_ne_zero 4 hd)

/-- [proved-derived; formal-checked] In particular for `0 < w < a`. -/
theorem eggCurve_isElliptic_of_lt {a w : ℚ} (hw : 0 < w) (hwa : w < a) : (eggCurve a w).IsElliptic :=
  eggCurve_isElliptic (by linarith) hw.ne' (by linarith) (by linarith)

/-- [proved-derived; formal-checked] **Its `j` is the egg's Legendre `j`**: `j = c₄³/Δ = j(λ)` with
`λ = ((a − w)/(a + w))²` (`EggModular.legendreJ`). -/
theorem eggCurve_j (a w : ℚ) [(eggCurve a w).IsElliptic] :
    (eggCurve a w).j = Geometry.EggModular.legendreJ (branchA a w / branchB a w) := by
  have hΔ : (eggCurve a w).Δ ≠ 0 := (WeierstrassCurve.isUnit_Δ (W := eggCurve a w)).ne_zero
  rw [(eggCurve_Δ a w).1] at hΔ
  have ha : a ≠ 0 := fun h => hΔ (by rw [h]; ring)
  have hw : w ≠ 0 := fun h => hΔ (by rw [h]; ring)
  have hm : a - w ≠ 0 := fun h => hΔ (by rw [show a ^ 2 - w ^ 2 = (a - w) * (a + w) by ring, h]; ring)
  have hp : a + w ≠ 0 := fun h => hΔ (by rw [show a ^ 2 - w ^ 2 = (a - w) * (a + w) by ring, h]; ring)
  have hAB : branchA a w - branchB a w ≠ 0 := by
    unfold branchA branchB
    rw [show (a - w) ^ 2 - (a + w) ^ 2 = -4 * a * w by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hw
  have hA : branchA a w ≠ 0 := pow_ne_zero 2 hm
  have hB : branchB a w ≠ 0 := pow_ne_zero 2 hp
  rw [legendreJ_ratio hA hB hAB, WeierstrassCurve.j,
    Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', (eggCurve_Δ a w).1, (eggCurve_c₄ a w).1]
  have e1 : branchA a w ^ 2 - branchA a w * branchB a w + branchB a w ^ 2 = a ^ 4 + 14 * a ^ 2 * w ^ 2 + w ^ 4 := by
    unfold branchA branchB; ring
  have e2 : branchA a w ^ 2 * branchB a w ^ 2 * (branchA a w - branchB a w) ^ 2 =
      16 * a ^ 2 * w ^ 2 * (a ^ 2 - w ^ 2) ^ 4 := by
    unfold branchA branchB; ring
  have hd : a ^ 2 - w ^ 2 ≠ 0 := by
    rw [show a ^ 2 - w ^ 2 = (a - w) * (a + w) by ring]; exact mul_ne_zero hm hp
  rw [e1, e2]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The rational curve depends only on `β = w/a`**: the change of variables with
`u = a` (`X = a² X'`, `V = a³ V'`) carries `eggCurve a w` to `eggCurve 1 (w/a)`. -/
theorem eggCurve_scale {a : ℚ} (ha : a ≠ 0) (w : ℚ) :
    (⟨Units.mk0 a ha, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ℚ) • (eggCurve a w : WeierstrassCurve ℚ) =
      eggCurve 1 (w / a) := by
  rw [WeierstrassCurve.variableChange_def]
  simp only [GeneralFace.E, rootA, rootB, Units.val_inv_eq_inv_val, Units.val_mk0]
  ext <;> simp only [] <;> field_simp <;> ring

/-- [proved-derived; formal-checked] `EggSource.eggPoint` is the point `(−u, (2w/b) u y)`. -/
theorem eggPoint_eq (a b w x y : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0) (hm : a - w ≠ 0) (hp : a + w ≠ 0)
    (hegg : (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2)) :
    ∃ h, eggPoint a b w x y ha hb hw hm hp hegg =
      Point.some (-(a ^ 2 + w ^ 2 + 2 * w * x)) ((2 * w / b) * (a ^ 2 + w ^ 2 + 2 * w * x) * y) h := by
  unfold eggPoint
  generalize roots_regular ha hw hm hp = H
  obtain ⟨hA, hB, hAB⟩ := H
  exact ⟨_, rfl⟩

/-- [proved-derived; formal-checked] **The egg's vertices are the rational two-torsion.** The rational points
`(a, 0)` and `(−a, 0)` of the egg map to `(−(a + w)², 0)` and `(−(a − w)², 0)`; each is its own inverse, they
are distinct, and their sum is `(0, 0)`, the image of the egg's vertical point at infinity
(`EggSource.secondInfinityCarrier`). With the origin they are the four points of `E[2](ℚ)`. -/
theorem vertices_two_torsion {a b w : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0) (hm : a - w ≠ 0)
    (hp : a + w ≠ 0) :
    let R := eggPoint a b w a 0 ha hb hw hm hp (by ring)
    let L := eggPoint a b w (-a) 0 ha hb hw hm hp (by ring)
    R + R = 0 ∧ L + L = 0 ∧ R + L = secondInfinityCarrier a w ha hw hm hp ∧ R ≠ L := by
  intro R L
  have hx : -(a ^ 2 + w ^ 2 + 2 * w * a) ≠ -(a ^ 2 + w ^ 2 + 2 * w * (-a)) := by
    intro h
    apply mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) ha) hw
    linear_combination -h
  obtain ⟨h1, hR⟩ := eggPoint_eq a b w a 0 ha hb hw hm hp (by ring)
  obtain ⟨h2, hL⟩ := eggPoint_eq a b w (-a) 0 ha hb hw hm hp (by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show eggPoint a b w a 0 ha hb hw hm hp _ + eggPoint a b w a 0 ha hb hw hm hp _ = 0
    rw [hR]
    apply Point.add_self_of_Y_eq
    simp [negY, GeneralFace.E]
  · show eggPoint a b w (-a) 0 ha hb hw hm hp _ + eggPoint a b w (-a) 0 ha hb hw hm hp _ = 0
    rw [hL]
    apply Point.add_self_of_Y_eq
    simp [negY, GeneralFace.E]
  · show eggPoint a b w a 0 ha hb hw hm hp _ + eggPoint a b w (-a) 0 ha hb hw hm hp _ = _
    rw [hR, hL, Point.add_of_X_ne hx]
    unfold secondInfinityCarrier
    simp only [Point.some.injEq]
    rw [slope_of_X_ne hx]
    simp [addY, negAddY, addX, negY, GeneralFace.E, rootA, rootB]
    ring
  · show eggPoint a b w a 0 ha hb hw hm hp _ ≠ eggPoint a b w (-a) 0 ha hb hw hm hp _
    rw [hR, hL]
    intro h
    exact hx (Point.some.inj h).1

/-! ### A concrete egg: `a = 2`, `b = 1`, `w = 1` -/

/-- [proved-derived; formal-checked] **The egg `a = 2, b = 1, w = 1`** (`β = 1/2`, `k² = 3`, `λ = 1/9 = k⁻⁴`) is the
elliptic curve `V² = X³ + 10 X² + 9 X = X (X + 1)(X + 9)` over `ℚ`, with `Δ = 82944 = 2¹⁰ · 3⁴`,
`c₄ = 1168 = 2⁴ · 73` and `j = 1556068/81 = 2² · 73³ / 3⁴`. -/
theorem egg_211 :
    eggCurve 2 1 = ⟨0, 10, 0, 9, 0⟩ ∧ branchA (2 : ℚ) 1 / branchB 2 1 = 1 / 9 ∧
      ((1 + (1 : ℚ) / 2) / (1 - 1 / 2)) ^ 2 = 9 ∧
      (eggCurve 2 1).Δ = 82944 ∧ (82944 : ℚ) = 2 ^ 10 * 3 ^ 4 ∧
      (eggCurve 2 1).c₄ = 1168 ∧ (1168 : ℚ) = 2 ^ 4 * 73 ∧
      ∃ _ : (eggCurve 2 1).IsElliptic, (eggCurve 2 1).j = 1556068 / 81 ∧ (1556068 : ℚ) = 2 ^ 2 * 73 ^ 3 := by
  have hE : (eggCurve 2 1).IsElliptic := eggCurve_isElliptic (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, by norm_num [branchA, branchB], by norm_num, by rw [(eggCurve_Δ 2 1).1]; norm_num, by norm_num,
    by rw [(eggCurve_c₄ 2 1).1]; norm_num, by norm_num, hE, ?_, by norm_num⟩
  · simp only [GeneralFace.E, rootA, rootB]
    norm_num
  · rw [eggCurve_j]
    norm_num [branchA, branchB, Geometry.EggModular.legendreJ]

end Rational

/-! ## §4 The logarithmic period at the neck -/

section Period

open Real Filter Topology intervalIntegral MeasureTheory Set
open Holonics.Geometry.CompleteEllipticSeries


/-- [definition] The radicand of `K(√(1 − λ))`: `1 − (1 − λ) sin²θ = cos²θ + λ sin²θ`. -/
noncomputable def neckRadicand (l θ : ℝ) : ℝ := cos θ ^ 2 + l * sin θ ^ 2

/-- [proved-standard; formal-checked] The radicand is positive for `0 < λ ≤ 1`. -/
theorem neckRadicand_pos {l : ℝ} (h0 : 0 < l) (h1 : l ≤ 1) (θ : ℝ) : 0 < neckRadicand l θ := by
  unfold neckRadicand
  have := sin_sq_add_cos_sq θ
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg (cos θ)), sq_nonneg (sin θ)]

/-- [proved-standard; formal-checked] Its square root is continuous in `θ`. -/
theorem continuous_sqrt_neckRadicand {l : ℝ} : Continuous fun θ => √(neckRadicand l θ) := by
  unfold neckRadicand; fun_prop

/-- [proved-standard; formal-checked] `K(√(1 − λ)) = ∫₀^(π/2) (cos²θ + λ sin²θ)^(−1/2) dθ`. -/
theorem ellipticK_complement {l : ℝ} (h1 : l ≤ 1) :
    ellipticK (√(1 - l)) = ∫ θ in (0)..(π / 2), (√(neckRadicand l θ))⁻¹ := by
  unfold ellipticK
  congr 1
  funext θ
  rw [Real.sq_sqrt (by linarith)]
  unfold neckRadicand
  congr 2
  linear_combination (-1 : ℝ) * sin_sq_add_cos_sq θ

/-- [proved-standard; formal-checked] **The elementary part** of `K(√(1 − λ))`, with `c = √(1 − λ)`:
`∫₀^(π/2) sin θ (cos²θ + λ sin²θ)^(−1/2) dθ = c⁻¹ (log(1 + c) − ½ log λ)`, from the antiderivative
`−c⁻¹ log(c cos θ + √(cos²θ + λ sin²θ))`. -/
theorem integral_g {l : ℝ} (h0 : 0 < l) (h1 : l < 1) :
    ∫ θ in (0)..(π / 2), sin θ * (√(neckRadicand l θ))⁻¹ =
      (√(1 - l))⁻¹ * (log (1 + √(1 - l)) - log l / 2) := by
  have hc : √(1 - l) ^ 2 = 1 - l := Real.sq_sqrt (by linarith)
  have hcpos : 0 < √(1 - l) := Real.sqrt_pos.mpr (by linarith)
  have key : ∀ c R s co : ℝ, c ≠ 0 → R ≠ 0 → c * co + R ≠ 0 →
      -c⁻¹ * ((c * -s + 2 * co * -s * c ^ 2 / (2 * R)) / (c * co + R)) = s * R⁻¹ := by
    intro c R s co hc0 hR hs
    field_simp
    ring
  have hderiv : ∀ θ ∈ uIcc 0 (π / 2), HasDerivAt
      (fun θ => -(√(1 - l))⁻¹ * log (√(1 - l) * cos θ + √(neckRadicand l θ))) (sin θ * (√(neckRadicand l θ))⁻¹) θ := by
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
    have hD := neckRadicand_pos h0 h1.le θ
    have hR : 0 < √(neckRadicand l θ) := Real.sqrt_pos.mpr hD
    have hsum : 0 < √(1 - l) * cos θ + √(neckRadicand l θ) := by positivity
    have hDd : HasDerivAt (neckRadicand l) (2 * cos θ * -sin θ * √(1 - l) ^ 2) θ := by
      have := ((hasDerivAt_cos θ).pow 2).add (((hasDerivAt_sin θ).pow 2).const_mul l)
      refine this.congr_deriv ?_
      rw [hc]
      norm_num
      ring
    have hs := hDd.sqrt hD.ne'
    have hin := ((hasDerivAt_cos θ).const_mul (√(1 - l))).add hs
    have hl := hin.log hsum.ne'
    have hG := hl.const_mul (-(√(1 - l))⁻¹)
    refine hG.congr_deriv ?_
    exact key _ _ _ _ hcpos.ne' hR.ne' hsum.ne'
  have hint : IntervalIntegrable (fun θ => sin θ * (√(neckRadicand l θ))⁻¹) volume 0 (π / 2) :=
    (continuous_sin.mul (continuous_sqrt_neckRadicand.inv₀ fun θ =>
      (Real.sqrt_pos.mpr (neckRadicand_pos h0 h1.le θ)).ne')).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [cos_pi_div_two, sin_pi_div_two, cos_zero, sin_zero, neckRadicand]
  norm_num
  rw [Real.log_sqrt h0.le, add_comm (√(1 - l)) 1]
  ring

/-- [proved-standard; formal-checked] The remainder's limit integrand integrates to `log 2`:
`∫₀^(π/2) (1 − sin θ)/|cos θ| dθ = [log(1 + sin θ)]₀^(π/2)`. -/
theorem integral_limit : ∫ θ in (0)..(π / 2), (1 - sin θ) * (√(neckRadicand 0 θ))⁻¹ = log 2 := by
  have hcongr : EqOn (fun θ => (1 - sin θ) * (√(neckRadicand 0 θ))⁻¹) (fun θ => cos θ / (1 + sin θ))
      (uIcc 0 (π / 2)) := by
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
    simp only [neckRadicand, zero_mul, add_zero, Real.sqrt_sq hcos]
    rcases hcos.eq_or_lt with h | h
    · rw [← h]; simp
    · have h1 : 1 + sin θ ≠ 0 := by linarith
      field_simp
      linear_combination (-1 : ℝ) * sin_sq_add_cos_sq θ
  rw [integral_congr hcongr]
  have hderiv : ∀ θ ∈ uIcc 0 (π / 2), HasDerivAt (fun θ => log (1 + sin θ)) (cos θ / (1 + sin θ)) θ := by
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
    exact ((hasDerivAt_sin θ).const_add 1).log (by linarith)
  have hint : IntervalIntegrable (fun θ => cos θ / (1 + sin θ)) volume 0 (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_cos.div (continuousOn_const.add continuousOn_sin)
    intro θ hθ
    rw [uIcc_of_le (by positivity)] at hθ
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
    show (1 : ℝ) + sin θ ≠ 0
    linarith
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [sin_pi_div_two, sin_zero, add_zero, log_one, sub_zero]
  norm_num

/-- [proved-standard; formal-checked] **The remainder tends to `log 2`** as `λ → 0⁺`, by dominated convergence under
the bound `1`. -/
theorem tendsto_integral_h :
    Tendsto (fun l => ∫ θ in (0)..(π / 2), (1 - sin θ) * (√(neckRadicand l θ))⁻¹) (𝓝[>] 0) (𝓝 (log 2)) := by
  rw [← integral_limit]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with l hl
    exact ((continuous_const.sub continuous_sin).mul (continuous_sqrt_neckRadicand.inv₀ fun θ =>
      (Real.sqrt_pos.mpr (neckRadicand_pos hl.1 hl.2.le θ)).ne')).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with l hl
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le (by positivity)] at hθ
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
    have hsin1 : sin θ ≤ 1 := sin_le_one θ
    have hR : 0 < √(neckRadicand l θ) := Real.sqrt_pos.mpr (neckRadicand_pos hl.1 hl.2.le θ)
    have hle : 1 - sin θ ≤ √(neckRadicand l θ) := by
      rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 - sin θ)]
      apply Real.sqrt_le_sqrt
      unfold neckRadicand
      nlinarith [sin_sq_add_cos_sq θ, mul_nonneg hl.1.le (sq_nonneg (sin θ))]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (inv_nonneg.mpr hR.le)),
      ← div_eq_mul_inv, div_le_one hR]
    exact hle
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ hθ => ?_
    rw [uIoc_of_le (by positivity)] at hθ
    rcases hθ.2.lt_or_eq with h | h
    · have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], h⟩
      have hne : √(neckRadicand 0 θ) ≠ 0 := by
        apply (Real.sqrt_pos.mpr _).ne'
        unfold neckRadicand; simp only [zero_mul, add_zero]; positivity
      have hcont : ContinuousAt (fun l => (1 - sin θ) * (√(neckRadicand l θ))⁻¹) 0 := by
        apply continuousAt_const.mul
        exact (by unfold neckRadicand; fun_prop : ContinuousAt (fun l => √(neckRadicand l θ)) 0).inv₀ hne
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    · subst h
      simp only [sin_pi_div_two, sub_self, zero_mul]
      exact tendsto_const_nhds

/-- [proved-standard; formal-checked] **The logarithmic period at the neck**:
`K(√(1 − λ)) − ½ log(16/λ) → 0` as `λ → 0⁺` (DLMF §19.12). -/
theorem ellipticK_neck :
    Tendsto (fun l => ellipticK (√(1 - l)) - log (16 / l) / 2) (𝓝[>] 0) (𝓝 0) := by
  have hA : Tendsto (fun l : ℝ => (√(1 - l))⁻¹ * log (1 + √(1 - l))) (𝓝[>] 0) (𝓝 (log 2)) := by
    have : ContinuousAt (fun l : ℝ => (√(1 - l))⁻¹ * log (1 + √(1 - l))) 0 := by
      apply ContinuousAt.mul
      · apply ContinuousAt.inv₀ (by fun_prop)
        simp
      · apply ContinuousAt.log (by fun_prop)
        simp
    have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    norm_num at h
    exact h
  have hB : Tendsto (fun l : ℝ => l * log l * (-(1 / 2) / (√(1 - l) * (1 + √(1 - l))))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun l : ℝ => l * log l) (𝓝[>] 0) (𝓝 0) := by
      have := Real.continuous_mul_log.tendsto 0
      simp only [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : ContinuousAt (fun l : ℝ => -(1 / 2) / (√(1 - l) * (1 + √(1 - l)))) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      norm_num
    simpa using h1.mul (h2.tendsto.mono_left nhdsWithin_le_nhds)
  have hsum := ((tendsto_integral_h.add hA).add hB).sub_const (2 * log 2)
  rw [show log 2 + log 2 + 0 - 2 * log 2 = 0 by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with l hl
  have hc : √(1 - l) ^ 2 = 1 - l := Real.sq_sqrt (by linarith [hl.2])
  have hcpos : 0 < √(1 - l) := Real.sqrt_pos.mpr (by linarith [hl.2])
  have hsplit : ellipticK (√(1 - l)) = (∫ θ in (0)..(π / 2), sin θ * (√(neckRadicand l θ))⁻¹) +
      ∫ θ in (0)..(π / 2), (1 - sin θ) * (√(neckRadicand l θ))⁻¹ := by
    have hinv : Continuous fun θ => (√(neckRadicand l θ))⁻¹ :=
      continuous_sqrt_neckRadicand.inv₀ fun θ => (Real.sqrt_pos.mpr (neckRadicand_pos hl.1 hl.2.le θ)).ne'
    have hi1 : IntervalIntegrable (fun θ => sin θ * (√(neckRadicand l θ))⁻¹) volume 0 (π / 2) :=
      (continuous_sin.mul hinv).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ => (1 - sin θ) * (√(neckRadicand l θ))⁻¹) volume 0 (π / 2) :=
      ((continuous_const.sub continuous_sin).mul hinv).intervalIntegrable _ _
    rw [← integral_add hi1 hi2, ellipticK_complement hl.2.le]
    congr 1
    funext θ
    ring
  rw [hsplit, integral_g hl.1 hl.2, log_div (by norm_num) hl.1.ne',
    show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
  have h1c : 1 + √(1 - l) ≠ 0 := by positivity
  field_simp
  linear_combination (-log l) * hc

/-- [proved-derived; formal-checked] **The egg's period grows as the logarithm of the modulus.** The record's
closed form `(2/(b(a + w))) K(√(1 − λ))` for the period of `ω = dx/F_y` round the oval (its identification with the
oval's integral is not proved here) satisfies `(2/(b(a + w))) K(√(1 − λ)) − (1/(2ab)) log(1/λ) → 2 log 2/(ab)` as
`w → a⁻`. -/
theorem egg_period_neck {a b : ℝ} (ha : 0 < a) (hb : b ≠ 0) :
    Tendsto (fun w => 2 / (b * (a + w)) * ellipticK (√(1 - branchA a w / branchB a w)) -
      log (branchA a w / branchB a w)⁻¹ / (2 * a * b)) (𝓝[<] a) (𝓝 (2 * log 2 / (a * b))) := by
  have h2a : (a + a) ^ 2 ≠ 0 := by positivity
  have hlam : Tendsto (fun w => branchA a w / branchB a w) (𝓝[<] a) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun w => branchA a w / branchB a w) a := by
        unfold branchA branchB
        exact ContinuousAt.div (by fun_prop) (by fun_prop) h2a
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio a))
      simpa [branchA] using h
    · filter_upwards [Ioo_mem_nhdsLT ha] with w hw
      have : 0 < a - w := sub_pos.mpr hw.2
      have : 0 < a + w := by linarith [hw.1]
      show 0 < branchA a w / branchB a w
      unfold branchA branchB
      positivity
  have hK := ellipticK_neck.comp hlam
  have hlin : Tendsto (fun w : ℝ => a - w) (𝓝[<] a) (𝓝 0) := by
    have h : Tendsto (fun w : ℝ => a - w) (𝓝 a) (𝓝 (a - a)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun w : ℝ => (a - w) * log (a - w)) (𝓝[<] a) (𝓝 0) := by
    have h := (Real.continuous_mul_log.tendsto 0).comp hlin
    rw [zero_mul] at h
    exact h
  have hcont : ∀ f : ℝ → ℝ, ContinuousAt f a → Tendsto f (𝓝[<] a) (𝓝 (f a)) :=
    fun f hf => hf.tendsto.mono_left nhdsWithin_le_nhds
  have hden : b * (a + a) ≠ 0 := mul_ne_zero hb (by positivity)
  have hden' : a * b * (a + a) ≠ 0 := mul_ne_zero (mul_ne_zero ha.ne' hb) (by positivity)
  have c1 : ContinuousAt (fun w : ℝ => 2 / (b * (a + w))) a := ContinuousAt.div (by fun_prop) (by fun_prop) hden
  have c2 : ContinuousAt (fun w : ℝ => 1 / (b * (a + w))) a := ContinuousAt.div (by fun_prop) (by fun_prop) hden
  have c3 : ContinuousAt (fun w : ℝ => 1 / (a * b * (a + w))) a :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hden'
  have t1 := (hcont _ c1).mul hK
  have t2 := hcont (fun w => 1 / (b * (a + w)) * log 16) (c2.mul continuousAt_const)
  have t3 := hR.mul (hcont _ c3)
  have hlog : ContinuousAt (fun w : ℝ => log (a + w)) a := ContinuousAt.log (by fun_prop) (by positivity)
  have t4 := hlin.mul (hcont (fun w => log (a + w) / (a * b * (a + w)))
    (ContinuousAt.div hlog (by fun_prop) hden'))
  have hsum := ((t1.add t2).sub t3).add t4
  have hval : 2 / (b * (a + a)) * 0 + 1 / (b * (a + a)) * log 16 - 0 * (1 / (a * b * (a + a))) +
      0 * (log (a + a) / (a * b * (a + a))) = 2 * log 2 / (a * b) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
    field_simp
    ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with w hw
  have hm : 0 < a - w := sub_pos.mpr hw.2
  have hp : 0 < a + w := by linarith [hw.1]
  have hl : log (branchA a w / branchB a w) = 2 * log (a - w) - 2 * log (a + w) := by
    unfold branchA branchB
    rw [log_div (by positivity) (by positivity), log_pow, log_pow]
    push_cast
    ring
  have hlpos : branchA a w / branchB a w ≠ 0 := by unfold branchA branchB; positivity
  simp only [Function.comp, log_inv, hl]
  rw [log_div (by norm_num) hlpos, hl]
  field_simp
  ring

end Period

end Holonics.EllipticCurve.EggFamily
