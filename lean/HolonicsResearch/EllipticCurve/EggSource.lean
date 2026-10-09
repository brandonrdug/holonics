import HolonicsResearch.Geometry.EggModular
import HolonicsResearch.EllipticCurve.GeneralTwoTorsion

/-!
# The actual egg equation enters the existing descent point group

The producing operands are retained: `X = -(a²+w²+2wx)` and
`V = (2w/b)(a²+w²+2wx)y`. The target is the negative-twist model
`GeneralFace.E (-(a-w)²) (-(a+w)²)`, not an arbitrary equal-j curve.

`eggPoint` constructs a nonsingular point in the existing arithmetic group, and
`egg_doubles_enter_descent` consumes its existing doubling/kernel theorem.
The inverse affine chart is proved only on `X ≠ 0`; the homogeneous source
equation retains both infinity points. This file does not assert a complete
projective source/group equivalence or an original-egg rank equality (#62).

Agent-inferred: use the existing descent point group directly, rather than
installing a group on an unconnected source datatype. The recorded failures
avoided are carrying a located defect unrepaired into a consumer and mistaking
a receiver quotient for retained arithmetic data.
-/

noncomputable section

namespace Holonics.EllipticCurve.EggSource

open WeierstrassCurve.Affine
open Holonics.EllipticCurve GeneralFace

def rootA (a w : ℚ) : ℚ := -(a - w) ^ 2
def rootB (a w : ℚ) : ℚ := -(a + w) ^ 2

lemma root_difference (a w : ℚ) : rootA a w - rootB a w = 4 * a * w := by
  unfold rootA rootB
  ring

lemma roots_regular {a w : ℚ} (ha : a ≠ 0) (hw : w ≠ 0)
    (hm : a - w ≠ 0) (hp : a + w ≠ 0) :
    rootA a w ≠ 0 ∧ rootB a w ≠ 0 ∧ rootA a w - rootB a w ≠ 0 := by
  refine ⟨neg_ne_zero.mpr (pow_ne_zero 2 hm),
    neg_ne_zero.mpr (pow_ne_zero 2 hp), ?_⟩
  rw [root_difference]
  exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hw

/-- The missing direction from an actual cubic equation to its nonsingular point.
The distinct-root hypotheses are essential and are supplied at the consumer. -/
private lemma nonsingular_of_cubic {A B X V : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A - B ≠ 0)
    (hcurve : V ^ 2 = X * (X - A) * (X - B)) : (E A B).Nonsingular X V := by
  apply (nonsingular_iff X V).mpr
  constructor
  · rw [equation_iff]
    simp only [E]
    linear_combination hcurve
  · by_cases hV : V = 0
    · left
      have hroots : X * (X - A) * (X - B) = 0 := by
        simpa [hV] using hcurve.symm
      intro hd
      simp only [E] at hd
      rcases mul_eq_zero.mp hroots with hleft | hright
      · rcases mul_eq_zero.mp hleft with hzero | hAroot
        · subst X
          exact (mul_ne_zero hA hB) (by linear_combination -hd)
        · have hx : X = A := sub_eq_zero.mp hAroot
          subst X
          exact (mul_ne_zero hA hAB) (by linear_combination -hd)
      · have hx : X = B := sub_eq_zero.mp hright
        subst X
        exact (mul_ne_zero hB (neg_ne_zero.mpr hAB)) (by
          linear_combination -hd)
    · right
      simp only [E]
      intro hd
      exact hV (by linarith)

/-- An actual affine egg point carried into the existing arithmetic point group. -/
def eggPoint (a b w x y : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0)
    (hm : a - w ≠ 0) (hp : a + w ≠ 0)
    (hegg : (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2)) :
    (E (rootA a w) (rootB a w)).Point := by
  obtain ⟨hA, hB, hAB⟩ := roots_regular ha hw hm hp
  refine Point.some (-(a ^ 2 + w ^ 2 + 2 * w * x))
    ((2 * w / b) * (a ^ 2 + w ^ 2 + 2 * w * x) * y)
    (nonsingular_of_cubic hA hB hAB ?_)
  simpa only [rootA, rootB, sub_neg_eq_add] using
    Holonics.Geometry.EggModular.egg_to_fullTwoTorsion a b w x y hb hegg

/-- The concrete consuming join: the actual carrier's double is in the existing
descent kernel, with its exceptional slot conventions retained. -/
theorem egg_doubles_enter_descent (a b w x y : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0)
    (hm : a - w ≠ 0) (hp : a + w ≠ 0)
    (hegg : (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2)) :
    let P := eggPoint a b w x y ha hb hw hm hp hegg
    Descent.SqCls (slotOne (rootA a w) (rootB a w) (P + P)) 1 ∧
      Descent.SqCls (slotTwo (rootA a w) (rootB a w) (P + P)) 1 := by
  obtain ⟨hA, hB, hAB⟩ := roots_regular ha hw hm hp
  exact theDoublesLandInTheKernelOnEveryFullTwoTorsionCurve hA hB hAB
    (eggPoint a b w x y ha hb hw hm hp hegg)

/-- The affine inverse requires `X ≠ 0`. It is not defined by dividing through
the target's two-torsion point `(0,0)`. -/
theorem inverse_affine_equation (a b w X V : ℚ) (hw : w ≠ 0) (hX : X ≠ 0)
    (hcurve : V ^ 2 = X * (X + (a - w) ^ 2) * (X + (a + w) ^ 2)) :
    let x := (-X - a ^ 2 - w ^ 2) / (2 * w)
    let y := (-b / (2 * w * X)) * V
    (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2) := by
  dsimp
  simp only [mul_pow, div_pow]
  rw [hcurve]
  field_simp [hw, hX]
  ring

/-- The producing affine coordinates return the very same arithmetic operands. -/
theorem inverse_affine_returns_carrier (a b w X V : ℚ)
    (hb : b ≠ 0) (hw : w ≠ 0) (hX : X ≠ 0) :
    let x := (-X - a ^ 2 - w ^ 2) / (2 * w)
    let y := (-b / (2 * w * X)) * V
    -(a ^ 2 + w ^ 2 + 2 * w * x) = X ∧
      (2 * w / b) * (a ^ 2 + w ^ 2 + 2 * w * x) * y = V := by
  dsimp
  constructor <;> field_simp [hb, hw, hX] <;> ring

/-- The original homogeneous cubic, rather than a new tagged source object. -/
def homogeneousEquation (a b w X Y Z : ℚ) : Prop :=
  ((a ^ 2 + w ^ 2) * Z + 2 * w * X) * Y ^ 2 =
    b ^ 2 * Z * (a ^ 2 * Z ^ 2 - X ^ 2)

theorem homogeneous_affine (a b w x y : ℚ) :
    homogeneousEquation a b w x y 1 ↔
      (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2) := by
  simp [homogeneousEquation]

theorem homogeneous_infinities (a b w : ℚ) :
    homogeneousEquation a b w 1 0 0 ∧ homogeneousEquation a b w 0 1 0 := by
  simp [homogeneousEquation]

/-- With `w ≠ 0`, every nonzero infinity representative is on one of the two
declared lines. The zero triple remains excluded by projective coordinates. -/
theorem homogeneous_infinity_classification (a b w X Y : ℚ) (hw : w ≠ 0) :
    homogeneousEquation a b w X Y 0 ↔ X = 0 ∨ Y = 0 := by
  simp only [homogeneousEquation, mul_zero, add_zero, zero_mul, zero_pow,
    zero_sub, mul_eq_zero, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]
  simp [hw]

/-- The second source infinity point is assigned the actual `(0,0)` carrier;
the declared source origin is assigned the existing group's zero. Extending
these assignments to a complete projective equivalence remains separate. -/
def secondInfinityCarrier (a w : ℚ) (ha : a ≠ 0) (hw : w ≠ 0)
    (hm : a - w ≠ 0) (hp : a + w ≠ 0) : (E (rootA a w) (rootB a w)).Point := by
  obtain ⟨hA, hB, hAB⟩ := roots_regular ha hw hm hp
  exact Point.some 0 0 (nonsingular_of_cubic hA hB hAB (by ring))

theorem secondInfinityCarrier_is_two_torsion (a w : ℚ)
    (ha : a ≠ 0) (hw : w ≠ 0) (hm : a - w ≠ 0) (hp : a + w ≠ 0) :
    secondInfinityCarrier a w ha hw hm hp + secondInfinityCarrier a w ha hw hm hp = 0 := by
  unfold secondInfinityCarrier
  apply Point.add_self_of_Y_eq
  simp [negY, E]

/-- An unconditional rank bound on the actual receiving model of `a=3,b=2,w=1`.
This does not transfer a rank back to an unproved source-group equivalence. -/
theorem egg_321_receiving_model_rank_bound :
    ∃ r : ℕ, RankIsOn (E (-4) (-16)) r ∧ 2 ^ r ≤ 1296 := by
  obtain ⟨r, hr, hbound⟩ :=
    GeneralTwoTorsion.theRankClauseIsWellPosedOnEveryFullTwoTorsionCurve
      (a := (-4 : ℤ)) (b := (-16 : ℤ)) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨r, ?_, ?_⟩
  · convert hr using 1 <;> norm_num
  · have hcard : (((-4 : ℤ) * (-16) * (-4 - (-16))).natAbs.divisors.card) = 18 := by
      decide
    simp only [hcard] at hbound
    norm_num at hbound
    exact hbound

end Holonics.EllipticCurve.EggSource

section Audit
open Holonics.EllipticCurve.EggSource
#print axioms egg_doubles_enter_descent
#print axioms inverse_affine_equation
#print axioms inverse_affine_returns_carrier
#print axioms homogeneous_infinity_classification
#print axioms secondInfinityCarrier_is_two_torsion
#print axioms egg_321_receiving_model_rank_bound
end Audit
