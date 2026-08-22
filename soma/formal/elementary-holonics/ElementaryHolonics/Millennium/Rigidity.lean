import Mathlib.Tactic

/-!
# Rigidity: the self-stress is a supported realizer, and its form's radical is the gauge

A bar framework's constraint geometry carries, in miniature and exactly, the shape this
development has been building around the index and placement statements:

* a **self-stress** — a tension/compression weighting on the bars that balances at every joint —
  is a *supported realizer* in the most literal sense: a physically supported object whose
  existence is a property of the configuration, not a declaration;
* the **stress form** it induces on vertex loads is symmetric and, for the right stress, positive
  semidefinite, and its **radical is exactly the rigid-body gauge** — the loads that no relative
  measurement sees; the descent through that radical is the faithful quotient of `Paying` and
  `AlgebraicGNS`, arriving on physical material;
* **prestress stability** demands positivity of the stress energy **on the flex subspace** — a
  *third* selection rule for "positivity on a declared subspace", beside the involution selector
  of `ReflectedPositivity` and the Lefschetz selector, which are already proved not to share a
  selection rule.  The selector here is the kernel of the rigidity Jacobian: material, not
  declared.

Two concrete instances are proved, both exact over `ℚ`:

1. **The square with both diagonals** (`K₄` on the unit square).  Its self-stress is exhibited and
   balanced at every joint; the induced stress form is the rank-one square of one slot functional;
   its radical is computed and contains the three gauge loads (the constant load and the two
   coordinate loads of the configuration itself); off the radical the form is strictly positive;
   and the quotient by the radical is one-dimensional — the maximal rank `n − d − 1 = 4 − 2 − 1`
   a planar four-vertex stress matrix can have.
2. **The collinear triangle** (three collinear joints, all three bars).  It carries a self-stress
   *and* a genuine first-order flex — the transverse motion of the middle joint — proved not to be
   any infinitesimal rigid motion of the plane; and the stress energy is **strictly positive** on
   that flex.  This is the textbook prestress-stable framework: infinitesimally flexible, yet
   rigid, with the rigidity carried by second-order information the stress form sees.

Both controls that make the structure falsifiable are present: the all-ones weighting is **not** a
self-stress (equilibrium fails at the first joint, exhibited), and the sign-flipped stress fails
positivity at an exhibited witness.  A check whose material cannot vary the property under test
carries nothing; here every declared input can fail and two of them do.

**Imported and not proved here** (each a classical theorem about real frameworks, cited so the
instances are read at their true height): Maxwell's counting rule and the Maxwell–Calladine index
relation; Connelly's super-stability theorem — a positive-semidefinite stress matrix of maximal
rank `n − d − 1`, with no affine flexes, forces global rigidity (Connelly 1982); prestress
stability implies rigidity (Connelly–Whiteley 1996); and the generic characterization of global
rigidity by a maximal-rank stress (Gortler–Healy–Thurston 2010).  Nothing below states or uses
those theorems; what is proved is the exact linear algebra of two witnesses.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`:
`grep -rli "rigidity" Mathlib --include='*.lean'` → 2 files, both analytic (Liouville-type)
rigidity; `grep -rli "self.stress\|tensegrity\|infinitesimal.*flex"` → 0 files.  Those commands
measure those names over that scope; they are not a claim that no related content exists under
another name.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here is a claim about any
named conjecture; no variety, cycle, curve or L-function appears, and no protein does either — the
constraint mathematics stands on its own carriers.
-/

namespace Soma.Holonics.Millennium.Rigidity

/-- A planar point (or load, or infinitesimal motion) over `ℚ`. -/
abbrev Pt : Type := ℚ × ℚ

/-- The planar dot pairing, written out. -/
def dot (a b : Pt) : ℚ := a.1 * b.1 + a.2 * b.2

/-! ## 1. The square with both diagonals: the self-stress balances

Joints `p1 p2 p3 p4` at the corners of the unit square; the four sides carry stress `+1`, the two
diagonals `−1`.  A *self-stress* means: at every joint, the stress-weighted sum of outgoing bar
vectors vanishes.  This is the equilibrium condition `ker Jᵀ`, and it holds. -/

def p1 : Pt := (0, 0)
def p2 : Pt := (1, 0)
def p3 : Pt := (1, 1)
def p4 : Pt := (0, 1)

/-- **The declared stress is a self-stress: it balances at every joint.**

Sides `12, 23, 34, 41` at `+1`; diagonals `13, 24` at `−1`.  Four vanishing sums, one per
joint. -/
theorem theStressBalancesAtEveryJoint :
    (1 : ℚ) • (p2 - p1) + (1 : ℚ) • (p4 - p1) + (-1 : ℚ) • (p3 - p1) = 0 ∧
    (1 : ℚ) • (p1 - p2) + (1 : ℚ) • (p3 - p2) + (-1 : ℚ) • (p4 - p2) = 0 ∧
    (1 : ℚ) • (p2 - p3) + (1 : ℚ) • (p4 - p3) + (-1 : ℚ) • (p1 - p3) = 0 ∧
    (1 : ℚ) • (p3 - p4) + (1 : ℚ) • (p1 - p4) + (-1 : ℚ) • (p2 - p4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [p1, p2, p3, p4, Prod.ext_iff]

/-- **The all-ones weighting is not a self-stress** — equilibrium fails at the first joint.  This
is the control that makes `theStressBalancesAtEveryJoint` a finding: the balance condition can
fail, and for a nearby weighting it does. -/
theorem theAllOnesWeightingIsNotASelfStress :
    (1 : ℚ) • (p2 - p1) + (1 : ℚ) • (p4 - p1) + (1 : ℚ) • (p3 - p1) ≠ 0 := by
  simp [p1, p2, p3, p4, Prod.ext_iff]

/-! ## 2. The stress form, its radical, and the gauge

A stress on the bars induces a symmetric form on scalar **loads** at the joints — the stress
matrix.  For the square-with-diagonals stress that form is the square of one slot functional, so
everything about it is computable by hand and is. -/

/-- A scalar load per joint of the four-joint framework. -/
abbrev Load4 : Type := ℚ × ℚ × ℚ × ℚ

/-- The slot functional of the square's self-stress: the alternating sum of the loads. -/
def slot (x : Load4) : ℚ := x.1 - x.2.1 + x.2.2.1 - x.2.2.2

/-- The stress form induced by the square's self-stress, in its factored presentation. -/
def stressForm (x y : Load4) : ℚ := slot x * slot y

/-- **The factored form IS the bar-sum form.**  The stress-weighted sum over the six bars of
`(xᵢ − xⱼ)(yᵢ − yⱼ)` — sides at `+1`, diagonals at `−1` — equals `slot x · slot y` identically.
So the rank-one square and the physical stress matrix are one object, by polynomial identity. -/
theorem theBarSumIsTheFactoredForm (x y : Load4) :
    (x.1 - x.2.1) * (y.1 - y.2.1) + (x.2.1 - x.2.2.1) * (y.2.1 - y.2.2.1)
      + (x.2.2.1 - x.2.2.2) * (y.2.2.1 - y.2.2.2) + (x.2.2.2 - x.1) * (y.2.2.2 - y.1)
      - (x.1 - x.2.2.1) * (y.1 - y.2.2.1) - (x.2.1 - x.2.2.2) * (y.2.1 - y.2.2.2)
      = stressForm x y := by
  simp only [stressForm, slot]; ring

/-- The stress form is symmetric.  *The proof is `mul_comm` — stated so the docstring says so.* -/
theorem theStressFormIsSymmetric (x y : Load4) : stressForm x y = stressForm y x :=
  mul_comm _ _

/-- The stress form is positive semidefinite. -/
theorem theStressFormIsNonnegative (x : Load4) : 0 ≤ stressForm x x :=
  mul_self_nonneg (slot x)

/-- **The null cone is the radical, concretely**: the self-pairing vanishes exactly on the kernel
of the slot.  This is `Paying.theNullConeIsTheRadical` arriving on a form small enough to see
through. -/
theorem theNullConeIsTheSlotKernel (x : Load4) : stressForm x x = 0 ↔ slot x = 0 :=
  mul_self_eq_zero

/-- **The radical is the kernel of the slot**: a load pairs to zero against everything iff its
slot vanishes.  Forward direction: pair against the first standard load. -/
theorem theRadicalIsTheSlotKernel (x : Load4) :
    (∀ y : Load4, stressForm x y = 0) ↔ slot x = 0 := by
  constructor
  · intro h
    have h1 := h ((1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ))
    simpa [stressForm, slot] using h1
  · intro h y
    simp [stressForm, h]

/-- **The three gauge loads lie in the radical.**  The constant load, the configuration's own
`x`-coordinates read as a load, and its `y`-coordinates read as a load, all have vanishing slot —
the affine gauge of the plane, which is exactly what a stress matrix must annihilate.  No relative
measurement sees these loads, and the form agrees. -/
theorem theGaugeIsInTheRadical :
    slot ((1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ)) = 0 ∧
    slot ((0 : ℚ), (1 : ℚ), (1 : ℚ), (0 : ℚ)) = 0 ∧
    slot ((0 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ)) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [slot]

/-- **Off the radical the form is strictly positive** — the descent through the radical is
faithful, which is the trichotomy's third row on this carrier. -/
theorem theFormPaysOffTheRadical (x : Load4) (hx : slot x ≠ 0) : 0 < stressForm x x :=
  mul_self_pos.mpr hx

/-- **The quotient by the radical is one-dimensional**: subtracting `slot x` times the first
standard load lands every load in the radical.  One dimension is the maximal rank `n − d − 1 =
4 − 2 − 1` a planar four-joint stress matrix can have — the rank Connelly's super-stability and
the generic global-rigidity characterization ask for, reached here exactly. -/
theorem theQuotientIsOneDimensional (x : Load4) :
    slot (x - (slot x) • ((1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ))) = 0 := by
  simp only [slot, Prod.smul_mk, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The sign-flipped stress fails positivity at an exhibited witness.**  Negating the stress
negates the form, and at the first standard load the flipped self-pairing is `−1 < 0`.  Positivity
is a property of *this* stress, not of the structure — the control the tautology rule demands. -/
theorem theFlippedStressFailsAtTheWitness :
    -(stressForm ((1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)) ((1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ))) < 0 := by
  norm_num [stressForm, slot]

/-! ## 3. The collinear triangle: a flex, a stress, and positivity on the flex

Three collinear joints with all three bars.  The framework is infinitesimally flexible — the
middle joint can move transversely at first order — yet it carries a self-stress whose energy is
strictly positive on that flex.  This is prestress stability's exact witness, and the subspace on
which positivity is demanded is the **flex space**: a selector read off the material, not
declared. -/

def q1 : Pt := (0, 0)
def q2 : Pt := (1, 0)
def q3 : Pt := (2, 0)

/-- **The collinear stress balances at every joint.**  Bars `12` and `23` at `+2`, the long bar
`13` at `−1`. -/
theorem theCollinearStressBalances :
    (2 : ℚ) • (q2 - q1) + (-1 : ℚ) • (q3 - q1) = 0 ∧
    (2 : ℚ) • (q1 - q2) + (2 : ℚ) • (q3 - q2) = 0 ∧
    (-1 : ℚ) • (q1 - q3) + (2 : ℚ) • (q2 - q3) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [q1, q2, q3, Prod.ext_iff] <;> norm_num

/-- The transverse flex: the middle joint moves off the line; the ends stand. -/
def u1 : Pt := (0, 0)
def u2 : Pt := (0, 1)
def u3 : Pt := (0, 0)

/-- **The transverse motion is a first-order flex**: on every bar, the bar vector is orthogonal to
the relative motion, so every bar length is stationary. -/
theorem theTransverseMotionIsAFirstOrderFlex :
    dot (q1 - q2) (u1 - u2) = 0 ∧ dot (q2 - q3) (u2 - u3) = 0 ∧ dot (q1 - q3) (u1 - u3) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [dot, q1, q2, q3, u1, u2, u3]

/-- **The flex is not a rigid motion of the plane.**  An infinitesimal rigid motion is a
translation plus an infinitesimal rotation, `p ↦ (a − c·p₂, b + c·p₁)`; no choice of `a, b, c`
returns the transverse flex, because the ends force `b = 0` and `b + 2c = 0` while the middle
forces `b + c = 1`. -/
theorem theFlexIsNotARigidMotion :
    ∀ a b c : ℚ,
      ¬ ((a - c * q1.2, b + c * q1.1) = u1 ∧ (a - c * q2.2, b + c * q2.1) = u2 ∧
         (a - c * q3.2, b + c * q3.1) = u3) := by
  intro a b c h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [q1, q2, q3, u1, u2, u3, Prod.ext_iff] at h1 h2 h3
  obtain ⟨-, hb⟩ := h1
  obtain ⟨-, hbc⟩ := h2
  obtain ⟨-, hb2c⟩ := h3
  norm_num at hb hbc hb2c
  linarith [hb, hbc, hb2c]

/-- **The stress energy is strictly positive on the flex.**  With the collinear self-stress, the
weighted sum of squared relative motions over the bars is `4 > 0`.  An infinitesimally flexible
framework whose stress energy pays on its flex — positivity on the material's own selected
subspace, which is what the imported prestress-stability theorem converts into rigidity. -/
theorem theStressEnergyPaysOnTheFlex :
    0 < (2 : ℚ) * dot (u1 - u2) (u1 - u2) + (2 : ℚ) * dot (u2 - u3) (u2 - u3)
        + (-1 : ℚ) * dot (u1 - u3) (u1 - u3) := by
  norm_num [dot, u1, u2, u3]

/-- **The flex energy can fail too**: with the sign-flipped collinear stress the same sum is
`−4 < 0`.  The positivity on the flex is a property of the stress, not of the flex. -/
theorem theFlippedStressFailsOnTheFlex :
    (-2 : ℚ) * dot (u1 - u2) (u1 - u2) + (-2 : ℚ) * dot (u2 - u3) (u2 - u3)
        + (1 : ℚ) * dot (u1 - u3) (u1 - u3) < 0 := by
  norm_num [dot, u1, u2, u3]

/-! ## 4. A shared junction intersects continuation fibres

The protein-fold deed needs no protein theorem. Its reusable law is the exact linear statement
behind a junction carrying two simultaneous constraints. If `F` and `G` read two local constraint
faces on the same continuation space, the combined receiver is `F.prod G`, and its invisible
continuations are precisely `ker F ⊓ ker G`. A count such as “two constraints” cannot say this:
the intersection may equal either kernel, may be strictly smaller, and its dimension depends on
the actual maps. The separating theorem below exhibits the strict case without assuming finite
dimension or choosing a basis. -/

section SharedJunction

variable {R V W₁ W₂ : Type*} [Semiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid W₁] [Module R W₁]
  [AddCommMonoid W₂] [Module R W₂]

/-- **The shared-junction continuation fibre is the intersection of the two local fibres.**

This is the exact object that a shared vertex contributes: not an independently subtracted degree
count, but the pullback of the two zero sections. -/
theorem theSharedJunctionFibreIsTheIntersection (F : V →ₗ[R] W₁) (G : V →ₗ[R] W₂) :
    LinearMap.ker (F.prod G) = LinearMap.ker F ⊓ LinearMap.ker G :=
  LinearMap.ker_prod F G

/-- Removing the second contact can only enlarge the continuation fibre. -/
theorem removingTheSecondConstraintCanOnlyEnlargeTheFibre (F : V →ₗ[R] W₁) (G : V →ₗ[R] W₂) :
    LinearMap.ker (F.prod G) ≤ LinearMap.ker F := by
  rw [theSharedJunctionFibreIsTheIntersection]
  exact inf_le_left

/-- **One continuation accepted by `F` and rejected by `G` is an exact separator.** It lies in the
fibre after the second contact is removed and not in the joined fibre before removal. Thus the
enlargement is material whenever such an occurrence exists; it is not inferred from the number of
maps. -/
theorem aContinuationSeenOnlyByTheSecondConstraintIsASeparator
    (F : V →ₗ[R] W₁) (G : V →ₗ[R] W₂) (x : V) (hF : F x = 0) (hG : G x ≠ 0) :
    x ∈ LinearMap.ker F ∧ x ∉ LinearMap.ker (F.prod G) := by
  constructor
  · exact hF
  · rw [theSharedJunctionFibreIsTheIntersection]
    simp only [Submodule.mem_inf, LinearMap.mem_ker]
    exact fun h => hG h.2

end SharedJunction

end Soma.Holonics.Millennium.Rigidity
