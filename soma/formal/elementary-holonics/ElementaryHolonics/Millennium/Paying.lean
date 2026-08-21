import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic
import ElementaryHolonics.Millennium.Gluing
import ElementaryHolonics.Millennium.Swing

/-!
# What pays — compressed positivity, and descent as an inductive partitioning

Two structures, both of which the previous records named as owed and neither of which existed.

**Compressed positivity.**  A form, a declared cutoff, and definiteness on the *orthogonal
complement of the cutoff*.  That single shape carries two very different-looking programmes:

* on a surface, the intersection form is **negative** definite on the orthogonal complement of an
  ample class, and that is what makes the trace form on correspondences positive;
* at the archimedean place, the trace of a scaling action compressed onto the orthogonal
  complement of the range of a phase-space cutoff is **positive**, and that is Weil positivity.

The two differ by a sign and by nothing else structural, so `sign` is carried as a field rather
than fixed.  In both readings the object that pays is **the retained remainder** — what the
declared aperture does not admit.

**Descent.**  A finite set of representatives modulo doubling plus a size that strictly falls
under halving, above a bound, generates everything.  That is the inductive partitioning by which a
finitely generated atlas is composed out of a bounded core, and it is the engine underneath the
finite generation of the rational points of an elliptic curve.

Every `theorem` here is discharged.  No named conjecture is formalized, and the two readings above
are recorded as readings.
-/

namespace Soma.Holonics.Millennium.Paying

open Soma.Holonics.Millennium Soma.Holonics.Millennium.Swing

universe u

/-! ## 1. Compressed positivity: definiteness on the retained remainder -/

variable {V : Type u} [AddCommGroup V]

/-- A **compressed positivity datum**: a symmetric form, a declared cutoff, a retained remainder
orthogonal to it, and definiteness of the form on the remainder up to one overall sign.

The `sign` is carried because it is the only structural difference between the two readings the
module docstring names: `-1` on a surface's intersection form, `+1` for the compressed trace at a
place.  Fixing it would make the structure fit one reading and refuse the other. -/
structure CompressedPositivity (V : Type u) [AddCommGroup V] where
  /-- The form.  **Bilinear by construction** — the earlier version of this structure assumed only
  symmetry, which left its radical outside the subgroup lattice and made the descent question
  unaskable.  That defect is repaired here. -/
  form : V →+ V →+ ℚ
  /-- It is symmetric. -/
  form_symm : ∀ a b, form a b = form b a
  /-- What the declared aperture admits. -/
  cutoff : AddSubgroup V
  /-- What it does not — the retained remainder. -/
  remainder : AddSubgroup V
  /-- The remainder is orthogonal to the cutoff. -/
  orthogonal : ∀ c ∈ cutoff, ∀ v ∈ remainder, form c v = 0
  /-- The overall sign. -/
  sign : ℚ
  /-- It is a unit. -/
  sign_unit : sign = 1 ∨ sign = -1
  /-- The form is semi-definite on the remainder, with that sign. -/
  definite : ∀ v ∈ remainder, 0 ≤ sign * form v v

namespace CompressedPositivity

variable (C : CompressedPositivity V)

/-- Scaling in the first slot, from bilinearity. -/
theorem form_zsmul (n : ℤ) (a b : V) : C.form (n • a) b = n * C.form a b := by
  rw [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul]

/-- Scaling in the second slot, by symmetry. -/
theorem form_zsmul_right (n : ℤ) (a b : V) : C.form a (n • b) = n * C.form a b := by
  rw [C.form_symm, C.form_zsmul, C.form_symm]

/-- A linear function of an integer that is never negative has zero slope. -/
private theorem linear_nonneg_forces_zero {b c : ℚ} (h : ∀ n : ℤ, 0 ≤ 2 * n * b + c) : b = 0 := by
  by_contra hb
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · obtain ⟨n, hn⟩ := exists_int_gt (-c / (2 * b))
    have h2b : 2 * b < 0 := by linarith
    have : 2 * b * (n : ℚ) < 2 * b * (-c / (2 * b)) := by
      exact mul_lt_mul_of_neg_left hn h2b
    rw [mul_div_cancel₀ _ (by linarith : (2 : ℚ) * b ≠ 0)] at this
    have := h n
    nlinarith [this]
  · obtain ⟨n, hn⟩ := exists_int_lt (-c / (2 * b))
    have h2b : (0 : ℚ) < 2 * b := by linarith
    have : 2 * b * (n : ℚ) < 2 * b * (-c / (2 * b)) := by
      exact mul_lt_mul_of_pos_left hn h2b
    rw [mul_div_cancel₀ _ (by linarith : (2 : ℚ) * b ≠ 0)] at this
    have := h n
    nlinarith [this]

/-- **A semi-definite form's null cone is its radical.**

If a member of the remainder pairs with itself to nothing, it pairs with *everything* in the
remainder to nothing.  So faithfulness is not an extra hypothesis about self-pairings — it is the
statement that the radical is trivial, and semi-definiteness alone forces the two to agree.

*Aside: this is the Cauchy-Schwarz consequence, argued over the integers because the carrier is an
abelian group and no rational scaling is available on it.*

**MEASURED 2026-08-20: mathlib already owns this, and more generally.**
`LinearMap.BilinForm.apply_apply_same_eq_zero_iff` in
`Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean` states `B x x = 0 <-> x in LinearMap.ker B` for a
symmetric form non-negative on the whole module, over any `[CommRing R] [LinearOrder R]
[IsStrictOrderedRing R]`, resting on `apply_mul_apply_le_of_forall_zero_le` — mathlib's own
Cauchy-Schwarz for positive semidefinite forms. The proof below is not wrong and is not redundant
*for this carrier*, because `CompressedPositivity.form` is a `V ->+ V ->+ Rat` on an abelian group
rather than a `BilinForm R M` on an `R`-module, and mathlib's lemma does not apply to it. **It
becomes redundant exactly when this development is restated over `LinearMap.BilinForm`, and that is
one of the reasons to restate it.** A hand proof of a mathlib lemma is a cost, not an asset. -/
theorem theNullConeIsTheRadical {v : V} (hv : v ∈ C.remainder)
    (hnull : C.sign * C.form v v = 0) {w : V} (hw : w ∈ C.remainder) :
    C.sign * C.form v w = 0 := by
  have key : ∀ n : ℤ, 0 ≤ 2 * (n : ℚ) * (C.sign * C.form v w) + C.sign * C.form w w := by
    intro n
    have hmem : n • v + w ∈ C.remainder :=
      C.remainder.add_mem (C.remainder.zsmul_mem hv n) hw
    have hexp : C.form (n • v + w) (n • v + w)
        = (n : ℚ) * (n : ℚ) * C.form v v + 2 * (n : ℚ) * C.form v w + C.form w w := by
      simp only [map_add, AddMonoidHom.add_apply, C.form_zsmul, C.form_zsmul_right]
      rw [C.form_symm w v]
      ring
    have := C.definite _ hmem
    rw [hexp] at this
    nlinarith [this, hnull]
  have := linear_nonneg_forces_zero key
  exact this

/-- **The radical of the form on the remainder** — a genuine subgroup, which it could not be before
the form was bilinear. -/
def radical : AddSubgroup V where
  carrier := {v | v ∈ C.remainder ∧ ∀ w ∈ C.remainder, C.form v w = 0}
  zero_mem' := ⟨C.remainder.zero_mem, by intro w _; simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
    refine ⟨C.remainder.add_mem ha hb, ?_⟩
    intro w hw
    rw [map_add, AddMonoidHom.add_apply, ha0 w hw, hb0 w hw, add_zero]
  neg_mem' := by
    rintro a ⟨ha, ha0⟩
    refine ⟨C.remainder.neg_mem ha, ?_⟩
    intro w hw
    rw [map_neg, AddMonoidHom.neg_apply, ha0 w hw, neg_zero]

/-- **Faithfulness is exactly triviality of the radical.**

The earlier structure carried faithfulness as a separate axiom about self-pairings.  It is not
separate: with a bilinear semi-definite form, a member pairs with itself to nothing exactly when it
is in the radical. -/
theorem theFaithfulConditionIsTheTrivialRadical :
    (∀ v ∈ C.remainder, C.sign * C.form v v = 0 → v = 0) ↔ ∀ v ∈ C.radical, v = 0 := by
  constructor
  · intro h v hv
    refine h v hv.1 ?_
    rw [hv.2 v hv.1, mul_zero]
  · intro h v hv hnull
    refine h v ⟨hv, ?_⟩
    intro w hw
    have := C.theNullConeIsTheRadical hv hnull hw
    rcases C.sign_unit with hs | hs <;> rw [hs] at this <;> linarith

/-- **A datum whose radical is trivial carries a paying pairing on its remainder.** -/
def payingPairing (htriv : ∀ v ∈ C.radical, v = 0) : PayingPairing C.remainder where
  pair a b := C.sign * C.form a b
  pair_symm := by intro a b; rw [C.form_symm]
  pair_self_nonneg := by intro a; exact C.definite a.1 a.2
  null_cone_is_a_point := by
    intro a ha
    exact Subtype.ext ((C.theFaithfulConditionIsTheTrivialRadical.mpr htriv) a.1 a.2 ha)

/-- **Therefore every nonzero element of the retained remainder is seen.** -/
theorem theRetainedRemainderIsSeparated (htriv : ∀ v ∈ C.radical, v = 0)
    {a : C.remainder} (ha : a ≠ 0) : ∃ b : C.remainder, C.sign * C.form a b ≠ 0 :=
  (C.payingPairing htriv).separates ha

/-- **The cutoff contributes nothing to the pairing.** -/
theorem theCutoffIsInvisibleToTheRemainder {c : V} (hc : c ∈ C.cutoff)
    {v : V} (hv : v ∈ C.remainder) : C.form c v = 0 :=
  C.orthogonal c hc v hv

/-- **The form descends to a quotient exactly when what is quotiented out is in the radical.**

This is the question the previous record could not pose.  A chain puts a quotient at the middle;
a compressed positivity datum puts a form on the retained population; and the form survives the
quotient exactly when the realized population pairs with everything retained to nothing. -/
theorem theFormDescendsIffTheQuotientedIsInTheRadical (N : AddSubgroup V)
    (hN : N ≤ C.remainder) :
    (∀ v ∈ C.remainder, ∀ r ∈ N, ∀ w ∈ C.remainder, C.form (v + r) w = C.form v w)
      ↔ (∀ r ∈ N, ∀ w ∈ C.remainder, C.form r w = 0) := by
  constructor
  · intro h r hr w hw
    have := h 0 C.remainder.zero_mem r hr w hw
    simpa using this
  · intro h v _ r hr w hw
    rw [map_add, AddMonoidHom.add_apply, h r hr w hw, add_zero]

/-! ### When the criterion can hold, and when it cannot

The descent criterion says the quotiented population must lie in the radical.  These three
theorems say exactly which chains can satisfy it, and they settle a question by structure rather
than by hunting for a witness. -/

/-- **A faithful form forces the criterion into the degenerate case.**

If the radical is trivial, then any population lying in it is zero.  So a chain whose form is
faithful on its retained population can only satisfy the descent criterion when it realized
nothing at all — which is why the hollow triangle's weld had a trivial realized population and
could not have had any other. -/
theorem faithfulForcesTrivialRealized (htriv : ∀ v ∈ C.radical, v = 0)
    (N : AddSubgroup V) (hN : N ≤ C.remainder)
    (hdesc : ∀ r ∈ N, ∀ w ∈ C.remainder, C.form r w = 0) :
    ∀ r ∈ N, r = 0 :=
  fun r hr => htriv r ⟨hN hr, hdesc r hr⟩

/-- The form vanishes on its own radical.

**DEFINITIONAL — this unfolds `radical` and proves nothing.**  The radical is *defined* as the
members that pair to nothing with everything retained.  The content near here is elsewhere: that
the radical is a subgroup (which needed bilinearity) and that it coincides with the null cone
(`theNullConeIsTheRadical`, a real argument).  Kept as a convenience accessor. -/
theorem theFormAlwaysDescendsOnItsRadical :
    ∀ r ∈ C.radical, ∀ w ∈ C.remainder, C.form r w = 0 :=
  fun _ hr w hw => hr.2 w hw

/-- **A null self-pairing on the remainder is exactly membership of the radical.**  So quotienting
by the radical leaves a form with no null vectors at all. -/
theorem theNullOnTheRemainderIsTheRadical {v : V} (hv : v ∈ C.remainder)
    (hnull : C.sign * C.form v v = 0) : v ∈ C.radical := by
  refine ⟨hv, ?_⟩
  intro w hw
  have h := C.theNullConeIsTheRadical hv hnull hw
  rcases C.sign_unit with hs | hs <;> rw [hs] at h <;> linarith

/-- **The descended form is faithful exactly when what was quotiented out is the whole radical.**

This completes the trichotomy.  A population outside the radical: the form does not descend.  A
population strictly inside it: the form descends but the quotient still has null classes.  The
radical itself: the form descends and the quotient is faithful.  **There is one right quotient and
the form names it.** -/
theorem theQuotientIsFaithfulIffTheRealizedIsTheWholeRadical
    (N : AddSubgroup V) (hN : N ≤ C.radical) :
    (∀ v ∈ C.remainder, C.sign * C.form v v = 0 → v ∈ N) ↔ C.radical ≤ N := by
  constructor
  · intro h v hv
    refine h v hv.1 ?_
    rw [hv.2 v hv.1, mul_zero]
  · intro h v hv hnull
    exact h (C.theNullOnTheRemainderIsTheRadical hv hnull)

/-! ### When an orthogonal cutoff can be chosen

The `orthogonal` field is an assumption, and the previous iteration reopened the question of when a
datum satisfying it exists.  It is answered here: **there is always a largest admissible cutoff,
it is computable from the form and the remainder, and whether it is nontrivial is decided by the
same radical that decides the descent.** -/

/-- The **perp of the remainder**: everything the form cannot see against what is retained.  This
is the largest cutoff any datum over this form and remainder may declare. -/
def perp : AddSubgroup V where
  carrier := {c | ∀ v ∈ C.remainder, C.form c v = 0}
  zero_mem' := by intro v _; simp
  add_mem' := by
    intro a b ha hb v hv
    rw [map_add, AddMonoidHom.add_apply, ha v hv, hb v hv, add_zero]
  neg_mem' := by
    intro a ha v hv
    rw [map_neg, AddMonoidHom.neg_apply, ha v hv, neg_zero]

/-- **A cutoff is admissible exactly when it sits inside the perp.**

So the orthogonality field is not a mystery condition: it has a largest solution, and that solution
is computed from the form and the remainder rather than declared. -/
theorem theCutoffIsAdmissibleIffInThePerp (K : AddSubgroup V) :
    (∀ c ∈ K, ∀ v ∈ C.remainder, C.form c v = 0) ↔ K ≤ C.perp := Iff.rfl

/-- The radical is the part of the perp that lies inside the remainder.

**DEFINITIONAL — `Iff.rfl` up to reordering.**  Both sides unfold to the same conjunction.  Stated
so the two objects are not conflated, which is a real risk: they differ, and the next theorem
exhibits the difference. -/
theorem theRadicalIsThePerpInsideTheRemainder (v : V) :
    v ∈ C.radical ↔ v ∈ C.remainder ∧ v ∈ C.perp := Iff.rfl

/-- **A faithful form over a full remainder admits only the zero cutoff.**

If everything is retained and nothing is null, then nothing at all is orthogonal to what is
retained, so the aperture must admit nothing.  The compression is vacuous exactly where the form
already separates. -/
theorem theFaithfulFormAdmitsOnlyTheZeroCutoff (htriv : ∀ v ∈ C.radical, v = 0)
    (hfull : C.remainder = ⊤) : C.perp = ⊥ := by
  refine AddSubgroup.eq_bot_iff_forall _ |>.mpr ?_
  intro c hc
  refine htriv c ?_
  rw [theRadicalIsThePerpInsideTheRemainder]
  exact ⟨by rw [hfull]; trivial, hc⟩

/-- **A datum with the opposite sign is a datum.**  The two readings — a surface's intersection
form and a compressed trace at a place — are one structure: negating the form and the sign together
changes nothing about what pays. -/
def flipSign : CompressedPositivity V where
  form := -C.form
  form_symm := by
    intro a b
    simp only [AddMonoidHom.neg_apply, neg_inj]
    exact C.form_symm a b
  cutoff := C.cutoff
  remainder := C.remainder
  orthogonal := by
    intro c hc v hv
    simp only [AddMonoidHom.neg_apply, neg_eq_zero]
    exact C.orthogonal c hc v hv
  sign := -C.sign
  sign_unit := by rcases C.sign_unit with h | h <;> simp [h]
  definite := by
    intro v hv
    have h := C.definite v hv
    simpa [AddMonoidHom.neg_apply, neg_mul_neg] using h

end CompressedPositivity

/-! ## 2. Descent: a bounded core and a finite set of representatives compose the whole atlas -/

variable {G : Type u} [AddCommGroup G]

/-- **Descent data**: every element splits as one of finitely many representatives plus a double,
and above a bound every such split strictly reduces a size.

*Aside: this is the shape of the classical descent by which the rational points of an elliptic
curve are shown finitely generated — the finite quotient modulo doubling, plus a height that falls
under halving.  No curve, height or quotient is constructed here; only the shape.* -/
structure DescentData (G : Type u) [AddCommGroup G] where
  /-- How large an element is. -/
  size : G → ℕ
  /-- Finitely many representatives modulo doubling. -/
  reps : Finset G
  /-- Below this size, descent stops. -/
  bound : ℕ
  /-- Every element is a representative plus a double. -/
  splits : ∀ g : G, ∃ r ∈ reps, ∃ g' : G, g = r + (g' + g')
  /-- Above the bound, halving strictly reduces the size. -/
  descends : ∀ g : G, bound < size g → ∀ r ∈ reps, ∀ g' : G,
    g = r + (g' + g') → size g' < size g

namespace DescentData

variable (D : DescentData G)

/-- The finite atlas: the representatives together with the bounded core. -/
def atlas : Set G := (D.reps : Set G) ∪ {x : G | D.size x ≤ D.bound}

/-- **Descent reaches every element.**

Every element of the group is built from the representatives and the bounded core.  The induction
is on the size and it terminates because halving strictly reduces it above the bound — which is
the inductive partitioning: a bounded core, a finite set of charts, and everything composed. -/
theorem theDescentReachesEveryElement :
    ∀ n : ℕ, ∀ g : G, D.size g = n → g ∈ AddSubgroup.closure D.atlas := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg
    by_cases hle : D.size g ≤ D.bound
    · exact AddSubgroup.subset_closure (Or.inr hle)
    · push_neg at hle
      obtain ⟨r, hr, g', hsplit⟩ := D.splits g
      have hlt : D.size g' < D.size g := D.descends g hle r hr g' hsplit
      have hg' : g' ∈ AddSubgroup.closure D.atlas := ih (D.size g') (by omega) g' rfl
      rw [hsplit]
      exact AddSubgroup.add_mem _
        (AddSubgroup.subset_closure (Or.inl (Finset.mem_coe.mpr hr)))
        (AddSubgroup.add_mem _ hg' hg')

/-- **The atlas generates.** -/
theorem theAtlasGenerates : AddSubgroup.closure D.atlas = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro g
  exact D.theDescentReachesEveryElement (D.size g) g rfl

/-- **If the bounded core is finite, the whole group is finitely generated.**

The emergent atlas is composed: finitely many representatives and a finite core, and every element
of the group is reached from them. -/
theorem theDescentComposesAFiniteAtlas (hfin : {x : G | D.size x ≤ D.bound}.Finite) :
    ∃ S : Finset G, AddSubgroup.closure (S : Set G) = ⊤ := by
  have hatlas : D.atlas.Finite := (D.reps.finite_toSet).union hfin
  refine ⟨hatlas.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact D.theAtlasGenerates

end DescentData

/-! ## 3. The triangle is the quantum of the antisymmetric form

The oriented span of two displacements is the elementary antisymmetric pairing on a plane lattice.
It is integer valued, so it has a smallest nonzero magnitude, and that magnitude is one: **a
nonzero span is at least one primitive triangle.** -/

/-- The elementary antisymmetric pairing on lattice displacements. -/
def spanOf (u v : Site) : ℤ := u.1 * v.2 - u.2 * v.1

/-- **The pairing is antisymmetric** — it is a symplectic form, not a metric one. -/
theorem theSpanIsAntisymmetric (u v : Site) : spanOf u v = - spanOf v u := by
  simp only [spanOf]; ring

/-- **And alternating.** -/
@[simp] theorem theSpanIsAlternating (u : Site) : spanOf u u = 0 := by
  simp only [spanOf]; ring

/-- **The oriented span of a configuration is this pairing on its two edges.** -/
theorem theOrientedSpanIsThePairingOnItsEdges (a b c : Site) :
    orientedSpan a b c = spanOf (b - a) (c - a) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  simp only [orientedSpan, spanOf, Prod.fst_sub, Prod.snd_sub]

/-- **The triangle is the quantum: a nonzero span is at least one.**

The pairing takes values in the integers, so there is a least nonzero magnitude and it is one.
A configuration either spans nothing or spans at least one primitive cell; there is nothing
between. -/
theorem theTriangleIsTheQuantum (u v : Site) (h : spanOf u v ≠ 0) : 1 ≤ (spanOf u v).natAbs := by
  omega

/-- **The pairing is bilinear in its first slot**, so the span is a genuine form and not a
convenience. -/
theorem theSpanIsAdditiveInTheFirstSlot (u u' v : Site) :
    spanOf (u + u') v = spanOf u v + spanOf u' v := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨v1, v2⟩ := v; obtain ⟨w1, w2⟩ := u'
  simp only [spanOf, Prod.fst_add, Prod.snd_add]
  ring

end Soma.Holonics.Millennium.Paying
