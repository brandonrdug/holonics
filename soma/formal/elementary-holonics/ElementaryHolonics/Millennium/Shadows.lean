import ElementaryHolonics.Millennium.LorentzianPerp
import ElementaryHolonics.Millennium.Swing

/-!
# Shadows of holonic interactions

A shadow is a projection.  What survives one is incidence and cross ratio; what dies is every
metric quantity.  This file is the projective reading of the two lines the development is focused
on, and its point is that the move the framework calls **the swing** — harmonic conjugation — is not
a neighbour of the positivity work but its primitive.

**The classical identification, and it is exact.**  A symmetric form `q` induces a polarity: each
class `ω` has a polar `ω^⊥`.  Two classes are **conjugate** with respect to the quadric `q = 0`
exactly when `q(ω,w) = 0` — so *the perp relation the reverse inequality is about IS conjugacy with
respect to a conic*.  Along the line `ω + t·w` the cross term drops out, the form is even in `t`, and
the two parameters at which the line meets the null cone are `±t₀`: a pair exchanged by the swing
about `ω`, whose harmonic conjugate is the point at infinity.  **The cross ratio is `−1` and the
configuration is the optical one — a class, a direction, and the two rays.**

Four steps run on that reading.

1. **The equivalence needs no field.**  `LorentzianPerp` proves the reverse inequality equivalent to
   non-positivity on the perp over an ordered field; the proof below clears the denominator by hand
   with `u = q(ω,ω)·x − q(ω,x)·ω`, which is the same vector the next step weighs.
2. **The denominator is the invariant.**  Over a lattice `q(ω,ω)·x` always lands in `ℤω ⊕ ω^⊥` and
   `x` need not.  On a signature `(1,3)` lattice with an ample-shaped class of self-pairing `24`, the
   class `(1,0,0,0)` is reached **only in the multiple 4** — the shape the engine's
   `ObstructionSpecies::ReachableOnlyInMultiple { factor }` returns, which the operating contract
   calls a faithful finite model of Kollár's counterexamples.
3. **The two obstructions are independent**, and both directions are witnessed: a lattice whose perp
   is definite and whose splitting fails by 4, and a lattice whose perp is indefinite and which
   splits every class.  So *failing by an amount* and *failing by a factor* are different objects.
4. **Placement needs the form to see the ray.**  A transport scaling the form places every stretch it
   realizes on a class of nonzero self-pairing; on an isotropic ray it places nothing, witnessed by
   an honest isometry of the hyperbolic form that stretches a null ray by two.

**Nothing here is a claim about any named conjecture.**  The carriers are a plane, a rank-three and
a rank-four lattice.  No curve, divisor, cycle class map, Frobenius or L-function appears, and the
classical inputs — that an ample class supplies a positive form, and that the archimedean estimate
holds — are imported, cited, and not proved here.  Every `theorem` is discharged and none depends on
`sorryAx`.
-/

namespace Soma.Holonics.Millennium.Shadows

universe u v
variable {R : Type u} {V : Type v}
variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]


/-- **Conjugacy with respect to the form.**  Two classes are conjugate exactly when the form does
not see them against each other — which is the perp condition, and classically the statement that
each lies on the other's polar. -/
def Conjugate (q : LinearMap.BilinForm R V) (a b : V) : Prop := q a b = 0

/-- **The conjugate line meets the null cone symmetrically.**

Along `ω + t·w` with `ω` and `w` conjugate, the cross term drops out and the form is even in `t`.
So the two parameters at which the line meets the cone are `±t₀` — and they are exchanged by the
swing about `ω`. -/
theorem theConjugateLineIsEvenInItsParameter
    (q : LinearMap.BilinForm R V) (hq : q.IsSymm) {om w : V} (h : Conjugate q om w) (t : R) :
    q (om + t • w) (om + t • w) = q om om + t * t * q w w := by
  have hsymm : ∀ a b : V, q a b = q b a := fun a b => by
    have := LinearMap.isSymm_def.mp (LinearMap.BilinForm.isSymm_iff.mp hq) a b
    simpa using this
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm w om, h]
  ring

/-- **The two null parameters are a swing pair about the class itself.**

`Soma.Holonics.Millennium.Swing.swing 0 t = −t`: the one move, about the anchor `ω` sits at, exchanges
the two directions in which the conjugate line leaves the cone.  *In the optical reading those two
directions are the two rays, and the swing is the mirror that trades them.* -/
theorem theSwingExchangesTheNullParameters (t : R) :
    Soma.Holonics.Millennium.Swing.swing (0 : R) t = -t := by
  simp [Soma.Holonics.Millennium.Swing.swing]

/-- **The harmonic conjugate of the anchor against a symmetric pair is the point at infinity.**

`harmonicConjugate`'s denominator `2a − b − d` vanishes at `a = 0`, `b = t₀`, `d = −t₀`.  That is the
projective statement that `ω` and `w` are harmonic conjugates with respect to the two null points on
their line — the cross ratio is `−1` — and it is the reason conjugacy and the swing are one relation
rather than two. -/
theorem theAnchorAndTheDirectionAreHarmonic (t : R) : 2 * (0 : R) - t - (-t) = 0 := by ring

/-! ## The sign decides whether the shadow has two rays -/

/-- **Where the form pays on the class and fails on the perp, the null parameter is a real square.**

`q(ω+tw, ω+tw) = 0` reads `t²·(−q(w,w)) = q(ω,ω)`, whose right side is positive and whose
coefficient is non-negative exactly under the reverse inequality.  So the conjugate line genuinely
crosses the cone: the interaction has two rays rather than none. -/
theorem theNullParameterIsAPositiveRatio
    (q : LinearMap.BilinForm R V) (hq : q.IsSymm) {om w : V} (h : Conjugate q om w)
    (hom : 0 < q om om) (hw : q w w < 0) (t : R)
    (hzero : q (om + t • w) (om + t • w) = 0) :
    0 < t * t := by
  rw [theConjugateLineIsEvenInItsParameter q hq h t] at hzero
  nlinarith



/-- **The equivalence needs no field.**

`LorentzianPerp` proves this over an ordered field by dividing; here the denominator is cleared by
hand with `u = d·x − q(ω,x)·ω`, and `q(u,u) = d²q(x,x) − d·q(ω,x)²`.  **That is the same vector the
next section weighs**, so the step that removes the field hypothesis is the step that exposes the
integral invariant — the division was hiding it. -/
theorem theReverseInequalityOverAnOrderedRing
    (q : LinearMap.BilinForm R V) (hq : q.IsSymm) (om : V) (hom : 0 < q om om) :
    (∀ x : V, q om om * q x x ≤ (q om x) ^ 2) ↔ (∀ w : V, q om w = 0 → q w w ≤ 0) := by
  have hsymm : ∀ a b : V, q a b = q b a := fun a b => by
    have := LinearMap.isSymm_def.mp (LinearMap.BilinForm.isSymm_iff.mp hq) a b
    simpa using this
  constructor
  · intro h w hw
    have := h w
    rw [hw] at this
    nlinarith
  · intro h x
    set d : R := q om om with hd
    set c : R := q om x with hc
    set u : V := d • x - c • om with hu
    have hqu : q om u = 0 := by
      rw [hu]; simp only [map_sub, map_smul, smul_eq_mul]; rw [← hd, ← hc]; ring
    have hexp : q u u = d * d * q x x - d * c * c := by
      rw [hu]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm x om, ← hc, ← hd]; ring
    have := h u hqu
    rw [hexp] at this
    nlinarith

/-! ## 4. The denominator is the invariant -/


/-- **The cleared vector is conjugate to the class.** -/
theorem theClearedVectorIsConjugate
    (q : LinearMap.BilinForm R V) (om x : V) :
    q om (q om om • x - q om x • om) = 0 := by
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- **Every class enters the span of the class and its perp after multiplying by the self-pairing.**
Over a field one divides; over a ring one cannot, and what is left behind is an invariant. -/
theorem theSelfPairingClearsTheDenominator
    (q : LinearMap.BilinForm R V) (om x : V) :
    q om om • x = q om x • om + (q om om • x - q om x • om) := by abel

/-! ## The integral defect, on a signature (1,3) lattice -/

abbrev ZLat : Type := ℤ × ℤ × ℤ × ℤ

def zl (u v : ZLat) : ℤ :=
  u.1 * v.1 - u.2.1 * v.2.1 - u.2.2.1 * v.2.2.1 - u.2.2.2 * v.2.2.2

def zamp : ZLat := (6, -2, -2, -2)
def zx : ZLat := (1, 0, 0, 0)

theorem theSelfPairingIsTwentyFour : zl zamp zamp = 24 := by norm_num [zl, zamp]
theorem thePairingWithTheClassIsSix : zl zamp zx = 6 := by norm_num [zl, zamp, zx]

/-- **The class is NOT in the integral span of the ample class and its perp.**

If `x = t·ω + w` with `w` conjugate, pairing against `ω` gives `6 = 24t`, which no integer solves.
*Over the rationals this never happens; the obstruction is invisible to a field.* -/
theorem theClassIsNotInTheIntegralSpan :
    ¬ ∃ (t : ℤ) (w : ZLat), zl zamp w = 0 ∧ zx = t • zamp + w := by
  rintro ⟨t, w, hw, hx⟩
  have h : zl zamp zx = t * 24 := by
    rw [hx]
    obtain ⟨w1, w2, w3, w4⟩ := w
    simp only [zl, zamp, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hw ⊢
    linarith [hw]
  rw [thePairingWithTheClassIsSix] at h
  omega

/-- **But four times the class is**, with the complement exhibited. -/
theorem theFourfoldIsInTheIntegralSpan :
    zl zamp ((-2, 2, 2, 2) : ZLat) = 0 ∧ (4 : ℤ) • zx = (1 : ℤ) • zamp + ((-2, 2, 2, 2) : ZLat) := by
  refine ⟨by norm_num [zl, zamp], ?_⟩
  simp only [zx, zamp, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  norm_num

/-- **And the factor divides the self-pairing of the class.** -/
theorem theFactorDividesTheSelfPairing : (4 : ℤ) ∣ zl zamp zamp := by
  rw [theSelfPairingIsTwentyFour]; norm_num

/-! ## The two obstructions are independent -/

/-- The perp of the ample class is where the form is negative — no sign failure. -/
theorem theAmplePerpIsNegative (w : ZLat) (hw : zl zamp w = 0) : zl w w ≤ 0 := by
  simp only [zl, zamp] at hw ⊢
  have h3 : 3 * w.1 = -(w.2.1 + w.2.2.1 + w.2.2.2) := by linarith
  have hsq : 9 * (w.1 * w.1) = (w.2.1 + w.2.2.1 + w.2.2.2) * (w.2.1 + w.2.2.1 + w.2.2.2) := by
    calc 9 * (w.1 * w.1) = (3 * w.1) * (3 * w.1) := by ring
      _ = (-(w.2.1 + w.2.2.1 + w.2.2.2)) * (-(w.2.1 + w.2.2.1 + w.2.2.2)) := by rw [h3]
      _ = (w.2.1 + w.2.2.1 + w.2.2.2) * (w.2.1 + w.2.2.1 + w.2.2.2) := by ring
  nlinarith [hsq, sq_nonneg (w.2.1 - w.2.2.1), sq_nonneg (w.2.1 - w.2.2.2),
    sq_nonneg (w.2.2.1 - w.2.2.2)]

/-- The other witness: signature `(2,1)` with a unit class. -/
abbrev ZThree : Type := ℤ × ℤ × ℤ
def z3 (u v : ZThree) : ℤ := u.1 * v.1 - u.2.1 * v.2.1 + u.2.2 * v.2.2
def unitClass : ZThree := (1, 0, 0)

theorem theUnitClassPaysOne : z3 unitClass unitClass = 1 := by norm_num [z3, unitClass]

/-- **The sign obstruction is present**: the perp of the unit class carries both signs. -/
theorem theUnitPerpIsIndefinite :
    z3 unitClass ((0,1,0) : ZThree) = 0 ∧ z3 ((0,1,0) : ZThree) (0,1,0) < 0
      ∧ z3 unitClass ((0,0,1) : ZThree) = 0 ∧ 0 < z3 ((0,0,1) : ZThree) (0,0,1) := by
  refine ⟨by norm_num [z3, unitClass], by norm_num [z3], by norm_num [z3, unitClass], by norm_num [z3]⟩

/-- **And the splitting obstruction is absent**: the self-pairing is a unit, so every class splits. -/
theorem theUnitClassSplitsEveryClass (x : ZThree) :
    z3 unitClass (x - (z3 unitClass x) • unitClass) = 0 ∧
      x = (z3 unitClass x) • unitClass + (x - (z3 unitClass x) • unitClass) := by
  constructor
  · obtain ⟨a, b, c⟩ := x
    simp only [z3, unitClass, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul]
    ring
  · abel



/-- **The self-pairing kills the quotient, in general.**

Every class lands in the span of the distinguished class and its perp after multiplying by the
self-pairing — so the residue `L / (ℤω ⊕ ω^⊥)` is annihilated by `q(ω,ω)` and is finite whenever the
carrier is finitely generated.  The witness in section 5 exhibits the residue at one class; this is
the law behind it. -/
theorem theSelfPairingKillsTheQuotient
    (q : LinearMap.BilinForm R V) (om x : V) :
    ∃ (c : R) (w : V), q om w = 0 ∧ q om om • x = c • om + w := by
  refine ⟨q om x, q om om • x - q om x • om, ?_, by abel⟩
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-! ## 7. Placement -/


/-- **A transport that scales the form places every stretch it realizes on a class the form can
still see.** -/
theorem theStretchIsPlacedWhereTheSelfPairingSurvives
    (q : LinearMap.BilinForm R V) (T : V →ₗ[R] V) (c : R)
    (hT : ∀ x y : V, q (T x) (T y) = c * q x y)
    {v : V} {lam : R} (hv : T v = lam • v) (hnz : q v v ≠ 0) :
    lam * lam = c := by
  have h := hT v v
  rw [hv] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have h2 : (lam * lam - c) * q v v = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith [sub_eq_zero.mp h3]
  · exact absurd h3 hnz

/-! ### The control: on an isotropic ray the placement says nothing -/
abbrev Pl : Type := ℚ × ℚ
/-- The hyperbolic form `u₁v₂ + u₂v₁` — its null cone is the two axes. -/
def hyp : LinearMap.BilinForm ℚ Pl :=
  LinearMap.mk₂ ℚ (fun u v => u.1 * v.2 + u.2 * v.1)
    (by intro a b c; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intro a b c; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro a c b; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
@[simp] theorem hyp_apply (u v : Pl) : hyp u v = u.1 * v.2 + u.2 * v.1 := rfl

/-- The squeeze `(x,y) ↦ (2x, y/2)`. -/
def squeeze : Pl →ₗ[ℚ] Pl where
  toFun p := (2 * p.1, p.2 / 2)
  map_add' _ _ := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  map_smul' _ _ := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk, RingHom.id_apply,
      Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

/-- **The squeeze is an honest isometry of the hyperbolic form.** -/
theorem theSqueezeIsAnIsometry (x y : Pl) : hyp (squeeze x) (squeeze y) = 1 * hyp x y := by
  simp only [hyp_apply, squeeze, LinearMap.coe_mk, AddHom.coe_mk]; ring

/-- **Yet it stretches a ray by two.** The ray is isotropic, so the placement hypothesis fails and
`λ² = 4 ≠ 1`.  *Preserving the form places nothing; the form having something to say on the ray is
what places it.* -/
theorem theStretchedRayIsIsotropic :
    squeeze ((1,0) : Pl) = (2 : ℚ) • (1,0) ∧ hyp ((1,0) : Pl) (1,0) = 0
      ∧ (2:ℚ) * 2 ≠ 1 := by
  refine ⟨by simp [squeeze, Prod.ext_iff], by simp, by norm_num⟩

end Soma.Holonics.Millennium.Shadows
