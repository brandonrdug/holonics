import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
import Mathlib.LinearAlgebra.Reflection

/-!
# The exact local reflection behind an odd-prime neighbour

For a symmetric full polar form `B` and an anisotropic vector `h`, reflection in
`h` is the involution

`x ↦ x - (2 B(h,x) / B(h,h)) h`.

The lemmas below isolate the quadratic-preserving algebra needed in the local
Brandt-neighbour passage.  The final scalar identity records why the
source-specific choice `h = v + p w` has exactly one `p` in its denominator
when `Q(v)` is divisible by `p²` and `B(v,w)` is a `p`-local unit.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtLocalReflection

open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The normalized full-polar functional belonging to `h`. -/
def polarReflectionFunctional (B : LinearMap.BilinForm K M) (h : M) : Module.Dual K M :=
  (2 / B h h) • B h

theorem polarReflectionFunctional_apply (B : LinearMap.BilinForm K M) (h x : M) :
    polarReflectionFunctional B h x = (2 / B h h) * B h x := by
  simp [polarReflectionFunctional]

theorem polarReflectionFunctional_self (B : LinearMap.BilinForm K M) (h : M)
    (hh : B h h ≠ 0) :
    polarReflectionFunctional B h h = 2 := by
  rw [polarReflectionFunctional_apply]
  field_simp

/-- Reflection in a vector with nonzero full-polar square. -/
def polarReflection (B : LinearMap.BilinForm K M) (h : M) (hh : B h h ≠ 0) :
    M ≃ₗ[K] M :=
  Module.reflection (polarReflectionFunctional_self B h hh)

theorem polarReflection_apply (B : LinearMap.BilinForm K M) (h : M)
    (hh : B h h ≠ 0) (x : M) :
    polarReflection B h hh x = x - ((2 / B h h) * B h x) • h := by
  rw [polarReflection, Module.reflection_apply]
  simp [polarReflectionFunctional_apply]

theorem polarReflection_involutive (B : LinearMap.BilinForm K M) (h : M)
    (hh : B h h ≠ 0) :
    Function.Involutive (polarReflection B h hh) :=
  Module.involutive_reflection (polarReflectionFunctional_self B h hh)

/-- The reflection preserves the full-polar quadratic value exactly. -/
theorem polarReflection_preserves_square (B : LinearMap.BilinForm K M)
    (hsymm : ∀ x y, B x y = B y x) (h : M) (hh : B h h ≠ 0) (x : M) :
    B (polarReflection B h hh x) (polarReflection B h hh x) = B x x := by
  rw [polarReflection_apply]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm x h]
  field_simp
  ring

/-- Polarization upgrades preservation of the square to preservation of the
entire symmetric bilinear form. -/
theorem polarReflection_preserves_form (B : LinearMap.BilinForm K M)
    (hsymm : ∀ x y, B x y = B y x) (h : M) (hh : B h h ≠ 0) (x y : M) :
    B (polarReflection B h hh x) (polarReflection B h hh y) = B x y := by
  rw [polarReflection_apply, polarReflection_apply]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm x h]
  field_simp
  ring

/-- If `Q(v)=p²q`, then the full-polar square of `h=v+pw` factors as
`p * (2*p*q + B(v,w) + p*Q₂(w))`.  Here `Q₂(w)=B(w,w)` is twice the usual
quadratic value.  Thus a `p`-local unit `B(v,w)` makes the parenthesized factor
a unit modulo `p`, exposing the unique local denominator of the reflection. -/
theorem neighbor_reflection_denominator_factor
    (B : LinearMap.BilinForm K M) (hsymm : ∀ x y, B x y = B y x)
    (p : K) (v w : M) (q : K) (hv : B v v = p ^ 2 * q) :
    B (v + p • w) (v + p • w) =
      p * (p * q + 2 * B v w + p * B w w) := by
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm w v, hv]
  ring

/-- The parenthesized denominator factor remains nonzero in the residue field.
This is the exact, finite statement that the polar pairing is a local unit. -/
theorem neighbor_reflection_cofactor_ne_zero_mod
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (b q r : ℤ)
    (hb : (b : ZMod p) ≠ 0) :
    ((p * q + 2 * b + p * r : ℤ) : ZMod p) ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  norm_num
  exact ⟨htwo, hb⟩

/-- Consequently `p * cofactor` is divisible by `p`, but not by `p²`.
No valuation or analytic estimate is used. -/
theorem neighbor_reflection_denominator_has_exactly_one_p
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (b q r : ℤ)
    (hb : (b : ZMod p) ≠ 0) :
    ¬ (p : ℤ) ^ 2 ∣
      (p : ℤ) * ((p : ℤ) * q + 2 * b + (p : ℤ) * r) := by
  intro hdvd
  rcases hdvd with ⟨k, hk⟩
  have hpZ : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcancel :
      (p : ℤ) * ((p : ℤ) * k) =
        (p : ℤ) * ((p : ℤ) * q + 2 * b + (p : ℤ) * r) := by
    calc
      (p : ℤ) * ((p : ℤ) * k) = (p : ℤ) ^ 2 * k := by ring
      _ = (p : ℤ) * ((p : ℤ) * q + 2 * b + (p : ℤ) * r) := hk.symm
  have hcofactor :
      (p : ℤ) * q + 2 * b + (p : ℤ) * r = (p : ℤ) * k := by
    exact (mul_left_cancel₀ hpZ hcancel).symm
  have hzero :
      (((p : ℤ) * q + 2 * b + (p : ℤ) * r : ℤ) : ZMod p) = 0 := by
    rw [hcofactor]
    norm_num
  exact neighbor_reflection_cofactor_ne_zero_mod hp2 b q r hb hzero

section HyperbolicPair

variable (B : LinearMap.BilinForm K M)

/-- Correct a polar partner by the isotropic direction itself.  This is the
post-Hensel algebraic step: it makes the partner isotropic without changing
its unit pairing with `e`. -/
def correctedIsotropicPartner (e f : M) : M :=
  f - (B f f / 2) • e

theorem correctedIsotropicPartner_pairing
    {e f : M} (hee : B e e = 0) (hef : B e f = 1) :
    B e (correctedIsotropicPartner B e f) = 1 := by
  simp [correctedIsotropicPartner, hee, hef]

theorem correctedIsotropicPartner_isotropic
    (hsymm : ∀ x y, B x y = B y x) {e f : M}
    (h2 : (2 : K) ≠ 0) (hee : B e e = 0) (hef : B e f = 1) :
    B (correctedIsotropicPartner B e f)
        (correctedIsotropicPartner B e f) = 0 := by
  simp only [correctedIsotropicPartner, map_sub, LinearMap.sub_apply,
    LinearMap.map_smul_of_tower, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm f e, hee, hef]
  field_simp
  ring

/-- Remainder after removing the two coordinates of a normalized hyperbolic
pair. -/
def hyperbolicRemainder (e f x : M) : M :=
  x - (B x f) • e - (B x e) • f

theorem hyperbolicRemainder_decomposition (e f x : M) :
    x = (B x f) • e + (B x e) • f + hyperbolicRemainder B e f x := by
  simp [hyperbolicRemainder]

theorem hyperbolicRemainder_ortho_left
    (hsymm : ∀ x y, B x y = B y x) {e f x : M}
    (hee : B e e = 0) (hef : B e f = 1) :
    B e (hyperbolicRemainder B e f x) = 0 := by
  simp only [hyperbolicRemainder, map_sub, LinearMap.map_smul_of_tower, smul_eq_mul]
  rw [hsymm x e, hee, hef]
  ring

theorem hyperbolicRemainder_ortho_right
    (hsymm : ∀ x y, B x y = B y x) {e f x : M}
    (hff : B f f = 0) (hef : B e f = 1) :
    B f (hyperbolicRemainder B e f x) = 0 := by
  simp only [hyperbolicRemainder, map_sub, LinearMap.map_smul_of_tower, smul_eq_mul]
  rw [hsymm f e, hsymm x f, hff, hef]
  ring

/-- Reciprocal scaling on a normalized hyperbolic pair, fixing its orthogonal
remainder. -/
def hyperbolicScale (e f : M) (a : K) : M →ₗ[K] M :=
  LinearMap.id +
    (((a⁻¹ - 1) • B f).smulRight e) +
    (((a - 1) • B e).smulRight f)

theorem hyperbolicScale_apply
    (hsymm : ∀ x y, B x y = B y x) (e f x : M) (a : K) :
    hyperbolicScale B e f a x =
      x + ((a⁻¹ - 1) * B x f) • e + ((a - 1) * B x e) • f := by
  simp [hyperbolicScale, hsymm f x, hsymm e x]

theorem hyperbolicScale_e
    (hsymm : ∀ x y, B x y = B y x) {e f : M} (a : K)
    (hee : B e e = 0) (hef : B e f = 1) :
    hyperbolicScale B e f a e = a⁻¹ • e := by
  rw [hyperbolicScale_apply B hsymm]
  simp [hee, hef]
  module

theorem hyperbolicScale_f
    (hsymm : ∀ x y, B x y = B y x) {e f : M} (a : K)
    (hff : B f f = 0) (hef : B e f = 1) :
    hyperbolicScale B e f a f = a • f := by
  rw [hyperbolicScale_apply B hsymm]
  simp [hff, hef, hsymm f e]
  module

theorem hyperbolicScale_preserves_form
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) (x y : M) :
    B (hyperbolicScale B e f a x) (hyperbolicScale B e f a y) = B x y := by
  rw [hyperbolicScale_apply B hsymm, hyperbolicScale_apply B hsymm]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm x e, hsymm x f, hsymm y e, hsymm y f,
    hsymm f e, hee, hff, hef]
  field_simp
  ring

theorem hyperbolicScale_pairing_right
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (ha : a ≠ 0) (hff : B f f = 0) (hef : B e f = 1) (x : M) :
    B (hyperbolicScale B e f a x) f = a⁻¹ * B x f := by
  rw [hyperbolicScale_apply B hsymm]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hff, hef]
  field_simp
  ring

theorem hyperbolicScale_pairing_left
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (hee : B e e = 0) (hef : B e f = 1) (x : M) :
    B (hyperbolicScale B e f a x) e = a * B x e := by
  rw [hyperbolicScale_apply B hsymm]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smul_of_tower,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm f e, hee, hef]
  ring

theorem hyperbolicScale_inverse_apply
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) (x : M) :
    hyperbolicScale B e f a⁻¹ (hyperbolicScale B e f a x) = x := by
  rw [hyperbolicScale_apply B hsymm, hyperbolicScale_pairing_right B hsymm ha hff hef,
    hyperbolicScale_pairing_left B hsymm hee hef,
    hyperbolicScale_apply B hsymm]
  simp only [inv_inv]
  have hainv : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  have hamul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  field_simp [ha]
  module

/-- The reciprocal hyperbolic rescaling as an actual invertible basis change.
It sends `e` to `a⁻¹e`, sends `f` to `af`, fixes the orthogonal complement,
and preserves `B`. -/
def hyperbolicScaleEquiv
    (hsymm : ∀ x y, B x y = B y x) (e f : M) (a : K)
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinear
    (hyperbolicScale B e f a)
    (hyperbolicScale B e f a⁻¹)
    (by
      ext x
      simpa only [inv_inv, LinearMap.comp_apply, LinearMap.id_apply] using
        (hyperbolicScale_inverse_apply B hsymm (inv_ne_zero ha) hee hff hef x))
    (by
      ext x
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        (hyperbolicScale_inverse_apply B hsymm ha hee hff hef x))

theorem hyperbolicScaleEquiv_preserves_form
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) (x y : M) :
    B (hyperbolicScaleEquiv B hsymm e f a ha hee hff hef x)
        (hyperbolicScaleEquiv B hsymm e f a ha hee hff hef y) = B x y :=
  hyperbolicScale_preserves_form B hsymm ha hee hff hef x y

theorem hyperbolicScaleEquiv_e
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) :
    hyperbolicScaleEquiv B hsymm e f a ha hee hff hef e = a⁻¹ • e :=
  hyperbolicScale_e B hsymm a hee hef

theorem hyperbolicScaleEquiv_f
    (hsymm : ∀ x y, B x y = B y x) {e f : M} {a : K}
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) :
    hyperbolicScaleEquiv B hsymm e f a ha hee hff hef f = a • f :=
  hyperbolicScale_f B hsymm a hff hef

theorem hyperbolicScaleEquiv_fix_of_orthogonal
    (hsymm : ∀ x y, B x y = B y x) {e f x : M} {a : K}
    (ha : a ≠ 0) (hee : B e e = 0) (hff : B f f = 0)
    (hef : B e f = 1) (hxe : B x e = 0) (hxf : B x f = 0) :
    hyperbolicScaleEquiv B hsymm e f a ha hee hff hef x = x := by
  rw [show hyperbolicScaleEquiv B hsymm e f a ha hee hff hef x =
      hyperbolicScale B e f a x from rfl,
    hyperbolicScale_apply B hsymm, hxe, hxf]
  simp

end HyperbolicPair

end Soma.Holonics.Millennium.FamilyTunnellBrandtLocalReflection
