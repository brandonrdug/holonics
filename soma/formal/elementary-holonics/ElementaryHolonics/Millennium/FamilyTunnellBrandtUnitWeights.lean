import ElementaryHolonics.Millennium.FamilyTunnellBrandtTwoClassInterchange
import ElementaryHolonics.Millennium.FamilyTunnellNormOneReturn

/-!
# Integral unit transports for the two Tunnell Brandt representatives

`Q₁ = 2x²+y²+32z²` and `Q₂ = 2x²+4y²+4yz+9z²` each carry an explicit
eight-element integral unit transport fibre.  The maps are retained as actual
bijective transports preserving the quadratic receiver; their receiver image
is not collapsed to the number eight.

The final arbitrary-isometry census is kept as an explicit obligation.  It is
the source boundary needed before weighted Brandt self-adjointness may be
reduced to literal two-class interchange.
-/

noncomputable section
namespace Soma.Holonics.Millennium.FamilyTunnellBrandtUnitWeights

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellNormOneReturn

abbrev Vec := IntTriple
def q₁ : Vec → ℤ := brandtFirstQuadratic
def q₂ : Vec → ℤ := brandtSecondQuadratic
def e₀ : Vec := (1, 0, 0)
def e₁ : Vec := (0, 1, 0)
def e₂ : Vec := (0, 0, 1)

structure LatticeTransport (q : Vec → ℤ) where
  toFun : Vec → Vec
  invFun : Vec → Vec
  map_zero : toFun 0 = 0
  map_add : ∀ u v, toFun (u + v) = toFun u + toFun v
  map_smul : ∀ (n : ℤ) u, toFun (n • u) = n • toFun u
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  preserves : ∀ v, q (toFun v) = q v

instance (q : Vec → ℤ) : CoeFun (LatticeTransport q) (fun _ => Vec → Vec) :=
  ⟨LatticeTransport.toFun⟩
noncomputable local instance (q : Vec → ℤ) : DecidableEq (LatticeTransport q) :=
  Classical.decEq _

private def sgn (b : Bool) : ℤ := if b then 1 else -1
private theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

private theorem vec_ext {u v : Vec}
    (hx : u.1 = v.1) (hy : u.2.1 = v.2.1) (hz : u.2.2 = v.2.2) : u = v := by
  apply Prod.ext
  · exact hx
  · apply Prod.ext <;> assumption

def q₁Map (a b c : Bool) (v : Vec) : Vec :=
  (sgn a * v.1, sgn b * v.2.1, sgn c * v.2.2)

def q₁Aut (a b c : Bool) : LatticeTransport q₁ where
  toFun := q₁Map a b c
  invFun := q₁Map a b c
  map_zero := by cases a <;> cases b <;> cases c <;> simp [q₁Map, sgn]
  map_add := by
    intro u v
    apply vec_ext
    · simp [q₁Map]; ring
    · simp [q₁Map]; ring
    · simp [q₁Map]; ring
  map_smul := by
    intro n v
    apply vec_ext
    · simp [q₁Map]; ring
    · simp [q₁Map]; ring
    · simp [q₁Map]; ring
  left_inv := by
    intro v; cases a <;> cases b <;> cases c <;>
      apply vec_ext <;> simp [q₁Map, sgn]
  right_inv := by
    intro v; cases a <;> cases b <;> cases c <;>
      apply vec_ext <;> simp [q₁Map, sgn]
  preserves := by
    intro v; cases a <;> cases b <;> cases c <;>
      simp [q₁Map, q₁, brandtFirstQuadratic, sgn]

def q₁UnitLabels : Finset (Bool × Bool × Bool) := Finset.univ
def q₁UnitTransports : Finset (LatticeTransport q₁) :=
  q₁UnitLabels.image (fun abc => q₁Aut abc.1 abc.2.1 abc.2.2)

theorem q₁UnitLabels_card : q₁UnitLabels.card = 8 := by
  simp [q₁UnitLabels]

theorem q₁Aut_injective : Function.Injective (fun abc : Bool × Bool × Bool =>
    q₁Aut abc.1 abc.2.1 abc.2.2) := by
  intro u v h
  have h0 := congrArg (fun A : LatticeTransport q₁ => A e₀) h
  have h1 := congrArg (fun A : LatticeTransport q₁ => A e₁) h
  have h2 := congrArg (fun A : LatticeTransport q₁ => A e₂) h
  cases u with
  | mk ua ub => cases ub with
    | mk uc ud =>
      cases v with
      | mk va vb => cases vb with
        | mk vc vd =>
          simp [q₁Aut, q₁Map, e₀, e₁, e₂, sgn] at h0 h1 h2
          cases ua <;> cases uc <;> cases ud <;>
            cases va <;> cases vc <;> cases vd <;> simp_all

theorem q₁UnitTransports_card : q₁UnitTransports.card = 8 := by
  rw [q₁UnitTransports, Finset.card_image_iff.mpr]
  · exact q₁UnitLabels_card
  · intro u hu v hv h; exact q₁Aut_injective h

def q₂Map (a b t : Bool) (v : Vec) : Vec :=
  match t with
  | false => (sgn a * v.1, sgn b * v.2.1, sgn b * v.2.2)
  | true => (sgn a * v.1, sgn b * (v.2.1 + v.2.2), -sgn b * v.2.2)

def q₂Aut (a b t : Bool) : LatticeTransport q₂ where
  toFun := q₂Map a b t
  invFun := q₂Map a b t
  map_zero := by cases a <;> cases b <;> cases t <;> simp [q₂Map, sgn]
  map_add := by
    intro u v
    cases t
    · apply vec_ext <;> simp [q₂Map] <;> ring
    · apply vec_ext <;> simp [q₂Map] <;> ring
  map_smul := by
    intro n v
    cases t
    · apply vec_ext <;> simp [q₂Map] <;> ring
    · apply vec_ext <;> simp [q₂Map] <;> ring
  left_inv := by
    intro v; cases a <;> cases b <;> cases t <;>
      simp [q₂Map, sgn] <;> apply vec_ext <;> simp <;> ring
  right_inv := by
    intro v; cases a <;> cases b <;> cases t <;>
      simp [q₂Map, sgn] <;> apply vec_ext <;> simp <;> ring
  preserves := by
    intro v; cases a <;> cases b <;> cases t <;>
      simp [q₂Map, q₂, brandtSecondQuadratic, sgn] <;> ring

def q₂UnitLabels : Finset (Bool × Bool × Bool) := Finset.univ
def q₂UnitTransports : Finset (LatticeTransport q₂) :=
  q₂UnitLabels.image (fun abc => q₂Aut abc.1 abc.2.1 abc.2.2)

theorem q₂UnitLabels_card : q₂UnitLabels.card = 8 := by
  simp [q₂UnitLabels]

theorem q₂Aut_injective : Function.Injective (fun abc : Bool × Bool × Bool =>
    q₂Aut abc.1 abc.2.1 abc.2.2) := by
  intro u v h
  have h0 := congrArg (fun A : LatticeTransport q₂ => A e₀) h
  have h1 := congrArg (fun A : LatticeTransport q₂ => A e₁) h
  have h2 := congrArg (fun A : LatticeTransport q₂ => A e₂) h
  cases u with
  | mk ua ub => cases ub with
    | mk uc ud =>
      cases v with
      | mk va vb => cases vb with
        | mk vc vd =>
          simp [q₂Aut, q₂Map, e₀, e₁, e₂, sgn] at h0 h1 h2
          cases ua <;> cases uc <;> cases ud <;>
            cases va <;> cases vc <;> cases vd <;> simp_all

theorem q₂UnitTransports_card : q₂UnitTransports.card = 8 := by
  rw [q₂UnitTransports, Finset.card_image_iff.mpr]
  · exact q₂UnitLabels_card
  · intro u hu v hv h; exact q₂Aut_injective h

theorem equal_explicit_unit_weights :
    q₁UnitTransports.card = q₂UnitTransports.card := by
  rw [q₁UnitTransports_card, q₂UnitTransports_card]

private theorem latticeTransport_ext {q : Vec → ℤ}
    {A B : LatticeTransport q}
    (h : ∀ v, A v = B v) : A = B := by
  have hto : A.toFun = B.toFun := funext h
  have hinv : A.invFun = B.invFun := by
    funext v
    calc
      A.invFun v = A.invFun (B (B.invFun v)) := by rw [B.right_inv]
      _ = A.invFun (A (B.invFun v)) := by rw [h]
      _ = B.invFun v := A.left_inv _
  cases A with
  | mk af ai az aa as al ar ap =>
    cases B with
    | mk bf bi bz ba bs bl br bp =>
      simp_all only [Function.LeftInverse, Function.RightInverse]

private theorem latticeTransport_decompose (A : LatticeTransport q)
    (v : Vec) :
    A v = v.1 • A e₀ + v.2.1 • A e₁ + v.2.2 • A e₂ := by
  have hv : v = v.1 • e₀ + v.2.1 • e₁ + v.2.2 • e₂ := by
    apply vec_ext <;> simp [e₀, e₁, e₂]
  calc
    A v = A (v.1 • e₀ + v.2.1 • e₁ + v.2.2 • e₂) := congrArg A hv
    _ = v.1 • A e₀ + v.2.1 • A e₁ + v.2.2 • A e₂ := by
      rw [A.map_add, A.map_add, A.map_smul, A.map_smul, A.map_smul]

private theorem q₁_image_middle_sign (A : LatticeTransport q₁) :
    A e₁ = e₁ ∨ A e₁ = -e₁ := by
  have hunit : q₁ (A e₁) = 1 := by
    simpa [q₁, e₁, brandtFirstQuadratic] using A.preserves e₁
  simpa [e₁] using (brandtFirstQuadratic_eq_one_iff (A e₁)).mp hunit

private theorem q₁_polar_middle (A : LatticeTransport q₁)
    (v : Vec) :
    q₁ (A e₁ + A v) - q₁ (A e₁) - q₁ (A v) =
      4 * (A e₁).1 * (A v).1 +
        2 * (A e₁).2.1 * (A v).2.1 +
        64 * (A e₁).2.2 * (A v).2.2 := by
  simp [q₁, brandtFirstQuadratic]
  ring

private theorem q₁_image_middle_coordinate
    (A : LatticeTransport q₁) (v : Vec)
    (hsign : A e₁ = e₁ ∨ A e₁ = -e₁) :
    (A v).2.1 = (if A e₁ = e₁ then v.2.1 else -v.2.1) := by
  have hp := q₁_polar_middle A v
  have hpres₁ := A.preserves e₁
  have hpresv := A.preserves v
  have hpolar :
      q₁ (A e₁ + A v) - q₁ (A e₁) - q₁ (A v) =
        q₁ (e₁ + v) - q₁ e₁ - q₁ v := by
    rw [← A.map_add, A.preserves, A.preserves, A.preserves]
  rcases hsign with hsign | hsign
  · rw [hsign] at hpolar
    simp [q₁, brandtFirstQuadratic, e₁] at hpolar
    rw [if_pos hsign]
    nlinarith [hpolar]
  · rw [hsign] at hp hpres₁
    rw [hsign] at hpolar
    simp [q₁, brandtFirstQuadratic, e₁] at hpolar
    have hne : ¬ A e₁ = e₁ := by
      intro h
      rw [h] at hsign
      simpa [e₁] using hsign
    rw [if_neg hne]
    nlinarith [hpolar]

private theorem q₁_image_first_or_four (A : LatticeTransport q₁)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁) :
    A e₀ = e₀ ∨ A e₀ = -e₀ := by
  have hc : (A e₀).2.1 = 0 := by
    rcases hmiddle with hm | hm
    · have hh := q₁_image_middle_coordinate A e₀ (Or.inl hm)
      simpa [if_pos hm, e₀] using hh
    · have hne : ¬ A e₁ = e₁ := by
        intro h
        rw [h] at hm
        simpa [e₁] using hm
      have hh := q₁_image_middle_coordinate A e₀ (Or.inr hm)
      simpa [if_neg hne, e₀] using hh
  have hq := A.preserves e₀
  have hq' :
      2 * (A e₀).1 ^ 2 + (A e₀).2.1 ^ 2 + 32 * (A e₀).2.2 ^ 2 = 2 := by
    simpa [q₁, brandtFirstQuadratic, e₀] using hq
  have hsq : (A e₀).1 ^ 2 = 1 := by
    have hx : 0 ≤ (A e₀).1 ^ 2 := sq_nonneg _
    have hz : 0 ≤ (A e₀).2.2 ^ 2 := sq_nonneg _
    rw [hc] at hq'
    norm_num at hq'
    have hlow : -1 ≤ (A e₀).1 := by nlinarith [hq', hz]
    have hupp : (A e₀).1 ≤ 1 := by nlinarith [hq', hz]
    have hcases : (A e₀).1 = -1 ∨ (A e₀).1 = 0 ∨ (A e₀).1 = 1 := by
      omega
    rcases hcases with hx' | hx' | hx'
    · nlinarith
    · rw [hx'] at hq'
      omega
    · nlinarith
  have hx : (A e₀).1 = 1 ∨ (A e₀).1 = -1 := sq_eq_one_iff.mp hsq
  rcases hx with hx | hx
  · left
    apply vec_ext
    · exact hx
    · exact hc
    · have hz : (A e₀).2.2 ^ 2 = 0 := by
        rw [hc] at hq'
        norm_num at hq'
        nlinarith
      simpa [e₀] using (sq_eq_zero_iff.mp hz)
  · right
    apply vec_ext
    · exact hx
    · exact hc
    · have hz : (A e₀).2.2 ^ 2 = 0 := by
        rw [hc] at hq'
        norm_num at hq'
        nlinarith
      simpa [e₀] using (sq_eq_zero_iff.mp hz)

private theorem q₁_image_third_classification (A : LatticeTransport q₁)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀) :
    A e₂ = e₂ ∨ A e₂ = -e₂ ∨ A e₂ = 4 • e₀ ∨ A e₂ = -4 • e₀ := by
  have hy : (A e₂).2.1 = 0 := by
    rcases hmiddle with hm | hm
    · have hh := q₁_image_middle_coordinate A e₂ (Or.inl hm)
      simpa [if_pos hm, e₂] using hh
    · have hne : ¬ A e₁ = e₁ := by
        intro h
        rw [h] at hm
        simpa [e₁] using hm
      have hh := q₁_image_middle_coordinate A e₂ (Or.inr hm)
      simpa [if_neg hne, e₂] using hh
  have hq := A.preserves e₂
  have hq' :
      2 * (A e₂).1 ^ 2 + (A e₂).2.1 ^ 2 + 32 * (A e₂).2.2 ^ 2 = 32 := by
    simpa [q₁, brandtFirstQuadratic, e₂] using hq
  rw [hy] at hq'
  norm_num at hq'
  have hzsq : (A e₂).2.2 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (A e₂).1]
  have hzlo : -1 ≤ (A e₂).2.2 := by nlinarith [hzsq]
  have zhupp : (A e₂).2.2 ≤ 1 := by nlinarith [hzsq]
  have zcases : (A e₂).2.2 = -1 ∨ (A e₂).2.2 = 0 ∨ (A e₂).2.2 = 1 := by
    omega
  rcases zcases with hz | hz | hz
  · have hx : (A e₂).1 = 0 := by
      rw [hz] at hq'
      nlinarith
    right
    left
    apply vec_ext
    · exact hx
    · exact hy
    · exact hz
  · have hx : (A e₂).1 = 4 ∨ (A e₂).1 = -4 := by
      rw [hz] at hq'
      have hxsq : (A e₂).1 ^ 2 = 16 := by nlinarith
      have hxsq' : (A e₂).1 ^ 2 = (4 : ℤ) ^ 2 := by
        norm_num [hxsq]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hxsq'
    rcases hx with hx | hx
    · right
      right
      left
      apply vec_ext
      · exact hx
      · exact hy
      · exact hz
    · right
      right
      right
      apply vec_ext
      · exact hx
      · exact hy
      · exact hz
  · have hx : (A e₂).1 = 0 := by
      rw [hz] at hq'
      nlinarith
    left
    apply vec_ext
    · exact hx
    · exact hy
    · exact hz

private theorem q₁_image_third_not_four (A : LatticeTransport q₁)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁) :
    ¬ (A e₂ = 4 • e₀ ∨ A e₂ = -4 • e₀) := by
  intro hbad
  have hz0 : (A e₀).2.2 = 0 := by
    rcases hfirst with h | h <;> rw [h] <;> simp [e₀]
  have hz1 : (A e₁).2.2 = 0 := by
    rcases hmiddle with h | h <;> rw [h] <;> simp [e₁]
  have hz2 : (A e₂).2.2 = 0 := by
    rcases hbad with h | h <;> rw [h] <;> simp [e₀]
  have hzero (v : Vec) : (A v).2.2 = 0 := by
    have hd := congrArg (fun w : Vec => w.2.2) (latticeTransport_decompose A v)
    simpa [hz0, hz1, hz2] using hd
  have hi := hzero (A.invFun e₂)
  rw [A.right_inv] at hi
  simpa [e₂] using hi

private theorem q₁_image_third_sign (A : LatticeTransport q₁)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁) :
    A e₂ = e₂ ∨ A e₂ = -e₂ := by
  rcases q₁_image_third_classification A hmiddle hfirst with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (q₁_image_third_not_four A hfirst hmiddle (Or.inl h))
  · exact False.elim (q₁_image_third_not_four A hfirst hmiddle (Or.inr h))

private theorem q₁_transport_of_basis (A : LatticeTransport q₁)
    (a b c : Bool)
    (ha : A e₀ = q₁Map a false false e₀)
    (hb : A e₁ = q₁Map false b false e₁)
    (hc : A e₂ = q₁Map false false c e₂) :
    A = q₁Aut a b c := by
  have hfun : ∀ v, A v = q₁Map a b c v := by
    intro v
    rw [latticeTransport_decompose A v, ha, hb, hc]
    apply vec_ext <;> simp [q₁Map, e₀, e₁, e₂, sgn] <;> ring
  apply latticeTransport_ext
  intro v
  simpa [q₁Aut] using hfun v

private theorem q₁_basis_transport (A : LatticeTransport q₁)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁)
    (hthird : A e₂ = e₂ ∨ A e₂ = -e₂) :
    ∃ a b c : Bool, A = q₁Aut a b c := by
  rcases hfirst with h0 | h0 <;> rcases hmiddle with h1 | h1 <;>
    rcases hthird with h2 | h2
  · refine ⟨true, true, true, q₁_transport_of_basis A true true true ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨true, true, false, q₁_transport_of_basis A true true false ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨true, false, true, q₁_transport_of_basis A true false true ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨true, false, false, q₁_transport_of_basis A true false false ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨false, true, true, q₁_transport_of_basis A false true true ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨false, true, false, q₁_transport_of_basis A false true false ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨false, false, true, q₁_transport_of_basis A false false true ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2
  · refine ⟨false, false, false, q₁_transport_of_basis A false false false ?_ ?_ ?_⟩
    · simpa [q₁Map, e₀, sgn] using h0
    · simpa [q₁Map, e₁, sgn] using h1
    · simpa [q₁Map, e₂, sgn] using h2

theorem q₁_exhaustive_unit_classification :
    ∀ A : LatticeTransport q₁, A ∈ q₁UnitTransports := by
  intro A
  have hm := q₁_image_middle_sign A
  have hf := q₁_image_first_or_four A hm
  have ht := q₁_image_third_sign A hf hm
  obtain ⟨a, b, c, hA⟩ := q₁_basis_transport A hf hm ht
  rw [q₁UnitTransports]
  exact Finset.mem_image.mpr ⟨(a, b, c), Finset.mem_univ _, hA.symm⟩

private theorem q₂_image_first_sign (A : LatticeTransport q₂) :
    A e₀ = e₀ ∨ A e₀ = -e₀ := by
  have hq := A.preserves e₀
  have hqorig :
      2 * (A e₀).1 ^ 2 + 4 * (A e₀).2.1 ^ 2 +
          4 * (A e₀).2.1 * (A e₀).2.2 + 9 * (A e₀).2.2 ^ 2 = 2 := by
    simpa [q₂, brandtSecondQuadratic, e₀] using hq
  have hq' :
      2 * (A e₀).1 ^ 2 + (2 * (A e₀).2.1 + (A e₀).2.2) ^ 2 +
        8 * (A e₀).2.2 ^ 2 = 2 := by
    calc
      _ = 2 * (A e₀).1 ^ 2 + 4 * (A e₀).2.1 ^ 2 +
          4 * (A e₀).2.1 * (A e₀).2.2 + 9 * (A e₀).2.2 ^ 2 := by ring
      _ = 2 := hqorig
  have hzsq : (A e₀).2.2 ^ 2 = 0 := by
    nlinarith [sq_nonneg (A e₀).1,
      sq_nonneg (2 * (A e₀).2.1 + (A e₀).2.2)]
  have hz : (A e₀).2.2 = 0 := sq_eq_zero_iff.mp hzsq
  rw [hz] at hq'
  norm_num at hq'
  ring_nf at hq'
  have hxl : -1 ≤ (A e₀).1 := by nlinarith [hq']
  have hxu : (A e₀).1 ≤ 1 := by nlinarith [hq']
  have hxcases : (A e₀).1 = -1 ∨ (A e₀).1 = 0 ∨ (A e₀).1 = 1 := by omega
  have hxsq : (A e₀).1 ^ 2 = 1 := by
    rcases hxcases with hx | hx | hx
    · nlinarith
    · rw [hx] at hq'
      omega
    · nlinarith
  have hy : (A e₀).2.1 = 0 := by
    have hwsq : (2 * (A e₀).2.1) ^ 2 = 0 := by
      rw [hxsq] at hq'
      nlinarith [hq']
    have : 2 * (A e₀).2.1 = 0 := sq_eq_zero_iff.mp hwsq
    omega
  rw [hy] at hq'
  rcases sq_eq_one_iff.mp hxsq with hx | hx
  · left
    apply vec_ext
    · exact hx
    · exact hy
    · exact hz
  · right
    apply vec_ext
    · exact hx
    · exact hy
    · exact hz

private theorem q₂_polar_first (A : LatticeTransport q₂) (v : Vec) :
    q₂ (A e₀ + A v) - q₂ (A e₀) - q₂ (A v) =
      4 * (A e₀).1 * (A v).1 +
        8 * (A e₀).2.1 * (A v).2.1 +
        4 * (A e₀).2.1 * (A v).2.2 +
        4 * (A v).2.1 * (A e₀).2.2 +
        18 * (A e₀).2.2 * (A v).2.2 := by
  simp [q₂, brandtSecondQuadratic]
  ring

private theorem q₂_image_first_coordinate (A : LatticeTransport q₂) (v : Vec)
    (hsign : A e₀ = e₀ ∨ A e₀ = -e₀) :
    (A v).1 = (if A e₀ = e₀ then v.1 else -v.1) := by
  have hp := q₂_polar_first A v
  have hpolar :
      q₂ (A e₀ + A v) - q₂ (A e₀) - q₂ (A v) =
        q₂ (e₀ + v) - q₂ e₀ - q₂ v := by
    rw [← A.map_add, A.preserves, A.preserves, A.preserves]
  rcases hsign with hsign | hsign
  · rw [hsign] at hp hpolar
    simp [q₂, brandtSecondQuadratic, e₀] at hp hpolar
    rw [if_pos hsign]
    nlinarith [hpolar]
  · rw [hsign] at hp hpolar
    simp [q₂, brandtSecondQuadratic, e₀] at hp hpolar
    have hne : ¬ A e₀ = e₀ := by
      intro h
      rw [h] at hsign
      simpa [e₀] using hsign
    rw [if_neg hne]
    nlinarith [hpolar]

private theorem q₂_image_middle_sign (A : LatticeTransport q₂)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀) :
    A e₁ = e₁ ∨ A e₁ = -e₁ := by
  have hx := q₂_image_first_coordinate A e₁ hfirst
  have hx0 : (A e₁).1 = 0 := by
    rcases hfirst with h | h
    · simpa [if_pos h, e₁] using hx
    · have hn : ¬ A e₀ = e₀ := by
        intro hh
        rw [hh] at h
        simpa [e₀] using h
      simpa [if_neg hn, e₁] using hx
  have hq := A.preserves e₁
  have hqorig :
      2 * (A e₁).1 ^ 2 + 4 * (A e₁).2.1 ^ 2 +
          4 * (A e₁).2.1 * (A e₁).2.2 + 9 * (A e₁).2.2 ^ 2 = 4 := by
    simpa [q₂, brandtSecondQuadratic, e₁] using hq
  have hq' :
      2 * (A e₁).1 ^ 2 + (2 * (A e₁).2.1 + (A e₁).2.2) ^ 2 +
        8 * (A e₁).2.2 ^ 2 = 4 := by
    calc
      _ = 2 * (A e₁).1 ^ 2 + 4 * (A e₁).2.1 ^ 2 +
          4 * (A e₁).2.1 * (A e₁).2.2 + 9 * (A e₁).2.2 ^ 2 := by ring
      _ = 4 := hqorig
  rw [hx0] at hq'
  have hzsq : (A e₁).2.2 ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (2 * (A e₁).2.1 + (A e₁).2.2)]
  have hz : (A e₁).2.2 = 0 := by
    have : (A e₁).2.2 ^ 2 = 0 := le_antisymm hzsq (sq_nonneg _)
    exact sq_eq_zero_iff.mp this
  rw [hz] at hq'
  have hysq : (A e₁).2.1 ^ 2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp hysq with hy | hy
  · left
    apply vec_ext
    · exact hx0
    · exact hy
    · exact hz
  · right
    apply vec_ext
    · exact hx0
    · exact hy
    · exact hz

private theorem q₂_polar_middle (A : LatticeTransport q₂) (v : Vec) :
    q₂ (A e₁ + A v) - q₂ (A e₁) - q₂ (A v) =
      4 * (A e₁).1 * (A v).1 +
        8 * (A e₁).2.1 * (A v).2.1 +
        4 * (A e₁).2.1 * (A v).2.2 +
        4 * (A v).2.1 * (A e₁).2.2 +
        18 * (A e₁).2.2 * (A v).2.2 := by
  simp [q₂, brandtSecondQuadratic]
  ring

private theorem q₂_image_third_correlated (A : LatticeTransport q₂)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁) :
    (A e₁ = e₁ ∧ (A e₂ = e₂ ∨ A e₂ = e₁ - e₂)) ∨
      (A e₁ = -e₁ ∧ (A e₂ = -e₂ ∨ A e₂ = -e₁ + e₂)) := by
  have hx := q₂_image_first_coordinate A e₂ hfirst
  have hx0 : (A e₂).1 = 0 := by
    rcases hfirst with h | h
    · simpa [if_pos h, e₂] using hx
    · have hn : ¬ A e₀ = e₀ := by
        intro hh
        rw [hh] at h
        have hne : e₀ ≠ -e₀ := by
          intro hne
          norm_num [e₀] at hne
        exact hne h
      simpa [if_neg hn, e₂] using hx
  have hq := A.preserves e₂
  have hqorig :
      2 * (A e₂).1 ^ 2 + 4 * (A e₂).2.1 ^ 2 +
          4 * (A e₂).2.1 * (A e₂).2.2 + 9 * (A e₂).2.2 ^ 2 = 9 := by
    simpa [q₂, brandtSecondQuadratic, e₂] using hq
  have hq' :
      2 * (A e₂).1 ^ 2 + (2 * (A e₂).2.1 + (A e₂).2.2) ^ 2 +
        8 * (A e₂).2.2 ^ 2 = 9 := by
    calc
      _ = 2 * (A e₂).1 ^ 2 + 4 * (A e₂).2.1 ^ 2 +
          4 * (A e₂).2.1 * (A e₂).2.2 + 9 * (A e₂).2.2 ^ 2 := by ring
      _ = 9 := hqorig
  rw [hx0] at hq'
  rcases hmiddle with hm | hm
  · have hrel : 2 * (A e₂).2.1 + (A e₂).2.2 = 1 := by
      have hp := q₂_polar_middle A e₂
      have hpolar :
          q₂ (A e₁ + A e₂) - q₂ (A e₁) - q₂ (A e₂) =
            q₂ (e₁ + e₂) - q₂ e₁ - q₂ e₂ := by
        rw [← A.map_add, A.preserves, A.preserves, A.preserves]
      rw [hm] at hp hpolar
      simp [q₂, brandtSecondQuadratic, e₁, e₂] at hp hpolar
      ring_nf at hpolar
      have hpolar' :
          8 * (A (0, 0, 1)).2.1 + 4 * (A (0, 0, 1)).2.2 = 4 := by
        convert hpolar using 1 <;> ring
      have hpolar'' :
          8 * (A e₂).2.1 + 4 * (A e₂).2.2 = 4 := by
        simpa [e₂] using hpolar'
      nlinarith [hpolar'']
    have hzsq : (A e₂).2.2 ^ 2 = 1 := by
      rw [hrel] at hq'
      nlinarith
    rcases sq_eq_one_iff.mp hzsq with hz | hz
    · rw [hz] at hrel
      have hy : (A e₂).2.1 = 0 := by omega
      left
      refine ⟨hm, Or.inl ?_⟩
      apply vec_ext
      · simpa [e₁, e₂] using hx0
      · simpa [e₁, e₂] using hy
      · simpa [e₁, e₂] using hz
    · rw [hz] at hrel
      have hy : (A e₂).2.1 = 1 := by omega
      left
      refine ⟨hm, Or.inr ?_⟩
      apply vec_ext
      · simpa [e₁, e₂] using hx0
      · simpa [e₁, e₂] using hy
      · simpa [e₁, e₂] using hz
  · have hrel : 2 * (A e₂).2.1 + (A e₂).2.2 = -1 := by
      have hp := q₂_polar_middle A e₂
      have hpolar :
          q₂ (A e₁ + A e₂) - q₂ (A e₁) - q₂ (A e₂) =
            q₂ (e₁ + e₂) - q₂ e₁ - q₂ e₂ := by
        rw [← A.map_add, A.preserves, A.preserves, A.preserves]
      rw [hm] at hp hpolar
      simp [q₂, brandtSecondQuadratic, e₁, e₂] at hp hpolar
      ring_nf at hpolar
      have hpolar' :
          -8 * (A (0, 0, 1)).2.1 - 4 * (A (0, 0, 1)).2.2 = 4 := by
        convert hpolar using 1 <;> ring
      have hpolar'' :
          -8 * (A e₂).2.1 - 4 * (A e₂).2.2 = 4 := by
        simpa [e₂] using hpolar'
      nlinarith [hpolar'']
    have hzsq : (A e₂).2.2 ^ 2 = 1 := by
      rw [hrel] at hq'
      nlinarith
    rcases sq_eq_one_iff.mp hzsq with hz | hz
    · rw [hz] at hrel
      have hy : (A e₂).2.1 = -1 := by omega
      right
      refine ⟨hm, Or.inr ?_⟩
      apply vec_ext
      · simpa [e₁, e₂] using hx0
      · simpa [e₁, e₂] using hy
      · simpa [e₁, e₂] using hz
    · rw [hz] at hrel
      have hy : (A e₂).2.1 = 0 := by omega
      right
      refine ⟨hm, Or.inl ?_⟩
      apply vec_ext
      · simpa [e₁, e₂] using hx0
      · simpa [e₁, e₂] using hy
      · simpa [e₁, e₂] using hz

private theorem q₂_transport_of_basis (A : LatticeTransport q₂)
    (a b t : Bool)
    (ha : A e₀ = q₂Map a b t e₀)
    (hb : A e₁ = q₂Map a b t e₁)
    (hc : A e₂ = q₂Map a b t e₂) :
    A = q₂Aut a b t := by
  have hfun : ∀ v, A v = q₂Map a b t v := by
    intro v
    rw [latticeTransport_decompose A v, ha, hb, hc]
    cases t
    · apply vec_ext <;> simp [q₂Map, e₀, e₁, e₂, sgn] <;> ring
    · apply vec_ext
      · simp [q₂Map, e₀, e₁, e₂, sgn]
      · by_cases h : b = true <;> simp [q₂Map, e₀, e₁, e₂, sgn, h] <;> ring
      · simp [q₂Map, e₀, e₁, e₂, sgn]
  apply latticeTransport_ext
  intro v
  simpa [q₂Aut] using hfun v

private theorem q₂_basis_transport (A : LatticeTransport q₂)
    (hfirst : A e₀ = e₀ ∨ A e₀ = -e₀)
    (hmiddle : A e₁ = e₁ ∨ A e₁ = -e₁) :
    ∃ a b t : Bool, A = q₂Aut a b t := by
  rcases q₂_image_third_correlated A hfirst hmiddle with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · rcases hfirst with h0 | h0
    · refine ⟨true, true, false, q₂_transport_of_basis A true true false ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, sgn] using h2
    · refine ⟨false, true, false, q₂_transport_of_basis A false true false ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, sgn] using h2
  · rcases hfirst with h0 | h0
    · refine ⟨true, true, true, q₂_transport_of_basis A true true true ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, e₁, sgn] using h2
    · refine ⟨false, true, true, q₂_transport_of_basis A false true true ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, e₁, sgn] using h2
  · rcases hfirst with h0 | h0
    · refine ⟨true, false, false, q₂_transport_of_basis A true false false ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, sgn] using h2
    · refine ⟨false, false, false, q₂_transport_of_basis A false false false ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, sgn] using h2
  · rcases hfirst with h0 | h0
    · refine ⟨true, false, true, q₂_transport_of_basis A true false true ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, e₁, sgn] using h2
    · refine ⟨false, false, true, q₂_transport_of_basis A false false true ?_ ?_ ?_⟩
      · simpa [q₂Map, e₀, sgn] using h0
      · simpa [q₂Map, e₁, sgn] using h1
      · simpa [q₂Map, e₂, e₁, sgn] using h2

theorem q₂_exhaustive_unit_classification :
    ∀ A : LatticeTransport q₂, A ∈ q₂UnitTransports := by
  intro A
  have hf := q₂_image_first_sign A
  have hm := q₂_image_middle_sign A hf
  obtain ⟨a, b, t, hA⟩ := q₂_basis_transport A hf hm
  rw [q₂UnitTransports]
  exact Finset.mem_image.mpr ⟨(a, b, t), Finset.mem_univ _, hA.symm⟩

theorem exhaustive_unit_classification :
    (∀ A : LatticeTransport q₁, A ∈ q₁UnitTransports) ∧
      (∀ A : LatticeTransport q₂, A ∈ q₂UnitTransports) :=
  ⟨q₁_exhaustive_unit_classification, q₂_exhaustive_unit_classification⟩

#print axioms q₁_exhaustive_unit_classification
#print axioms q₂_exhaustive_unit_classification
#print axioms exhaustive_unit_classification

def exhaustiveUnitClassificationObligation : Prop :=
  (∀ A : LatticeTransport q₁, A ∈ q₁UnitTransports) ∧
  (∀ A : LatticeTransport q₂, A ∈ q₂UnitTransports)

end Soma.Holonics.Millennium.FamilyTunnellBrandtUnitWeights
