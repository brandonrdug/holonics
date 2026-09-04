import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# AlternatingParity: a nondegenerate alternating space has even dimension

The collapse is a phase object, and this is its parity law.  The Cassels–Tate pairing on
the Tate–Shafarevich group is alternating, which classically forces the group's order to be
a square when finite: the collapsed population pairs off with a hand, every member
partnered, none fixed.  This file proves the linear-algebra heart of that law, over **any**
field: a finite-dimensional vector space carrying a nondegenerate alternating bilinear form
has even dimension.  Applied over the two-element field it types the two-descent face of
the collapse: the Ш[2] of a two-descent, carrying its alternating pairing, has even
𝔽₂-dimension — its order is a square — which is exactly the parity that two-descent rank
bounds lean on.

The proof is the symplectic split, run through one product functional: pick `v ≠ 0`, get
`w` with `B v w = 1` by nondegeneracy and scaling; the pair of readings
`z ↦ (B v z, B w z)` is a surjection onto the plane (it sends `w ↦ (1, 0)` and
`v ↦ (0, −1)`, alternation supplying the zeros), so its kernel — the symplectic complement
of the plane `⟨v, w⟩` — has dimension exactly two less, and the form restricts to it
nondegenerately because the two coefficients of the complement decomposition are themselves
the two readings.  Descend by two and induct: the dimension is even.

`measured` (2026-08-21): mathlib carries `IsAlt` and `Nondegenerate` but no even-dimension
theorem for alternating forms
(`grep -rn "even\|Even" Mathlib/LinearAlgebra/BilinearForm/Properties.lean` → 0 relevant).

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the
finite-abelian-group form of the Cassels law (order a square via a nondegenerate
alternating pairing into ℚ/ℤ) needs the cocyclic value group and is not proved here; the
Cassels–Tate pairing itself and its alternation are imported literature, cited in the
ledger record.
-/

namespace Soma.Holonics.Millennium.AlternatingParity

open Module LinearMap

universe u v

variable {K : Type u} [Field K]

/-- **A nondegenerate alternating space has even dimension.**  Over any field, any
finite-dimensional space: the phase object's parity law. -/
theorem theAlternatingNondegenerateSpaceHasEvenDimension :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : LinearMap.BilinForm K V), B.IsAlt → B.Nondegenerate →
      Module.finrank K V = n → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ B halt hnd hrank
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exact hn0 ▸ ⟨0, rfl⟩
    -- a nonzero vector, and a partner reading one on it
    have hnt : Nontrivial V := by
      rw [← Module.finrank_pos_iff (R := K)]
      omega
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hex : ¬ ∀ w, B v w = 0 := fun hall => hv (hnd.1 v hall)
    push_neg at hex
    obtain ⟨w0, hw0⟩ := hex
    obtain ⟨w, hvw⟩ : ∃ w, B v w = 1 :=
      ⟨(B v w0)⁻¹ • w0, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw0]⟩
    have hskew : ∀ x y : V, B x y = -B y x := by
      intro x y
      have h0 := halt (x + y)
      simp only [map_add, LinearMap.add_apply] at h0
      have hx := halt x
      have hy := halt y
      linear_combination h0 - hx - hy
    have hwv : B w v = -1 := by
      rw [hskew w v, hvw]
    -- the product functional and its surjectivity
    set Φ : V →ₗ[K] K × K := (B v).prod (B w) with hΦdef
    have hΦapp : ∀ z : V, Φ z = (B v z, B w z) := fun z => rfl
    have hΦv : Φ v = ((0 : K), (-1 : K)) := by
      rw [hΦapp, halt v, hwv]
    have hΦw : Φ w = ((1 : K), (0 : K)) := by
      rw [hΦapp, hvw, halt w]
    have hsurj : Function.Surjective Φ := by
      intro p
      refine ⟨p.1 • w + (-p.2) • v, ?_⟩
      calc Φ (p.1 • w + (-p.2) • v)
          = p.1 • Φ w + (-p.2) • Φ v := by
            rw [map_add, map_smul, map_smul]
      _ = p.1 • ((1 : K), (0 : K)) + (-p.2) • ((0 : K), (-1 : K)) := by rw [hΦw, hΦv]
      _ = p := by
            ext <;> simp
    -- the symplectic complement and its dimension
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have hrange : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hrange2 : Module.finrank K (LinearMap.range Φ) = 2 := by
      rw [hrange]
      simp [finrank_top, Module.finrank_prod, Module.finrank_self]
    rw [hrange2, hrank] at hrn
    -- the restricted form on the kernel
    set W : Submodule K V := LinearMap.ker Φ with hWdef
    set B' : LinearMap.BilinForm K W := B.compl₁₂ W.subtype W.subtype with hB'def
    have hmem : ∀ x : W, B v (x : V) = 0 ∧ B w (x : V) = 0 := by
      intro x
      have hx : Φ (x : V) = 0 := LinearMap.mem_ker.mp x.2
      rw [hΦapp] at hx
      exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    have halt' : B'.IsAlt := fun x => halt (x : V)
    have hleft' : ∀ x : W, (∀ z : W, B' x z = 0) → x = 0 := by
      intro x hx
      have hzero : ∀ z : V, B (x : V) z = 0 := by
        intro z
        have hy : z - (B v z) • w - (-(B w z)) • v ∈ W := by
          have h1 : B v (z - (B v z) • w - (-(B w z)) • v) = 0 := by
            rw [map_sub, map_sub, map_smul, map_smul, hvw, halt v]
            simp [smul_eq_mul]
          have h2 : B w (z - (B v z) • w - (-(B w z)) • v) = 0 := by
            rw [map_sub, map_sub, map_smul, map_smul, halt w, hwv]
            simp [smul_eq_mul]
          have hker : Φ (z - (B v z) • w - (-(B w z)) • v) = 0 := by
            rw [hΦapp, h1, h2]
            rfl
          exact LinearMap.mem_ker.mpr hker
        have hxv : B (x : V) v = 0 := by
          rw [hskew (x : V) v, (hmem x).1, neg_zero]
        have hxw : B (x : V) w = 0 := by
          rw [hskew (x : V) w, (hmem x).2, neg_zero]
        have hxy : B (x : V) (z - (B v z) • w - (-(B w z)) • v) = 0 := hx ⟨_, hy⟩
        simp only [map_sub, map_smul, smul_eq_mul] at hxy
        linear_combination hxy + (B v z) * hxw + (-(B w z)) * hxv
      exact Subtype.ext (hnd.1 (x : V) hzero)
    have hskew' : ∀ x y : W, B' x y = -B' y x := by
      intro x y
      exact hskew (x : V) (y : V)
    have hright' : ∀ y : W, (∀ x : W, B' x y = 0) → y = 0 := by
      intro y hy
      apply hleft' y
      intro x
      rw [hskew' y x, hy x, neg_zero]
    have hnd' : B'.Nondegenerate := ⟨hleft', hright'⟩
    -- induct on the complement
    have hWrank : Module.finrank K W = n - 2 := by omega
    have hlt : n - 2 < n := by omega
    have heven := ih (n - 2) hlt W B' halt' hnd' hWrank
    have hn2 : 2 + (n - 2) = n := by omega
    have hfin : Even (2 + (n - 2)) := Even.add (⟨1, rfl⟩ : Even 2) heven
    rwa [hn2] at hfin

end Soma.Holonics.Millennium.AlternatingParity
