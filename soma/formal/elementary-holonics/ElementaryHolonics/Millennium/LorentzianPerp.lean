import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic

/-!
# The reverse inequality, and what is definite on a perp

Two of the open lines this development touches turn on a symmetric form being definite on the
orthogonal complement of one distinguished class.

* On the **arithmetic** line, the archimedean estimate reads `⟨ξ, N ξ⟩ ≤ γ|⟨ξ₀,ξ⟩|²`, whose
  right-hand side vanishes on `ξ₀^⊥` — so the compression `−P₀ N P₀` pays there.  The compression is
  needed rather than a restriction because `N` does not preserve that perp.
* On the **cycle** line, the Hodge index theorem says a surface's intersection form has signature
  `(1, ρ−1)`: definite of one sign on an ample class and of the other on its perp.  The
  Hodge–Riemann form on a matroid's Chow ring is the same shape on the primitive part.

**They are one statement, and it is the reverse of Cauchy–Schwarz.**

    Cauchy–Schwarz          ⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩     holds for a POSITIVE SEMIDEFINITE form
                                                     and is what makes the GNS quotient work
    the reverse inequality  ⟨ω,v⟩² ≥ ⟨ω,ω⟩⟨v,v⟩     holds against a class of positive self-pairing
                                                     and IS non-positivity on that class's perp

The second is proved here to be *equivalent* to non-positivity on the perp, so it is not an
analogy: the index statement and the reverse inequality are the same hypothesis written twice.

**Measured 2026-08-20** over `Mathlib` at `v4.27.0`:
`grep -rl "Lorentzian" Mathlib --include='*.lean'` → 0 files, and a search for a reverse
Cauchy–Schwarz returns nothing.  Sylvester's law is present only over `ℝ` for nondegenerate forms as
a diagonalization (`Mathlib/LinearAlgebra/QuadraticForm/Real.lean`), not as a signature invariant.
Those commands measure those names over that scope; they are not a claim that no related content
exists under another name.

**No Cauchy–Schwarz is proved here** — the forward direction is mathlib's, and this file proves only
its reverse and the equivalence.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here is a claim about any
named conjecture: the two instances below are a two-dimensional Minkowski plane and a
four-dimensional lattice, and no curve, divisor, Frobenius or L-function appears.
-/

namespace Soma.Holonics.Millennium.LorentzianPerp

universe u v

variable {K : Type u} {V : Type v}
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]

/-! ## 1. The general shape: a bound against one class -/

omit [IsStrictOrderedRing K] in
/-- **A form bounded by a multiple of the square of a pairing against one class is non-positive on
that class's perp.**

The bound's right-hand side vanishes there, and nothing else is used — no symmetry, no
non-degeneracy, and no relation between the two forms.  *This is the archimedean step: the estimate
is stated against the ambient pairing while the form being signed is a different one, which is
exactly why a compression rather than a restriction is required.* -/
theorem theBoundedFormIsNonpositiveOnThePerp
    (q p : LinearMap.BilinForm K V) (om : V) (g : K)
    (h : ∀ x : V, q x x ≤ g * (p om x) ^ 2) {w : V} (hw : p om w = 0) :
    q w w ≤ 0 := by
  have := h w
  rw [hw] at this
  simpa using this

/-! ## 2. The equivalence -/

/-- **The reverse Cauchy-Schwarz inequality against a positive vector is exactly
non-positivity on that vector's perp.** -/
theorem theReverseCauchySchwarzIsNonpositivityOnThePerp
    (q : LinearMap.BilinForm K V) (hq : q.IsSymm) (om : V) (hom : 0 < q om om) :
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
    set t : K := q om x / q om om with ht
    set w : V := x - t • om with hwdef
    have hw : q om w = 0 := by
      rw [hwdef]
      simp only [map_sub, map_smul, smul_eq_mul]
      rw [ht]; field_simp; ring
    have hwo : q w om = 0 := by rw [hsymm w om]; exact hw
    have hx : x = w + t • om := by rw [hwdef]; abel
    have hexp : q x x = q w w + t * t * q om om := by
      rw [hx]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [hw, hwo]; ring
    have hto : q om x = t * q om om := by
      rw [hx]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [hw]; ring
    have hneg := h w hw
    rw [hexp, hto]
    nlinarith

/-! ## 3. The two instances, on concrete carriers -/

abbrev Plane : Type := ℚ × ℚ

/-- The Minkowski form `x₀y₀ − x₁y₁`. -/
def mink : LinearMap.BilinForm ℚ Plane :=
  LinearMap.mk₂ ℚ (fun u v => u.1 * v.1 - u.2 * v.2)
    (by intro a b c; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intro a b c; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro a c b; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp] theorem mink_apply (u v : Plane) : mink u v = u.1 * v.1 - u.2 * v.2 := rfl

theorem minkIsSymm : mink.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def]
  intro x y; simp; ring

/-- The timelike class. -/
def tau : Plane := (1, 0)

theorem theTimelikeClassPays : (0:ℚ) < mink tau tau := by simp [tau]

/-- **The form is negative semi-definite on the timelike class's perp** — the index statement. -/
theorem theMinkowskiPerpIsNonpositive (w : Plane) (hw : mink tau w = 0) : mink w w ≤ 0 := by
  simp only [mink_apply, tau] at hw ⊢
  have h0 : w.1 = 0 := by linarith
  rw [h0]; nlinarith [sq_nonneg w.2]

/-- **So the reverse inequality holds**, obtained from the equivalence rather than recomputed. -/
theorem theReverseInequalityHoldsOnThePlane (x : Plane) :
    mink tau tau * mink x x ≤ (mink tau x) ^ 2 :=
  (theReverseCauchySchwarzIsNonpositivityOnThePerp mink minkIsSymm tau theTimelikeClassPays).mpr
    theMinkowskiPerpIsNonpositive x

/-- **And Cauchy–Schwarz proper FAILS on the same form at the same pair.**

The two inequalities genuinely point in opposite directions; the reverse one is not a weakening. -/
theorem theForwardInequalityFailsOnThePlane :
    ¬ ((mink tau ((0,1) : Plane)) ^ 2 ≤ mink tau tau * mink (0,1) (0,1)) := by
  simp [tau]

/-! ### The cycle-line shape: signature `(1,3)` with a class that is not a basis vector -/

abbrev Lat : Type := ℚ × ℚ × ℚ × ℚ

/-- `diag(1,−1,−1,−1)`. -/
def lat (u v : Lat) : ℚ :=
  u.1 * v.1 - u.2.1 * v.2.1 - u.2.2.1 * v.2.2.1 - u.2.2.2 * v.2.2.2

/-- An ample-shaped class: self-pairing `24`, and no coordinate of it is zero. -/
def amp : Lat := (6, -2, -2, -2)

theorem theAmpleClassPays : lat amp amp = 24 := by norm_num [lat, amp]

/-- **The lattice form is negative definite on that class's perp.**

`6w₀ + 2w₁ + 2w₂ + 2w₃ = 0` forces `3w₀ = −(w₁+w₂+w₃)`, and then
`9·(w₀² − w₁² − w₂² − w₃²) = (w₁+w₂+w₃)² − 9(w₁²+w₂²+w₃²) ≤ −6(w₁²+w₂²+w₃²) ≤ 0`
by the ordinary Cauchy–Schwarz on three coordinates — so the *forward* inequality on the spacelike
part is what proves the *reverse* one against the timelike class. -/
theorem theAmplePerpIsNonpositive (w : Lat) (hw : lat amp w = 0) : lat w w ≤ 0 := by
  simp only [lat, amp] at hw ⊢
  have h3 : 3 * w.1 = -(w.2.1 + w.2.2.1 + w.2.2.2) := by linarith
  have hsq : 9 * (w.1 * w.1)
      = (w.2.1 + w.2.2.1 + w.2.2.2) * (w.2.1 + w.2.2.1 + w.2.2.2) := by
    calc 9 * (w.1 * w.1) = (3 * w.1) * (3 * w.1) := by ring
      _ = (-(w.2.1 + w.2.2.1 + w.2.2.2)) * (-(w.2.1 + w.2.2.1 + w.2.2.2)) := by rw [h3]
      _ = (w.2.1 + w.2.2.1 + w.2.2.2) * (w.2.1 + w.2.2.1 + w.2.2.2) := by ring
  nlinarith [hsq, sq_nonneg (w.2.1 - w.2.2.1), sq_nonneg (w.2.1 - w.2.2.2),
    sq_nonneg (w.2.2.1 - w.2.2.2)]

/-! ### The arithmetic-line shape: a bound against a distinguished mode -/

/-- The Euclidean pairing on the plane. -/
def ip (u v : Plane) : ℚ := u.1 * v.1 + u.2 * v.2

/-- `A = [[1,1],[1,−1]]`, paired through the Euclidean form. -/
def qA (u v : Plane) : ℚ := u.1 * (v.1 + v.2) + u.2 * (v.1 - v.2)

/-- **The estimate holds, and its slack is an exact square** — `⟨v, A v⟩ ≤ 2⟨τ,v⟩²` is `0 ≤ (x−y)²`. -/
theorem theEstimateSlackIsASquare (v : Plane) :
    2 * (ip tau v) ^ 2 - qA v v = (v.1 - v.2) ^ 2 := by
  simp only [ip, qA, tau]; ring

/-- **So the compressed form pays on the distinguished mode's perp**, which is the archimedean step
with the analysis removed: the bound's right-hand side vanishes there. -/
theorem theCompressionPaysOnThePerp (w : Plane) (hw : ip tau w = 0) : qA w w ≤ 0 := by
  have h := theEstimateSlackIsASquare w
  simp only [ip, tau] at hw
  simp only [qA] at h ⊢
  nlinarith [sq_nonneg (w.1 - w.2)]

/-- **The `qA` witness lies in the distinguished perp but has nonzero `qA` self-pairing.**

This records the numeric separation used by the example.  No operator is defined in this file, so
it makes no operator-invariance claim. -/
theorem theQAPerpWitnessHasNonzeroSelfPairing :
    ip tau ((0, 1) : Plane) = 0 ∧ qA ((0, 1) : Plane) ((0, 1) : Plane) ≠ 0 := by
  refine ⟨by simp [ip, tau], by norm_num [qA]⟩

end Soma.Holonics.Millennium.LorentzianPerp
