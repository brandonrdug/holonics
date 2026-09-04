import ElementaryHolonics.Millennium.Towers
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The sail: the convergent chain already carries the integer angle's complete invariant

**Integer geometry** is the geometry of `Aff_n(ℤ) = GL_n(ℤ) ⋉ ℤⁿ`, and every one of its invariants
is an *index of a sublattice in a lattice* (Karpenkov 2008, 2013).  Two of them are elementary:

```text
Il  P Q   = index of ⟨PQ⟩ in the lattice on the segment   = gcd of the coordinate differences
Isin u v  = index of ⟨u, v⟩ in the plane lattice          = |det (u, v)|
```

The **sail** of a cone is the boundary of the convex hull of the cone's non-vertex integer points
(Klein 1895; Karpenkov's *Klein polyhedron*).  In dimension two this **is** the ordinary continued
fraction: for the angle between `y = 0` and `y = αx` the sail's broken line `A₀A₁A₂…` satisfies
`a₀ = Il(A₀A₁)`, `a₁ = Isin(∠A₀A₁A₂)`, `a₂ = Il(A₁A₂)`, `a₃ = Isin(∠A₁A₂A₃)`, … — the **LLS
sequence**, alternating lengths and sines, and it is the complete `Aff_2(ℤ)` invariant of the angle.

**What this file proves is that no convex hull is needed to get it.**  `Towers` already proved the
only input — `h_{n+1}k_n − h_n k_{n+1} = (−1)ⁿ`, by integer induction — and from that one identity
the whole LLS sequence falls out of the recurrence:

* every convergent point `A n = (k_n, h_n)` is **primitive**, from the determinant alone;
* the edge law `A(n+2) − A n = a(n+2) • A(n+1)` is a definitional unfolding;
* so `Il(A n, A(n+2)) = |a(n+2)|` and `Isin(A(n+1), A(n+3)) = |a(n+3)|`.

The edge from `A n` to `A(n+2)` therefore carries exactly `a(n+2)` lattice steps of the primitive
vector `A(n+1)`.  `Towers` and `Farey` were the sail's complete invariant all along, under a
different vocabulary; this file names the sail and joins them, with no real number, no analysis and
no new machinery.  All four theorems hold for **every** `a : ℕ → ℤ` — no positivity hypothesis, and
in particular none on `a (n+2)`, because the two invariants are indices and land in `ℕ` already.

The second half formalizes one family from the three-dimensional theory, where the classification is
open.  Karpenkov's triangular pyramid `T^ξ_{a,r}` (apex at the origin, base `(ξ, r−1, −r)`,
`(a+ξ, r−1, −r)`, `(ξ, r, −r)`) carries the residual content of the face classification at integer
distance `r ≥ 3`, and here **its complete emptiness is exactly the primitivity of one ray** — the
whole condition collapses to a single `gcd`, proved by integer inequalities and one coprimality step.

## What is refused, and what is imported

**Not proved here, and stated in prose rather than smuggled into a `Prop`:** that the points
`A n` are the vertices of the convex hull of the lattice points in the angle.  Every theorem below is
about the *recurrence*; the identification of that recurrence with a convex hull is Klein's theorem
and Karpenkov's §1.2, and it is imported.  So this file proves that the convergent chain carries the
LLS sequence — **it does not prove that the convergent chain is the sail.**  Nothing here is a claim
about Karpenkov's Problem 3 (*"classify all combinatorial possible types of faces"*, arXiv:1712.01450
§3.2), which asks for a classification in every dimension and at every integer distance; a single
family with its emptiness criterion founds terrain, it does not cross it.

**Cited, used as motivation, and not stated below:** Klein, *Nachr. Ges. Wiss. Göttingen* 3 (1895)
352–357 (the geometric continued fraction); Karpenkov, *Elementary notions of lattice trigonometry*,
Math. Scand. 102 (2008) 161–205 (`Il`, `Isin`, and the LLS sequence as the complete invariant of an
integer angle); Karpenkov, *Geometry of Continued Fractions*, Springer (2013, 2nd ed. 2022);
Karpenkov, *Completely empty pyramids…*, arXiv:math/0510482v2 (2006), Theorem A and Corollary C
(the list `M–W` and the statement that the integer-linear and integer-affine classifications
coincide for `r < 5` and diverge for `r ≥ 5`); Moussafir, *Voiles et polyèdres de Klein* (2002)
(a compact two-dimensional face at integer distance `r ≥ 3` has exactly three vertices).

**One thing is carried as a named-open `Prop` and not as a theorem**, because it is Karpenkov's
Theorem A and is not verified here: that the pyramids in the family are *pairwise* integer-linearly
non-equivalent.  Without it the family's parametrisation by `ξ` counts nothing — a partition whose
blocks are separated only by a declared coordinate carries no evidence — so the collapse is proved
and the irredundancy is imported, and the two are kept apart.

**Anti-tautology control, and it fires.**  The emptiness criterion is not a restatement of its own
hypothesis: at `(a, r, ξ) = (1, 4, 2)`, where the ray fails to be primitive, the occluding lattice
point `(1, 2, −2)` is exhibited and the emptiness side of the equivalence is refuted outright.

**Measured 2026-08-21** from the repository root:
`grep -rn "sail\|Klein polyhedron\|integerSine\|integer sine" --include='*.lean' formal` → 0
hits outside this file, the vendored `.lake` mathlib tree included in the scope.  That command
measures those four strings over that scope and nothing else; a path or name search can never
establish a content absence, and it is not a claim that no related content exists under another name.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.Sail

open Soma.Holonics.Millennium.Towers

/-! ## Part I — the two-dimensional sail is the convergent chain

Karpenkov's two elementary invariants, and the four facts that make the convergent recurrence carry
the LLS sequence.  Every proof here is integer algebra over `Towers.theConvergentDeterminantAlternates`.
-/

variable (a : ℕ → ℤ)

/-- The `n`-th point of the two-dimensional sail: the convergent `h_n / k_n` read as the lattice
point `(k_n, h_n)`, so that the ray through it has slope `h_n / k_n`. -/
def sailPoint (n : ℕ) : ℤ × ℤ := (kk a n, hh a n)

/-- **Integer length** `Il(PQ)`: the index of `⟨PQ⟩` in the lattice of integer points on the
segment, which is the `gcd` of the coordinate differences — one less than the number of lattice
points on the closed segment. -/
def integerLength (P Q : ℤ × ℤ) : ℕ := Int.gcd (Q.1 - P.1) (Q.2 - P.2)

/-- **Integer sine** `Isin`: the index of the sublattice generated by two rays' primitive vectors
inside the plane lattice, which is the absolute determinant. -/
def integerSine (u v : ℤ × ℤ) : ℕ := (u.1 * v.2 - u.2 * v.1).natAbs

/-- **Every convergent point is primitive**, for every integer word.

A common divisor of `k_n` and `h_n` divides `h_{n+1}k_n − h_n k_{n+1} = (−1)ⁿ`, hence divides a
unit.  This is Bezout with no analysis: the determinant identity is the whole input, and no
positivity of the partial quotients is used.  Primitivity is what makes `A n` a candidate sail
vertex — a non-primitive point `v = m·w` lies in `w + C` and is never extreme. -/
theorem theConvergentIsPrimitive (n : ℕ) : Int.gcd (kk a n) (hh a n) = 1 := by
  have hd := theConvergentDeterminantAlternates a n
  have hL : ((Int.gcd (kk a n) (hh a n) : ℕ) : ℤ) ∣ kk a n := Int.gcd_dvd_left _ _
  have hR : ((Int.gcd (kk a n) (hh a n) : ℕ) : ℤ) ∣ hh a n := Int.gcd_dvd_right _ _
  have h1 : ((Int.gcd (kk a n) (hh a n) : ℕ) : ℤ) ∣ ((-1 : ℤ) ^ n) := by
    rw [← hd]
    exact dvd_sub (hL.mul_left _) (hR.mul_right _)
  have h2 : Int.gcd (kk a n) (hh a n) ∣ 1 := by
    have h3 := Int.natAbs_dvd_natAbs.mpr h1
    simpa using h3
  exact Nat.dvd_one.mp h2

/-- **The sail's edge law**: `A(n+2) − A n = a(n+2) • A(n+1)`.

Both recurrences unfold definitionally, so the step from one even-indexed point to the next is
exactly `a(n+2)` copies of the odd-indexed point between them.  Since `A(n+1)` is primitive, the
segment `A n → A(n+2)` carries precisely `a(n+2)` lattice steps and its interior lattice points are
`A n + j • A(n+1)` for `0 < j < a(n+2)`. -/
theorem theEdgeIsThePartialQuotientTimesTheOddConvergent (n : ℕ) :
    sailPoint a (n + 2) - sailPoint a n = a (n + 2) • sailPoint a (n + 1) := by
  have hk : kk a (n + 2) = a (n + 2) * kk a (n + 1) + kk a n := rfl
  have hn : hh a (n + 2) = a (n + 2) * hh a (n + 1) + hh a n := rfl
  simp only [sailPoint, hk, hn, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

/-- **The even partial quotient is an integer length**: `Il(A n, A(n+2)) = |a(n+2)|`.

From the edge law and primitivity, since `gcd (m·u, m·v) = |m| · gcd (u, v)`.  No hypothesis on the
sign of `a (n+2)` is needed — `Il` is an index and lands in `ℕ`, so the absolute value is already
taken by the invariant rather than imposed by a side condition. -/
theorem theIntegerLengthIsThePartialQuotient (n : ℕ) :
    integerLength (sailPoint a n) (sailPoint a (n + 2)) = (a (n + 2)).natAbs := by
  have hk : kk a (n + 2) = a (n + 2) * kk a (n + 1) + kk a n := rfl
  have hn : hh a (n + 2) = a (n + 2) * hh a (n + 1) + hh a n := rfl
  simp only [integerLength, sailPoint, hk, hn]
  rw [show a (n + 2) * kk a (n + 1) + kk a n - kk a n = a (n + 2) * kk a (n + 1) by ring,
    show a (n + 2) * hh a (n + 1) + hh a n - hh a n = a (n + 2) * hh a (n + 1) by ring,
    Int.gcd_mul_left, theConvergentIsPrimitive]
  exact Nat.mul_one _

/-- **The odd partial quotient is an integer sine**: `Isin(A(n+1), A(n+3)) = |a(n+3)|`.

`det(A(n+1), A(n+3)) = det(A(n+1), a(n+3)·A(n+2) + A(n+1)) = a(n+3) · det(A(n+1), A(n+2))`, and the
inner determinant is the alternating unit `(−1)^{n+1}`.  Together with the previous theorem this is
the whole LLS sequence: lengths at the even places, sines at the odd ones. -/
theorem theIntegerSineIsTheNextPartialQuotient (n : ℕ) :
    integerSine (sailPoint a (n + 1)) (sailPoint a (n + 3)) = (a (n + 3)).natAbs := by
  have hk : kk a (n + 3) = a (n + 3) * kk a (n + 2) + kk a (n + 1) := rfl
  have hn : hh a (n + 3) = a (n + 3) * hh a (n + 2) + hh a (n + 1) := rfl
  have hd := theConvergentDeterminantAlternates a (n + 1)
  have key : kk a (n + 1) * hh a (n + 3) - hh a (n + 1) * kk a (n + 3)
      = a (n + 3) * (-1 : ℤ) ^ (n + 1) := by
    rw [hk, hn, ← hd]; ring
  simp only [integerSine, sailPoint, key]
  simp [Int.natAbs_mul]

/-! ### One word, exhibited

The rising word `a i = i + 1`, i.e. the partial quotients `1, 2, 3, 4, 5, 6, 7, …`.  The chain and
both invariant families are computed by kernel reduction, so these are `rfl`-class receipts.  They
are the variation control for Part I: the returned lengths and sines *move with the word*, so the
four theorems above are not reporting a constant. -/

/-- The word whose partial quotients are `1, 2, 3, 4, 5, 6, 7, …`. -/
def risingWord : ℕ → ℤ := fun i => (i : ℤ) + 1

/-- **The rising word's convergent chain, exhibited.**  `rfl`-class: computed by kernel reduction. -/
theorem theRisingWordReturnsItsConvergentChain :
    (List.range 7).map (fun n => sailPoint risingWord n)
      = [(1, 1), (2, 3), (7, 10), (30, 43), (157, 225), (972, 1393), (6961, 9976)] := by
  decide

/-- **Every point of that chain is primitive, exhibited.**  `rfl`-class. -/
theorem theRisingWordChainIsPrimitive :
    (List.range 7).map (fun n => Int.gcd (kk risingWord n) (hh risingWord n))
      = [1, 1, 1, 1, 1, 1, 1] := by
  decide

/-- **The integer lengths of that chain are its even partial quotients, exhibited.**  `rfl`-class,
and it is the variation control: the returned invariants are `3, 4, 5, 6, 7`, not a constant. -/
theorem theRisingWordIntegerLengthsAreItsPartialQuotients :
    (List.range 5).map
        (fun n => integerLength (sailPoint risingWord n) (sailPoint risingWord (n + 2)))
      = [3, 4, 5, 6, 7] := by
  decide

/-- **The integer sines of that chain are its odd partial quotients, exhibited.**  `rfl`-class. -/
theorem theRisingWordIntegerSinesAreItsPartialQuotients :
    (List.range 4).map
        (fun n => integerSine (sailPoint risingWord (n + 1)) (sailPoint risingWord (n + 3)))
      = [4, 5, 6, 7] := by
  decide

/-! ## Part II — the completely empty pyramid, and its emptiness is one `gcd`

Karpenkov's triangular family `T^ξ_{a,r}` (arXiv:math/0510482v2, Theorem A) has apex at the origin
and base `(ξ, r−1, −r)`, `(a+ξ, r−1, −r)`, `(ξ, r, −r)` in the plane at integer distance `r`.  Its
cross-section at level `z = −k` is `(k/r) · T`, so a lattice point sits in the pyramid exactly when
`r·(x, y)` lies in `k · T` — three integer inequalities, no rational arithmetic.

*Reported, not encoded:* the determinant of the three primitive ray generators is `−a·r`, not `−r`
(verified by exact integer computation on 5 × 8 × (r−1) parameter triples), so `ξ/r` is **not** the
cone's singularity type and any Hirzebruch–Jung reading of this family through `r/ξ` alone is wrong.
-/

/-- The lattice point `(x, y, −k)` lies in Karpenkov's pyramid `T^ξ_{a,r}`.

`0 ≤ k ≤ r` places it between apex and base plane; the remaining three inequalities are the base
triangle's three edges, scaled to level `k`. -/
def inPyramidAtLevel (a r ξ x y k : ℤ) : Prop :=
  0 ≤ k ∧ k ≤ r ∧ k * ξ ≤ r * x ∧ k * (r - 1) ≤ r * y ∧
    (r * x - k * ξ) + a * (r * y - k * (r - 1)) ≤ a * k

/-- **The emptiness is the ray's primitivity.**

For `a ≥ 1` and `r ≥ 2`, the pyramid `T^ξ_{a,r}` has no lattice point at any strictly intermediate
level `0 < k < r` **exactly when** `gcd(ξ, r) = 1` — i.e. exactly when the ray through the base's
apex vertex `(ξ, r, −r)` is primitive.  The whole `Aff_3(ℤ)`-emptiness of an infinite family reduces
to a single `gcd`, and neither `a` nor the base's integer area enters the condition.

The forward proof is a squeeze: the last two inequalities force `y = k`, which forces `r·x = k·ξ`,
so `r ∣ k·ξ`, and coprimality moves the divisor onto `k`, contradicting `0 < k < r`.  The converse
exhibits the occluding point directly: with `d = gcd(ξ, r) > 1` it is `(ξ/d, r/d, −r/d)`, the lattice
point on the non-primitive ray itself. -/
theorem theEmptinessIsTheRayPrimitivity (a r ξ : ℤ) (ha : 1 ≤ a) (hr : 2 ≤ r) :
    (∀ x y k : ℤ, 0 < k → k < r → ¬ inPyramidAtLevel a r ξ x y k) ↔ Int.gcd ξ r = 1 := by
  have hr0 : (0 : ℤ) < r := by omega
  have ha0 : (0 : ℤ) < a := by omega
  constructor
  · intro hempty
    by_contra hne
    obtain ⟨x', hx'⟩ := Int.gcd_dvd_left ξ r
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right ξ r
    have hgne0 : Int.gcd ξ r ≠ 0 := by
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      omega
    have hd2 : (2 : ℤ) ≤ ((Int.gcd ξ r : ℕ) : ℤ) := by
      have h2 : 2 ≤ Int.gcd ξ r := by omega
      exact_mod_cast h2
    have hy0 : 0 < y' := by nlinarith
    have hklt : y' < r := by nlinarith
    have hxeq : y' * ξ = r * x' := by linear_combination y' * hx' - x' * hy'
    have hveq : r * y' - y' * (r - 1) = y' := by ring
    refine hempty x' y' y' hy0 hklt ⟨by omega, by nlinarith, le_of_eq hxeq, by nlinarith, ?_⟩
    rw [hveq]
    linarith [hxeq]
  · intro hg x y k hk0 hkr hp
    obtain ⟨_, _, h3, h4, h5⟩ := hp
    have e1 : k * (r - 1) = k * r - k := by ring
    rw [e1] at h4 h5
    have hu : 0 ≤ r * x - k * ξ := by linarith
    have hav : a * (r * y - (k * r - k)) ≤ a * k := by linarith
    have hvk : r * y - (k * r - k) ≤ k := le_of_mul_le_mul_left hav ha0
    have hyk : y ≤ k := by
      have hry : r * y ≤ r * k := by nlinarith
      exact le_of_mul_le_mul_left hry hr0
    have hky : k ≤ y := by
      by_contra hc
      push_neg at hc
      have hy1 : y ≤ k - 1 := by omega
      have : r * y ≤ r * (k - 1) := mul_le_mul_of_nonneg_left hy1 (le_of_lt hr0)
      nlinarith
    have hyeq : y = k := le_antisymm hyk hky
    rw [hyeq] at h5
    have e2 : r * k - (k * r - k) = k := by ring
    rw [e2] at h5
    have hxeq : k * ξ = r * x := by linarith
    have hdvd : r ∣ k * ξ := ⟨x, hxeq⟩
    have hcop : IsCoprime r ξ := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact hg
    have hrk : r ≤ k := Int.le_of_dvd hk0 (hcop.dvd_of_dvd_mul_right hdvd)
    omega

/-- **The occluding point on a non-primitive ray, exhibited.**

At `(a, r, ξ) = (1, 4, 2)` the ray `(2, 4, −4)` is `2 · (1, 2, −2)`, and that halving point sits in
the pyramid at level `k = 2`. -/
theorem theNonPrimitiveRayCarriesAnOccludingPoint : inPyramidAtLevel 1 4 2 1 2 2 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The anti-tautology control: coprimality genuinely fires.**

The emptiness side of the equivalence is *refuted outright* at `(a, r, ξ) = (1, 4, 2)`, where
`gcd(2, 4) = 2`.  So the criterion is not a restatement of its own hypothesis — varying `ξ` alone,
with `a` and `r` held fixed, moves the pyramid from empty to occupied, and the theorem above is not
reporting a property its declaration already forced. -/
theorem theNonPrimitiveRayRefutesEmptiness :
    ¬ (∀ x y k : ℤ, 0 < k → k < 4 → ¬ inPyramidAtLevel 1 4 2 x y k) := fun h =>
  h 1 2 2 (by norm_num) (by norm_num) theNonPrimitiveRayCarriesAnOccludingPoint

/-- **And the primitive sibling is empty**, by the theorem, at the same `a` and `r`.

`gcd(1, 4) = 1`, so `T^1_{1,4}` has no lattice point at level `1`, `2` or `3` — the same pyramid
shape, the same integer area, the same integer distance, one different ray. -/
theorem thePrimitiveRayLeavesThePyramidEmpty :
    ∀ x y k : ℤ, 0 < k → k < 4 → ¬ inPyramidAtLevel 1 4 1 x y k :=
  (theEmptinessIsTheRayPrimitivity 1 4 1 (by norm_num) (by norm_num)).mpr (by decide)

/-! ### The irredundancy is imported, and it is carried as a named-open `Prop`

The collapse is proved above; what makes the family a *classification* is that its members are
pairwise inequivalent, and that is Karpenkov's Theorem A rather than anything established here.
Declaring the `ξ`'s and then counting them would author the partition, so the count is not stated
and the non-equivalence is named. -/

/-- The apex and the three base vertices of `T^ξ_{a,r}`, as vectors in `ℤ³`. -/
def pyramidVertices (a r ξ : ℤ) : Set (Fin 3 → ℤ) :=
  {![0, 0, 0], ![ξ, r - 1, -r], ![a + ξ, r - 1, -r], ![ξ, r, -r]}

/-- **Named open — the fiber of the collapse is irredundant.**

For fixed `a` and `r`, the pyramids `T^ξ_{a,r}` with `0 < ξ ≤ r/2` and `gcd(ξ, r) = 1` are pairwise
*integer-linearly* non-equivalent: no element of `GL₃(ℤ)` carries one vertex set onto another.  This
is Karpenkov, arXiv:math/0510482v2, Theorem A together with Corollary C, and it is **not verified
here** — the emptiness criterion above says nothing about it.

It is stated rather than assumed because it is exactly the load-bearing half: without it the
parametrisation by `ξ` is a declared coordinate and the family's size is a restatement of its own
declaration table.  Note also that the acting group matters — Corollary C's content is that the
integer-*linear* and integer-*affine* classifications coincide for `r < 5` and diverge for `r ≥ 5`,
so the datum carried by `ξ` belongs to the pair (face, origin), not to the face alone. -/
def ThePyramidFiberIsIrredundant : Prop :=
  ∀ a r ξ ξ' : ℤ, 1 ≤ a → 2 ≤ r →
    0 < ξ → 2 * ξ ≤ r → Int.gcd ξ r = 1 →
    0 < ξ' → 2 * ξ' ≤ r → Int.gcd ξ' r = 1 →
    (∃ M : Matrix (Fin 3) (Fin 3) ℤ, IsUnit M.det ∧
      (fun v => M.mulVec v) '' pyramidVertices a r ξ = pyramidVertices a r ξ') →
    ξ = ξ'

end Soma.Holonics.Millennium.Sail
