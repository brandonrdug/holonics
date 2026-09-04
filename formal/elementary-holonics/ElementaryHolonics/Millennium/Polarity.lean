import Mathlib.Tactic

/-!
# Polarity: the decomposition word carries what the volume product deletes

A centrally symmetric convex body `K ⊆ V` and its polar `K° ⊆ V*` live in different frames.
`Vol K` needs a chosen element of `ΛⁿV*` and `Vol K°` needs one of `ΛⁿV`, and those two choices
pair canonically — so the **volume product** `ν(K) = Vol K · Vol K°` is defined with no inner
product anywhere, while each factor alone is frame-relative.  That is the horizon law read
literally: a magnitude does not cross the frame boundary, the pairing does.

The **Hanner family** — the closure of the segment under the two sums `⊕₁` (the `ℓ₁` sum, the
convex hull of `K × 0` and `0 × L`) and `×_∞` (the direct product) — is the conjectured equality
set of Mahler's inequality, and polarity acts on it by **exchanging the two constructors**.  This
file founds that family as a finite inductive *word*, entirely over `ℕ` and `ℚ`, and proves the
one structural fact that makes it a collapsed population with an exhibited separator:

* the polarity of the word is an **involution** that preserves dimension and **fixes only the
  segment** — the conjectured minimiser family has an empty polarity fixed locus above dimension
  one, while Blaschke–Santaló's maximiser class (the ellipsoids) is a fixed point;
* the **cleared volume** `W h = Vol h · (dim h)!` keeps every quantity in `ℕ`: the `ℓ₁` sum
  divides by `(a+b)!` and the clearing removes the division exactly, leaving
  `W (a ×_∞ b) = W a · W b · C(a+b, a)` and `W (a ⊕₁ b) = W a · W b`;
* **the product is flat**: `W h · W (polar h) = 4 ^ dim h · (dim h)!` for every word, hence
  `ν(h) = 4 ^ dim h / (dim h)!` over `ℚ` — so **every receiver built from the volume product alone
  collapses the entire family to one point**, while the word separates it;
* the separator is exhibited at the smallest dimension where it exists: the four-cube and the
  three-cube-summed-with-a-segment have the same dimension and the same volume product `32/3`, and
  `16 ≠ 10` vertices.  The collapsed pair carries its distinguishing datum;
* the two collapse thresholds are integer facts.  Cube and cross-polytope have equal vertex counts
  exactly in dimension `≤ 2` (`2ⁿ = 2n` at `n ∈ {1,2}`), and in dimension two the collapse is
  *realised* by the integral quarter-turn `(x,y) ↦ (x+y, y−x)`, which doubles every oriented area
  — and that factor two is the carrier's own rational volume ratio, `vol square = 2 · vol diamond`,
  i.e. `4 = 2 · 2`, computed on a different carrier and agreeing.

Two controls are present, and both can fail: the single-slot magnitude does **not** collapse the
family (`W` separates the three-cube from the octahedron, `48 ≠ 8`), so flatness is a property of
the pairing rather than of the carrier; and the receiver schema below is exhibited failing on a
declared carrier, so it is not `True` in disguise.

**Named open, and stated as receiver schemas over a declared population rather than smuggled in as
hypotheses** (`MahlerLowerBoundHolds`, `TheEqualitySetIsCarriedByWords`).  Nothing here constructs
the convex-body carrier, Lebesgue measure, or the polar of an actual body; the schemas become
Mahler's conjecture (Mahler 1939) and the Hanner-uniqueness conjecture only once instantiated at
that carrier, which this file does not build.

**Imported and not proved here**, each a classical theorem cited so the words above are read at
their true height: Mahler (1939) for `n = 2` and the original statement `ν(K) ≥ 4ⁿ/n!`;
Blaschke–Santaló with Petty's equality characterization (the maximum is the ellipsoid class);
Hanner (1956) and Hansen–Lima for the `ℓ₁`/`ℓ∞` construction and the fact that polarity exchanges
the two sums; Iriyeh–Shibata, *Duke Math. J.* **169** (2020) 1077–1134, for `n = 3` together with
the equality characterization; Bourgain–Milman (1987), Kuperberg (*GAFA* **18** (2008) 870–892)
and Nazarov (2012) for the isomorphic reverse Santaló inequality; Saint-Raymond (1981), Meyer,
Reisner (1986) for the unconditional and zonoid cases; Artstein-Avidan–Karasev–Ostrover,
*Duke Math. J.* **163** (2014) 2003–2022, for `c_HZ(K × K°) = 4` and Viterbo ⟹ Mahler.

**Refused, and recorded so the refusal is checkable.**  The correspondence between the two
collapse thresholds proved below and the two difficulty steps in the literature is
**retrodictive**: both were computed after reading the answers, and it is circular to cite
Iriyeh–Shibata's own result as the explanation of why their proof reaches dimension three and no
further.  That correspondence is `interpretation` with two witnesses and it grades nothing here.  Likewise refused: the reading that the constant missing
from the isomorphic bounds is a phase datum (a constant is a magnitude, so this is an
equivocation), and the reading that the failure of Viterbo's conjecture is caused by the
refuting body's rotational order (one witness, and its authors attribute nothing of the kind).
Everything below is a theorem about decomposition words; the identification of that family with
the minimiser set is the open Hanner-uniqueness conjecture and is never used as a premise.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`, from
`formal/elementary-holonics/.lake/packages/mathlib`:
`grep -rli "hanner" Mathlib --include='*.lean'` → 1 file, and it is Hanner's *inequalities* in
`Analysis/Convex/Uniform.lean`, a different object;
`grep -rli "volume product\|Mahler conjecture\|polar dual\|polar body" Mathlib --include='*.lean'`
→ 0 files; `grep -rli "mahler" Mathlib --include='*.lean'` → 4 files, every one of them the
Mahler *measure* of a polynomial or the Mahler basis of `p`-adic continuous functions.  Those
commands measure those names over that scope; they are not a content-absence proof.

Every `theorem` is discharged and none depends on `sorryAx`.  The exhibited tables are `decide`-
and `norm_num`-class evaluations of the definitions below.  **Boundary:** nothing here claims any
movement on Mahler's conjecture, on Viterbo's conjecture, or on Hanner uniqueness; no convex body,
no measure, no capacity and no billiard appears, and the volume of a word is a *definition* on the
word — its agreement with the Lebesgue volume of the corresponding polytope is imported from
Hanner (1956) and is not proved here.
-/

namespace Soma.Holonics.Millennium.Polarity

/-! ## 1. The decomposition word

The Hanner family is the free closure of one landmark — the segment — under two binary
operations.  A word is therefore a binary tree with segment leaves and a constructor label at
every node, and *that label is the whole datum polarity acts on*. -/

/-- A **Hanner decomposition word**: the segment, the `ℓ₁` sum `⊕₁`, and the `ℓ∞` sum `×_∞`
(the direct product).  Geometrically `a ⊕₁ b = conv ((a × 0) ∪ (0 × b))` and `a ×_∞ b = a × b`;
here the word *is* the object and the geometry is imported. -/
inductive Hanner : Type
  | seg : Hanner
  | l1 : Hanner → Hanner → Hanner
  | linf : Hanner → Hanner → Hanner
  deriving DecidableEq

/-- The dimension of a word: both sums add dimensions, and the segment is one-dimensional.
Every word has dimension at least one; there is no point in this family. -/
def dim : Hanner → ℕ
  | .seg => 1
  | .l1 a b => dim a + dim b
  | .linf a b => dim a + dim b

/-- **Polarity acts on the word by exchanging the two sums**: `(a ×_∞ b)° = a° ⊕₁ b°` and
`(a ⊕₁ b)° = a° ×_∞ b°`, with the segment self-polar.  No geometry is used; this is Hanner's
construction taken as the definition of the involution on words. -/
def polar : Hanner → Hanner
  | .seg => .seg
  | .l1 a b => .linf (polar a) (polar b)
  | .linf a b => .l1 (polar a) (polar b)

/-- The **cleared volume** `W h = Vol h · (dim h)!`.  The three geometric rules are
`Vol seg = 2`, `Vol (a ⊕₁ b) = Vol a · Vol b · a! b! / (a+b)!` and `Vol (a ×_∞ b) = Vol a · Vol b`;
multiplying through by `(dim h)!` deletes the only division in the family and leaves natural
numbers, with the binomial coefficient appearing exactly where the product does. -/
def W : Hanner → ℕ
  | .seg => 2
  | .l1 a b => W a * W b
  | .linf a b => W a * W b * Nat.choose (dim a + dim b) (dim a)

/-- The vertex population of a word: the `ℓ₁` sum takes the union of the two vertex sets and the
direct product takes their product.  Vertex count is invariant under linear equivalence, so
*inequality* of vertex counts refutes linear equivalence; equality never establishes it. -/
def verts : Hanner → ℕ
  | .seg => 2
  | .l1 a b => verts a + verts b
  | .linf a b => verts a * verts b

/-- The cube word on `n + 1` segments, so `dim (cube n) = n + 1`: `cube 0` is the segment,
`cube 1` the square, `cube 2` the three-cube, `cube 3` the four-cube. -/
def cube : ℕ → Hanner
  | 0 => .seg
  | (n + 1) => .linf .seg (cube n)

/-- The cross-polytope word on `n + 1` segments, so `dim (cross n) = n + 1`: `cross 1` is the
diamond, `cross 2` the octahedron. -/
def cross : ℕ → Hanner
  | 0 => .seg
  | (n + 1) => .l1 .seg (cross n)

/-- The four-dimensional **mixed** word: the three-cube summed with a segment in the `ℓ₁` chart.
It is neither the four-cube nor the four-dimensional cross-polytope, and it is the witness that
the family stops being one orbit at dimension four. -/
def mixedFour : Hanner := .l1 (cube 2) .seg

/-! ## 2. The polarity is an involution with an almost empty fixed locus -/

/-- **Polarity preserves dimension.**  Structural induction; both constructors add dimensions and
the exchange does not touch the addition. -/
theorem theDimensionSurvivesPolarity (h : Hanner) : dim (polar h) = dim h := by
  induction h with
  | seg => rfl
  | l1 a b iha ihb => simp only [polar, dim, iha, ihb]
  | linf a b iha ihb => simp only [polar, dim, iha, ihb]

/-- **Polarity is an involution** — the word-level bipolar theorem `K°° = K`.  It is a rebase with
zero remainder, not a compression: exchanging the labels twice returns the identical tree. -/
theorem thePolarityIsAnInvolution (h : Hanner) : polar (polar h) = h := by
  induction h with
  | seg => rfl
  | l1 a b iha ihb => simp only [polar, iha, ihb]
  | linf a b iha ihb => simp only [polar, iha, ihb]

/-- **The polarity fixes only the segment.**  Every non-leaf node changes its constructor, so no
word of dimension above one is self-polar.  The conjectured *minimiser* family therefore has an
empty fixed locus above dimension one, in contrast with the ellipsoid class, which is the
maximiser and is a fixed point of polarity — that contrast is a description of the two equality
sets, and this file grades nothing by it. -/
theorem thePolarityFixesOnlyTheSegment (h : Hanner) : polar h = h ↔ h = .seg := by
  constructor
  · intro hp
    cases h with
    | seg => rfl
    | l1 a b =>
      simp only [polar] at hp
      exact Hanner.noConfusion hp
    | linf a b =>
      simp only [polar] at hp
      exact Hanner.noConfusion hp
  · rintro rfl
    rfl

/-! ## 3. The flat volume product

The single arithmetic fact behind the flatness is that the binomial coefficient supplied by a
direct product is exactly the reciprocal of the factorials the `ℓ₁` sum would have divided by. -/

/-- The factorial-clearing identity `C(a+b, a) · a! · b! = (a+b)!`, in the denominator-cleared
form this file runs in. -/
theorem theChooseClearsTheFactorials (a b : ℕ) :
    Nat.choose (a + b) a * Nat.factorial a * Nat.factorial b = Nat.factorial (a + b) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rwa [Nat.add_sub_cancel_left] at h

/-- **The cleared volume product is flat across the whole family**:
`W h · W (polar h) = 4 ^ dim h · (dim h)!` for every decomposition word.

Structural induction.  In each inductive case exactly one side of the pair contributes the
binomial coefficient — the `ℓ₁` node contributes none and its polar direct product contributes
`C(a+b,a)` — and the two induction hypotheses contribute `4 ^ a · a!` and `4 ^ b · b!`, whose
factorials the coefficient clears into `(a+b)!`.

This is the flatness the whole reading rests on: dividing through by `((dim h)!)²` gives
`ν(h) = 4 ^ dim h / (dim h)!` uniformly, so the volume product is constant on the family. -/
theorem theClearedVolumeProductIsFlat (h : Hanner) :
    W h * W (polar h) = 4 ^ dim h * Nat.factorial (dim h) := by
  induction h with
  | seg => rfl
  | l1 a b iha ihb =>
    simp only [polar, W, dim, theDimensionSurvivesPolarity]
    calc W a * W b * (W (polar a) * W (polar b) * Nat.choose (dim a + dim b) (dim a))
        = W a * W (polar a) * (W b * W (polar b)) *
            Nat.choose (dim a + dim b) (dim a) := by ring
      _ = 4 ^ dim a * Nat.factorial (dim a) * (4 ^ dim b * Nat.factorial (dim b)) *
            Nat.choose (dim a + dim b) (dim a) := by rw [iha, ihb]
      _ = 4 ^ (dim a + dim b) *
            (Nat.choose (dim a + dim b) (dim a) * Nat.factorial (dim a) *
              Nat.factorial (dim b)) := by rw [pow_add]; ring
      _ = 4 ^ (dim a + dim b) * Nat.factorial (dim a + dim b) := by
            rw [theChooseClearsTheFactorials]
  | linf a b iha ihb =>
    simp only [polar, W, dim]
    calc W a * W b * Nat.choose (dim a + dim b) (dim a) * (W (polar a) * W (polar b))
        = W a * W (polar a) * (W b * W (polar b)) *
            Nat.choose (dim a + dim b) (dim a) := by ring
      _ = 4 ^ dim a * Nat.factorial (dim a) * (4 ^ dim b * Nat.factorial (dim b)) *
            Nat.choose (dim a + dim b) (dim a) := by rw [iha, ihb]
      _ = 4 ^ (dim a + dim b) *
            (Nat.choose (dim a + dim b) (dim a) * Nat.factorial (dim a) *
              Nat.factorial (dim b)) := by rw [pow_add]; ring
      _ = 4 ^ (dim a + dim b) * Nat.factorial (dim a + dim b) := by
            rw [theChooseClearsTheFactorials]

/-- The rational volume of a word, `W h / (dim h)!`. -/
def vol (h : Hanner) : ℚ := (W h : ℚ) / (Nat.factorial (dim h) : ℚ)

/-- The **volume product** of a word: the canonical two-frame pairing `⟨h° | h⟩`. -/
def volumeProduct (h : Hanner) : ℚ := vol h * vol (polar h)

/-- **The volume product is `4 ^ n / n!` on every word of dimension `n`** — the conjectured
Mahler minimum, attained across the whole family with equality. -/
theorem theVolumeProductIsFlatOverTheRationals (h : Hanner) :
    volumeProduct h = (4 : ℚ) ^ dim h / (Nat.factorial (dim h) : ℚ) := by
  have hf : (Nat.factorial (dim h) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have key : (W h : ℚ) * (W (polar h) : ℚ)
      = (4 : ℚ) ^ dim h * (Nat.factorial (dim h) : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (theClearedVolumeProductIsFlat h)
  simp only [volumeProduct, vol, theDimensionSurvivesPolarity]
  field_simp
  linear_combination key

/-- **No volume-product receiver separates any two words of the same dimension.**  The collapsed
population is the entire family; this is the statement that the magnitude face carries no
information about which body it is looking at. -/
theorem theMagnitudeCannotSeparateTheFamily (h h' : Hanner) (hd : dim h = dim h') :
    volumeProduct h = volumeProduct h' := by
  rw [theVolumeProductIsFlatOverTheRationals, theVolumeProductIsFlatOverTheRationals, hd]

/-- **The single slot does separate**, and this is the control that makes the theorem above a
statement about the *pairing* rather than about the carrier: the three-cube's cleared volume is
`48` and the octahedron's is `8`.  A magnitude in one frame is not flat; only the two-frame
pairing is.  `decide`-class. -/
theorem theSingleSlotStillSeparates : W (cube 2) ≠ W (cross 2) := by decide

/-! ## 4. The exhibited tables

Every entry was recomputed by exact integer arithmetic before being written here. -/

/-- **The cleared-product table**, `decide`-class: segment `2·2 = 4`; square/diamond `8·4 = 32`;
three-cube/octahedron `48·8 = 384`; four-cube/four-cross `384·16 = 6144`; and the mixed word
`96·64 = 6144` — the same product from a different word. -/
theorem theClearedProductTableIsExhibited :
    W .seg * W (polar .seg) = 4 ∧
    W (cube 1) * W (polar (cube 1)) = 32 ∧
    W (cross 1) * W (polar (cross 1)) = 32 ∧
    W (cube 2) * W (polar (cube 2)) = 384 ∧
    W (cross 2) * W (polar (cross 2)) = 384 ∧
    W (cube 3) * W (polar (cube 3)) = 6144 ∧
    W (cross 3) * W (polar (cross 3)) = 6144 ∧
    W mixedFour * W (polar mixedFour) = 6144 := by decide

/-- **The cleared volumes themselves**, `decide`-class, so the table above can be read off its
factors: `W (cube 2) = 48`, `W (cross 2) = 8`, `W mixedFour = 96`, `W (polar mixedFour) = 64`. -/
theorem theClearedVolumeTableIsExhibited :
    W .seg = 2 ∧ W (cube 1) = 8 ∧ W (cross 1) = 4 ∧ W (cube 2) = 48 ∧ W (cross 2) = 8 ∧
    W (cube 3) = 384 ∧ W (cross 3) = 16 ∧ W mixedFour = 96 ∧ W (polar mixedFour) = 64 := by
  decide

/-- **The rational volumes**: segment `2`, square `4`, diamond `2`, three-cube `8`, octahedron
`4/3`, mixed word `4` and its polar `8/3`.  `norm_num`-class evaluation of `vol`. -/
theorem theRationalVolumeTableIsExhibited :
    vol .seg = 2 ∧ vol (cube 1) = 4 ∧ vol (cross 1) = 2 ∧ vol (cube 2) = 8 ∧
    vol (cross 2) = 4 / 3 ∧ vol mixedFour = 4 ∧ vol (polar mixedFour) = 8 / 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [vol]
      norm_num [W, dim, polar, cube, cross, mixedFour, Nat.factorial]

/-- **The volume product at dimension four is `32/3`** for the four-cube, the four-dimensional
cross-polytope and the mixed word alike. -/
theorem theVolumeProductAtDimensionFourIsExhibited :
    volumeProduct (cube 3) = 32 / 3 ∧ volumeProduct (cross 3) = 32 / 3 ∧
    volumeProduct mixedFour = 32 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [theVolumeProductIsFlatOverTheRationals]
      norm_num [dim, cube, cross, mixedFour, Nat.factorial]

/-! ## 5. The word separates where the magnitude cannot -/

/-- **The collapsed pair with its distinguishing datum exhibited**, at the smallest dimension
where one exists.  The four-cube and the three-cube-summed-with-a-segment have equal dimension and
equal volume product, and `16 ≠ 10` vertices.  Vertex count is invariant under linear equivalence,
so the inequality refutes linear equivalence; the converse direction is not claimed anywhere in
this file. -/
theorem theWordSeparatesWhereTheMagnitudeCannot :
    dim (cube 3) = dim mixedFour ∧
    volumeProduct (cube 3) = volumeProduct mixedFour ∧
    verts (cube 3) = 16 ∧ verts mixedFour = 10 ∧
    verts (cube 3) ≠ verts mixedFour := by
  refine ⟨by decide, theMagnitudeCannotSeparateTheFamily _ _ (by decide), by decide, by decide,
    by decide⟩

/-! ## 6. The two collapse thresholds, as integer facts -/

/-- `dim (cube n) = n + 1`. -/
theorem theCubeWordHasSuccessorDimension (n : ℕ) : dim (cube n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cube, dim, ih]
    omega

/-- `dim (cross n) = n + 1`. -/
theorem theCrossWordHasSuccessorDimension (n : ℕ) : dim (cross n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cross, dim, ih]
    omega

/-- The cube word has `2 ^ dim` vertices. -/
theorem theCubeHasTwoToTheDimensionVertices (n : ℕ) : verts (cube n) = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cube, verts, ih, pow_succ]
    ring

/-- The cross-polytope word has twice its dimension many vertices. -/
theorem theCrossHasTwiceTheDimensionVertices (n : ℕ) : verts (cross n) = 2 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cross, verts, ih]
    ring

/-- `n + 1 < 2 ^ n` for `n ≥ 2` — the arithmetic that closes the vertex-collapse threshold. -/
theorem theSuccessorFallsBelowTheBinaryPowerFromTwo (n : ℕ) (hn : 2 ≤ n) : n + 1 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    have h2 : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega

/-- **The cube and the cross-polytope collapse exactly below dimension three.**  Their vertex
populations agree iff `2 ^ n = 2n`, which holds at `n = 1` and `n = 2` and nowhere else.  This is
the first of the two thresholds; that it coincides with the boundary of the elementary case of
Mahler's inequality is recorded in the header as retrodictive interpretation and grades nothing. -/
theorem theVertexCollapseHoldsOnlyBelowThree (n : ℕ) :
    verts (cube n) = verts (cross n) ↔ dim (cube n) ≤ 2 := by
  rw [theCubeHasTwoToTheDimensionVertices, theCrossHasTwiceTheDimensionVertices,
    theCubeWordHasSuccessorDimension]
  constructor
  · intro h
    by_contra hc
    have hn : 2 ≤ n := by omega
    have hlt := theSuccessorFallsBelowTheBinaryPowerFromTwo n hn
    rw [pow_succ] at h
    omega
  · intro h
    have hn : n ≤ 1 := by omega
    interval_cases n <;> norm_num

/-! ## 7. The plane collapse is an integral quarter-turn

In dimension two the collapse of the two words is not merely a coincidence of counts: it is
realised by a linear map with an integral presentation.  Everything here is over `ℤ`; no rotation
angle, no square root and no real number enters. -/

/-- The oriented area pairing of the integer plane — antisymmetric, not a metric one. -/
def spanOf (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

/-- The plane's **quarter-turn**, presented over `ℤ`: `(x, y) ↦ (x + y, y − x)`. -/
def turn (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + p.2, p.2 - p.1)

/-- **The quarter-turn doubles every oriented area**, which is its determinant read off the
pairing rather than declared.  `ring`-class after unfolding. -/
theorem theQuarterTurnDoublesEveryOrientedArea (u v : ℤ × ℤ) :
    spanOf (turn u) (turn v) = 2 * spanOf u v := by
  simp only [spanOf, turn]
  ring

/-- **The quarter-turn carries the four cross-polytope vertices onto the four cube vertices**,
exhibited one by one over `ℤ`.  This is the `n = 2` accident with an integral presentation: the
two words of dimension two are one body up to a linear map of determinant two. -/
theorem theQuarterTurnCarriesTheCrossOntoTheCube :
    turn (1, 0) = (1, -1) ∧ turn (0, 1) = (1, 1) ∧
    turn (-1, 0) = (-1, 1) ∧ turn (0, -1) = (-1, -1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [turn]

/-- **The quarter-turn is not unimodular**, and its factor two is exactly the ratio the carrier's
own rational volumes report: `vol (square) = 4 = 2 · vol (diamond)`.  The integer determinant and
the rational volume ratio are the same number, computed on two different carriers. -/
theorem theQuarterTurnFactorIsTheVolumeRatio :
    spanOf (turn (1, 0)) (turn (0, 1)) = 2 * spanOf (1, 0) (0, 1) ∧
    spanOf ((1 : ℤ), (0 : ℤ)) (0, 1) = 1 ∧
    vol (cube 1) = 2 * vol (cross 1) := by
  refine ⟨theQuarterTurnDoublesEveryOrientedArea _ _, by decide, ?_⟩
  rw [vol, vol]
  norm_num [W, dim, cube, cross, Nat.factorial]

/-! ## 8. What is named open

Neither proposition below is proved, and neither is `True` in disguise: each is a statement about
its declared parameters, and each is exhibited failing on a declared carrier.  They are receiver
schemas — instantiating them at the actual carrier of centrally symmetric convex bodies with
Lebesgue volume and the genuine polar is what turns them into the named conjectures, and this
file does not construct that carrier. -/

/-- **Named open — Mahler's conjecture (Mahler 1939), in receiver-schema form.**  For a declared
population `Body` with a dimension face `d` and a volume-product face `nu` valued in `ℚ`, every
member's volume product is at least `4 ^ d / d!`.

Proved for `d ≤ 3` in the centrally symmetric case (Mahler 1939 for `d = 2`; Iriyeh–Shibata 2020
for `d = 3`) and open for `d ≥ 4`; known up to an exponential factor by Bourgain–Milman 1987. -/
def MahlerLowerBoundHolds (Body : Type) (d : Body → ℕ) (nu : Body → ℚ) : Prop :=
  ∀ b : Body, (4 : ℚ) ^ d b / (Nat.factorial (d b) : ℚ) ≤ nu b

/-- **Named open — Hanner uniqueness, in receiver-schema form.**  Every member of the declared
population whose volume product attains `4 ^ d / d!` is realised by some decomposition word.
Known for `d = 2, 3` (Iriyeh–Shibata's equality characterization) and open for `d ≥ 4`.

This is exactly the proposition that must never be used as a premise here: if a non-Hanner
minimiser exists in some dimension, every theorem above remains true and its identification with
the minimiser set evaporates. -/
def TheEqualitySetIsCarriedByWords (Body : Type) (d : Body → ℕ) (nu : Body → ℚ)
    (realize : Hanner → Body) : Prop :=
  ∀ b : Body, nu b = (4 : ℚ) ^ d b / (Nat.factorial (d b) : ℚ) → ∃ h : Hanner, realize h = b

/-- **The word carrier meets the conjectured bound, with equality everywhere.**  The schema is
therefore satisfiable and tight on this population — which is the content of the flatness theorem
restated as a receiver reading. -/
theorem theWordCarrierMeetsTheConjecturedBound :
    MahlerLowerBoundHolds Hanner dim volumeProduct := by
  intro h
  rw [theVolumeProductIsFlatOverTheRationals]

/-- **The Mahler schema can fail**, exhibited: a population whose volume-product face returns zero
refutes it at the segment.  A check whose material cannot vary the property under test carries
nothing; this one varies and fails. -/
theorem theMahlerSchemaCanFail :
    ¬ MahlerLowerBoundHolds Hanner dim (fun _ => 0) := by
  intro hcon
  have h := hcon .seg
  norm_num [dim, Nat.factorial] at h

/-- **The Hanner-uniqueness schema can fail**, exhibited: a two-element population at the
conjectured value with a realization map that reaches only one of them.  So the proposition above
is a real statement about its parameters, not a tautology. -/
theorem theUniquenessSchemaCanFail :
    ¬ TheEqualitySetIsCarriedByWords Bool (fun _ => 1) (fun _ => 4) (fun _ => true) := by
  intro hcon
  obtain ⟨_, hw⟩ := hcon false (by norm_num [Nat.factorial])
  exact Bool.noConfusion hw

end Soma.Holonics.Millennium.Polarity
