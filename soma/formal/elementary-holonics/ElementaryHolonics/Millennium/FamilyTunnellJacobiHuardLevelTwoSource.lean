import ElementaryHolonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction

/-!
# The finite Huard--Ou--Spearman--Williams level-two source

This file gives the source-side carrier for equation (4.4) of Huard--Ou--
Spearman--Williams.  The two congruence currents retain the complete positive
factorization data `(a,x)` of `m` and `(b,y)` of `n-m`; the displayed divisor
convolutions are receiver sums of that carrier.

The complete paper-side diagonal/off-diagonal reindexing is constructed
below through exact summand-preserving bijections and involutions.  The
elementary level-two parity partition is retained as a separately owned
source proposition; the downstream reduction is exact.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource

open Finset
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct
open Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction

/-! ## The source's finite positive-quadruple carrier -/

/-- The bounded carrier of positive quadruples `(a,b,x,y)` with
`a*x+b*y=n`.  The nested pair keeps the two factor occurrences `(a,b)` and
the two cofactor occurrences `(x,y)` separately addressed. -/
def huardPositiveQuadruples (n : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((((Finset.Icc 1 n).product (Finset.Icc 1 n)).product
      ((Finset.Icc 1 n).product (Finset.Icc 1 n))).filter
    fun q => q.1.1 * q.2.1 + q.1.2 * q.2.2 = n)

@[simp] theorem mem_huardPositiveQuadruples
    {n a b x y : ℕ} :
    ((a, b), (x, y)) ∈ huardPositiveQuadruples n ↔
      1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧
        1 ≤ x ∧ x ≤ n ∧ 1 ≤ y ∧ y ≤ n ∧
          a * x + b * y = n := by
  simp [huardPositiveQuadruples, and_assoc]

/-- The divisor boundary of the positive-quadruple carrier.  Its points are
`(d,t)` with `d | n` and `0<t<d`. -/
def huardBoundaryPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors.product (Finset.range n)).filter
    fun dt => 0 < dt.2 ∧ dt.2 < dt.1

/-- The three-term current obtained in the source after passing from `f` to
its oriented difference `g=f-f∘swap`. -/
def huardOrientedCurrent
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g q.1.1 (q.1.1 - q.1.2) (q.2.1 + q.2.2) q.2.2 +
    g (q.1.1 - q.1.2) q.1.1 q.2.2 (q.2.1 + q.2.2) +
    g q.1.1 q.1.2 q.2.1 (-q.2.2)

/-- The two affine-transport terms of the oriented current. -/
def huardAffinePair
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g q.1.1 (q.1.1 - q.1.2) (q.2.1 + q.2.2) q.2.2 +
    g (q.1.1 - q.1.2) q.1.1 q.2.2 (q.2.1 + q.2.2)

/-- The remaining crossing term of the oriented current. -/
def huardCrossingTerm
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g q.1.1 q.1.2 q.2.1 (-q.2.2)

theorem huardOrientedCurrent_eq_affine_add_crossing
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    huardOrientedCurrent g q = huardAffinePair g q + huardCrossingTerm g q := by
  rfl

def huardFactorLT (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (huardPositiveQuadruples n).filter fun q => q.1.1 < q.1.2

def huardFactorGT (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (huardPositiveQuadruples n).filter fun q => q.1.2 < q.1.1

def huardCofactorLT (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (huardPositiveQuadruples n).filter fun q => q.2.1 < q.2.2

def huardCofactorGT (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (huardPositiveQuadruples n).filter fun q => q.2.2 < q.2.1

/-- The common pair exposed after transporting an `a<b` occurrence through
`(a,b,x,y) ↦ (a,b-a,x+y,y)`. -/
def huardLTReindexedPair
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g (q.1.1 : ℤ) (-(q.1.2 : ℤ)) (q.2.1 : ℤ) (q.2.2 : ℤ) +
    g (-(q.1.2 : ℤ)) (q.1.1 : ℤ) (q.2.2 : ℤ) (q.2.1 : ℤ)

/-- The source's affine transport from the `a<b` face to the `x>y` face. -/
def huardLTTransport : ((ℕ × ℕ) × (ℕ × ℕ)) →
    ((ℕ × ℕ) × (ℕ × ℕ))
  | ((a, b), (x, y)) => ((a, b - a), (x + y, y))

/-- Its exact inverse on the positive `x>y` carrier. -/
def huardLTTransportInv : ((ℕ × ℕ) × (ℕ × ℕ)) →
    ((ℕ × ℕ) × (ℕ × ℕ))
  | ((a, b), (x, y)) => ((a, a + b), (x - y, y))

/-- Exact affine reindexing of the two `a<b` summands. -/
theorem huardAffinePair_factorLT_reindex
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) (n : ℕ) :
    (∑ q ∈ huardFactorLT n, huardAffinePair g q) =
      ∑ q ∈ huardCofactorGT n, huardLTReindexedPair g q := by
  apply Finset.sum_bij (fun q _hq => huardLTTransport q)
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [huardFactorLT, Finset.mem_filter] at hq
    change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ a < b at hq
    rcases hq with ⟨hquad, hab⟩
    rcases mem_huardPositiveQuadruples.mp hquad with
      ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
    rw [huardCofactorGT, Finset.mem_filter]
    change ((a, b - a), (x + y, y)) ∈ huardPositiveQuadruples n ∧
      y < x + y
    have hnewsum : a * (x + y) + (b - a) * y = n := by
      calc
        a * (x + y) + (b - a) * y =
            a * x + (a + (b - a)) * y := by ring
        _ = a * x + b * y := by rw [Nat.add_sub_of_le (Nat.le_of_lt hab)]
        _ = n := hsum
    have hxy_le : x + y ≤ n := by
      exact le_trans (Nat.le_mul_of_pos_left (x + y) ha1) (by omega)
    constructor
    · exact mem_huardPositiveQuadruples.mpr
        ⟨ha1, han, by omega, le_trans (Nat.sub_le b a) hbn,
          by omega, hxy_le, hy1, hyn, hnewsum⟩
    · omega
  · intro q₁ hq₁ q₂ hq₂ heq
    rcases q₁ with ⟨⟨a₁, b₁⟩, ⟨x₁, y₁⟩⟩
    rcases q₂ with ⟨⟨a₂, b₂⟩, ⟨x₂, y₂⟩⟩
    rw [huardFactorLT, Finset.mem_filter] at hq₁ hq₂
    change ((a₁, b₁), (x₁, y₁)) ∈ huardPositiveQuadruples n ∧ a₁ < b₁ at hq₁
    change ((a₂, b₂), (x₂, y₂)) ∈ huardPositiveQuadruples n ∧ a₂ < b₂ at hq₂
    change ((a₁, b₁ - a₁), (x₁ + y₁, y₁)) =
      ((a₂, b₂ - a₂), (x₂ + y₂, y₂)) at heq
    have ha : a₁ = a₂ := congrArg (fun q => q.1.1) heq
    have hbd : b₁ - a₁ = b₂ - a₂ := congrArg (fun q => q.1.2) heq
    have hxy : x₁ + y₁ = x₂ + y₂ := congrArg (fun q => q.2.1) heq
    have hy : y₁ = y₂ := congrArg (fun q => q.2.2) heq
    have hb : b₁ = b₂ := by omega
    have hx : x₁ = x₂ := by omega
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hx hy)
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [huardCofactorGT, Finset.mem_filter] at hq
    change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ y < x at hq
    rcases hq with ⟨hquad, hyx⟩
    rcases mem_huardPositiveQuadruples.mp hquad with
      ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
    refine ⟨huardLTTransportInv ((a, b), (x, y)), ?_, ?_⟩
    · rw [huardFactorLT, Finset.mem_filter]
      change ((a, a + b), (x - y, y)) ∈ huardPositiveQuadruples n ∧
        a < a + b
      have hnewsum : a * (x - y) + (a + b) * y = n := by
        calc
          a * (x - y) + (a + b) * y =
              a * ((x - y) + y) + b * y := by ring
          _ = a * x + b * y := by rw [Nat.sub_add_cancel (Nat.le_of_lt hyx)]
          _ = n := hsum
      have hab_le : a + b ≤ n := by
        exact le_trans (Nat.le_mul_of_pos_right (a + b) hy1) (by omega)
      constructor
      · exact mem_huardPositiveQuadruples.mpr
          ⟨ha1, han, by omega, hab_le, by omega,
            le_trans (Nat.sub_le x y) hxn, hy1, hyn, hnewsum⟩
      · omega
    · simp [huardLTTransport, huardLTTransportInv]
      exact Nat.sub_add_cancel (Nat.le_of_lt hyx)
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [huardFactorLT, Finset.mem_filter] at hq
    change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ a < b at hq
    have hab := hq.2
    simp only [huardAffinePair, huardLTReindexedPair, huardLTTransport]
    rw [Int.ofNat_sub (Nat.le_of_lt hab), Nat.cast_add]
    have hdiff : (a : ℤ) - (b : ℤ) = -((b : ℤ) - (a : ℤ)) := by ring
    rw [hdiff]

/-- Swap the factor pair with the cofactor pair. -/
def huardFullSwap : ((ℕ × ℕ) × (ℕ × ℕ)) →
    ((ℕ × ℕ) × (ℕ × ℕ))
  | (ab, xy) => (xy, ab)

/-- The crossing term after factor/cofactor swap. -/
def huardCommonCrossing
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g (q.2.1 : ℤ) (q.2.2 : ℤ) (q.1.1 : ℤ) (-(q.1.2 : ℤ))

theorem huardCrossing_factorLT_swap
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) (n : ℕ) :
    (∑ q ∈ huardFactorLT n, huardCrossingTerm g q) =
      ∑ q ∈ huardCofactorLT n, huardCommonCrossing g q := by
  apply Finset.sum_bij (fun q _hq => huardFullSwap q)
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [huardFactorLT, Finset.mem_filter] at hq
    change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ a < b at hq
    rcases hq with ⟨hquad, hab⟩
    rcases mem_huardPositiveQuadruples.mp hquad with
      ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
    rw [huardCofactorLT, Finset.mem_filter]
    change ((x, y), (a, b)) ∈ huardPositiveQuadruples n ∧ a < b
    constructor
    · apply mem_huardPositiveQuadruples.mpr
      exact ⟨hx1, hxn, hy1, hyn, ha1, han, hb1, hbn, by
        calc
          x * a + y * b = a * x + b * y := by ring
          _ = n := hsum⟩
    · exact hab
  · intro q₁ _hq₁ q₂ _hq₂ heq
    rcases q₁ with ⟨ab₁, xy₁⟩
    rcases q₂ with ⟨ab₂, xy₂⟩
    change (xy₁, ab₁) = (xy₂, ab₂) at heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro q hq
    refine ⟨huardFullSwap q, ?_, ?_⟩
    · rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
      rw [huardCofactorLT, Finset.mem_filter] at hq
      change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ x < y at hq
      rcases hq with ⟨hquad, hxy⟩
      rcases mem_huardPositiveQuadruples.mp hquad with
        ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
      rw [huardFactorLT, Finset.mem_filter]
      change ((x, y), (a, b)) ∈ huardPositiveQuadruples n ∧ x < y
      constructor
      · apply mem_huardPositiveQuadruples.mpr
        exact ⟨hx1, hxn, hy1, hyn, ha1, han, hb1, hbn, by
          calc
            x * a + y * b = a * x + b * y := by ring
            _ = n := hsum⟩
      · exact hxy
    · rcases q with ⟨ab, xy⟩
      rfl
  · intro q _hq
    rcases q with ⟨ab, xy⟩
    rfl

theorem huardCrossing_factorGT_swap
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) (n : ℕ) :
    (∑ q ∈ huardFactorGT n, huardCrossingTerm g q) =
      ∑ q ∈ huardCofactorGT n, huardCommonCrossing g q := by
  apply Finset.sum_bij (fun q _hq => huardFullSwap q)
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [huardFactorGT, Finset.mem_filter] at hq
    change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ b < a at hq
    rcases hq with ⟨hquad, hba⟩
    rcases mem_huardPositiveQuadruples.mp hquad with
      ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
    rw [huardCofactorGT, Finset.mem_filter]
    change ((x, y), (a, b)) ∈ huardPositiveQuadruples n ∧ b < a
    constructor
    · apply mem_huardPositiveQuadruples.mpr
      exact ⟨hx1, hxn, hy1, hyn, ha1, han, hb1, hbn, by
        calc
          x * a + y * b = a * x + b * y := by ring
          _ = n := hsum⟩
    · exact hba
  · intro q₁ _hq₁ q₂ _hq₂ heq
    rcases q₁ with ⟨ab₁, xy₁⟩
    rcases q₂ with ⟨ab₂, xy₂⟩
    change (xy₁, ab₁) = (xy₂, ab₂) at heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro q hq
    refine ⟨huardFullSwap q, ?_, ?_⟩
    · rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
      rw [huardCofactorGT, Finset.mem_filter] at hq
      change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ y < x at hq
      rcases hq with ⟨hquad, hyx⟩
      rcases mem_huardPositiveQuadruples.mp hquad with
        ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
      rw [huardFactorGT, Finset.mem_filter]
      change ((x, y), (a, b)) ∈ huardPositiveQuadruples n ∧ y < x
      constructor
      · apply mem_huardPositiveQuadruples.mpr
        exact ⟨hx1, hxn, hy1, hyn, ha1, han, hb1, hbn, by
          calc
            x * a + y * b = a * x + b * y := by ring
            _ = n := hsum⟩
      · exact hyx
    · rcases q with ⟨ab, xy⟩
      rfl
  · intro q _hq
    rcases q with ⟨ab, xy⟩
    rfl

/-- The first member of the reindexed affine pair. -/
def huardBaseTerm
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g (q.1.1 : ℤ) (-(q.1.2 : ℤ)) (q.2.1 : ℤ) (q.2.2 : ℤ)

/-- The second member of the reindexed affine pair. -/
def huardSecondTerm
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  g (-(q.1.2 : ℤ)) (q.1.1 : ℤ) (q.2.2 : ℤ) (q.2.1 : ℤ)

theorem huardLTReindexedPair_eq (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    huardLTReindexedPair g q = huardBaseTerm g q + huardSecondTerm g q := by
  rfl

/-- Exchange both ordered pairs.  This carries `x>y` to `x<y` while
preserving `a*x+b*y`. -/
def huardPairSwap : ((ℕ × ℕ) × (ℕ × ℕ)) →
    ((ℕ × ℕ) × (ℕ × ℕ))
  | ((a, b), (x, y)) => ((b, a), (y, x))

theorem huardSecond_cofactorGT_reindex
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hflip : ∀ a b x y : ℤ, g a (-b) x y = g (-a) b x y)
    (n : ℕ) :
    (∑ q ∈ huardCofactorGT n, huardSecondTerm g q) =
      ∑ q ∈ huardCofactorLT n, huardBaseTerm g q := by
  apply Finset.sum_bij (fun q _hq => huardPairSwap q)
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [huardCofactorGT, Finset.mem_filter] at hq
    change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ y < x at hq
    rcases hq with ⟨hquad, hyx⟩
    rcases mem_huardPositiveQuadruples.mp hquad with
      ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
    rw [huardCofactorLT, Finset.mem_filter]
    change ((b, a), (y, x)) ∈ huardPositiveQuadruples n ∧ y < x
    constructor
    · apply mem_huardPositiveQuadruples.mpr
      exact ⟨hb1, hbn, ha1, han, hy1, hyn, hx1, hxn, by
        calc
          b * y + a * x = a * x + b * y := by ring
          _ = n := hsum⟩
    · exact hyx
  · intro q₁ _hq₁ q₂ _hq₂ heq
    rcases q₁ with ⟨⟨a₁, b₁⟩, ⟨x₁, y₁⟩⟩
    rcases q₂ with ⟨⟨a₂, b₂⟩, ⟨x₂, y₂⟩⟩
    change ((b₁, a₁), (y₁, x₁)) = ((b₂, a₂), (y₂, x₂)) at heq
    have ha : a₁ = a₂ := congrArg (fun q => q.1.2) heq
    have hb : b₁ = b₂ := congrArg (fun q => q.1.1) heq
    have hx : x₁ = x₂ := congrArg (fun q => q.2.2) heq
    have hy : y₁ = y₂ := congrArg (fun q => q.2.1) heq
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hx hy)
  · intro q hq
    refine ⟨huardPairSwap q, ?_, ?_⟩
    · rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
      rw [huardCofactorLT, Finset.mem_filter] at hq
      change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ x < y at hq
      rcases hq with ⟨hquad, hxy⟩
      rcases mem_huardPositiveQuadruples.mp hquad with
        ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
      rw [huardCofactorGT, Finset.mem_filter]
      change ((b, a), (y, x)) ∈ huardPositiveQuadruples n ∧ x < y
      constructor
      · apply mem_huardPositiveQuadruples.mpr
        exact ⟨hb1, hbn, ha1, han, hy1, hyn, hx1, hxn, by
          calc
            b * y + a * x = a * x + b * y := by ring
            _ = n := hsum⟩
      · exact hxy
    · rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
      rfl
  · intro q _hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    simp only [huardSecondTerm, huardBaseTerm, huardPairSwap]
    exact (hflip (b : ℤ) (a : ℤ) (y : ℤ) (x : ℤ)).symm

/-- Swap antisymmetry turns the reindexed base term into the negative common
crossing term on every retained carrier. -/
theorem sum_huardBaseTerm_eq_neg_common
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hanti : ∀ a b x y : ℤ, g a b x y = -g x y a b)
    (s : Finset ((ℕ × ℕ) × (ℕ × ℕ))) :
    (∑ q ∈ s, huardBaseTerm g q) =
      -(∑ q ∈ s, huardCommonCrossing g q) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
  simp only [huardBaseTerm, huardCommonCrossing]
  exact hanti (a : ℤ) (-(b : ℤ)) (x : ℤ) (y : ℤ)

/-- The self-inverse affine turn on the `a>b` carrier. -/
def huardGTInvolution : ((ℕ × ℕ) × (ℕ × ℕ)) →
    ((ℕ × ℕ) × (ℕ × ℕ))
  | ((a, b), (x, y)) => ((x + y, x), (b, a - b))

/-- The two affine terms on the `a>b` face cancel under the source's exact
self-inverse turn. -/
theorem huardAffinePair_factorGT_zero
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hanti : ∀ a b x y : ℤ, g a b x y = -g x y a b)
    (n : ℕ) :
    (∑ q ∈ huardFactorGT n, huardAffinePair g q) = 0 := by
  let S := ∑ q ∈ huardFactorGT n, huardAffinePair g q
  have hneg : S = -S := by
    dsimp only [S]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_bij (fun q _hq => huardGTInvolution q)
    · intro q hq
      rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
      rw [huardFactorGT, Finset.mem_filter] at hq
      change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ b < a at hq
      rcases hq with ⟨hquad, hba⟩
      rcases mem_huardPositiveQuadruples.mp hquad with
        ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
      rw [huardFactorGT, Finset.mem_filter]
      change ((x + y, x), (b, a - b)) ∈ huardPositiveQuadruples n ∧
        x < x + y
      have hnewsum : (x + y) * b + x * (a - b) = n := by
        calc
          (x + y) * b + x * (a - b) =
              x * (b + (a - b)) + b * y := by ring
          _ = x * a + b * y := by rw [Nat.add_sub_of_le (Nat.le_of_lt hba)]
          _ = n := by simpa [mul_comm] using hsum
      have hxy_le : x + y ≤ n := by
        exact le_trans (Nat.le_mul_of_pos_right (x + y) hb1) (by omega)
      constructor
      · exact mem_huardPositiveQuadruples.mpr
          ⟨by omega, hxy_le, hx1, hxn, hb1, hbn, by omega,
            le_trans (Nat.sub_le a b) han, hnewsum⟩
      · omega
    · intro q₁ hq₁ q₂ hq₂ heq
      rcases q₁ with ⟨⟨a₁, b₁⟩, ⟨x₁, y₁⟩⟩
      rcases q₂ with ⟨⟨a₂, b₂⟩, ⟨x₂, y₂⟩⟩
      rw [huardFactorGT, Finset.mem_filter] at hq₁ hq₂
      change ((a₁, b₁), (x₁, y₁)) ∈ huardPositiveQuadruples n ∧ b₁ < a₁ at hq₁
      change ((a₂, b₂), (x₂, y₂)) ∈ huardPositiveQuadruples n ∧ b₂ < a₂ at hq₂
      change ((x₁ + y₁, x₁), (b₁, a₁ - b₁)) =
        ((x₂ + y₂, x₂), (b₂, a₂ - b₂)) at heq
      have hx : x₁ = x₂ := congrArg (fun q => q.1.2) heq
      have hxy : x₁ + y₁ = x₂ + y₂ := congrArg (fun q => q.1.1) heq
      have hb : b₁ = b₂ := congrArg (fun q => q.2.1) heq
      have had : a₁ - b₁ = a₂ - b₂ := congrArg (fun q => q.2.2) heq
      have hy : y₁ = y₂ := by omega
      have ha : a₁ = a₂ := by omega
      exact Prod.ext (Prod.ext ha hb) (Prod.ext hx hy)
    · intro q hq
      refine ⟨huardGTInvolution q, ?_, ?_⟩
      · rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
        rw [huardFactorGT, Finset.mem_filter] at hq
        change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ b < a at hq
        rcases hq with ⟨hquad, hba⟩
        rcases mem_huardPositiveQuadruples.mp hquad with
          ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
        rw [huardFactorGT, Finset.mem_filter]
        change ((x + y, x), (b, a - b)) ∈ huardPositiveQuadruples n ∧
          x < x + y
        have hnewsum : (x + y) * b + x * (a - b) = n := by
          calc
            (x + y) * b + x * (a - b) =
                x * (b + (a - b)) + b * y := by ring
            _ = x * a + b * y := by rw [Nat.add_sub_of_le (Nat.le_of_lt hba)]
            _ = n := by simpa [mul_comm] using hsum
        have hxy_le : x + y ≤ n := by
          exact le_trans (Nat.le_mul_of_pos_right (x + y) hb1) (by omega)
        constructor
        · exact mem_huardPositiveQuadruples.mpr
            ⟨by omega, hxy_le, hx1, hxn, hb1, hbn, by omega,
              le_trans (Nat.sub_le a b) han, hnewsum⟩
        · omega
      · rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
        rw [huardFactorGT, Finset.mem_filter] at hq
        change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ b < a at hq
        change ((b + (a - b), b), (x, (x + y) - x)) = ((a, b), (x, y))
        exact Prod.ext
          (Prod.ext (Nat.add_sub_of_le (Nat.le_of_lt hq.2)) rfl)
          (Prod.ext rfl (Nat.add_sub_cancel_left x y))
    · intro q hq
      rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
      rw [huardFactorGT, Finset.mem_filter] at hq
      change ((a, b), (x, y)) ∈ huardPositiveQuadruples n ∧ b < a at hq
      have hba := hq.2
      simp only [huardAffinePair, huardGTInvolution, Nat.cast_add,
        Int.ofNat_sub (Nat.le_of_lt hba)]
      have hxy : (x : ℤ) + (y : ℤ) - (x : ℤ) = (y : ℤ) := by ring
      have hab : (b : ℤ) + ((a : ℤ) - (b : ℤ)) = (a : ℤ) := by ring
      rw [hxy, hab]
      rw [hanti (a : ℤ) ((a : ℤ) - (b : ℤ))
          ((x : ℤ) + (y : ℤ)) (y : ℤ),
        hanti ((a : ℤ) - (b : ℤ)) (a : ℤ)
          (y : ℤ) ((x : ℤ) + (y : ℤ))]
      ring
  linarith

theorem huardOriented_factorLT_eq_neg_common
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hflip : ∀ a b x y : ℤ, g a (-b) x y = g (-a) b x y)
    (hanti : ∀ a b x y : ℤ, g a b x y = -g x y a b)
    (n : ℕ) :
    (∑ q ∈ huardFactorLT n, huardOrientedCurrent g q) =
      -(∑ q ∈ huardCofactorGT n, huardCommonCrossing g q) := by
  have hsplit :
      (∑ q ∈ huardFactorLT n, huardOrientedCurrent g q) =
        (∑ q ∈ huardFactorLT n, huardAffinePair g q) +
          ∑ q ∈ huardFactorLT n, huardCrossingTerm g q := by
    simp only [huardOrientedCurrent_eq_affine_add_crossing,
      Finset.sum_add_distrib]
  have haffine := huardAffinePair_factorLT_reindex g n
  have hreindexed :
      (∑ q ∈ huardCofactorGT n, huardLTReindexedPair g q) =
        (∑ q ∈ huardCofactorGT n, huardBaseTerm g q) +
          ∑ q ∈ huardCofactorGT n, huardSecondTerm g q := by
    simp only [huardLTReindexedPair_eq, Finset.sum_add_distrib]
  have hsecond := huardSecond_cofactorGT_reindex g hflip n
  have hbaseGT := sum_huardBaseTerm_eq_neg_common g hanti
    (huardCofactorGT n)
  have hbaseLT := sum_huardBaseTerm_eq_neg_common g hanti
    (huardCofactorLT n)
  have hcross := huardCrossing_factorLT_swap g n
  linarith

theorem huardOriented_factorGT_eq_common
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hanti : ∀ a b x y : ℤ, g a b x y = -g x y a b)
    (n : ℕ) :
    (∑ q ∈ huardFactorGT n, huardOrientedCurrent g q) =
      ∑ q ∈ huardCofactorGT n, huardCommonCrossing g q := by
  have hsplit :
      (∑ q ∈ huardFactorGT n, huardOrientedCurrent g q) =
        (∑ q ∈ huardFactorGT n, huardAffinePair g q) +
          ∑ q ∈ huardFactorGT n, huardCrossingTerm g q := by
    simp only [huardOrientedCurrent_eq_affine_add_crossing,
      Finset.sum_add_distrib]
  have haffine := huardAffinePair_factorGT_zero g hanti n
  have hcross := huardCrossing_factorGT_swap g n
  linarith

/-- The surviving divisor-boundary current in the oriented `g` chart. -/
def huardBoundaryCurrent
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) (n : ℕ) (dt : ℕ × ℕ) : ℤ :=
  g (↑(n / dt.1)) 0 (↑dt.1) (↑dt.2) +
    g 0 (↑(n / dt.1)) (↑dt.2) (↑dt.1) +
    g (↑(n / dt.1)) (↑(n / dt.1))
      ((dt.1 : ℤ) - (dt.2 : ℤ)) (-(dt.2 : ℤ))

/-- The diagonal `a=b` is not merely equinumerous with the source boundary:
the affine map `(a,a,x,y) ↦ (x+y,y)` transports every oriented summand to
the corresponding divisor-boundary summand. -/
theorem huardDiagonal_eq_boundary
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) {n : ℕ} (hn : 0 < n) :
    (∑ q ∈ (huardPositiveQuadruples n).filter (fun q => q.1.1 = q.1.2),
        huardOrientedCurrent g q) =
      ∑ dt ∈ huardBoundaryPairs n, huardBoundaryCurrent g n dt := by
  apply Finset.sum_bij (fun q _hq => (q.2.1 + q.2.2, q.2.2))
  · intro q hq
    rw [Finset.mem_filter] at hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rcases hq with ⟨hquad, hab⟩
    rw [huardPositiveQuadruples, Finset.mem_filter] at hquad
    rcases hquad with ⟨hbox, heq⟩
    change a = b at hab
    change a * x + b * y = n at heq
    have hxyBox := (Finset.mem_product.mp hbox).2
    have hxMem := (Finset.mem_product.mp hxyBox).1
    have hyMem := (Finset.mem_product.mp hxyBox).2
    change x ∈ Finset.Icc 1 n at hxMem
    change y ∈ Finset.Icc 1 n at hyMem
    have hxpos := (Finset.mem_Icc.mp hxMem).1
    have hypos := (Finset.mem_Icc.mp hyMem).1
    have hnform : a * (x + y) = n := by
      simpa [hab, mul_add] using heq
    have hdvd : x + y ∣ n := ⟨a, by simpa [mul_comm] using hnform.symm⟩
    have hdle : x + y ≤ n := Nat.le_of_dvd hn hdvd
    change (x + y, y) ∈ huardBoundaryPairs n
    rw [huardBoundaryPairs, Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt hn⟩,
          Finset.mem_range.mpr (by omega)⟩
    · omega
  · intro q₁ hq₁ q₂ hq₂ heq
    rcases q₁ with ⟨⟨a₁, b₁⟩, ⟨x₁, y₁⟩⟩
    rcases q₂ with ⟨⟨a₂, b₂⟩, ⟨x₂, y₂⟩⟩
    rw [Finset.mem_filter] at hq₁ hq₂
    rcases hq₁ with ⟨hquad₁, hab₁⟩
    rcases hq₂ with ⟨hquad₂, hab₂⟩
    rw [huardPositiveQuadruples, Finset.mem_filter] at hquad₁ hquad₂
    rcases hquad₁ with ⟨_hbox₁, hsum₁⟩
    rcases hquad₂ with ⟨_hbox₂, hsum₂⟩
    change a₁ = b₁ at hab₁
    change a₂ = b₂ at hab₂
    change a₁ * x₁ + b₁ * y₁ = n at hsum₁
    change a₂ * x₂ + b₂ * y₂ = n at hsum₂
    have hsumxy : x₁ + y₁ = x₂ + y₂ := congrArg Prod.fst heq
    have hy : y₁ = y₂ := congrArg Prod.snd heq
    have hxy : x₁ = x₂ := by omega
    have hform₁ : a₁ * (x₁ + y₁) = n := by
      simpa [hab₁, mul_add] using hsum₁
    have hform₂ : a₂ * (x₂ + y₂) = n := by
      simpa [hab₂, mul_add] using hsum₂
    have ha : a₁ = a₂ := by
      have hpos : 0 < x₁ + y₁ := by
        have hxyMem := (Finset.mem_product.mp _hbox₁).2
        have hxMem := (Finset.mem_product.mp hxyMem).1
        change x₁ ∈ Finset.Icc 1 n at hxMem
        exact lt_of_lt_of_le (Finset.mem_Icc.mp hxMem).1 (Nat.le_add_right x₁ y₁)
      apply Nat.eq_of_mul_eq_mul_right hpos
      simpa [hxy, hy] using hform₁.trans hform₂.symm
    have hb : b₁ = b₂ := hab₁.symm.trans (ha.trans hab₂)
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hxy hy)
  · intro dt hdt
    rcases dt with ⟨d, t⟩
    change (d, t) ∈ huardBoundaryPairs n at hdt
    rw [huardBoundaryPairs, Finset.mem_filter] at hdt
    rcases hdt with ⟨hbase, htpos, htd⟩
    rcases Finset.mem_product.mp hbase with ⟨hdmem, htn⟩
    rcases Nat.mem_divisors.mp hdmem with ⟨hdvd, hnne⟩
    have htn' : t < n := Finset.mem_range.mp htn
    change 0 < t at htpos
    change t < d at htd
    have hdpos : 0 < d := lt_trans htpos htd
    have hdle : d ≤ n := Nat.le_of_dvd hn hdvd
    have hquotpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hquotle : n / d ≤ n := Nat.div_le_self n d
    let q : (ℕ × ℕ) × (ℕ × ℕ) :=
      ((n / d, n / d), (d - t, t))
    refine ⟨q, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [huardPositiveQuadruples, Finset.mem_filter]
        constructor
        · have habMem : (n / d, n / d) ∈
              (Finset.Icc 1 n).product (Finset.Icc 1 n) :=
            Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨hquotpos, hquotle⟩,
                Finset.mem_Icc.mpr ⟨hquotpos, hquotle⟩⟩
          have hxyMem : (d - t, t) ∈
              (Finset.Icc 1 n).product (Finset.Icc 1 n) :=
            Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
                Finset.mem_Icc.mpr ⟨htpos, by omega⟩⟩
          simpa only [q] using Finset.mem_product.mpr ⟨habMem, hxyMem⟩
        · change n / d * (d - t) + n / d * t = n
          have hmul : n / d * d = n := Nat.div_mul_cancel hdvd
          calc
            n / d * (d - t) + n / d * t = n / d * ((d - t) + t) := by
              rw [mul_add]
            _ = n / d * d := by rw [Nat.sub_add_cancel (Nat.le_of_lt htd)]
            _ = n := hmul
      · rfl
    · change (d - t + t, t) = (d, t)
      exact Prod.ext (Nat.sub_add_cancel (Nat.le_of_lt htd)) rfl
  · intro q hq
    rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
    rw [Finset.mem_filter] at hq
    rcases hq with ⟨hquad, hab⟩
    rw [huardPositiveQuadruples, Finset.mem_filter] at hquad
    rcases hquad with ⟨hbox, heq⟩
    change a = b at hab
    change a * x + b * y = n at heq
    have hxyMem := (Finset.mem_product.mp hbox).2
    have hxMem := (Finset.mem_product.mp hxyMem).1
    have hyMem := (Finset.mem_product.mp hxyMem).2
    change x ∈ Finset.Icc 1 n at hxMem
    change y ∈ Finset.Icc 1 n at hyMem
    have hnform : a * (x + y) = n := by
      simpa [hab, mul_add] using heq
    have hdvd : x + y ∣ n := ⟨a, by simpa [mul_comm] using hnform.symm⟩
    have hquot : n / (x + y) = a := by
      rw [← hnform]
      exact Nat.mul_div_cancel a (by
        have hxpos := (Finset.mem_Icc.mp hxMem).1
        have hypos := (Finset.mem_Icc.mp hyMem).1
        omega)
    simp [huardOrientedCurrent, huardBoundaryCurrent, hab, hquot]

/-- The only unmatched occurrence population after the diagonal carrier has
returned.  The two displayed laws are precisely the source's
`g(a,-b,x,y)=g(-a,b,x,y)` and swap antisymmetry. -/
def HuardOffDiagonalCancellation : Prop :=
  ∀ g : ℤ → ℤ → ℤ → ℤ → ℤ,
    (∀ a b x y : ℤ, g a (-b) x y = g (-a) b x y) →
    (∀ a b x y : ℤ, g a b x y = -g x y a b) →
    ∀ n : ℕ, 0 < n →
      (∑ q ∈ (huardPositiveQuadruples n).filter
          (fun q => ¬ q.1.1 = q.1.2), huardOrientedCurrent g q) = 0

theorem huardOffDiagonal_sum_partition
    (g : ℤ → ℤ → ℤ → ℤ → ℤ) (n : ℕ) :
    (∑ q ∈ (huardPositiveQuadruples n).filter
        (fun q => ¬ q.1.1 = q.1.2), huardOrientedCurrent g q) =
      (∑ q ∈ huardFactorLT n, huardOrientedCurrent g q) +
        ∑ q ∈ huardFactorGT n, huardOrientedCurrent g q := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((huardPositiveQuadruples n).filter (fun q => ¬ q.1.1 = q.1.2))
    (fun q => q.1.1 < q.1.2) (huardOrientedCurrent g)
  have hlt :
      ((huardPositiveQuadruples n).filter
        (fun q => ¬ q.1.1 = q.1.2)).filter
          (fun q => q.1.1 < q.1.2) = huardFactorLT n := by
    rw [huardFactorLT]
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, _hne⟩, hlt⟩
      exact ⟨hq, hlt⟩
    · rintro ⟨hq, hlt⟩
      exact ⟨⟨hq, Nat.ne_of_lt hlt⟩, hlt⟩
  have hgt :
      ((huardPositiveQuadruples n).filter
        (fun q => ¬ q.1.1 = q.1.2)).filter
          (fun q => ¬ q.1.1 < q.1.2) = huardFactorGT n := by
    rw [huardFactorGT]
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, hne⟩, hnlt⟩
      refine ⟨hq, ?_⟩
      omega
    · rintro ⟨hq, hgt⟩
      refine ⟨⟨hq, ?_⟩, ?_⟩ <;> omega
  rw [hlt, hgt] at hsplit
  exact hsplit.symm

/-- **OFF-DIAGONAL RETURN.**  The two oriented source faces cancel exactly;
no cardinality or coefficient test replaces the affine occurrence maps. -/
theorem huardOffDiagonalCancellation_proved :
    HuardOffDiagonalCancellation := by
  intro g hflip hanti n _hn
  rw [huardOffDiagonal_sum_partition]
  have hlt := huardOriented_factorLT_eq_neg_common g hflip hanti n
  have hgt := huardOriented_factorGT_eq_common g hanti n
  linarith

/-- Once the off-diagonal involutions are supplied, the already checked
diagonal bijection closes the complete oriented form of HOSW Theorem 1. -/
theorem huardOrientedTheoremOne_of_offDiagonal
    (hoff : HuardOffDiagonalCancellation)
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hflip : ∀ a b x y : ℤ, g a (-b) x y = g (-a) b x y)
    (hanti : ∀ a b x y : ℤ, g a b x y = -g x y a b)
    {n : ℕ} (hn : 0 < n) :
    (∑ q ∈ huardPositiveQuadruples n, huardOrientedCurrent g q) =
      ∑ dt ∈ huardBoundaryPairs n, huardBoundaryCurrent g n dt := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (huardPositiveQuadruples n) (fun q => q.1.1 = q.1.2)
    (huardOrientedCurrent g)
  have hdiag := huardDiagonal_eq_boundary g hn
  have hcancel := hoff g hflip hanti n hn
  linarith

/-- The complete oriented HOSW Theorem 1, with both off-diagonal
involutions and the divisor boundary now internal Lean theorems. -/
theorem huardOrientedTheoremOne
    (g : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hflip : ∀ a b x y : ℤ, g a (-b) x y = g (-a) b x y)
    (hanti : ∀ a b x y : ℤ, g a b x y = -g x y a b)
    {n : ℕ} (hn : 0 < n) :
    (∑ q ∈ huardPositiveQuadruples n, huardOrientedCurrent g q) =
      ∑ dt ∈ huardBoundaryPairs n, huardBoundaryCurrent g n dt := by
  exact huardOrientedTheoremOne_of_offDiagonal
    huardOffDiagonalCancellation_proved g hflip hanti hn

/-- The additive divisor convolution at scale `k`. -/
def scaledDivisorConvolution (k n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range n,
    ordinaryDivisorCurrent m * ordinaryDivisorCurrent (n - k * m)

/-- The positive-factor carrier with `x ≡ y (mod k)`, where `m = ax` and
`n-m = by`. -/
def huardPlusCurrent (k n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range n,
    ∑ a ∈ m.divisors,
      ∑ b ∈ (n - m).divisors,
        if (m / a) % k = ((n - m) / b) % k then
          (a : ℤ) * (b : ℤ)
        else 0

/-- The positive-factor carrier with `x ≡ -y (mod k)`. -/
def huardMinusCurrent (k n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range n,
    ∑ a ∈ m.divisors,
      ∑ b ∈ (n - m).divisors,
        if ((m / a) + (n - m) / b) % k = 0 then
          (a : ℤ) * (b : ℤ)
        else 0

theorem scaledDivisorConvolution_one (n : ℕ) :
    scaledDivisorConvolution 1 n = ordinaryDivisorConvolution n := by
  simp [scaledDivisorConvolution, ordinaryDivisorConvolution]

theorem scaledDivisorConvolution_two (n : ℕ) :
    scaledDivisorConvolution 2 n = doubledDivisorConvolution n := by
  rfl

/-- At modulus one both congruence receivers retain the complete level-one
convolution population. -/
theorem huardPlusCurrent_one (n : ℕ) :
    huardPlusCurrent 1 n = ordinaryDivisorConvolution n := by
  rw [huardPlusCurrent, ordinaryDivisorConvolution]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Nat.mod_one, ↓reduceIte]
  rw [ordinaryDivisorCurrent, ordinaryDivisorCurrent,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

theorem huardMinusCurrent_one (n : ℕ) :
    huardMinusCurrent 1 n = ordinaryDivisorConvolution n := by
  rw [huardMinusCurrent, ordinaryDivisorConvolution]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Nat.mod_one, ↓reduceIte]
  rw [ordinaryDivisorCurrent, ordinaryDivisorCurrent,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

/-- Modulo two, `x-y` and `x+y` have the same parity. -/
theorem huardMinusCurrent_two_eq_plus (n : ℕ) :
    huardMinusCurrent 2 n = huardPlusCurrent 2 n := by
  rw [huardMinusCurrent, huardPlusCurrent]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hparity :
      (((m / a) + (n - m) / b) % 2 = 0) ↔
        ((m / a) % 2 = ((n - m) / b) % 2) := by
    omega
  by_cases h : ((m / a) + (n - m) / b) % 2 = 0
  · rw [if_pos h, if_pos (hparity.mp h)]
  · rw [if_neg h, if_neg (fun hp => h (hparity.mpr hp))]

/-- Cleared-denominator form of Lemma 1 / equation (4.3) in the source.
The half-address divisor currents are present only when the address is
exactly divisible by the scale. -/
def HuardLemmaOneCleared : Prop :=
  ∀ k n : ℕ, 0 < k → 0 < n →
    24 * scaledDivisorConvolution k n =
      -cubicDivisorCurrent n + ordinaryDivisorCurrent n +
        (if k ∣ n then
          6 * cubicDivisorCurrent (n / k) -
            6 * (n : ℤ) * ordinaryDivisorCurrent (n / k)
        else 0) +
        6 * huardMinusCurrent k n + 6 * huardPlusCurrent k n

/-- The exact parity partition used on page 19 of the source.  It says that
the same-parity factor carrier is the total carrier, minus the two one-even
faces, plus twice their intersection. -/
def HuardParityReindexing : Prop :=
  ∀ n : ℕ,
    2 * huardPlusCurrent 2 n =
      (if 2 ∣ n then 4 * ordinaryDivisorConvolution (n / 2) else 0) +
        2 * ordinaryDivisorConvolution n -
        4 * doubledDivisorConvolution n

/-- The complete finite source obligation, separated from every downstream
Euler-current and theta reconstruction theorem. -/
def HuardOuSpearmanWilliamsFiniteSource : Prop :=
  HuardLemmaOneCleared ∧ HuardParityReindexing

/-- The modulus-one instance of the Huard identity is exactly the Besge
level-one convolution law. -/
theorem ordinaryDivisorConvolution_formula_of_huard
    (hhuard : HuardLemmaOneCleared) {n : ℕ} (hn : 0 < n) :
    12 * ordinaryDivisorConvolution n =
      5 * cubicDivisorCurrent n +
        (1 - 6 * (n : ℤ)) * ordinaryDivisorCurrent n := by
  have h := hhuard 1 n (by decide) hn
  rw [scaledDivisorConvolution_one, huardMinusCurrent_one,
    huardPlusCurrent_one, if_pos (one_dvd n), Nat.div_one] at h
  ring_nf at h ⊢
  linarith

/-- The modulus-two Huard instance, before the parity carrier is folded. -/
theorem doubledDivisorConvolution_formula_before_parity
    (hhuard : HuardLemmaOneCleared) {n : ℕ} (hn : 0 < n) :
    24 * doubledDivisorConvolution n =
      -cubicDivisorCurrent n + ordinaryDivisorCurrent n +
        (if 2 ∣ n then
          6 * cubicDivisorCurrent (n / 2) -
            6 * (n : ℤ) * ordinaryDivisorCurrent (n / 2)
        else 0) +
        12 * huardPlusCurrent 2 n := by
  have h := hhuard 2 n (by decide) hn
  rw [scaledDivisorConvolution_two,
    huardMinusCurrent_two_eq_plus] at h
  linarith

/-- **HUARD LEVEL-TWO RETURN.**  The two finite source identities imply the
uniform level-two divisor convolution formula, including the exact zero
address. -/
theorem doubledDivisorConvolutionFormula_of_finiteSource
    (hsource : HuardOuSpearmanWilliamsFiniteSource) :
    DoubledDivisorConvolutionFormula := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [doubledDivisorConvolution, cubicDivisorCurrent,
      ordinaryDivisorCurrent]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have htwo :=
    doubledDivisorConvolution_formula_before_parity hsource.1 hnpos
  have hparity := hsource.2 n
  have hone := ordinaryDivisorConvolution_formula_of_huard hsource.1 hnpos
  by_cases heven : 2 ∣ n
  · have hhalfpos : 0 < n / 2 :=
      Nat.div_pos (Nat.le_of_dvd hnpos heven) (by decide)
    have hhalf :=
      ordinaryDivisorConvolution_formula_of_huard hsource.1 hhalfpos
    simp only [if_pos heven] at htwo hparity ⊢
    have hcastHalf : ((n / 2 : ℕ) : ℤ) * 2 = (n : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel heven
    rw [← hcastHalf] at htwo hone ⊢
    ring_nf at htwo hparity hone hhalf ⊢
    linarith
  · simp only [if_neg heven] at htwo hparity ⊢
    ring_nf at htwo hparity hone ⊢
    linarith

/-- Once the finite source carrier is closed, every previously checked
Jacobi consequence fires without another hypothesis. -/
theorem totalShellDivisorLaw_of_finiteSource
    (hsource : HuardOuSpearmanWilliamsFiniteSource) :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  exact totalShellDivisorLaw_of_doubled
    (doubledDivisorConvolutionFormula_of_finiteSource hsource)

#print axioms huardMinusCurrent_two_eq_plus
#print axioms huardDiagonal_eq_boundary
#print axioms huardOffDiagonalCancellation_proved
#print axioms huardOrientedTheoremOne_of_offDiagonal
#print axioms huardOrientedTheoremOne
#print axioms ordinaryDivisorConvolution_formula_of_huard
#print axioms doubledDivisorConvolutionFormula_of_finiteSource
#print axioms totalShellDivisorLaw_of_finiteSource

end Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource
