import ElementaryHolonics.Mathematics.CopsonDeBruijnFiniteRecurrence

/-!
# The admissible real Copson--de Bruijn recurrence

The principal real square root is totalized by Mathlib outside its analytic domain.  This owner
therefore distinguishes the raw recurrence from an admissible dependent carrier whose every
iterate carries the proof that it is at least one.  A failed proof returns an explicit finite or
first obstruction; it is not silently continued through a negative radicand.

The bridge to `infiniteSharpBoundary` composes the finite variational recurrence, strict parameter
transport, one explicit globally admissible coefficient, and the least-upper-bound theorem. None
of those conclusions is stored as a field of this carrier.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set
open scoped NNReal ENNReal

/-! ## Raw values and the dependent admissible carrier -/

/-- The raw principal-square-root recurrence, with zero-based Lean indexing. -/
def realRecurrenceValue (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      x / Real.sqrt (n + 2) + Real.sqrt (realRecurrenceValue x n ^ 2 - 1)

@[simp] theorem realRecurrenceValue_zero (x : ℝ) :
    realRecurrenceValue x 0 = x := rfl

@[simp] theorem realRecurrenceValue_succ (x : ℝ) (n : ℕ) :
    realRecurrenceValue x (n + 1) =
      x / Real.sqrt (n + 2) + Real.sqrt (realRecurrenceValue x n ^ 2 - 1) := rfl

/--
An admissible recurrence returns each iterate in the closed ray `[1, ∞)`.  Its step equation uses
the principal real square root; nonnegativity of every radicand is derived below.
-/
structure AdmissibleRealRecurrence (x : ℝ) where
  iterate : (n : ℕ) → Set.Ici (1 : ℝ)
  initial : (iterate 0).1 = x
  step : ∀ n,
    (iterate (n + 1)).1 =
      x / Real.sqrt (n + 2) + Real.sqrt ((iterate n).1 ^ 2 - 1)

namespace AdmissibleRealRecurrence

/-- Admissibility makes every next square-root radicand nonnegative. -/
theorem radicand_nonnegative {x : ℝ} (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    0 ≤ (recurrence.iterate n).1 ^ 2 - 1 := by
  have hone := (recurrence.iterate n).2
  change 1 ≤ (recurrence.iterate n).1 at hone
  have hsquare : (1 : ℝ) ^ 2 ≤ (recurrence.iterate n).1 ^ 2 :=
    pow_le_pow_left₀ zero_le_one hone 2
  nlinarith

/-- The square root used at every admitted step is the nonnegative principal branch. -/
theorem principalSqrt_nonnegative {x : ℝ} (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    0 ≤ Real.sqrt ((recurrence.iterate n).1 ^ 2 - 1) :=
  Real.sqrt_nonneg _

/-- Every dependent admitted recurrence agrees with the deterministic raw recurrence. -/
theorem iterate_eq_realRecurrenceValue {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    (recurrence.iterate n).1 = realRecurrenceValue x n := by
  induction n with
  | zero => exact recurrence.initial
  | succ n ih =>
      rw [recurrence.step, realRecurrenceValue_succ, ih]

/-- A proof that all raw values are admitted constructs the dependent carrier. -/
def ofRaw (x : ℝ) (admissible : ∀ n, 1 ≤ realRecurrenceValue x n) :
    AdmissibleRealRecurrence x where
  iterate n := ⟨realRecurrenceValue x n, admissible n⟩
  initial := rfl
  step _ := rfl

end AdmissibleRealRecurrence

/-- A finite prefix is admissible through and including index `N`. -/
def FiniteRecurrenceAdmissible (x : ℝ) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → 1 ≤ realRecurrenceValue x n

/-- The raw recurrence first fails its admissible ray at index `N`. -/
def FirstRecurrenceObstruction (x : ℝ) (N : ℕ) : Prop :=
  realRecurrenceValue x N < 1 ∧ ∀ n, n < N → 1 ≤ realRecurrenceValue x n

/-- Some finite index is an explicit obstruction to an infinite dependent carrier. -/
def HasRecurrenceObstruction (x : ℝ) : Prop :=
  ∃ n, realRecurrenceValue x n < 1

/-- Failure of a finite prefix is witnessed by an obstructed index inside that prefix. -/
theorem not_finiteRecurrenceAdmissible_iff_exists_obstruction_le (x : ℝ) (N : ℕ) :
    ¬FiniteRecurrenceAdmissible x N ↔
      ∃ n, n ≤ N ∧ realRecurrenceValue x n < 1 := by
  simp only [FiniteRecurrenceAdmissible, not_forall]
  constructor
  · rintro ⟨n, hnN, hn⟩
    exact ⟨n, hnN, lt_of_not_ge hn⟩
  · rintro ⟨n, hnN, hn⟩
    exact ⟨n, hnN, not_le.mpr hn⟩

/-- Every obstruction has a least, hence first, obstructed index. -/
theorem exists_firstRecurrenceObstruction {x : ℝ} (obstruction : HasRecurrenceObstruction x) :
    ∃ N, FirstRecurrenceObstruction x N := by
  let N := Nat.find obstruction
  refine ⟨N, Nat.find_spec obstruction, ?_⟩
  intro n hn
  exact not_lt.mp (Nat.find_min obstruction hn)

/-- Infinite admissibility is exactly admissibility of every finite prefix. -/
theorem nonempty_admissibleRealRecurrence_iff_all_finite (x : ℝ) :
    Nonempty (AdmissibleRealRecurrence x) ↔
      ∀ N, FiniteRecurrenceAdmissible x N := by
  constructor
  · rintro ⟨recurrence⟩ N n _hn
    rw [← recurrence.iterate_eq_realRecurrenceValue n]
    exact (recurrence.iterate n).2
  · intro hall
    exact ⟨AdmissibleRealRecurrence.ofRaw x (fun n ↦ hall n n le_rfl)⟩

/-- Failure of the dependent carrier is witnessed at a finite iterate. -/
theorem not_nonempty_admissibleRealRecurrence_iff_obstruction (x : ℝ) :
    ¬Nonempty (AdmissibleRealRecurrence x) ↔ HasRecurrenceObstruction x := by
  rw [nonempty_admissibleRealRecurrence_iff_all_finite]
  simp only [HasRecurrenceObstruction, FiniteRecurrenceAdmissible, not_forall]
  constructor
  · rintro ⟨N, n, _hn, hn⟩
    exact ⟨n, lt_of_not_ge hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, n, le_rfl, not_le.mpr hn⟩

/-- A longer finite admissible prefix restricts to every shorter prefix. -/
theorem finiteRecurrenceAdmissible_anti {x : ℝ} {N M : ℕ} (hNM : N ≤ M)
    (admissible : FiniteRecurrenceAdmissible x M) : FiniteRecurrenceAdmissible x N :=
  fun n hn ↦ admissible n (hn.trans hNM)

/-! ## Monotonicity in the coefficient -/

/-- Raw recurrence values increase with the coefficient above an admitted lower recurrence. -/
theorem realRecurrenceValue_mono_of_admissible {x y : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (hxy : x ≤ y) (n : ℕ) :
    realRecurrenceValue x n ≤ realRecurrenceValue y n := by
  induction n with
  | zero => simpa using hxy
  | succ n ih =>
      rw [realRecurrenceValue_succ, realRecurrenceValue_succ]
      have hxone : 1 ≤ realRecurrenceValue x n := by
        rw [← recurrence.iterate_eq_realRecurrenceValue n]
        exact (recurrence.iterate n).2
      have hxnonneg : 0 ≤ realRecurrenceValue x n := zero_le_one.trans hxone
      have hynonneg : 0 ≤ realRecurrenceValue y n := hxnonneg.trans ih
      have hsquare : realRecurrenceValue x n ^ 2 - 1 ≤
          realRecurrenceValue y n ^ 2 - 1 := by
        nlinarith
      have hsqrt := Real.sqrt_le_sqrt hsquare
      have hdenom : 0 ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_nonneg _
      exact add_le_add (div_le_div_of_nonneg_right hxy hdenom) hsqrt

/-- The same upper-set law holds on any declared finite admissible prefix. -/
theorem realRecurrenceValue_mono_of_finite_admissible {x y : ℝ} {N : ℕ}
    (admissible : FiniteRecurrenceAdmissible x N) (hxy : x ≤ y)
    {n : ℕ} (hn : n ≤ N) :
    realRecurrenceValue x n ≤ realRecurrenceValue y n := by
  induction n with
  | zero => simpa using hxy
  | succ n ih =>
      rw [realRecurrenceValue_succ, realRecurrenceValue_succ]
      have hnN : n ≤ N := (Nat.le_succ n).trans hn
      have hxone := admissible n hnN
      have hprev := ih hnN
      have hxnonneg : 0 ≤ realRecurrenceValue x n := zero_le_one.trans hxone
      have hynonneg : 0 ≤ realRecurrenceValue y n := hxnonneg.trans hprev
      have hsquare : realRecurrenceValue x n ^ 2 - 1 ≤
          realRecurrenceValue y n ^ 2 - 1 := by
        nlinarith
      have hsqrt := Real.sqrt_le_sqrt hsquare
      have hdenom : 0 ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_nonneg _
      exact add_le_add (div_le_div_of_nonneg_right hxy hdenom) hsqrt

/-- Every finite admissible set is upper closed in its real coefficient. -/
theorem FiniteRecurrenceAdmissible.mono {x y : ℝ} {N : ℕ}
    (admissible : FiniteRecurrenceAdmissible x N) (hxy : x ≤ y) :
    FiniteRecurrenceAdmissible y N :=
  fun n hn ↦ (admissible n hn).trans
    (realRecurrenceValue_mono_of_finite_admissible admissible hxy hn)

/-- Admissible coefficients form an upper set. -/
def AdmissibleRealRecurrence.raise {x y : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (hxy : x ≤ y) :
    AdmissibleRealRecurrence y :=
  AdmissibleRealRecurrence.ofRaw y (fun n ↦ by
      have hxone : 1 ≤ realRecurrenceValue x n := by
        rw [← recurrence.iterate_eq_realRecurrenceValue n]
        exact (recurrence.iterate n).2
      exact hxone.trans (realRecurrenceValue_mono_of_admissible recurrence hxy n))

/-! ## The attained finite recurrence and strict parameter separation -/

/-- The raw recurrence at the attained coefficient is the variational recurrence at every slot. -/
theorem realRecurrenceValue_finiteSharpCoefficient_eq_finiteRecurrenceValue
    (N : ℕ) (i : Fin (N + 1)) :
    realRecurrenceValue (finiteSharpCoefficient N : ℝ) i.val =
      finiteRecurrenceValue N i := by
  induction i using Fin.induction with
  | zero => simpa using (finiteRecurrenceValue_initial N).symm
  | succ i ih =>
      change realRecurrenceValue (finiteSharpCoefficient N : ℝ) (i.val + 1) =
        finiteRecurrenceValue N i.succ
      rw [realRecurrenceValue_succ]
      rw [show realRecurrenceValue (finiteSharpCoefficient N : ℝ) i.val =
        finiteRecurrenceValue N i.castSucc by simpa using ih]
      rw [finiteRecurrenceValue_step]

/-- Every attained finite sharp coefficient is recurrence-admissible through its terminal slot. -/
theorem finiteSharpCoefficient_finiteRecurrenceAdmissible (N : ℕ) :
    FiniteRecurrenceAdmissible (finiteSharpCoefficient N : ℝ) N := by
  intro n hn
  let i : Fin (N + 1) := ⟨n, Nat.lt_succ_iff.mpr hn⟩
  rw [realRecurrenceValue_finiteSharpCoefficient_eq_finiteRecurrenceValue N i]
  exact finiteRecurrenceValue_one_le N i

/-- Raw recurrence values are strictly increasing on a finite admitted lower recurrence. -/
theorem realRecurrenceValue_strictMono_of_finite_admissible {x y : ℝ} {N : ℕ}
    (admissible : FiniteRecurrenceAdmissible x N) (hxy : x < y)
    {n : ℕ} (hn : n ≤ N) :
    realRecurrenceValue x n < realRecurrenceValue y n := by
  induction n with
  | zero => simpa using hxy
  | succ n ih =>
      rw [realRecurrenceValue_succ, realRecurrenceValue_succ]
      have hnN : n ≤ N := (Nat.le_succ n).trans hn
      have hxone := admissible n hnN
      have hprev := ih hnN
      have hxnonneg : 0 ≤ realRecurrenceValue x n := zero_le_one.trans hxone
      have hynonneg : 0 ≤ realRecurrenceValue y n := hxnonneg.trans hprev.le
      have hsquare : realRecurrenceValue x n ^ 2 - 1 <
          realRecurrenceValue y n ^ 2 - 1 := by
        have := (sq_lt_sq₀ hxnonneg hynonneg).2 hprev
        linarith
      have hradicand : 0 ≤ realRecurrenceValue x n ^ 2 - 1 := by
        have hsquareOne : (1 : ℝ) ^ 2 ≤ realRecurrenceValue x n ^ 2 :=
          pow_le_pow_left₀ zero_le_one hxone 2
        nlinarith
      have hsqrt := Real.sqrt_lt_sqrt hradicand hsquare
      have hdenom : 0 < Real.sqrt ((n : ℝ) + 2) := by positivity
      exact add_lt_add (div_lt_div_of_pos_right hxy hdenom) hsqrt

/-- No coefficient below the attained finite sharp coefficient can remain admissible to the end. -/
theorem finiteSharpCoefficient_le_of_finiteRecurrenceAdmissible
    (N : ℕ) {x : ℝ} (admissible : FiniteRecurrenceAdmissible x N) :
    (finiteSharpCoefficient N : ℝ) ≤ x := by
  apply le_of_not_gt
  intro hx
  have hterminal := realRecurrenceValue_strictMono_of_finite_admissible admissible hx
    (n := N) le_rfl
  let last : Fin (N + 1) := Fin.last N
  have hsharpTerminal :
      realRecurrenceValue (finiteSharpCoefficient N : ℝ) N = 1 := by
    calc
      realRecurrenceValue (finiteSharpCoefficient N : ℝ) N =
          finiteRecurrenceValue N last := by
            exact realRecurrenceValue_finiteSharpCoefficient_eq_finiteRecurrenceValue N last
      _ = 1 := finiteRecurrenceValue_terminal N
  rw [hsharpTerminal] at hterminal
  exact (not_lt_of_ge (admissible N le_rfl)) hterminal

/-- Finite admissibility is exactly the upper ray founded by the attained coefficient. -/
theorem finiteRecurrenceAdmissible_iff_finiteSharpCoefficient_le (x : ℝ) (N : ℕ) :
    FiniteRecurrenceAdmissible x N ↔ (finiteSharpCoefficient N : ℝ) ≤ x := by
  constructor
  · exact finiteSharpCoefficient_le_of_finiteRecurrenceAdmissible N
  · intro h
    exact (finiteSharpCoefficient_finiteRecurrenceAdmissible N).mono h

/-- A real recurrence is globally admissible exactly when it bounds every finite coefficient. -/
theorem nonempty_admissibleRealRecurrence_iff_all_finiteSharpCoefficient_le (x : ℝ) :
    Nonempty (AdmissibleRealRecurrence x) ↔
      ∀ N, (finiteSharpCoefficient N : ℝ) ≤ x := by
  rw [nonempty_admissibleRealRecurrence_iff_all_finite]
  exact forall_congr' fun N ↦ finiteRecurrenceAdmissible_iff_finiteSharpCoefficient_le x N

/-- For a nonnegative real coefficient, global admissibility is the infinite-boundary upper ray. -/
theorem nonempty_admissibleRealRecurrence_iff_infiniteSharpBoundary_le_ofReal
    {x : ℝ} (hx : 0 ≤ x) :
    Nonempty (AdmissibleRealRecurrence x) ↔
      infiniteSharpBoundary ≤ ENNReal.ofReal x := by
  rw [nonempty_admissibleRealRecurrence_iff_all_finiteSharpCoefficient_le]
  constructor
  · intro hall
    rw [infiniteSharpBoundary]
    refine iSup_le fun N ↦ ?_
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hx]
    exact hall N
  · intro hboundary N
    have hN : (finiteSharpCoefficient N : ℝ≥0∞) ≤ ENNReal.ofReal x :=
      (coe_finiteSharpCoefficient_le_infiniteSharpBoundary N).trans hboundary
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hx] at hN
    exact hN

/-! ## A concrete global upper coefficient -/

/-- The elementary square-root estimate which sustains the coefficient-two invariant. -/
theorem sqrt_nat_add_two_le_two_div_sqrt_add_sqrt_nat (n : ℕ) :
    Real.sqrt ((n : ℝ) + 2) ≤
      2 / Real.sqrt ((n : ℝ) + 2) + Real.sqrt (n : ℝ) := by
  let a := Real.sqrt ((n : ℝ) + 2)
  let b := Real.sqrt (n : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    exact Real.sqrt_nonneg _
  have hba : b ≤ a := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hmul : b * b ≤ a * b := mul_le_mul_of_nonneg_right hba hb
  have haSq : a ^ 2 = (n : ℝ) + 2 := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hbSq : b ^ 2 = (n : ℝ) := by
    dsimp [b]
    exact Real.sq_sqrt (by positivity)
  have heq : 2 / a + b = (2 + b * a) / a := by
    field_simp [ha.ne']
  change a ≤ 2 / a + b
  rw [heq, le_div_iff₀ ha]
  nlinarith [hmul]

/-- The coefficient-two recurrence dominates `sqrt (n+1)` at every finite index. -/
theorem sqrt_nat_succ_le_realRecurrenceValue_two : ∀ n : ℕ,
    Real.sqrt ((n : ℝ) + 1) ≤ realRecurrenceValue 2 n
  | 0 => by norm_num
  | n + 1 => by
      rw [realRecurrenceValue_succ]
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
        norm_num
        ring
      rw [hcast]
      change Real.sqrt ((n : ℝ) + 2) ≤
        2 / Real.sqrt ((n : ℝ) + 2) +
          Real.sqrt (realRecurrenceValue 2 n ^ 2 - 1)
      have ih := sqrt_nat_succ_le_realRecurrenceValue_two n
      have hsqrtNonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
      have hrawNonneg : 0 ≤ realRecurrenceValue 2 n := hsqrtNonneg.trans ih
      have hsquare : Real.sqrt ((n : ℝ) + 1) ^ 2 ≤
          realRecurrenceValue 2 n ^ 2 :=
        (sq_le_sq₀ hsqrtNonneg hrawNonneg).2 ih
      have hsqrtSq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hradicand : (n : ℝ) ≤ realRecurrenceValue 2 n ^ 2 - 1 := by
        nlinarith
      have hsqrt := Real.sqrt_le_sqrt hradicand
      exact (sqrt_nat_add_two_le_two_div_sqrt_add_sqrt_nat n).trans
        (add_le_add le_rfl hsqrt)

/-- Two is an explicit globally admissible real coefficient. -/
def twoAdmissibleRealRecurrence : AdmissibleRealRecurrence 2 :=
  AdmissibleRealRecurrence.ofRaw 2 fun n ↦ by
    have hone : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
      have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
      have := Real.sqrt_le_sqrt hbase
      simpa only [Real.sqrt_one] using this
    exact hone.trans (sqrt_nat_succ_le_realRecurrenceValue_two n)

/-- The infinite sharp boundary is finite because the explicit coefficient two controls it. -/
theorem infiniteSharpBoundary_ne_top : infiniteSharpBoundary ≠ ⊤ := by
  have hle : infiniteSharpBoundary ≤ ENNReal.ofReal 2 :=
    (nonempty_admissibleRealRecurrence_iff_infiniteSharpBoundary_le_ofReal
      (x := 2) (by positivity)).1 ⟨twoAdmissibleRealRecurrence⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-! ## Finite threshold faces and the exact sharp bridge -/

/-- The infimum of nonnegative coefficients whose raw recurrence is admitted through `N`. -/
def finiteRecurrenceThreshold (N : ℕ) : ℝ≥0∞ :=
  by
    classical
    exact ⨅ x : ℝ≥0,
      if FiniteRecurrenceAdmissible (x : ℝ) N then (x : ℝ≥0∞) else ⊤

/-- Every finite-admissible coefficient bounds the corresponding threshold. -/
theorem finiteRecurrenceThreshold_le (N : ℕ) (x : ℝ≥0)
    (admissible : FiniteRecurrenceAdmissible (x : ℝ) N) :
    finiteRecurrenceThreshold N ≤ (x : ℝ≥0∞) := by
  classical
  exact (iInf_le (fun y : ℝ≥0 ↦
    if FiniteRecurrenceAdmissible (y : ℝ) N then (y : ℝ≥0∞) else ⊤) x).trans_eq
      (if_pos admissible)

/-- Finite recurrence thresholds are monotone with prefix length. -/
theorem finiteRecurrenceThreshold_mono {N M : ℕ} (hNM : N ≤ M) :
    finiteRecurrenceThreshold N ≤ finiteRecurrenceThreshold M := by
  classical
  change finiteRecurrenceThreshold N ≤
    (⨅ x : ℝ≥0,
      if FiniteRecurrenceAdmissible (x : ℝ) M then (x : ℝ≥0∞) else ⊤)
  refine le_iInf fun x ↦ ?_
  by_cases hM : FiniteRecurrenceAdmissible (x : ℝ) M
  · have hN := finiteRecurrenceAdmissible_anti hNM hM
    rw [if_pos hM]
    exact finiteRecurrenceThreshold_le N x hN
  · rw [if_neg hM]
    exact le_top

/-- The recurrence threshold at each finite length is the attained variational coefficient. -/
theorem finiteRecurrenceThreshold_eq_finiteSharpCoefficient (N : ℕ) :
    finiteRecurrenceThreshold N = (finiteSharpCoefficient N : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · exact finiteRecurrenceThreshold_le N (finiteSharpCoefficient N)
      (finiteSharpCoefficient_finiteRecurrenceAdmissible N)
  · rw [finiteRecurrenceThreshold]
    refine le_iInf fun x ↦ ?_
    by_cases hx : FiniteRecurrenceAdmissible (x : ℝ) N
    · simpa [hx] using ENNReal.coe_le_coe.2
        (finiteSharpCoefficient_le_of_finiteRecurrenceAdmissible N hx)
    · simp [hx]

/-- The supremum of finite recurrence thresholds is the proved infinite sharp boundary. -/
theorem iSup_finiteRecurrenceThreshold_eq_infiniteSharpBoundary :
    (⨆ N, finiteRecurrenceThreshold N) = infiniteSharpBoundary := by
  unfold infiniteSharpBoundary
  apply iSup_congr
  intro N
  exact finiteRecurrenceThreshold_eq_finiteSharpCoefficient N

/-! ## The attained real threshold -/

/-- The nonnegative real coefficients carrying a complete admissible recurrence. -/
def nonnegativeAdmissibleCoefficientSet : Set ℝ :=
  {x | 0 ≤ x ∧ Nonempty (AdmissibleRealRecurrence x)}

/-- The genuine real recurrence threshold is the infimum of admitted nonnegative coefficients. -/
def recurrenceThreshold : ℝ :=
  sInf nonnegativeAdmissibleCoefficientSet

theorem nonnegativeAdmissibleCoefficientSet_nonempty :
    nonnegativeAdmissibleCoefficientSet.Nonempty := by
  refine ⟨2, ?_, ⟨twoAdmissibleRealRecurrence⟩⟩
  positivity

theorem nonnegativeAdmissibleCoefficientSet_bddBelow :
    BddBelow nonnegativeAdmissibleCoefficientSet := by
  refine ⟨0, ?_⟩
  rintro x ⟨hx, _hadmissible⟩
  exact hx

/-- The real infimum is the real value of the already-founded finite sharp boundary. -/
theorem recurrenceThreshold_eq_infiniteSharpBoundary_toReal :
    recurrenceThreshold = infiniteSharpBoundary.toReal := by
  let boundaryReal := infiniteSharpBoundary.toReal
  have hboundaryNonnegative : 0 ≤ boundaryReal := ENNReal.toReal_nonneg
  have hboundaryAdmissible : Nonempty (AdmissibleRealRecurrence boundaryReal) := by
    apply (nonempty_admissibleRealRecurrence_iff_infiniteSharpBoundary_le_ofReal
      hboundaryNonnegative).2
    rw [ENNReal.ofReal_toReal infiniteSharpBoundary_ne_top]
  have hboundaryMem : boundaryReal ∈ nonnegativeAdmissibleCoefficientSet :=
    ⟨hboundaryNonnegative, hboundaryAdmissible⟩
  have hboundaryLower : ∀ x ∈ nonnegativeAdmissibleCoefficientSet, boundaryReal ≤ x := by
    rintro x ⟨hx, hadmissible⟩
    have hle : infiniteSharpBoundary ≤ ENNReal.ofReal x :=
      (nonempty_admissibleRealRecurrence_iff_infiniteSharpBoundary_le_ofReal hx).1 hadmissible
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal hx] at htoReal
    exact htoReal
  apply le_antisymm
  · exact csInf_le nonnegativeAdmissibleCoefficientSet_bddBelow hboundaryMem
  · exact le_csInf nonnegativeAdmissibleCoefficientSet_nonempty hboundaryLower

/-- The real threshold and the extended-nonnegative boundary are exactly the same face. -/
theorem ofReal_recurrenceThreshold_eq_infiniteSharpBoundary :
    ENNReal.ofReal recurrenceThreshold = infiniteSharpBoundary := by
  rw [recurrenceThreshold_eq_infiniteSharpBoundary_toReal,
    ENNReal.ofReal_toReal infiniteSharpBoundary_ne_top]

theorem recurrenceThreshold_nonnegative : 0 ≤ recurrenceThreshold := by
  rw [recurrenceThreshold_eq_infiniteSharpBoundary_toReal]
  exact ENNReal.toReal_nonneg

/-- The admissible real coefficients are exactly the closed upper ray from the threshold. -/
theorem nonempty_admissibleRealRecurrence_iff_recurrenceThreshold_le
    {x : ℝ} (hx : 0 ≤ x) :
    Nonempty (AdmissibleRealRecurrence x) ↔ recurrenceThreshold ≤ x := by
  rw [nonempty_admissibleRealRecurrence_iff_infiniteSharpBoundary_le_ofReal hx,
    ← ofReal_recurrenceThreshold_eq_infiniteSharpBoundary,
    ENNReal.ofReal_le_ofReal_iff hx]

/-- The infimum itself carries a complete dependent admissible recurrence. -/
theorem recurrenceThreshold_admissible :
    Nonempty (AdmissibleRealRecurrence recurrenceThreshold) :=
  (nonempty_admissibleRealRecurrence_iff_recurrenceThreshold_le
    recurrenceThreshold_nonnegative).2 le_rfl

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

section Audit
open Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
#print axioms AdmissibleRealRecurrence.radicand_nonnegative
#print axioms AdmissibleRealRecurrence.iterate_eq_realRecurrenceValue
#print axioms nonempty_admissibleRealRecurrence_iff_all_finite
#print axioms not_finiteRecurrenceAdmissible_iff_exists_obstruction_le
#print axioms exists_firstRecurrenceObstruction
#print axioms not_nonempty_admissibleRealRecurrence_iff_obstruction
#print axioms realRecurrenceValue_mono_of_admissible
#print axioms realRecurrenceValue_mono_of_finite_admissible
#print axioms FiniteRecurrenceAdmissible.mono
#print axioms AdmissibleRealRecurrence.raise
#print axioms realRecurrenceValue_finiteSharpCoefficient_eq_finiteRecurrenceValue
#print axioms finiteSharpCoefficient_finiteRecurrenceAdmissible
#print axioms realRecurrenceValue_strictMono_of_finite_admissible
#print axioms finiteRecurrenceAdmissible_iff_finiteSharpCoefficient_le
#print axioms nonempty_admissibleRealRecurrence_iff_all_finiteSharpCoefficient_le
#print axioms sqrt_nat_succ_le_realRecurrenceValue_two
#print axioms twoAdmissibleRealRecurrence
#print axioms infiniteSharpBoundary_ne_top
#print axioms finiteRecurrenceThreshold_mono
#print axioms finiteRecurrenceThreshold_eq_finiteSharpCoefficient
#print axioms iSup_finiteRecurrenceThreshold_eq_infiniteSharpBoundary
#print axioms recurrenceThreshold_eq_infiniteSharpBoundary_toReal
#print axioms ofReal_recurrenceThreshold_eq_infiniteSharpBoundary
#print axioms nonempty_admissibleRealRecurrence_iff_recurrenceThreshold_le
#print axioms recurrenceThreshold_admissible
end Audit
