import Mathlib.Tactic
import Mathlib.FieldTheory.Separable
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Separation: the difference is the object, and the collapse is exhibited

`§2b` of the operating contract rules that **which side is called positive is a hand**,
and that a count of signs is a state reading.  What survives every frame is not a sign
but whether a passage returns *nothing* — whether two things can be told apart.  This
file carries that for polynomials, where it is the whole content of separability.

The discriminant `∏_{i<j}(αᵢ − αⱼ)²` is **not** a magnitude collapse — it is a *count
of differences*, a top-grade object.  It is the square of the Vandermonde blade
`∏_{i<j}(αⱼ − αᵢ)`, which is the oriented volume of the whole root configuration and
the exact rank-`n` analogue of `clifford.rs`'s `area_squared` at rank two: both vanish
precisely when the population degenerates.  Mathlib carries no discriminant at all;
this file builds the blade, because the blade is the object and the discriminant is its
hand-free face.

**And the hand it deletes is named here.**  A transposition of two roots reverses the
blade and fixes its square, so squaring erases exactly the permutation parity — which
is the sign character of the Galois group.  `√disc` reopens it; that is why the
discriminant being a square decides whether the group sits inside `A_n`.

* **`collapsedPopulation`** — the excess occurrences of the roots, exhibited as a
  multiset rather than summarised.  It is what a receiver counting *distinct* roots
  cannot see.
* **`theSeparationIsTheEmptyCollapse`** — separable exactly when that population is
  empty.
* **`theSeparatorIsACoprimality`** — the separator is a gcd; no comparison occurs.
* **`theDegreeIsTheDistinguishableCountPlusTheCollapse`** — the two receivers differ
  by exactly what the coarser one erased.

This is `receiver_exact_compression`'s shape in the field-theoretic setting: a coarse
receiver, its collapsed population, and the exact defect between the two readings.
Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.Separation

open Polynomial Multiset

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The collapsed population of a polynomial**: the excess occurrences of its roots —
the multiset that a receiver counting *distinct* roots cannot see.  Exhibited by
address, not summarised by a discriminant. -/
def collapsedPopulation (f : F[X]) : Multiset F := f.roots - f.roots.toFinset.val

/-- **SEPARATION IS THE EMPTY COLLAPSE**: a split polynomial is separable exactly when
its collapsed population is the zero multiset — when nothing was erased. -/
theorem theSeparationIsTheEmptyCollapse {f : F[X]} (hf : f ≠ 0) (h : f.Splits) :
    collapsedPopulation f = 0 ↔ f.Separable := by
  rw [← nodup_roots_iff_of_splits hf h]
  unfold collapsedPopulation
  rw [Multiset.toFinset_val, tsub_eq_zero_iff_le]
  constructor
  · intro hle
    have := le_antisymm (Multiset.dedup_le f.roots) hle
    exact Multiset.dedup_eq_self.mp this
  · intro hnd
    rw [Multiset.dedup_eq_self.mpr hnd]

omit [DecidableEq F] in
/-- **THE SEPARATOR IS A COPRIMALITY**, and no comparison sign occurs anywhere in it.
Separation is decided by a gcd — `Sturm`'s sign-change count is a *hand* reading of the
same question, and the hand is not what separation is about. -/
theorem theSeparatorIsACoprimality (f : F[X]) :
    f.Separable ↔ IsCoprime f (derivative f) := Iff.rfl

/-- **THE DEGREE IS THE DISTINGUISHABLE COUNT PLUS THE COLLAPSE.**  Two receivers read
the same polynomial — one counts distinct roots, one counts occurrences — and the
*difference between the two readings is exactly the population the coarser one erased*.
Separation is the case where that difference is zero. -/
theorem theDegreeIsTheDistinguishableCountPlusTheCollapse {f : F[X]} (hf : f ≠ 0)
    (h : f.Splits) :
    f.roots.toFinset.card + Multiset.card (collapsedPopulation f) = f.natDegree := by
  unfold collapsedPopulation
  rw [Multiset.toFinset_val, Multiset.card_sub (Multiset.dedup_le f.roots)]
  have hcard : f.roots.toFinset.card = Multiset.card f.roots.dedup := by
    rw [← Multiset.toFinset_val]; rfl
  have hle : Multiset.card f.roots.dedup ≤ Multiset.card f.roots :=
    Multiset.card_le_card (Multiset.dedup_le f.roots)
  rw [hcard, h.natDegree_eq_card_roots]
  omega

/-! ## The Vandermonde blade: the discriminant's oriented source -/

section Blade
variable {F : Type*} [Field F]

/-- **The Vandermonde blade of a root population**: `∏_{i<j} (αⱼ − αᵢ)`, the top-grade
oriented volume of the configuration.  The discriminant is its SQUARE. -/
def blade : List F → F
  | [] => 1
  | a :: rest => (rest.map (fun b => b - a)).prod * blade rest

/-- The discriminant: the blade with its hand squared away. -/
def disc (l : List F) : F := blade l * blade l

/-- **THE BLADE VANISHES EXACTLY ON THE COLLAPSE**: the oriented volume of the root
configuration is null precisely when two roots coincide. -/
theorem theBladeVanishesExactlyOnTheCollapse (l : List F) :
    blade l = 0 ↔ ¬ l.Nodup := by
  induction l with
  | nil => simp [blade]
  | cons a rest ih =>
    rw [blade, mul_eq_zero, ih, List.prod_eq_zero_iff, List.mem_map]
    constructor
    · rintro (⟨b, hb, hab⟩ | hnd)
      · intro hnodup
        exact (List.nodup_cons.mp hnodup).1 (by rwa [sub_eq_zero.mp hab] at hb)
      · intro hnodup; exact hnd (List.nodup_cons.mp hnodup).2
    · intro hnd
      by_cases hnodup : rest.Nodup
      · left
        by_contra hmem
        push_neg at hmem
        exact hnd (List.nodup_cons.mpr ⟨fun hc => hmem a hc (by ring), hnodup⟩)
      · exact Or.inr hnodup

/-- **THE SQUARE DELETES THE PERMUTATION HAND**: a transposition reverses the blade
and fixes the discriminant.  What the discriminant erased is exactly the parity of the
permutation — the Galois group's sign character — and taking the square root reopens
it. -/
theorem theSquareDeletesThePermutationHand (a b : F) (rest : List F) :
    blade (a :: b :: rest) = - blade (b :: a :: rest)
      ∧ disc (a :: b :: rest) = disc (b :: a :: rest) := by
  have hb : blade (a :: b :: rest) = - blade (b :: a :: rest) := by
    simp only [blade, List.map_cons, List.prod_cons]
    ring
  exact ⟨hb, by unfold disc; rw [hb]; ring⟩

end Blade

/-! ## The receiver, its collapsed population, and the separator -/

section Receiver
variable {X Y : Type*}

/-- A **receiver family**: a set of readings of `X`. -/
abbrev ReceiverFamily (X Y : Type*) := Set (X → Y)

/-- The **collapse** a receiver family induces: the pairs it cannot tell apart. -/
def collapseOf (F : ReceiverFamily X Y) (a b : X) : Prop := ∀ f ∈ F, f a = f b

/-- The readings that **respect** a declared relation — the ones blind to it. -/
def respecting (r : X → X → Prop) : ReceiverFamily X Y := {f | ∀ a b, r a b → f a = f b}

/-- **COLLAPSE AND RESPECT ARE ADJOINT**: an antitone Galois connection between receiver
families and relations.  The fundamental theorem of Galois theory is this adjunction
with fields for readings and automorphisms for the collapse. -/
theorem theCollapseAndTheRespectAreAdjoint (F : ReceiverFamily X Y) (r : X → X → Prop) :
    F ⊆ respecting r ↔ (∀ a b, r a b → collapseOf F a b) := by
  constructor
  · intro h a b hr f hf
    exact h hf a b hr
  · intro h f hf a b hr
    exact h a b hr f hf

/-- **A PAIR IS OFF THE COLLAPSE EXACTLY WHEN A SEPARATOR EXISTS.** -/
theorem theSeparatorExistsExactlyOffTheCollapse (F : ReceiverFamily X Y) (a b : X) :
    ¬ collapseOf F a b ↔ ∃ f ∈ F, f a ≠ f b := by
  unfold collapseOf
  push_neg
  rfl

/-- **A FINER RECEIVER COLLAPSES LESS**: inclusion of families reverses into inclusion
of collapses.  A bigger group sees less. -/
theorem theFinerReceiverCollapsesLess {F G : ReceiverFamily X Y} (h : F ⊆ G) (a b : X) :
    collapseOf G a b → collapseOf F a b := by
  intro hG f hf
  exact hG f (h hf)

/-- **THE COLLAPSE IS AN EQUIVALENCE**, so the readable quotient exists. -/
theorem theCollapseIsAnEquivalence (F : ReceiverFamily X Y) :
    Equivalence (collapseOf F) where
  refl _ _ _ := rfl
  symm h f hf := (h f hf).symm
  trans h1 h2 f hf := (h1 f hf).trans (h2 f hf)

/-- **THE COLLAPSED POPULATION HAS A SEPARATOR.**  The object, in one statement: what a
receiver family cannot distinguish is an equivalence relation, and its complement is
exactly the population carrying an exhibited separating reading.  Repeated roots, the
square classes, a Galois group, and `Ш` are this object at different ranks. -/
theorem theCollapsedPopulationHasASeparator (F : ReceiverFamily X Y) :
    Equivalence (collapseOf F) ∧
      ∀ a b : X, ¬ collapseOf F a b ↔ ∃ f ∈ F, f a ≠ f b :=
  ⟨theCollapseIsAnEquivalence F, theSeparatorExistsExactlyOffTheCollapse F⟩

/-- A language is **readable** by a receiver family when the family's collapse never
crosses its boundary: collapsed instances get the same verdict. -/
def Readable (R : ReceiverFamily X Y) (L : X → Prop) : Prop :=
  ∀ x y, collapseOf R x y → (L x ↔ L y)

/-- **THE CERTIFICATE IS A SEPARATOR.**  A family that decides a language
must separate every accepted instance from every rejected one, and the separating
reading is exactly the certificate. -/
theorem theCertificateIsASeparator {R : ReceiverFamily X Y} {L : X → Prop}
    (h : Readable R L) {x y : X} (hx : L x) (hy : ¬ L y) :
    ∃ f ∈ R, f x ≠ f y := by
  by_contra hno
  refine hy ((h x y ?_).mp hx)
  by_contra hc
  exact hno ((theSeparatorExistsExactlyOffTheCollapse R x y).mp hc)

/-- **A COLLAPSED PAIR ACROSS THE BOUNDARY REFUSES THE FAMILY** — a collapsed pair straddling the boundary makes the
language unreadable by that family, at any cost.  No amount of work inside the family
recovers a verdict it cannot see. -/
theorem theCollapsedPairAcrossTheBoundaryRefusesTheFamily {R : ReceiverFamily X Y}
    {L : X → Prop} {x y : X} (hcol : collapseOf R x y) (hx : L x) (hy : ¬ L y) :
    ¬ Readable R L := fun h => hy ((h x y hcol).mp hx)

/-- The join of two receiver families. -/
theorem theJoinOfFamiliesIntersectsTheirCollapses (R S : ReceiverFamily X Y) (a b : X) :
    collapseOf (R ∪ S) a b ↔ collapseOf R a b ∧ collapseOf S a b := by
  constructor
  · intro h
    exact ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩
  · rintro ⟨hR, hS⟩ f (hf | hf)
    · exact hR f hf
    · exact hS f hf

/-- **The order receiver**: one reading per rational cut. -/
def cutFamily : ReceiverFamily ℝ Prop := {f | ∃ q : ℚ, f = fun x => x < (q : ℝ)}

/-- **THE RATIONAL CUTS SEPARATE THE REALS.**  A real number is exactly what the
rational cuts can distinguish: the collapse of the cut receiver is equality, with the
separating cut exhibited.  This is the limit receiver the squeeze runs through. -/
theorem theRationalCutsSeparateTheReals (u v : ℝ) :
    collapseOf cutFamily u v ↔ u = v := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have := h (fun x => x < (q : ℝ)) ⟨q, rfl⟩
      rw [eq_iff_iff] at this
      exact absurd (this.mp hq1) (not_lt.mpr hq2.le)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have := h (fun x => x < (q : ℝ)) ⟨q, rfl⟩
      rw [eq_iff_iff] at this
      exact absurd (this.mpr hq1) (not_lt.mpr hq2.le)
  · rintro rfl f _; rfl

/-! ### The polarity of a relation -/

/-- The two polars of a relation. -/
def polarLeft (R : A → B → Prop) (T : Set B) : Set A := {a | ∀ b ∈ T, R a b}
def polarRight (R : A → B → Prop) (S : Set A) : Set B := {b | ∀ a ∈ S, R a b}

/-- **EVERY RELATION INDUCES AN ANTITONE GALOIS CONNECTION.**  Both sides say the
same thing: `∀ a ∈ S, ∀ b ∈ T, R a b`.  The correspondence is the relation, read from
either end. -/
theorem thePolarityIsAdjoint (R : A → B → Prop) (S : Set A) (T : Set B) :
    S ⊆ polarLeft R T ↔ T ⊆ polarRight R S := by
  constructor
  · intro h b hb a ha; exact h ha b hb
  · intro h a ha b hb; exact h hb a ha

/-- **THE POLARS REVERSE INCLUSION** — a larger constraint set admits fewer. -/
theorem thePolarsReverseInclusion (R : A → B → Prop) {T T' : Set B} (h : T ⊆ T') :
    polarLeft R T' ⊆ polarLeft R T := fun a ha b hb => ha b (h hb)

/-- **THE CLOSURE IS IDEMPOTENT** — one round trip is all there is. -/
theorem theClosureIsIdempotent (R : A → B → Prop) (S : Set A) :
    polarLeft R (polarRight R (polarLeft R (polarRight R S)))
      = polarLeft R (polarRight R S) := by
  have hexp : ∀ (U : Set A), U ⊆ polarLeft R (polarRight R U) :=
    fun U => (thePolarityIsAdjoint R U (polarRight R U)).mpr (fun _ h => h)
  have hexp' : ∀ (V : Set B), V ⊆ polarRight R (polarLeft R V) :=
    fun V => (thePolarityIsAdjoint R (polarLeft R V) V).mp (fun _ h => h)
  have hfgf : ∀ (V : Set B),
      polarLeft R (polarRight R (polarLeft R V)) = polarLeft R V := by
    intro V
    refine Set.Subset.antisymm ?_ (hexp _)
    exact thePolarsReverseInclusion R (hexp' V)
  exact hfgf (polarRight R S)

/-- **THE GALOIS CORRESPONDENCE IS THE RECEIVER DUALITY.**  Both are the polarity of a
relation: here
"the automorphism fixes the element": `Fix` and `Stab` are the two polars. -/
theorem theGaloisCorrespondenceIsTheReceiverDuality {L : Type*} [Field L]
    (S : Set (L ≃+* L)) (T : Set L) :
    S ⊆ polarLeft (fun (σ : L ≃+* L) (x : L) => σ x = x) T
      ↔ T ⊆ polarRight (fun (σ : L ≃+* L) (x : L) => σ x = x) S :=
  thePolarityIsAdjoint _ S T

/-- The agreement relation between a reading and a pair. -/
def Agree : (X → Y) → X × X → Prop := fun f p => f p.1 = f p.2

/-- **THE COLLAPSE IS THE POLARITY OF AGREEMENT.**  The receiver construction and the
relation polarity are one object: the collapsed pairs are the right polar of a receiver
family, and the respecting readings are the left polar of a relation. -/
theorem theCollapseIsThePolarityOfAgreement (R : ReceiverFamily X Y) (a b : X) :
    collapseOf R a b ↔ (a, b) ∈ polarRight (Agree (X := X) (Y := Y)) R := Iff.rfl

/-- And the other polar is exactly `respecting`. -/
theorem theRespectingIsTheLeftPolar (r : X → X → Prop) :
    respecting (Y := Y) r = polarLeft (Agree (X := X) (Y := Y)) {p | r p.1 p.2} := by
  ext f
  constructor
  · intro hf p hp; exact hf p.1 p.2 hp
  · intro hf a b hab; exact hf (a, b) hab

end Receiver

/-! ## The squeeze: a constraint that computes nothing and determines everything -/

section Squeeze
open Filter Topology

/-- **THE SQUEEZE IS SEPARATION AT THE LIMIT.**  The squeeze theorem is a separation statement — every tolerance reading
eventually collapses the fenced sequence onto the limit, so no receiver in the family
separates them, and nothing about `b` is ever computed. -/
theorem theSqueezeIsSeparationAtTheLimit {a b c : ℕ → ℝ} {L : ℝ}
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Tendsto a atTop (𝓝 L)) (hc : Tendsto c atTop (𝓝 L))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, |b n - L| < ε := by
  have hA : ∀ᶠ n in atTop, |a n - L| < ε := by
    filter_upwards [Metric.tendsto_nhds.mp ha ε hε] with n hn
    simpa [Real.dist_eq] using hn
  have hC : ∀ᶠ n in atTop, |c n - L| < ε := by
    filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hA, hC] with n hAn hCn
  rw [abs_lt] at hAn hCn ⊢
  constructor
  · linarith [hab n, hAn.1]
  · linarith [hbc n, hCn.2]

/-- **THE FENCE DETERMINES THE LIMIT** — and therefore the limit, with the fence supplying everything. -/
theorem theFenceDeterminesTheLimit {a b c : ℕ → ℝ} {L : ℝ}
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Tendsto a atTop (𝓝 L)) (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto b atTop (𝓝 L) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [theSqueezeIsSeparationAtTheLimit hab hbc ha hc hε] with n hn
  simpa [Real.dist_eq] using hn

end Squeeze

/-! ## The moves are constraints, not heuristics -/

section Moves

/-- **SUBSTITUTION IS A CHART TRANSITION CARRYING A JACOBIAN.** -/
theorem theSubstitutionMoveIsAChartTransition {F φ : ℝ → ℝ} {v φ' : ℝ} {x : ℝ}
    (hF : HasDerivAt F v (φ x)) (hφ : HasDerivAt φ φ' x) :
    HasDerivAt (F ∘ φ) (v * φ') x := hF.comp x hφ

/-- **THE BY-PARTS MOVE IS A COBOUNDARY**: it changes the representative by the exact
term `F·G` and nothing else. -/
theorem theByPartsMoveIsACoboundary {F G f g : ℝ → ℝ} {x : ℝ}
    (hF : HasDerivAt F (f x) x) (hG : HasDerivAt G (g x) x) :
    HasDerivAt (fun y => F y * G y) (f x * G x + F x * g x) x := hF.mul hG

/-- **THE CLASS IS WHAT SURVIVES**: two representatives of one constraint differ by a
constant, so the moves above act on representatives while the class is fixed.  This is
`H⁰` of the de Rham complex on the line, and it is why the moves work. -/
theorem theClassIsWhatSurvives {F G d : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (d x) x) (hG : ∀ x, HasDerivAt G (d x) x) (x y : ℝ) :
    F x - G x = F y - G y := by
  have hH : ∀ z, HasDerivAt (fun w => F w - G w) 0 z := by
    intro z
    change HasDerivAt (F - G) 0 z
    simpa using (hF z).sub (hG z)
  have hdiff : Differentiable ℝ (fun w => F w - G w) := fun z => (hH z).differentiableAt
  have hzero : ∀ z, deriv (fun w => F w - G w) z = 0 := fun z => (hH z).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero x y

/-- **THE PARTIAL-FRACTION MOVE IS A LOCAL–GLOBAL SPLIT.**  A global rational function
with two simple poles is the *sum of its local principal parts*, each carrying one pole
and nothing else.  The obstruction to such a splitting is what `H¹(ℙ¹, O) = 0` says
vanishes; here it is exhibited as an identity, with the residues `±1/(a−b)` as the local
data. -/
theorem thePartialFractionMoveIsALocalGlobalSplit {a b x : ℝ}
    (hab : a ≠ b) (ha : x ≠ a) (hb : x ≠ b) :
    1 / ((x - a) * (x - b)) = (1 / (a - b)) * (1 / (x - a)) - (1 / (a - b)) * (1 / (x - b)) := by
  have h1 : x - a ≠ 0 := sub_ne_zero.mpr ha
  have h2 : x - b ≠ 0 := sub_ne_zero.mpr hb
  have h3 : a - b ≠ 0 := sub_ne_zero.mpr hab
  field_simp
  ring

end Moves

/-! ## The modulus: what decomposes and what does not -/

section Modulus

/-- **THE MODULUS DOES NOT DISTRIBUTE OVER A SUM.**  There is no law relating
`A % (B+C)` to `A % B` and `A % C`: the counterexample is immediate. -/
theorem theModulusDoesNotDistributeOverTheSum :
    8 % (2 + 3) ≠ (8 % 2 + 8 % 3) % (2 + 3) := by decide

/-- **A PRODUCT OF BINARY CHARTS IS NOT A SINGLE MODULUS.**  `(ℤ/2)³` has exponent two —
every element is its own inverse — while `ℤ/2³` does not.  So `2^N` as *N independent
binary axes* and `2^N` as *one cyclic modulus* are different objects, and only the first
is the vertex set of an `N`-cube. -/
theorem theCubeIsNotTheCyclicModulus :
    (∀ x : ZMod 2 × ZMod 2 × ZMod 2, x + x = 0) ∧ ((1 : ZMod 8) + 1 ≠ 0) := by
  constructor
  · decide
  · decide

/-- **THE SAME SEPARATION ONE LEVEL DOWN**: `ℤ/2²` is not `(ℤ/2)²` either. -/
theorem theSquareModulusIsNotTheSquareChart :
    (∀ x : ZMod 2 × ZMod 2, x + x = 0) ∧ ((1 : ZMod 4) + 1 ≠ 0) := by
  constructor
  · decide
  · decide

/-- **THE CUBE AND THE SIMPLEX COUNT DIFFERENTLY.**  A shape whose vertices are the
binary combinations of `N` axes has `2^N` of them and carries the group `(ℤ/2)^N`; a
simplex on `N` axes has `N+1` and carries no such group.  They agree only at `N ≤ 1`. -/
theorem theCubeAndTheSimplexAgreeOnlyBelowTwo (N : ℕ) :
    2 ^ N = N + 1 ↔ N = 0 ∨ N = 1 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hN : 2 ≤ N := by omega
    have key : ∀ n : ℕ, 2 ≤ n → n + 1 < 2 ^ n := by
      intro n hn
      induction n with
      | zero => omega
      | succ k ih =>
        rcases Nat.lt_or_ge k 2 with hk | hk
        · interval_cases k
          · omega
          · norm_num
        · have hih := ih (by omega)
          have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          omega
    have := key N hN
    omega
  · rintro (rfl | rfl) <;> norm_num

end Modulus

/-! ## The gauge: what a ratio deletes, and what a magnitude deletes -/

section Gauge
open Real

/-- The softmax ratio: the multiplicative chart of a difference. -/
noncomputable def softmaxRatio {n : Type*} (x : n → ℝ) (i j : n) : ℝ := Real.exp (x i - x j)

/-- **THE RATIO IS THE CHART TRANSITION.**  `exp` carries the additive chart to the
multiplicative one, so the softmax ratio is the quotient of the two exponentials — no
normalising constant appears, and none is needed. -/
theorem theRatioIsTheChartTransition {n : Type*} (x : n → ℝ) (i j : n) :
    softmaxRatio x i j = Real.exp (x i) / Real.exp (x j) := by
  unfold softmaxRatio
  rw [Real.exp_sub]

/-- **THE RATIO IS GAUGE-INVARIANT**: shifting every coordinate by a common constant
changes nothing.  Absolute position is gauge. -/
theorem theRatioIsGaugeInvariant {n : Type*} (x : n → ℝ) (c : ℝ) (i j : n) :
    softmaxRatio (fun k => x k + c) i j = softmaxRatio x i j := by
  unfold softmaxRatio
  congr 1
  ring

/-- **THE RATIOS DETERMINE EVERYTHING EXCEPT THE ORIGIN.**  Two coordinate vectors have
the same softmax ratios exactly when they differ by a common shift.  So the softmax
deletes **one** dimension — the declared gauge — and retains every difference; where
root-mean-square deletes every difference and retains one magnitude.  That is why this
is a chart transition and not a statistic. -/
theorem theRatiosDetermineTheGaugeClass {n : Type*} (x y : n → ℝ) (i₀ : n) :
    (∀ i j, softmaxRatio x i j = softmaxRatio y i j) ↔ ∃ c : ℝ, ∀ i, y i = x i + c := by
  constructor
  · intro h
    refine ⟨y i₀ - x i₀, fun i => ?_⟩
    have hij := h i i₀
    unfold softmaxRatio at hij
    have := Real.exp_injective hij
    linarith
  · rintro ⟨c, hc⟩ i j
    unfold softmaxRatio
    rw [hc i, hc j]
    congr 1
    ring

end Gauge

end Soma.Holonics.Millennium.Separation
