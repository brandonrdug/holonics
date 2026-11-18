import Mathlib
import HolonicsResearch.Compression.Landmark.NecklaceIntegrality
import HolonicsResearch.Landmarks.IharaBass

/-!
# Ihara's product over prime cycles: the dynamical side of a finite complex's zeta

`IharaBass` proves the determinant side of `trace.ihara-zeta`: the dart operator's determinant
`det (1 − u B)` is Bass's cell determinant with its two powers of `1 − u²`.  This owner proves the
product side: the same determinant is the product of `(1 − u^d)^(N_d)` over the lengths `d`, where
`N_d` counts the prime cycles of `d` darts, read to any horizon `N` (every coefficient up to `u^N`).

**The owner of the counting** is `Compression/Landmark/NecklaceIntegrality`.  For a matrix of
natural numbers it builds the closed walks of its multigraph and proves that those of least
rotation period `n` number `n` times the necklace count, that `tr Mⁿ = Σ_(d ∣ n) d · p_d`, the
Möbius form with its integrality, and the horizon-truncated Euler product of `det (1 − u M)`.
Nothing of it is proved again here.  This module is its instance on the dart operator, joined to
Bass's determinant of `IharaBass`: the box `trace.ihara-zeta` of #410.

**The model** is `IharaBass`'s.  Cells `V` and contacts `E` are types, `a b : E → V` give each
contact its two ends, a dart is an element of `E ⊕ E` and the reversal is `Sum.swap`.  Loops and
parallel contacts are allowed, and nothing is assumed of connectivity or of the degrees.

* [definition] `dartMatrix a b`: the dart operator with entries in `ℕ`, `1` where `f` leaves the
  cell `d` enters and `f` is not `d` reversed.  `ClosedWalk a b n`: a cyclic word of darts
  `w : ZMod n → E ⊕ E` in which every dart leaves the cell the dart before it enters and is never
  that dart reversed, the wrap from the last dart to the first included (a closed walk with no
  backtrack and no tail).  `walkRot`: its rotation by one dart.  A prime cycle of `d` darts is an
  orbit of the rotation on the closed walks of least period `d`, and `primeCycles a b d` is their
  count, the owner's `necklaceCount` of the dart matrix.
* [proved-derived; formal-checked] the dart matrix: `dartMatrix_map` (its cast to any commutative
  ring is `IharaBass.hashimoto`), `dartMatrix_le_one`, `dartMatrix_pos_iff`, and `edge_step`,
  `edge_ext` (an edge of its multigraph is a pair of darts that follow, with no further choice).
* [proved-derived; formal-checked] the walks in the complex's own terms: `loopEquiv` (the owner's
  closed walks of the dart matrix are the cyclic words of darts above, by an equivalence),
  `loopEquiv_rot` (it carries rotation to rotation), `minimalPeriod_loopEquiv` (so least periods
  agree), `card_closedWalk` and `card_closedWalk_eq_trace` (their count is `tr Bⁿ`),
  `card_primitive_closedWalk` (those of least period `d` number `d · primeCycles d`) and
  `primeCycles_eq_primitiveCount` (the count is the count of rotation orbits of least period `d`
  on the cyclic words of darts).
* [proved-derived; formal-checked] the counting identity: `trace_hashimoto_pow`
  (`tr Bⁿ = Σ_(d ∣ n) d · primeCycles d` for `n ≥ 1`, in every commutative ring),
  `primeCycles_moebius` (`Σ_(d ∣ n) μ(n/d) · tr B^d = n · primeCycles n` over `ℤ`) and
  `primeCycles_one` (the prime cycles of one dart are the loops, each in its two directions).
* [proved-derived; formal-checked] **Ihara's product to a horizon**:
  `ihara_euler_product_coeff` (over `ℚ`, the coefficients of `det (1 − u B)` and of
  `∏_(d ≤ N) (1 − u^d)^(primeCycles d)` agree up to order `N`), `ihara_euler_product` (the same as
  a divisibility by `X^(N+1)` in `ℚ[X]`), `ihara_euler_product_int` (in `ℤ[X]`) and
  `ihara_euler_product_ring` (in `R[X]` for every commutative ring `R`, since both sides have
  integer coefficients); `ihara_zeta_euler_product_coeff` (with the tree's zeta
  `exp (Σ tr Bⁿ uⁿ / n)` of `Aeon/Production/Zeta`: zeta times the truncated product has the
  coefficients of `1` up to order `N`).
* [proved-derived; formal-checked] **the three faces**: `ihara_three_faces` and
  `ihara_three_faces_coeff`.  With `IharaBass.ihara_bass_charpolyRev`, in `R[X]` and without
  division,
  `(1 − X²)^|V| · ∏_(d ≤ N) (1 − X^d)^(primeCycles d)` and
  `det (1 − X A + X² (D − 1)) · (1 − X²)^|E|` agree in every coefficient up to order `N`: the
  product over prime cycles, the dart determinant between them, and Bass's cell determinant.
* [proved-derived; formal-checked] a ruler, one cell with one loop: `dartMatrix_oneLoop` (the dart
  operator is the identity on the two darts), `primeCycles_oneLoop_one` (two prime cycles of one
  dart, the loop in its two directions), `primeCycles_oneLoop_of_two_le` (none of any greater
  length), `charpolyRev_oneLoop` (`det (1 − X B) = (1 − X)²`) and `prod_oneLoop` (the product is
  `(1 − X)²` at every horizon `N ≥ 1`, so here the two sides agree as polynomials).
* [proved-standard; formal-checked] supporting statements: `charpolyRev_map` (the reversed
  characteristic polynomial commutes with a ring map), `hashimoto_charpolyRev_map`,
  `coe_prod_factors`, `map_prod_factors`.

[from training] Ihara 1966 (the zeta of a regular complex as a product over prime cycles),
Hashimoto 1989 (the dart operator and `det (1 − u B)`), Bass 1992 (the cell determinant for every
finite complex), Bowen and Lanford 1970 (the zeta of a matrix of natural numbers as a transfer
determinant).  The statements here are proved in the file from the tree's owners and Mathlib; the
citations name where the laws were first written.

**What this does not state.**  The product over every length is not formed as one power series:
each statement is to a horizon `N`, and each coefficient is reached at `N` equal to its order and
does not move after.  Nothing is said of convergence or of a continuation in `u`.  A prime cycle
here has a direction, so a cycle and its reversal are counted apart, and nothing is said of
conjugacy classes of a fundamental group, which is how Ihara's first statement reads the same
count.  Nothing is stated with a connection on the darts (a twisted product).  Nothing is stated
about where the zeros stand; that is `RegularComplexZeros`'.

No `axiom`, no `sorry`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Landmarks.IharaEulerProduct

open Finset Function PowerSeries
open Holonics.Aeon.Production.Zeta
open Holonics.Compression.Landmark.PrimitiveCycle
open Holonics.Compression.Landmark.NecklaceIntegrality
open Holonics.Landmarks.IharaBass

/-! ## The dart matrix and the cyclic words of darts -/

section Dart

variable {V E : Type*} [DecidableEq V] [DecidableEq E] (a b : E → V)

/-- [definition] The dart operator with entries in `ℕ`: `1` where `f` leaves the cell `d` enters
and `f` is not `d` reversed, `0` elsewhere. -/
def dartMatrix : Matrix (E ⊕ E) (E ⊕ E) ℕ :=
  Matrix.of fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap then 1 else 0

@[simp]
theorem dartMatrix_apply (d f : E ⊕ E) :
    dartMatrix a b d f = if tgt a b d = src a b f ∧ f ≠ d.swap then 1 else 0 :=
  rfl

/-- [proved-derived; formal-checked] Read in any commutative ring, the dart matrix is
`IharaBass`'s dart operator. -/
theorem dartMatrix_map (R : Type*) [CommRing R] :
    (dartMatrix a b).map (Nat.cast : ℕ → R) = hashimoto R a b := by
  ext d f
  simp only [Matrix.map_apply, dartMatrix_apply, hashimoto_apply]
  split_ifs <;> simp

/-- [proved-derived; formal-checked] Between two darts there is at most one edge. -/
theorem dartMatrix_le_one (d f : E ⊕ E) : dartMatrix a b d f ≤ 1 := by
  rw [dartMatrix_apply]
  split_ifs <;> simp

/-- [proved-derived; formal-checked] There is an edge from `d` to `f` when `f` leaves the cell `d`
enters and is not `d` reversed. -/
theorem dartMatrix_pos_iff (d f : E ⊕ E) :
    0 < dartMatrix a b d f ↔ tgt a b d = src a b f ∧ f ≠ d.swap := by
  rw [dartMatrix_apply]
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] An edge of the dart matrix's multigraph joins two darts that
follow each other without a backtrack. -/
theorem edge_step (e : Edge (dartMatrix a b)) :
    tgt a b e.src = src a b e.tgt ∧ e.tgt ≠ e.src.swap :=
  (dartMatrix_pos_iff a b e.src e.tgt).mp (Fin.pos e.idx)

/-- [proved-derived; formal-checked] An edge of the dart matrix's multigraph is its two darts:
no further choice stands between them. -/
theorem edge_ext {e e' : Edge (dartMatrix a b)} (hs : e.src = e'.src) (ht : e.tgt = e'.tgt) :
    e = e' := by
  obtain ⟨s, t, i⟩ := e
  obtain ⟨s', t', i'⟩ := e'
  dsimp only at hs ht
  subst hs ht
  have hi : i = i' := by
    apply Fin.ext
    have h1 := dartMatrix_le_one a b s t
    have h2 := i.isLt
    have h3 := i'.isLt
    omega
  rw [hi]

/-- [definition] A closed walk of `n` darts with no backtrack and no tail: a cyclic word of darts
in which every dart leaves the cell the dart before it enters and is never that dart reversed, the
wrap included. -/
abbrev ClosedWalk (n : ℕ) : Type _ :=
  {w : ZMod n → E ⊕ E // ∀ i, tgt a b (w i) = src a b (w (i + 1)) ∧ w (i + 1) ≠ (w i).swap}

/-- [definition] The rotation of a closed walk by one dart. -/
def walkRot (n : ℕ) (w : ClosedWalk a b n) : ClosedWalk a b n :=
  ⟨fun i => w.1 (i + 1), fun i => w.2 (i + 1)⟩

/-- [proved-derived; formal-checked] **The owner's closed walks of the dart matrix are the cyclic
words of darts**: a walk is sent to the darts its edges leave, and a word of darts to the edges
between its neighbours. -/
def loopEquiv (n : ℕ) : Loop (dartMatrix a b) n ≃ ClosedWalk a b n where
  toFun w := ⟨fun i => (w.1 i).src, fun i => by
    have h := edge_step a b (w.1 i)
    rw [w.2 i] at h
    exact h⟩
  invFun v := ⟨fun i => ⟨v.1 i, v.1 (i + 1), ⟨0, (dartMatrix_pos_iff a b _ _).mpr (v.2 i)⟩⟩,
    fun _ => rfl⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact edge_ext a b rfl (w.2 i).symm
  right_inv _ := rfl

/-- [proved-derived; formal-checked] The equivalence carries rotation to rotation. -/
theorem loopEquiv_rot (n : ℕ) (w : Loop (dartMatrix a b) n) :
    loopEquiv a b n (rot w) = walkRot a b n (loopEquiv a b n w) :=
  rfl

/-- [proved-derived; formal-checked] A closed walk and its word of darts have the same least
period under rotation. -/
theorem minimalPeriod_loopEquiv (n : ℕ) (w : Loop (dartMatrix a b) n) :
    minimalPeriod (walkRot a b n) (loopEquiv a b n w) = minimalPeriod rot w := by
  rw [minimalPeriod_eq_minimalPeriod_iff]
  intro j
  have hs : Semiconj (loopEquiv a b n) rot (walkRot a b n) := fun w => loopEquiv_rot a b n w
  have hj : loopEquiv a b n (rot^[j] w) = (walkRot a b n)^[j] (loopEquiv a b n w) :=
    (hs.iterate_right j).eq w
  constructor
  · intro hp
    have hp' : (walkRot a b n)^[j] (loopEquiv a b n w) = loopEquiv a b n w := hp
    show rot^[j] w = w
    apply (loopEquiv a b n).injective
    rw [hj, hp']
  · intro hp
    have hp' : rot^[j] w = w := hp
    show (walkRot a b n)^[j] (loopEquiv a b n w) = loopEquiv a b n w
    rw [← hj, hp']

end Dart

/-! ## The counts -/

section Count

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)

/-- [definition] The number of prime cycles of `d` darts: the rotation orbits of least period `d`
on the closed walks of `d` darts, the owner's necklace count of the dart matrix. -/
def primeCycles (d : ℕ) : ℕ := necklaceCount (dartMatrix a b) d

/-- [proved-derived; formal-checked] The closed walks of `n` darts number `tr Bⁿ`, read on the
dart matrix. -/
theorem card_closedWalk (n : ℕ) [NeZero n] :
    Fintype.card (ClosedWalk a b n) = (dartMatrix a b ^ n).trace := by
  rw [← card_loop (dartMatrix a b) n]
  exact (Fintype.card_congr (loopEquiv a b n)).symm

/-- [proved-derived; formal-checked] **A prime cycle of `d` darts has `d` rotations**: the closed
walks of `d` darts of least period `d` number `d · primeCycles d`. -/
theorem card_primitive_closedWalk (d : ℕ) [NeZero d] :
    (univ.filter fun v : ClosedWalk a b d => minimalPeriod (walkRot a b d) v = d).card
      = d * primeCycles a b d := by
  rw [primeCycles, ← card_primitive_loops (dartMatrix a b) d]
  symm
  refine Finset.card_bij (fun w _ => loopEquiv a b d w) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [minimalPeriod_loopEquiv, hw]
  · intro w _ w' _ h
    exact (loopEquiv a b d).injective h
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    refine ⟨(loopEquiv a b d).symm v, ?_, (loopEquiv a b d).apply_symm_apply v⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [← minimalPeriod_loopEquiv, Equiv.apply_symm_apply, hv]

/-- [proved-derived; formal-checked] The count of prime cycles is the count of rotation orbits of
least period `d` on the cyclic words of darts. -/
theorem primeCycles_eq_primitiveCount (d : ℕ) [NeZero d] :
    primeCycles a b d = primitiveCount (walkRot a b d) d := by
  have h1 := card_primitive_closedWalk a b d
  rw [card_minimalPeriod_eq (walkRot a b d) d (NeZero.pos d)] at h1
  exact (Nat.eq_of_mul_eq_mul_left (NeZero.pos d) h1).symm

/-- [proved-standard; formal-checked] The traces of the dart operator in a ring are the dart
matrix's traces. -/
theorem trace_hashimoto_pow_eq_natCast (R : Type*) [CommRing R] (n : ℕ) :
    (hashimoto R a b ^ n).trace = (((dartMatrix a b) ^ n).trace : R) := by
  rw [← dartMatrix_map a b R]
  have h : (dartMatrix a b).map (Nat.cast : ℕ → R)
      = (Nat.castRingHom R).mapMatrix (dartMatrix a b) := rfl
  rw [h, ← map_pow]
  simp [Matrix.trace, Matrix.map_apply]

/-- [proved-derived; formal-checked] The closed walks of `n` darts number `tr Bⁿ`. -/
theorem card_closedWalk_eq_trace (n : ℕ) [NeZero n] :
    (Fintype.card (ClosedWalk a b n) : ℚ) = (hashimoto ℚ a b ^ n).trace := by
  rw [trace_hashimoto_pow_eq_natCast, card_closedWalk]

/-- [proved-derived; formal-checked] **The counting identity of the dart operator**:
`tr Bⁿ = Σ_(d ∣ n) d · primeCycles d` for every `n ≥ 1`, in every commutative ring. -/
theorem trace_hashimoto_pow (R : Type*) [CommRing R] (n : ℕ) (hn : 0 < n) :
    (hashimoto R a b ^ n).trace
      = ∑ d ∈ n.divisors, ((d : ℕ) : R) * (primeCycles a b d : R) := by
  rw [trace_hashimoto_pow_eq_natCast, trace_pow_eq_sum_necklace (dartMatrix a b) n hn]
  simp only [primeCycles, Nat.cast_sum, Nat.cast_mul]

/-- [proved-derived; formal-checked] **The Möbius form**: the prime cycles are read from the
traces, `Σ_(d ∣ n) μ(n/d) · tr B^d = n · primeCycles n`, so the sum on the left is a nonnegative
multiple of `n`. -/
theorem primeCycles_moebius (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * (hashimoto ℤ a b ^ d).trace
      = (n : ℤ) * (primeCycles a b n : ℤ) := by
  have h := necklace_integrality (dartMatrix a b) n hn
  simp only [trace_hashimoto_pow_eq_natCast]
  exact h

/-- [proved-derived; formal-checked] The prime cycles of one dart are the loops, each in its two
directions. -/
theorem primeCycles_one : primeCycles a b 1 = 2 * (univ.filter fun e => a e = b e).card := by
  have h := trace_pow_eq_sum_necklace (dartMatrix a b) 1 Nat.one_pos
  rw [Nat.divisors_one, sum_singleton, one_mul, pow_one] at h
  rw [primeCycles, ← h, Matrix.trace, Fintype.sum_sum_type]
  simp only [Matrix.diag_apply, dartMatrix_apply, tgt_inl, src_inl, tgt_inr, src_inr,
    Sum.swap_inl, Sum.swap_inr, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  rw [two_mul, Finset.card_filter]
  congr 1
  exact sum_congr rfl fun e _ => if_congr eq_comm rfl rfl

end Count

/-! ## Ihara's product to a horizon -/

section Product

/-- [proved-standard; formal-checked] The reversed characteristic polynomial commutes with a ring
map. -/
theorem charpolyRev_map {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (M : Matrix n n R) (f : R →+* S) : M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Polynomial.coe_mapRingHom, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
  split_ifs <;> simp

/-- [proved-standard; formal-checked] The truncated product read as a power series. -/
theorem coe_prod_factors (p : ℕ → ℕ) (N : ℕ) :
    ((∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ p d : Polynomial ℚ) : PowerSeries ℚ)
      = ∏ d ∈ Icc 1 N, (1 - X ^ d) ^ p d := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine prod_congr rfl fun d _ => ?_
  rw [map_pow, map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]

/-- [proved-standard; formal-checked] The truncated product is carried by every ring map. -/
theorem map_prod_factors {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : ℕ → ℕ)
    (N : ℕ) :
    (∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ p d : Polynomial R).map f
      = ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ p d := by
  rw [Polynomial.map_prod]
  refine prod_congr rfl fun d _ => ?_
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X]

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)

/-- [proved-standard; formal-checked] The dart determinant is carried by every ring map. -/
theorem hashimoto_charpolyRev_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (hashimoto R a b).charpolyRev.map f = (hashimoto S a b).charpolyRev := by
  rw [charpolyRev_map, hashimoto_map]

/-- [proved-derived; formal-checked] **Ihara's product to a horizon, coefficient by coefficient**:
every coefficient of the dart determinant `det (1 − u B)` of order at most `N` is the coefficient
of `∏_(d = 1)^N (1 − u^d)^(primeCycles d)`. -/
theorem ihara_euler_product_coeff (N k : ℕ) (hk : k ≤ N) :
    coeff k ((hashimoto ℚ a b).charpolyRev : PowerSeries ℚ)
      = coeff k (∏ d ∈ Icc 1 N, (1 - X ^ d) ^ primeCycles a b d : PowerSeries ℚ) := by
  rw [← dartMatrix_map a b ℚ]
  exact euler_product_coeff (dartMatrix a b) N k hk

/-- [proved-derived; formal-checked] **Ihara's product to a horizon, as polynomials over `ℚ`**:
`det (1 − X B) ≡ ∏_(d ≤ N) (1 − X^d)^(primeCycles d)` modulo `X^(N+1)`. -/
theorem ihara_euler_product (N : ℕ) :
    (Polynomial.X : Polynomial ℚ) ^ (N + 1) ∣
      (hashimoto ℚ a b).charpolyRev
        - ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles a b d := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub, sub_eq_zero]
  have hc := ihara_euler_product_coeff a b N k (by omega)
  rw [← coe_prod_factors, Polynomial.coeff_coe, Polynomial.coeff_coe] at hc
  exact hc

/-- [proved-derived; formal-checked] The same over `ℤ`, where both sides already stand. -/
theorem ihara_euler_product_int (N : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (N + 1) ∣
      (hashimoto ℤ a b).charpolyRev
        - ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles a b d := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  have h := (Polynomial.X_pow_dvd_iff.mp (ihara_euler_product a b N)) k hk
  rw [← hashimoto_charpolyRev_map a b (Int.castRingHom ℚ),
    ← map_prod_factors (Int.castRingHom ℚ), ← Polynomial.map_sub, Polynomial.coeff_map,
    eq_intCast, Int.cast_eq_zero] at h
  exact h

/-- [proved-derived; formal-checked] **Ihara's product to a horizon in every commutative ring**:
`det (1 − X B) ≡ ∏_(d ≤ N) (1 − X^d)^(primeCycles d)` modulo `X^(N+1)` in `R[X]`. -/
theorem ihara_euler_product_ring (R : Type*) [CommRing R] (N : ℕ) :
    (Polynomial.X : Polynomial R) ^ (N + 1) ∣
      (hashimoto R a b).charpolyRev
        - ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles a b d := by
  have h := Polynomial.map_dvd (Int.castRingHom R) (ihara_euler_product_int a b N)
  rw [Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, hashimoto_charpolyRev_map,
    map_prod_factors] at h
  exact h

/-- [proved-derived; formal-checked] **The zeta against the product**: with the tree's zeta
`exp (Σ tr Bⁿ uⁿ / n)` of the dart operator, zeta times the product over the prime cycles of at
most `N` darts has the coefficients of `1` up to order `N`. -/
theorem ihara_zeta_euler_product_coeff (N k : ℕ) (hk : k ≤ N) :
    coeff k ((PowerSeries.exp ℚ).subst (cycleLog (hashimoto ℚ a b)) *
        ∏ d ∈ Icc 1 N, (1 - X ^ d) ^ primeCycles a b d)
      = coeff k (1 : PowerSeries ℚ) := by
  calc coeff k ((PowerSeries.exp ℚ).subst (cycleLog (hashimoto ℚ a b)) *
        ∏ d ∈ Icc 1 N, (1 - X ^ d) ^ primeCycles a b d)
      = coeff k ((PowerSeries.exp ℚ).subst (cycleLog (hashimoto ℚ a b)) *
          ((hashimoto ℚ a b).charpolyRev : PowerSeries ℚ)) := by
        rw [coeff_mul, coeff_mul]
        refine sum_congr rfl fun p hp => ?_
        have hp' := mem_antidiagonal.mp hp
        rw [ihara_euler_product_coeff a b N p.2 (by omega)]
    _ = coeff k (1 : PowerSeries ℚ) := by rw [zeta_eq_exp]

end Product

/-! ## The three faces -/

section ThreeFaces

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)

/-- [proved-derived; formal-checked] **The three faces of a finite complex's zeta, to a horizon
and without division.**  In `R[X]`, for every commutative ring `R`,
`(1 − X²)^|V| · ∏_(d ≤ N) (1 − X^d)^(primeCycles d) ≡ det (1 − X A + X² (D − 1)) · (1 − X²)^|E|`
modulo `X^(N+1)`: the product over prime cycles is the dart determinant to the horizon, and the
dart determinant is Bass's cell determinant. -/
theorem ihara_three_faces (R : Type*) [CommRing R] (N : ℕ) :
    (Polynomial.X : Polynomial R) ^ (N + 1) ∣
      (1 - (Polynomial.X : Polynomial R) ^ 2) ^ Fintype.card V *
          ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles a b d
        - (1 - (Polynomial.X : Polynomial R) • (adjacency R a b).map Polynomial.C +
              (Polynomial.X : Polynomial R) ^ 2 • ((degree R a b).map Polynomial.C - 1)).det *
            (1 - (Polynomial.X : Polynomial R) ^ 2) ^ Fintype.card E := by
  rw [← ihara_bass_charpolyRev R a b, ← mul_sub]
  have h1 := ihara_euler_product_ring a b R N
  have h2 : (Polynomial.X : Polynomial R) ^ (N + 1) ∣
      -((hashimoto R a b).charpolyRev
        - ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles a b d) := (dvd_neg).mpr h1
  rw [neg_sub] at h2
  exact Dvd.dvd.mul_left h2 _

/-- [proved-derived; formal-checked] **The three faces, coefficient by coefficient**: up to order
`N` the product over prime cycles with its power of `1 − X²` and Bass's cell determinant with its
power have the same coefficients. -/
theorem ihara_three_faces_coeff (R : Type*) [CommRing R] (N k : ℕ) (hk : k ≤ N) :
    ((1 - (Polynomial.X : Polynomial R) ^ 2) ^ Fintype.card V *
        ∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles a b d).coeff k
      = ((1 - (Polynomial.X : Polynomial R) • (adjacency R a b).map Polynomial.C +
            (Polynomial.X : Polynomial R) ^ 2 • ((degree R a b).map Polynomial.C - 1)).det *
          (1 - (Polynomial.X : Polynomial R) ^ 2) ^ Fintype.card E).coeff k := by
  have h := (Polynomial.X_pow_dvd_iff.mp (ihara_three_faces a b R N)) k (by omega)
  rwa [Polynomial.coeff_sub, sub_eq_zero] at h

end ThreeFaces

/-! ## A ruler: one cell with one loop -/

section Ruler

/-- [definition] The complex of one cell and one contact, a loop. -/
abbrev oneLoop : Unit → Unit := fun _ => ()

/-- [proved-derived; formal-checked] On one loop each dart is followed by itself alone: the dart
operator is the identity on the two darts. -/
theorem dartMatrix_oneLoop : dartMatrix oneLoop oneLoop = 1 := by
  ext d f
  rcases d with ⟨⟩ | ⟨⟩ <;> rcases f with ⟨⟩ | ⟨⟩ <;> simp

/-- [proved-derived; formal-checked] One loop has two prime cycles of one dart, the loop in its
two directions. -/
theorem primeCycles_oneLoop_one : primeCycles oneLoop oneLoop 1 = 2 := by
  rw [primeCycles_one]
  simp

/-- [proved-derived; formal-checked] Every power of one loop's dart operator has trace `2`. -/
theorem trace_dartMatrix_oneLoop_pow (n : ℕ) : (dartMatrix oneLoop oneLoop ^ n).trace = 2 := by
  rw [dartMatrix_oneLoop, one_pow, Matrix.trace_one]
  simp

/-- [proved-derived; formal-checked] One loop has no prime cycle of two darts or more: a longer
closed walk repeats one of the two. -/
theorem primeCycles_oneLoop_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    primeCycles oneLoop oneLoop n = 0 := by
  have h := trace_pow_eq_sum_necklace (dartMatrix oneLoop oneLoop) n (by omega)
  rw [trace_dartMatrix_oneLoop_pow] at h
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    rw [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have hle := Finset.sum_le_sum_of_subset
    (f := fun d => d * necklaceCount (dartMatrix oneLoop oneLoop) d) hsub
  rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ n)] at hle
  have h1 : necklaceCount (dartMatrix oneLoop oneLoop) 1 = 2 := primeCycles_oneLoop_one
  rw [← h, h1] at hle
  have h0 : n * necklaceCount (dartMatrix oneLoop oneLoop) n = 0 := by omega
  rcases Nat.mul_eq_zero.mp h0 with h' | h'
  · omega
  · exact h'

/-- [proved-derived; formal-checked] One loop's dart determinant is `(1 − X)²`. -/
theorem charpolyRev_oneLoop :
    (hashimoto ℚ oneLoop oneLoop).charpolyRev = (1 - Polynomial.X) ^ 2 := by
  have h1 : hashimoto ℚ oneLoop oneLoop = 1 := by
    rw [← dartMatrix_map oneLoop oneLoop ℚ, dartMatrix_oneLoop]
    exact Matrix.map_one _ Nat.cast_zero Nat.cast_one
  have h2 : (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (Polynomial ℚ))
      - (Polynomial.X : Polynomial ℚ) • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) (Polynomial ℚ))
      = (1 - Polynomial.X : Polynomial ℚ) • 1 := by
    rw [sub_smul, one_smul]
  rw [h1, Matrix.charpolyRev, Matrix.map_one _ (map_zero _) (map_one _), h2, Matrix.det_smul,
    Matrix.det_one, mul_one]
  simp

/-- [proved-derived; formal-checked] One loop's product over prime cycles is `(1 − X)²` at every
horizon `N ≥ 1`, the dart determinant itself. -/
theorem prod_oneLoop (N : ℕ) (hN : 1 ≤ N) :
    (∏ d ∈ Icc 1 N, (1 - Polynomial.X ^ d) ^ primeCycles oneLoop oneLoop d : Polynomial ℚ)
      = (1 - Polynomial.X) ^ 2 := by
  rw [Finset.prod_eq_single 1]
  · rw [primeCycles_oneLoop_one, pow_one]
  · intro d hd hd1
    have hd' := (mem_Icc.mp hd).1
    rw [primeCycles_oneLoop_of_two_le d (by omega), pow_zero]
  · intro h
    exact absurd (mem_Icc.mpr ⟨le_rfl, hN⟩) h

end Ruler

section Audit

#print axioms dartMatrix_map
#print axioms edge_ext
#print axioms loopEquiv
#print axioms minimalPeriod_loopEquiv
#print axioms card_closedWalk
#print axioms card_closedWalk_eq_trace
#print axioms card_primitive_closedWalk
#print axioms primeCycles_eq_primitiveCount
#print axioms trace_hashimoto_pow
#print axioms primeCycles_moebius
#print axioms primeCycles_one
#print axioms ihara_euler_product_coeff
#print axioms ihara_euler_product
#print axioms ihara_euler_product_int
#print axioms ihara_euler_product_ring
#print axioms ihara_zeta_euler_product_coeff
#print axioms ihara_three_faces
#print axioms ihara_three_faces_coeff
#print axioms primeCycles_oneLoop_one
#print axioms primeCycles_oneLoop_of_two_le
#print axioms charpolyRev_oneLoop
#print axioms prod_oneLoop

end Audit

end Holonics.Landmarks.IharaEulerProduct
