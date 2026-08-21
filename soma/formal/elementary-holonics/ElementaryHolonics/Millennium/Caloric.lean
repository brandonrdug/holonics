import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import ElementaryHolonics.Millennium.Ricci

/-!
# Caloric: the exact heat carrier over ℚ, and the aperture that belongs to the carrier

The backward heat problem is the standard example of an irreversible transport.  The sharpest
form of the question is a property of a *domain* rather than of the operator.  Li and Šverák
(*Backward uniqueness for the heat equation in cones*, CPDE 37 (2012); arXiv:1011.2796) state it
as: an open set `Ω ⊆ ℝⁿ` has the backward uniqueness property when a bounded solution of the heat
equation on `Ω × (0,T)` that vanishes at the final time vanishes identically, **with no assumption
whatever at the parabolic boundary**.  Escauriaza showed the property *fails* on a cone of opening
less than a right angle, by carrying a Gaussian-decaying harmonic function through the Appell
transformation `u(x,t) = Γ(x,t)·v(x/t, 1/t)`; Wu and Wang (arXiv:1310.6249) and Rüland
(*manuscripta math.* 2015; arXiv:1310.6655) closed the positive side down to about 99° and 95°.
Whether the critical opening is exactly a right angle is open, and the general-domain reduction
attributed to Gurarii and Matsaev has, in both citing papers' own words, no proof in print.

**This file touches none of that.**  It builds the one place where the whole flow can be carried
exactly over `ℚ` — the heat polynomials `v₀ = 1`, `v_{n+1} = x·v_n + 2t·∂ₓv_n` (Widder's classical
carrier) — and proves what the flow does there:

* **the recurrence solves the heat equation**: `∂_t v_n = ∂ₓ² v_n`, over `MvPolynomial (Fin 2) ℚ`
  with `pderiv`, by induction, with the commutation of the two partials proved rather than assumed;
* **the family is an Appell sequence**: `∂ₓ v_{n+1} = (n+1)·v_n`, exactly;
* **the time-reversal at `t = −1/2` is mathlib's Hermite polynomial**, `v_n(x, −1/2) = Heₙ(x)`.
  This is the join mathlib does not carry: it owns `Polynomial.hermite` with its recursion and it
  owns `hermite_eq_deriv_gaussian` — both ends of the Appell pair — and owns no heat equation
  between them;
* **the truncated exponential flow** `E N τ = Σ_{k≤N} (τ^k/k!)·(d²/dx²)^k` on `ℚ[x]`, realized as
  `Polynomial.aeval` of a nilpotent operator so that composition *is* polynomial multiplication;
* **the backward flow has no aperture**: `E N (−τ) (E N τ p) = p` for every rational `τ` and every
  `p` of degree at most `N`, with no exceptional value; hence `E N τ` is injective on the window
  and `E N τ − 1` is nilpotent of order at most `N + 1`, so the flow's only eigenvalue is `1`;
* **the two frames disagree, and the disagreement is the reading.**  `Millennium/Ricci.lean`'s
  triangle flow contracts its deviation at `1 − 3τ` and *collapses many-to-one at exactly*
  `τ = 1/3`; the polynomial carrier has no such value.  So the aperture is a property of the
  carrier — of the three-cycle's winding spectrum — and not of diffusion.

**What this file does not claim, stated first because a reader will otherwise hear it.**  That the
backward flow is invertible here is a fact about **nilpotency**: `d²/dx²` is nilpotent on every
degree-`≤N` window, and the exponential of a nilpotent operator is unipotent, hence invertible.
It is not evidence that backward heat is well posed, and `Ricci.theFlowIsInvertibleWithTestimony`
should not be read that way either — "invertible away from the determinant's zero locus" is true
of every linear map.  The non-vacuous residue is the negative one, and it is the reason to run the
deed: `theNilpotencyOrderIsNotUniform` exhibits, for every window, a construction outside it, so no
single window carries every polynomial and the classical counterexample — current entering from
infinity along a narrow cone — lives in no polynomial or finite carrier at all.  Nothing here
bears on the backward uniqueness property, on the `(PI) ⟺ (PII)` equivalence, or on any critical
opening angle.  The reading that the Appell transformation is "a half-turn whose square is parity"
is **withdrawn**: the normalisation was never checked end to end, so `theParabolicScalingIsHomogeneous`
and `theSpaceParityIsTheDegreeSign` below are stated as what they are — parabolic homogeneity and
the degree sign — and carry no half-turn interpretation.  The sector aperture `α·θ = π` is a
cone-only coordinate and has no referent for a general domain.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`, from
`soma/formal/elementary-holonics/.lake/packages/mathlib`:
`grep -rli "heat equation\|heatKernel" Mathlib --include='*.lean'` → **0 files**;
`grep -rli "caloric" Mathlib --include='*.lean'` → **0**;
`grep -rli "appell" Mathlib --include='*.lean'` → **0**;
`grep -rli "backward uniqueness" Mathlib --include='*.lean'` → **0**;
`grep -rli "hermite" Mathlib --include='*.lean'` → **3**.  Name searches over a stated scope, not
content-absence proofs.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on any
named conjecture: the classical backward-uniqueness problem is carried as cited prose and as the
two named propositions of the last section, which are stated and not proved.
-/

namespace Soma.Holonics.Millennium.Caloric

open MvPolynomial

/-! ## 1. The exact caloric carrier over ℚ

Two variables: `X 0` is the space coordinate, `X 1` the time coordinate. -/

/-- The caloric carrier: rational polynomials in one space and one time coordinate. -/
abbrev Cal : Type := MvPolynomial (Fin 2) ℚ

/-- **The two partials commute.**  Proved rather than assumed; mathlib's `pderiv` carries no such
lemma, and the heat equation below cannot be closed without it. -/
theorem theSpacePartialsCommute (i j : Fin 2) (q : Cal) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rfl
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, pderiv_X, Pi.single_apply]
      by_cases h1 : k = i <;> by_cases h2 : k = j <;>
        (try simp [h1, h2, hij, hij.symm, hp]) <;> ring

/-- The heat polynomials: `v₀ = 1` and `v_{n+1} = x·v_n + 2t·∂ₓv_n`.  Widder's classical carrier,
here exact over `ℚ`. -/
noncomputable def heatPoly : ℕ → Cal
  | 0 => 1
  | n + 1 => X 0 * heatPoly n + C 2 * X 1 * pderiv 0 (heatPoly n)

theorem heatPoly_succ (n : ℕ) :
    heatPoly (n + 1) = X 0 * heatPoly n + C 2 * X 1 * pderiv 0 (heatPoly n) := rfl

/-- **The recurrence solves the heat equation**: `∂_t v_n = ∂ₓ² v_n`, exactly, for every `n`. -/
theorem theCaloricRecurrenceSolvesTheHeatEquation (n : ℕ) :
    pderiv 1 (heatPoly n) = pderiv 0 (pderiv 0 (heatPoly n)) := by
  induction n with
  | zero => simp [heatPoly]
  | succ n ih =>
      have hcomm : pderiv 1 (pderiv 0 (heatPoly n))
          = pderiv 0 (pderiv 0 (pderiv 0 (heatPoly n))) := by
        rw [theSpacePartialsCommute 1 0, ih]
      simp only [heatPoly, Derivation.leibniz, smul_eq_mul, map_add, pderiv_X, Pi.single_apply,
        pderiv_C, ih, hcomm]
      norm_num [map_ofNat]
      ring

/-- **The family is an Appell sequence**: `∂ₓ v_{n+1} = (n+1)·v_n`.  This is what makes the
time-reversal below structural rather than a coincidence of small cases. -/
theorem theCaloricFamilyIsAnAppellSequence (n : ℕ) :
    pderiv 0 (heatPoly (n + 1)) = C ((n : ℚ) + 1) * heatPoly n := by
  induction n with
  | zero => simp [heatPoly]
  | succ n ih =>
      have hrec : heatPoly (n + 2)
          = X 0 * heatPoly (n + 1) + C 2 * X 1 * (C ((n : ℚ) + 1) * heatPoly n) := by
        rw [heatPoly_succ (n + 1), ih]
      rw [hrec]
      simp only [Derivation.leibniz, smul_eq_mul, map_add, pderiv_X, Pi.single_apply,
        pderiv_C, ih]
      norm_num
      rw [heatPoly_succ n]
      ring

/-- **The carrier, exhibited.**  The first four nonconstant members, computed from the recurrence
through the Appell identity. -/
theorem theFirstCaloricPolynomials :
    heatPoly 1 = X 0 ∧
    heatPoly 2 = X 0 ^ 2 + 2 * X 1 ∧
    heatPoly 3 = X 0 ^ 3 + 6 * X 0 * X 1 ∧
    heatPoly 4 = X 0 ^ 4 + 12 * X 0 ^ 2 * X 1 + 12 * X 1 ^ 2 := by
  have h0 : heatPoly 0 = 1 := rfl
  have h1 : heatPoly 1 = X 0 := by rw [heatPoly_succ, h0]; simp
  have h2 : heatPoly 2 = X 0 ^ 2 + 2 * X 1 := by
    rw [heatPoly_succ 1, theCaloricFamilyIsAnAppellSequence 0, h0, h1]
    norm_num [map_ofNat]
    ring
  have h3 : heatPoly 3 = X 0 ^ 3 + 6 * X 0 * X 1 := by
    rw [heatPoly_succ 2, theCaloricFamilyIsAnAppellSequence 1, h1, h2]
    norm_num [map_ofNat]
    ring
  refine ⟨h1, h2, h3, ?_⟩
  rw [heatPoly_succ 3, theCaloricFamilyIsAnAppellSequence 2, h2, h3]
  norm_num [map_ofNat]
  ring

/-! ## 2. The time chart, and the Appell time-reversal onto mathlib's Hermite family -/

/-- Reading the carrier at one rational time: `x ↦ x`, `t ↦ τ`.  A chart from the two-variable
carrier onto `ℚ[x]`. -/
noncomputable def atTime (τ : ℚ) : Cal →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C τ]

@[simp] theorem atTime_X0 (τ : ℚ) : atTime τ (X 0) = Polynomial.X := by simp [atTime]

@[simp] theorem atTime_X1 (τ : ℚ) : atTime τ (X 1) = Polynomial.C τ := by simp [atTime]

/-- **The time chart carries the space derivative.**  Substituting a constant for the time
coordinate commutes with `∂ₓ`; without this the identification below cannot be run. -/
theorem theTimeChartCarriesTheSpaceDerivative (τ : ℚ) (q : Cal) :
    atTime τ (pderiv 0 q) = Polynomial.derivative (atTime τ q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp [atTime]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => fin_cases k <;> simp [Derivation.leibniz, hp, mul_comm]

/-- **The carrier starts at the monomials**: `v_n(x, 0) = xⁿ`.  So `v_n` is the heat evolution of
the monomial and nothing else. -/
theorem theCaloricCarrierStartsAtTheMonomials (n : ℕ) :
    atTime 0 (heatPoly n) = Polynomial.X ^ n := by
  induction n with
  | zero => simp [heatPoly]
  | succ n ih => simp [heatPoly, ih]; ring

/-- **The Appell time-reversal is the Hermite polynomial**: `v_n(x, −1/2) = Heₙ(x)`, mathlib's
probabilists' `Polynomial.hermite` mapped into `ℚ[x]`.  Running the heat flow backwards by exactly
`1/2` carries the heat polynomials onto the Hermite family; mathlib owns that family and owns
`hermite_eq_deriv_gaussian`, the other end of the Appell pair, and owns nothing joining them. -/
theorem theAppellTimeReversalIsTheHermitePolynomial (n : ℕ) :
    atTime (-(1 / 2)) (heatPoly n) = (Polynomial.hermite n).map (Int.castRingHom ℚ) := by
  induction n with
  | zero => simp [heatPoly]
  | succ n ih =>
      have hC : (C 2 : Cal) = 2 := map_ofNat _ _
      simp only [heatPoly, map_add, map_mul, atTime_X0, atTime_X1, hC, map_ofNat,
        theTimeChartCarriesTheSpaceDerivative, ih, Polynomial.hermite_succ,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Polynomial.derivative_map]
      have key : (Polynomial.C (-(1 / 2) : ℚ)) * 2 = -1 := by
        rw [show ((2 : Polynomial ℚ)) = Polynomial.C 2 from (map_ofNat Polynomial.C 2).symm,
          ← Polynomial.C_mul]
        norm_num
      linear_combination
        (Polynomial.map (Int.castRingHom ℚ) (Polynomial.derivative (Polynomial.hermite n))) * key

/-! ## 3. The parabolic scaling, and the degree sign

These are stated as what they are.  The reading that they are shadows of a "half-turn whose square
is parity" is withdrawn: the Appell normalisation behind it was never checked end to end. -/

/-- The parabolic scaling `x ↦ l·x`, `t ↦ l²·t` — the symmetry the heat operator has because
`|x|² ~ t`. -/
noncomputable def scaleP (l : ℚ) : Cal →ₐ[ℚ] Cal :=
  MvPolynomial.aeval ![C l * X 0, C (l ^ 2) * X 1]

@[simp] theorem scaleP_X0 (l : ℚ) : scaleP l (X 0) = C l * X 0 := by simp [scaleP]

@[simp] theorem scaleP_X1 (l : ℚ) : scaleP l (X 1) = C (l ^ 2) * X 1 := by simp [scaleP]

/-- The chain rule for the parabolic scaling. -/
theorem theScalingChainRule (l : ℚ) (q : Cal) :
    pderiv 0 (scaleP l q) = C l * scaleP l (pderiv 0 q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [scaleP]
  | add p q hp hq => simp [hp, hq, mul_add]
  | mul_X p k hp => fin_cases k <;> simp [Derivation.leibniz, hp, mul_add] <;> ring

/-- **The carrier is parabolically homogeneous**: `v_n(l·x, l²·t) = lⁿ·v_n(x, t)`, for every
rational `l`, including `l = 0`. -/
theorem theParabolicScalingIsHomogeneous (l : ℚ) (n : ℕ) :
    scaleP l (heatPoly n) = C (l ^ n) * heatPoly n := by
  induction n with
  | zero => simp [heatPoly]
  | succ n ih =>
      have hd : C l * scaleP l (pderiv 0 (heatPoly n)) = C (l ^ n) * pderiv 0 (heatPoly n) := by
        have h := congrArg (fun q : Cal => pderiv 0 q) ih
        simpa [theScalingChainRule, pderiv_C_mul] using h
      have hC2 : (C 2 : Cal) = 2 := map_ofNat _ _
      rw [heatPoly_succ n]
      simp only [map_add, map_mul, scaleP_X0, scaleP_X1, ih, hC2, map_ofNat]
      have e1 : (C (l ^ (n + 1)) : Cal) = C l * C (l ^ n) := by
        rw [← map_mul]; congr 1; ring
      have e2 : (C (l ^ 2) : Cal) = C l * C l := by
        rw [← map_mul]; congr 1; ring
      rw [e1, e2]
      linear_combination (2 * X 1 * C l) * hd

/-- **The degree sign**: `v_n(−x, t) = (−1)ⁿ·v_n(x, t)`, the parabolic scaling at `l = −1`. -/
theorem theSpaceParityIsTheDegreeSign (n : ℕ) :
    MvPolynomial.aeval ![-X 0, X 1] (heatPoly n) = C ((-1 : ℚ) ^ n) * heatPoly n := by
  have hmap : (![C (-1 : ℚ) * X 0, C ((-1 : ℚ) ^ 2) * X 1] : Fin 2 → Cal) = ![-X 0, X 1] := by
    funext i; fin_cases i <;> simp
  have h := theParabolicScalingIsHomogeneous (-1) n
  simpa only [scaleP, hmap] using h

/-! ## 4. The time flow on the carrier

Translation of the time coordinate.  On the caloric family this *is* the heat evolution, because
`v_n` solves the heat equation; the group law is then substitution composition and costs nothing. -/

/-- The heat evolution by rational time `τ`, read on the carrier as translation of the time
coordinate. -/
noncomputable def flowT (τ : ℚ) : Cal →ₐ[ℚ] Cal :=
  MvPolynomial.aeval ![X 0, X 1 + C τ]

@[simp] theorem flowT_X0 (τ : ℚ) : flowT τ (X 0) = X 0 := by simp [flowT]

@[simp] theorem flowT_X1 (τ : ℚ) : flowT τ (X 1) = X 1 + C τ := by simp [flowT]

@[simp] theorem flowT_zero (q : Cal) : flowT 0 q = q := by
  have h : (![X 0, X 1 + C (0 : ℚ)] : Fin 2 → Cal) = fun i => X i := by
    funext i; fin_cases i <;> simp
  simp only [flowT, h, MvPolynomial.aeval_X_left_apply]

/-- **The time flow composes additively.** -/
theorem theTimeFlowComposesAdditively (σ τ : ℚ) (q : Cal) :
    flowT σ (flowT τ q) = flowT (σ + τ) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [flowT]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      rw [map_mul, map_mul, map_mul, hp]
      congr 1
      fin_cases k
      · simp
      · simp [map_add]; ring

/-- **The backward time flow has no aperture on the carrier**: every rational time is undone
exactly, with no exceptional value. -/
theorem theBackwardTimeFlowHasNoAperture (τ : ℚ) (q : Cal) : flowT (-τ) (flowT τ q) = q := by
  rw [theTimeFlowComposesAdditively]
  simp

/-! ## 5. The truncated exponential flow on `ℚ[x]`, and the backward identity

`E N τ = Σ_{k ≤ N} (τ^k/k!)·(d²/dx²)^k`, realized as `Polynomial.aeval` of the operator `d²/dx²`
inside `Module.End ℚ ℚ[X]`.  Realizing it that way is the whole trick: composition of two flows
becomes multiplication of two polynomials, so the Cauchy product is done by `Polynomial.coeff_mul`
and never by hand. -/

/-- The space Laplacian on `ℚ[x]`, as an endomorphism. -/
noncomputable def laplace : Module.End ℚ (Polynomial ℚ) :=
  (Polynomial.derivative (R := ℚ)) ∘ₗ (Polynomial.derivative (R := ℚ))

theorem laplacePow (k : ℕ) (p : Polynomial ℚ) :
    (laplace ^ k) p = (Polynomial.derivative (R := ℚ))^[2 * k] p := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      rw [pow_succ', h]
      simp only [Module.End.mul_apply, ih, Function.iterate_succ_apply']
      rfl

/-- The truncated exponential, as a polynomial in one formal variable. -/
noncomputable def expTrunc (N : ℕ) (τ : ℚ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (τ ^ k / (Nat.factorial k : ℚ)) * Polynomial.X ^ k

theorem expTruncCoeff (N : ℕ) (τ : ℚ) (j : ℕ) :
    (expTrunc N τ).coeff j = if j ≤ N then τ ^ j / (Nat.factorial j : ℚ) else 0 := by
  simp only [expTrunc, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) j (fun k => τ ^ k / (Nat.factorial k : ℚ))]
  simp

/-- The heat flow by rational time `τ` on the degree-`≤N` window of `ℚ[x]`. -/
noncomputable def E (N : ℕ) (τ : ℚ) : Module.End ℚ (Polynomial ℚ) :=
  Polynomial.aeval laplace (expTrunc N τ)

/-- **The flow is the truncated heat series**, written out: `E N τ p = Σ_{k≤N} (τ^k/k!)·p^{(2k)}`.
The `aeval` presentation above is a compilation of exactly this sum. -/
theorem theFlowIsTheTruncatedHeatSeries (N : ℕ) (τ : ℚ) (p : Polynomial ℚ) :
    E N τ p = ∑ k ∈ Finset.range (N + 1),
      (τ ^ k / (Nat.factorial k : ℚ)) • (Polynomial.derivative (R := ℚ))^[2 * k] p := by
  simp only [E, expTrunc, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← laplacePow]
  simp [Algebra.smul_def]

/-- **Opposite times cancel below the window.**  Every coefficient of index at most `N` in the
product `expTrunc N (−τ) · expTrunc N τ` is that of `1`.  This is the binomial theorem read through
`Polynomial.coeff_mul`; the coefficients of index above `N` are *not* claimed to vanish, and do
not have to. -/
theorem theOppositeTimesCancelBelowTheWindow (N : ℕ) (τ : ℚ) {m : ℕ} (hm : m ≤ N) :
    (expTrunc N (-τ) * expTrunc N τ).coeff m = if m = 0 then 1 else 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hfac : ((Nat.factorial m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have step : ∀ j ∈ Finset.range (m + 1),
      (expTrunc N (-τ)).coeff j * (expTrunc N τ).coeff (m - j)
        = ((-τ) ^ j * τ ^ (m - j) * (m.choose j : ℚ)) / (Nat.factorial m : ℚ) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : ((Nat.factorial j : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have h2 : ((Nat.factorial (m - j) : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - j))
    rw [expTruncCoeff, expTruncCoeff, if_pos (hjm.trans hm),
      if_pos ((Nat.sub_le m j).trans hm), Nat.cast_choose ℚ hjm]
    field_simp
  rw [Finset.sum_congr rfl step, ← Finset.sum_div]
  have hz : ∑ j ∈ Finset.range (m + 1), ((-τ) ^ j * τ ^ (m - j) * (m.choose j : ℚ))
      = (0 : ℚ) ^ m := by
    rw [← add_pow]; ring_nf
  rw [hz]
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · have hne : m ≠ 0 := hpos.ne'
    simp [hne, zero_pow hne]

/-- **The window kills the high-order part.**  An operator polynomial whose coefficients vanish
below index `N + 1` annihilates every construction of degree at most `N`, because `d²/dx²` is
nilpotent there.  This is the nilpotency, isolated, so that everything downstream can name it. -/
theorem theWindowKillsTheHighOrderPart {N : ℕ} {q p : Polynomial ℚ}
    (hp : p.natDegree ≤ N) (hq : ∀ i ≤ N, q.coeff i = 0) :
    (Polynomial.aeval laplace q) p = 0 := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro i _
  rcases le_or_gt i N with h | h
  · rw [hq i h]; simp
  · have hz : (laplace ^ i) p = 0 := by
      rw [laplacePow]
      exact Polynomial.iterate_derivative_eq_zero (by omega)
    simp [hz]

/-- **The backward flow has no aperture**: `E N (−τ) (E N τ p) = p` for *every* rational `τ` and
every `p` of degree at most `N`.  There is no exceptional value, in contrast with the finite cycle
carrier of `Millennium/Ricci.lean`.  Read it as a statement about the carrier: the exponential of a
nilpotent operator is unipotent. -/
theorem theBackwardFlowHasNoAperture (N : ℕ) (τ : ℚ) {p : Polynomial ℚ}
    (hp : p.natDegree ≤ N) : E N (-τ) (E N τ p) = p := by
  have hkill : (Polynomial.aeval laplace (expTrunc N (-τ) * expTrunc N τ - 1)) p = 0 := by
    refine theWindowKillsTheHighOrderPart hp ?_
    intro i hi
    rw [Polynomial.coeff_sub, theOppositeTimesCancelBelowTheWindow N τ hi, Polynomial.coeff_one]
    simp
  have hcomp : E N (-τ) (E N τ p)
      = (Polynomial.aeval laplace (expTrunc N (-τ) * expTrunc N τ)) p := by
    rw [map_mul]; rfl
  have hsplit : Polynomial.aeval laplace (expTrunc N (-τ) * expTrunc N τ)
      = Polynomial.aeval laplace (expTrunc N (-τ) * expTrunc N τ - 1) + 1 := by
    rw [map_sub, map_one]; abel
  rw [hcomp, hsplit, LinearMap.add_apply, hkill, zero_add]
  rfl

/-- **Every monomial comes back**, which is the falsifier the reading names: run `xᵐ` forward by
`τ` and back by `τ` and the monomial returns, for every rational `τ` and every `m ≤ N`. -/
theorem theBackwardFlowRecoversEveryMonomial (N m : ℕ) (τ : ℚ) (h : m ≤ N) :
    E N (-τ) (E N τ (Polynomial.X ^ m)) = Polynomial.X ^ m := by
  refine theBackwardFlowHasNoAperture N τ ?_
  simpa using h

/-- **The flow is injective on its window**, at every rational time — nothing is collapsed. -/
theorem theCaloricFlowIsInjectiveOnItsWindow (N : ℕ) (τ : ℚ) {p q : Polynomial ℚ}
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) (h : E N τ p = E N τ q) : p = q := by
  have hb := theBackwardFlowHasNoAperture N τ hp
  rw [h, theBackwardFlowHasNoAperture N τ hq] at hb
  exact hb.symm

/-- **The flow's only eigenvalue is one**: `E N τ − 1` is nilpotent of order at most `N + 1` on the
window.  A flow whose spectrum is `{1}` has no value at which a mode dies, which is exactly what
the cycle carrier does have. -/
theorem theDifferenceIsNilpotentOnTheWindow (N : ℕ) (τ : ℚ) {p : Polynomial ℚ}
    (hp : p.natDegree ≤ N) : ((E N τ - 1) ^ (N + 1)) p = 0 := by
  have h1 : E N τ - 1 = Polynomial.aeval laplace (expTrunc N τ - 1) := by
    rw [map_sub, map_one]; rfl
  have h2 : (E N τ - 1) ^ (N + 1) = Polynomial.aeval laplace ((expTrunc N τ - 1) ^ (N + 1)) := by
    rw [h1, ← map_pow]
  rw [h2]
  refine theWindowKillsTheHighOrderPart hp ?_
  intro i hi
  have hdvd : (Polynomial.X : Polynomial ℚ) ^ (N + 1) ∣ (expTrunc N τ - 1) ^ (N + 1) := by
    refine pow_dvd_pow_of_dvd ?_ _
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, expTruncCoeff, Polynomial.coeff_one]
    simp
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, mul_comm, Polynomial.coeff_mul_X_pow', if_neg (by omega)]

/-! ## 6. The two presentations agree, exhibited

The two constructions above — the recurrence carrier `v_n(x, t)` and the exponential series
`E N τ` — are the same object.  The general identity is named in the last section and is not
proved here; what is proved is the table. -/

/-- **The series agrees with the recurrence**, at degrees two and three, for every rational time.
`E 3 τ (x²) = x² + 2τ` and `E 3 τ (x³) = x³ + 6τx`, which are `v₂(x, τ)` and `v₃(x, τ)`. -/
theorem theSeriesAgreesWithTheRecurrenceThroughDegreeThree (τ : ℚ) :
    E 3 τ (Polynomial.X ^ 2) = atTime τ (X 0 ^ 2 + 2 * X 1) ∧
    E 3 τ (Polynomial.X ^ 3) = atTime τ (X 0 ^ 3 + 6 * X 0 * X 1) := by
  constructor <;>
  · rw [theFlowIsTheTruncatedHeatSeries]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Function.iterate_succ_apply',
      Function.iterate_zero_apply, atTime, map_add, map_mul, map_pow, MvPolynomial.aeval_X,
      Polynomial.derivative_X_pow, Polynomial.smul_eq_C_mul, map_ofNat]
    norm_num
    simp only [map_ofNat]
    ring

/-! ## 7. Two frames, and what their disagreement measures -/

/-- **The aperture belongs to the carrier, not to the operator.**  Four facts side by side.  On the
three-cycle of `Millennium/Ricci.lean` the roundness reading obeys `W' = (1 − 3τ)²·W`, so the
deviation dies at `τ = 1/3` and the flow there is many-to-one by witness — two different terrains
land on one round triangle.  On the polynomial carrier the flow is invertible at every rational
`τ`, and its difference from the identity is nilpotent, so its spectrum is `{1}` and no value
exists at which a mode can die.  The value `1/3` is the vanishing of a *winding eigenvalue* of the
three-cycle, `1 − 2τ + 2τ·cos(2π/3)`; it is a fact about that terrain and not about diffusion. -/
theorem theTwoCarriersDisagreeAboutTheAperture :
    (∀ (τ : ℚ) (l : Ricci.Tri), Ricci.W (Ricci.flow τ l) = (1 - 3 * τ) ^ 2 * Ricci.W l) ∧
    Ricci.flow (1 / 3) ((0 : ℚ), 1, 2) = Ricci.flow (1 / 3) ((1 : ℚ), 1, 1) ∧
    (∀ (N : ℕ) (τ : ℚ) (p : Polynomial ℚ), p.natDegree ≤ N → E N (-τ) (E N τ p) = p) ∧
    (∀ (N : ℕ) (τ : ℚ) (p : Polynomial ℚ), p.natDegree ≤ N → ((E N τ - 1) ^ (N + 1)) p = 0) :=
  ⟨fun τ l => Ricci.theReadingObeysItsExactRate τ l,
    Ricci.theCollapseApertureDeletes.2,
    fun N τ _p hp => theBackwardFlowHasNoAperture N τ hp,
    fun N τ _p hp => theDifferenceIsNilpotentOnTheWindow N τ hp⟩

/-- **The nilpotency order is not uniform**, and this is the honest residue of the whole section.
Every window `N` has a construction outside it, so the invertibility above is never a statement
about `ℚ[x]` as a whole and can never become one.  What the classical counterexample requires —
current entering from infinity — is exactly what no finite window admits. -/
theorem theNilpotencyOrderIsNotUniform (N : ℕ) :
    ∃ p : Polynomial ℚ, (Polynomial.derivative (R := ℚ))^[2 * (N + 1)] p ≠ 0 := by
  refine ⟨Polynomial.X ^ (2 * (N + 1)), ?_⟩
  rw [Polynomial.iterate_derivative_X_pow_eq_natCast_mul]
  simp

/-! ## 8. What is named and not proved

Two propositions.  Both are real statements; neither is proved here, and neither is a conjecture of
this development. -/

/-- The general identification of the two presentations: the truncated exponential flow of a
monomial is the heat polynomial read at that time.  Classical — it is what Widder's heat
polynomials are — and absent from mathlib, which carries no heat equation at any grain.  Verified
here at degrees two and three by `theSeriesAgreesWithTheRecurrenceThroughDegreeThree`, and outside
Lean by exact rational computation at every degree up to ten. -/
def TheSeriesAgreesWithTheRecurrenceAtEveryDegree : Prop :=
  ∀ (N n : ℕ), n ≤ N → ∀ τ : ℚ, E N τ (Polynomial.X ^ n) = atTime τ (heatPoly n)

/-- The elliptic side of the classical problem, on the plane sector of opening `θ`: a harmonic
function on the open sector minus the origin, nonzero somewhere, bounded in modulus by a Gaussian.
No boundary condition is imposed — that absence is the whole content of the classical statement. -/
def TheSectorCarriesAGaussianDecayingHarmonicRealizer (θ : ℝ) : Prop :=
  ∃ v : ℂ → ℝ, ∃ A : ℝ, 0 < A ∧
    (∀ z : ℂ, z ≠ 0 → |Complex.arg z| < θ / 2 → InnerProductSpace.HarmonicAt v z) ∧
    (∃ z : ℂ, z ≠ 0 ∧ |Complex.arg z| < θ / 2 ∧ v z ≠ 0) ∧
    (∀ z : ℂ, z ≠ 0 → |Complex.arg z| < θ / 2 → |v z| ≤ Real.exp (-A * ‖z‖ ^ 2))

/-- Rüland's elliptic statement, formalized: at opening at least a right angle the sector carries
no Gaussian-decaying harmonic realizer.  Verbatim (arXiv:1310.6655, p. 4): *"In domains of opening
angles greater than or equal to 90° there are no harmonic functions decaying with a Gaussian
rate."*  Classically a theorem, by Phragmén–Lindelöf; mathlib carries Phragmén–Lindelöf for strips,
half-planes and the four quadrants, holomorphic only, and not for a general sector, so this is
stated and not proved.  It is the elliptic half of the classical question; the parabolic half —
the backward uniqueness property itself — is carried in this file's prose only, because
formalizing it needs a caloric object on an unbounded domain, which is exactly what §7 shows no
polynomial carrier supplies. -/
def TheRightAngleRefusesEveryGaussianRealizer : Prop :=
  ∀ θ : ℝ, Real.pi / 2 ≤ θ → θ ≤ Real.pi →
    ¬ TheSectorCarriesAGaussianDecayingHarmonicRealizer θ

end Soma.Holonics.Millennium.Caloric
