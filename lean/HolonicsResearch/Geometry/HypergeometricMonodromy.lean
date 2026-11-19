import HolonicsResearch.Geometry.LegendreLevelTwo
import HolonicsResearch.Geometry.CompleteEllipticSeries

/-!
# Riemann's scheme and rigidity: Legendre's local moves fix `Γ(2)`, the `(½, ⅓, 0)` triangle's fix `PSL(2, ℤ)`

Source: #410's box "Monodromy as a group of moves", its clause left after `Geometry/ModularFreeProduct`,
`Geometry/LegendreLevelTwo` and `Geometry/CompleteEllipticSeries`: "the Schwarz map and its monodromy, and `Γ(2)`
as Legendre's monodromy". `LegendreLevelTwo` gives the group that Legendre's monodromy is claimed to be and leaves
"that `Γ(2)` is the monodromy of Legendre's family" open; `ModularFreeProduct` leaves "the identification of [the
`(½, ⅓, 0)` triangle's] monodromy with this group"; `CompleteEllipticSeries` leaves "the continuation of `K` round
`λ = 0` and `λ = 1`". The record of September 27 on probability as a receiver geometry, §5, states Gauss's
equation and its exponent differences, and names `modular_exponent_differences` as a Lean return. Atlas rows:
`lock.gamma-two-index`, `lock.modular-free-product`, `egg.period-coefficients`, `landmark.hypergeometric-residues`.
This file takes the monodromy side as finite algebra: Riemann's scheme of the operator, Frobenius's logarithm at a
double exponent, and the rigidity that makes the local data fix the group up to a change of frame.

[proved-standard; formal-checked] What is proved.

1. **The operator and its Riemann scheme** (§1). Gauss's operator `L = λ(1 − λ)∂² + (c − (a + b + 1)λ)∂ − ab` on
   `K⟦X⟧` (`op`, Mathlib's derivative) acts on coefficients by
   `[λⁿ] L f = (n + 1)(n + c) f_(n+1) − (n + a)(n + b) fₙ` (`coeff_op`). Its Euler form
   `λL = θ(θ + c − 1) − λ(θ + a)(θ + b)`, `θ = λ d/dλ` (`euler`, `euler_zero`, `euler_eq`, `X_mul_op`), read on
   `λ^r g` for an exponent `r ∈ K` is the twist `twisted a b c r` (Frobenius's device), whose constant coefficient is
   `I₀(r) g₀` (`coeff_zero_twisted`, `coeff_zero_twisted_eq_indicial`, with the recursion `coeff_succ_twisted`), and
   whose action on the monomial is `λL λ^r = r(r + c − 1) λ^r − (r + a)(r + b) λ^(r+1)`
   (`twisted_one`, `twisted_one_eq_indicial`). The indicial polynomials `I₀ = r(r − (1 − c))`,
   `I₁ = r(r − (c − a − b))` and `I_∞ = (s − a)(s − b)` (`indicialZero`, `indicialOne`, `indicialInf`) have the
   roots `{0, 1 − c}`, `{0, c − a − b}`, `{a, b}` (`roots_indicialZero`, `roots_indicialOne`, `roots_indicialInf`),
   and the six exponents sum to `1` (Fuchs' relation, `fuchs`). In the chart `μ = 1/λ` (`twistedInf`) the constant
   coefficient is `I_∞(s) h₀` (`coeff_zero_twistedInf`), the operator is again hypergeometric with parameters
   `(a, a + 1 − c; a − b + 1)` (`twistedInf_eq`), and its monomial action is `twisted_one`'s at `r = −s` with the two
   coefficients exchanged (`twistedInf_one`). On polynomials (`opPoly`, joined to `op` by `op_coe`), `λ ↦ 1 − λ`
   carries `L_(a,b,c)` to `L_(a,b,a+b+1−c)` (`opPoly_comp_one_sub`), so `I₁` is that operator's `I₀`
   (`indicialOne_eq`). Legendre (`a = b = ½`, `c = 1`): exponents `(0, 0)`, `(0, 0)`, `(½, ½)` and an operator
   invariant under `λ ↦ 1 − λ` (`legendre_exponents`, `legendre_comp_one_sub`). The triangle (`a = b = 1/12`,
   `c = ½`): exponents `(0, ½)`, `(0, ⅓)`, `(1/12, 1/12)`, so the differences are `½`, `⅓`, `0`
   (`triangle_exponents`); the record's chart `(1/12, 5/12; 1)` has the differences `0`, `½`, `⅓`
   (`triangle_exponents_cusp_at_zero`).
2. **Frobenius at a double exponent** (§2). The series `hyperSeries a b c` with Mathlib's
   `ordinaryHypergeometricCoefficient` solves `L F = 0` when `c` is not a nonpositive integer (`op_hyperSeries`, from
   the ratio `coeff_hyperSeries_succ`). Legendre's `F = ₂F₁(½, ½; 1; ·)` has `F(0) = 1`,
   `(n + 1)² f_(n+1) = (n + ½)² fₙ` and `L F = 0` (`legendreF`, `coeff_zero_legendreF`, `coeff_legendreF_succ`,
   `op_legendreF`), and over `ℝ` its coefficients are the `wₙ²` of `K(√λ) = (π/2) F(λ)` (`coeff_legendreF_real`).
   A formal logarithm `ℓ` with `θℓ = 1` (`ℓ′ = 1/λ`) is carried by the pair `(A, B) = A + Bℓ`, and `λL` acts on pairs
   by the Leibniz rule (`eulerL`, `mulXL`, `opL`, `opL_pair`). For Legendre,
   `L(Fℓ + G) = ℓ·L F + 2(1 − λ)F′ − F + L G`, multiplied through by `λ` (`legendre_opL`), so `Fℓ + G` is a solution
   iff `L G = F − 2(1 − λ)F′` (`legendre_log_iff`); with `(m + 1)² g_(m+1) − (m + ½)² gₘ = rₘ`
   (`coeff_op_legendre`) that equation has one solution with `G(0) = 0` (`solveCoeff`, `existsUnique_op_eq`,
   `legendre_log_solution`). The substitution `ℓ ↦ ℓ + κ` commutes with `L` on pairs (`shiftLog`, `opL_shiftLog`,
   with `opL_smul`); on the basis `(F, (Fℓ + G)/κ)` of two independent solutions (`legendreBasis`,
   `opL_legendreBasis`, `legendreBasis_linearIndependent`) the move `ℓ ↦ ℓ + 2κ` sends the `j`-th member to
   `Σᵢ Aᵢⱼ eᵢ` with `A = [[1, 2], [0, 1]] = LegendreLevelTwo.A` (`shiftLog_legendreBasis`, the column convention);
   over `ℂ` with `κ = πi` it is the continuation `ℓ ↦ ℓ + 2πi` round `λ = 0` (`continuation_round_zero`).
3. **Rigidity: the local moves fix the group** (§3). Conjugation by `GL(2, K)` on `SL(2, K)` (`toK`, `conjBy`,
   `conjBy_eq_iff`, `conjBy_mul`, `trace_conjBy`, `trace_inv`); a move of trace `2` other than `1` is conjugate to
   `[[1, 1], [0, 1]]` (`exists_conj_shear`). (Legendre) Over `K` with `2 ≠ 0`, `X, Y ∈ SL(2, K)` with
   `tr X = tr Y = 2` and `tr XY = −2` are conjugate to `(A, B⁻¹)`, `B⁻¹ = [[1, 0], [−2, 1]]`
   (`legendre_rigidity`); `X ≠ 1`, `Y ≠ 1` and `XY ≠ −1` follow (`legendre_nontrivial`); and the same conjugation
   carries the group they generate onto the image over `K` of Sanov's range (`legendre_monodromy_group`, with
   `range_sanov`, `closure_pair_inv`), whose image in `PSL(2, ℤ)` is `Γ(2)/±1` (`range_sanov_map_proj`, from
   `LegendreLevelTwo.map_Gamma_two_eq_range`). (`(2, 3, ∞)`) Over any field, `tr X = 0`, `tr Y = 1` and
   `tr XY = −2` give `XY ≠ −1` (`triangle_mul_ne_neg_one`) and a conjugation to `(S, U)`, `U = S T`
   (`triangle_rigidity`), which carries the group they generate onto the image of `SL(2, ℤ)`
   (`triangle_monodromy_group`, with `closure_S_U`); projectively `s` and `u` generate `PSL(2, ℤ)` (`closure_s_u`)
   with orders `2` and `3` (`ModularFreeProduct.orderOf_s`, `ModularFreeProduct.orderOf_u`).
4. **Witnesses** (§4). `tr A = tr B⁻¹ = 2`, `tr(A B⁻¹) = −2` and `A B⁻¹ ≠ −1` (`legendre_witness`); `tr S = 0`,
   `tr U = 1`, `S U = −T` of trace `−2` (`triangle_witness`); `2 cos(π d) = 0, 1, 2` at `d = ½, ⅓, 0`
   (`two_cos_exponent_differences`).

The local data, as a remark. Exponents `ρ₁, ρ₂` at a puncture give a local monodromy with eigenvalues `e^(2πiρ₁)`,
`e^(2πiρ₂)`; scaled to determinant one by a square root of their product, its trace is `±2 cos(π(ρ₁ − ρ₂))`, the
signs chosen so that the three scaled moves still multiply to one. Legendre: at `0` and `1` the eigenvalues are
`1, 1` (trace `2`), and the double exponent brings the logarithm of §2, a nontrivial Jordan block; at `∞` the
exponents `½, ½` give `M_∞ = (M₀M₁)⁻¹` the eigenvalue `−1` twice, so `tr M₀M₁ = −2`: the hypotheses of
`legendre_rigidity`, whose conclusion makes the Jordan blocks forced (`legendre_nontrivial`). The triangle: the
scaled moves at `0` and `1` have traces `2 cos(π/2) = 0` and `2 cos(π/3) = 1`; at `∞` the exponents `1/12, 1/12`
give the eigenvalue `e^(πi/6)` twice, and the scaling `e^(5πi/6)` that the product fixes makes it `−1`, so
`tr XY = −2`: the hypotheses of `triangle_rigidity`.

What is not claimed. The analytic continuation of the periods: that the monodromy representation of Gauss's
equation on its solutions near a base point has these local data (the formal `ℓ` read as `log λ`, the continuation
round `λ = 0` read as `ℓ ↦ ℓ + 2πi`, the scaling at `∞`). The convergence of `G`. The connection matrix between the
bases at `0` and at `1`, so that `M₁ = B⁻¹` in the basis adapted to `0` is read from rigidity, not computed from
Legendre's periods. The Schwarz map as a conformal map of the upper half plane onto the triangle, its inverse
`1728/j`, and the `j`-function. The conjugations are in `GL(2, K)`, not in `SL(2, K)` or `GL(2, ℤ)`; Sanov's range
is the part of `Γ(2)` without `−1` (`LegendreLevelTwo.neg_one_not_mem_levelFour`), and `Γ(2)` itself enters through
its image in `PSL(2, ℤ)`. Legendre's rigidity is stated for `2 ≠ 0` only. The box stays part done.

The computational object is the helical pair interaction: a pair of solutions of a second-order equation is a
pair whose ratio is the Schwarz map, and continuing round a puncture moves the pair. The formal logarithm is the
helix's carry: one round of `λ = 0` adds the whole turn `2πi` to `ℓ`, the lift and carry of a ratio, and at a
double exponent the move is a pure shear, the free-fall factor of the swing's turn · boost · shear,
`A = [[1, 2], [0, 1]]`. The exponent differences are the local turn rates: `½` and `⅓` give the half-turn `S` and
the third of a turn `U`, `0` the shear at the cusp; rigidity says that the three local moves, whose product is one,
fix the pair's whole group of moves up to a change of frame. Of the winding guide's six general objects this
touches the helix (the carry `ℓ ↦ ℓ + 2πi`), the pair (the moves of a pair of solutions and their conjugation) and
the cell holonomy (the local moves round `0`, `1`, `∞`); faces and placement, the tube and the tower thread stay
attached.

Consumers: the #410 box "Monodromy as a group of moves"; the atlas rows `lock.gamma-two-index`,
`lock.modular-free-product` and `landmark.hypergeometric-residues` (the local turn differences `1 − c`, `c − a − b`,
`a − b`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Geometry.HypergeometricMonodromy

open PowerSeries
open scoped MatrixGroups Polynomial

variable {K : Type*} [Field K]

/-! ## 1. The operator and its Riemann scheme -/

/-- [definition] The Euler operator shifted by `s`, `θ + s` with `θ = λ d/dλ`, coefficient by coefficient. -/
def euler (s : K) (g : K⟦X⟧) : K⟦X⟧ := mk fun n => ((n : K) + s) * coeff n g

/-- [proved-standard; formal-checked] The `n`-th coefficient of `(θ + s) g` is `(n + s) gₙ`. -/
@[simp] theorem coeff_euler (s : K) (g : K⟦X⟧) (n : ℕ) :
    coeff n (euler s g) = ((n : K) + s) * coeff n g := coeff_mk _ _

/-- [proved-standard; formal-checked] `θ = λ d/dλ`: the unshifted Euler operator is `X` times the derivative. -/
theorem euler_zero (g : K⟦X⟧) : euler 0 g = X * d⁄dX K g := by
  ext n; rcases n with _ | n <;> simp [coeff_succ_X_mul, coeff_derivative, mul_comm]

/-- [proved-standard; formal-checked] `θ + s = λ d/dλ + s`. -/
theorem euler_eq (s : K) (g : K⟦X⟧) : euler s g = X * d⁄dX K g + C s * g := by
  ext n; rcases n with _ | n <;> simp [coeff_succ_X_mul, coeff_derivative, coeff_zero_X_mul,
    -coeff_zero_eq_constantCoeff]
  ring

/-- [definition] Gauss's hypergeometric operator `L = λ(1 − λ)∂² + (c − (a + b + 1)λ)∂ − ab` on `K⟦X⟧`. -/
def op (a b c : K) (f : K⟦X⟧) : K⟦X⟧ :=
  X * (1 - X) * d⁄dX K (d⁄dX K f) + (C c - C (a + b + 1) * X) * d⁄dX K f - C (a * b) * f

/-- [proved-standard; formal-checked] `[λⁿ] L f = (n + 1)(n + c) f_(n+1) − (n + a)(n + b) fₙ`. -/
theorem coeff_op (a b c : K) (f : K⟦X⟧) (n : ℕ) :
    coeff n (op a b c f) =
      ((n : K) + 1) * (n + c) * coeff (n + 1) f - (n + a) * (n + b) * coeff n f := by
  rcases n with _ | _ | n <;>
    simp [op, mul_sub, sub_mul, mul_assoc, add_mul, coeff_succ_X_mul, coeff_derivative,
      coeff_zero_X_mul, -coeff_zero_eq_constantCoeff] <;> ring

/-- [definition] The Euler form of `λ L` on `λ^r g`, read on `g`:
`(θ + r)(θ + r + c − 1) g − λ (θ + r + a)(θ + r + b) g` (Frobenius's twist by the exponent `r`). -/
def twisted (a b c r : K) (g : K⟦X⟧) : K⟦X⟧ :=
  euler r (euler (r + c - 1) g) - X * euler (r + a) (euler (r + b) g)

/-- [proved-standard; formal-checked] The constant coefficient of the twist is `r(r + c − 1) g₀`. -/
theorem coeff_zero_twisted (a b c r : K) (g : K⟦X⟧) :
    coeff 0 (twisted a b c r g) = r * (r + c - 1) * coeff 0 g := by
  simp [twisted, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff]; ring

/-- [proved-standard; formal-checked] The recursion of the twist:
`[λ^(n+1)] = (n + 1 + r)(n + r + c) g_(n+1) − (n + r + a)(n + r + b) gₙ`. -/
theorem coeff_succ_twisted (a b c r : K) (g : K⟦X⟧) (n : ℕ) :
    coeff (n + 1) (twisted a b c r g) =
      ((n : K) + 1 + r) * (n + r + c) * coeff (n + 1) g - (n + r + a) * (n + r + b) * coeff n g := by
  simp [twisted, coeff_succ_X_mul]; ring

/-- [proved-standard; formal-checked] At the exponent `r = 0` the twist is `λ L`, the Euler form of the operator. -/
theorem X_mul_op (a b c : K) (f : K⟦X⟧) : X * op a b c f = twisted a b c 0 f := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_twisted, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff]
  · rw [coeff_succ_X_mul, coeff_op, coeff_succ_twisted]; ring

/-- [proved-standard; formal-checked] **The action on a monomial**: `λ L λ^r = λ^r (r(r + c − 1) − (r + a)(r + b) λ)`,
that is `L(λ^r) = r(r − 1 + c) λ^(r−1) − (r + a)(r + b) λ^r`. -/
theorem twisted_one (a b c r : K) :
    twisted a b c r 1 = (r * (r + c - 1)) • 1 - ((r + a) * (r + b)) • X := by
  ext n
  rcases n with _ | _ | n <;>
    simp [twisted, coeff_X, coeff_one, coeff_succ_X_mul, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff]

/-- [definition] The indicial polynomial at `0`, `r(r − (1 − c))`: exponents `0` and `1 − c`. -/
def indicialZero (c : K) : K[X] := Polynomial.X * (Polynomial.X - Polynomial.C (1 - c))

/-- [definition] The indicial polynomial at `1`, `r(r − (c − a − b))`: exponents `0` and `c − a − b`. -/
def indicialOne (a b c : K) : K[X] := Polynomial.X * (Polynomial.X - Polynomial.C (c - a - b))

/-- [definition] The indicial polynomial at `∞` in `y ~ λ^(−s)`, `(s − a)(s − b)`: exponents `a` and `b`. -/
def indicialInf (a b : K) : K[X] := (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)

/-- [proved-standard; formal-checked] The constant coefficient of the twist is the indicial polynomial at `0`. -/
theorem coeff_zero_twisted_eq_indicial (a b c r : K) (g : K⟦X⟧) :
    coeff 0 (twisted a b c r g) = (indicialZero c).eval r * coeff 0 g := by
  rw [coeff_zero_twisted]
  simp only [indicialZero, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]; ring

/-- [proved-standard; formal-checked] The monomial action read through both indicial polynomials:
`λ L λ^r = I₀(r) λ^r − I_∞(−r) λ^(r+1)`. -/
theorem twisted_one_eq_indicial (a b c r : K) :
    twisted a b c r 1 = (indicialZero c).eval r • 1 - (indicialInf a b).eval (-r) • X := by
  rw [twisted_one]
  simp only [indicialZero, indicialInf, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C]
  congr 2 <;> ring

/-- [definition] The operator in the chart `μ = 1/λ` on `μ^s h`, read on `h`: with `θ_λ = −θ_μ`,
`−μ · λL = (θ_μ + s − a)(θ_μ + s − b) − μ (θ_μ + s)(θ_μ + s + 1 − c)`. -/
def twistedInf (a b c s : K) (h : K⟦X⟧) : K⟦X⟧ :=
  euler (s - a) (euler (s - b) h) - X * euler s (euler (s + 1 - c) h)

/-- [proved-standard; formal-checked] The constant coefficient at `∞` is the indicial polynomial at `∞`. -/
theorem coeff_zero_twistedInf (a b c s : K) (h : K⟦X⟧) :
    coeff 0 (twistedInf a b c s h) = (indicialInf a b).eval s * coeff 0 h := by
  simp only [twistedInf, indicialInf, map_sub, coeff_zero_X_mul, coeff_euler, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
  push_cast; ring

/-- [proved-standard; formal-checked] The chart at `∞` is again hypergeometric: the twist with parameters
`(a, a + 1 − c; a − b + 1)` at the exponent `s − a` (the solution `λ^(−a) ₂F₁(a, a − c + 1; a − b + 1; 1/λ)`). -/
theorem twistedInf_eq (a b c s : K) : twistedInf a b c s = twisted a (a + 1 - c) (a - b + 1) (s - a) := by
  funext h
  simp only [twistedInf, twisted]
  congr 2 <;> ring_nf

/-- [proved-standard; formal-checked] The chart check on the monomial: `−μ · λL λ^(−s) = I_∞(s) μ^s − I₀(−s) μ^(s+1)`,
the two coefficients of `twisted_one_eq_indicial` at `r = −s`, exchanged with a sign. -/
theorem twistedInf_one (a b c s : K) :
    twistedInf a b c s 1 = (indicialInf a b).eval s • 1 - (indicialZero c).eval (-s) • X := by
  simp only [indicialZero, indicialInf, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C]
  ext n
  rcases n with _ | _ | n <;>
    simp [twistedInf, coeff_X, coeff_one, coeff_succ_X_mul, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff]
  ring

/-- [definition] Gauss's operator on polynomials, where `λ ↦ 1 − λ` is a substitution. -/
def opPoly (a b c : K) (p : K[X]) : K[X] :=
  Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Polynomial.derivative p) +
    (Polynomial.C c - Polynomial.C (a + b + 1) * Polynomial.X) * Polynomial.derivative p -
      Polynomial.C (a * b) * p

/-- [proved-standard; formal-checked] On a polynomial the two operators agree. -/
theorem op_coe (a b c : K) (p : K[X]) : op a b c (p : K⟦X⟧) = (opPoly a b c p : K⟦X⟧) := by
  simp [op, opPoly, derivative_coe]

/-- [proved-standard; formal-checked] **`λ ↦ 1 − λ`** carries `L_(a,b,c)` to `L_(a,b,a+b+1−c)`. -/
theorem opPoly_comp_one_sub (a b c : K) (p : K[X]) :
    opPoly a b c (p.comp (1 - Polynomial.X)) =
      (opPoly a b (a + b + 1 - c) p).comp (1 - Polynomial.X) := by
  simp [opPoly, Polynomial.derivative_comp, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.add_comp]
  ring

/-- [proved-standard; formal-checked] The indicial polynomial at `1` is the one at `0` of the operator that
`λ ↦ 1 − λ` gives. -/
theorem indicialOne_eq (a b c : K) : indicialOne a b c = indicialZero (a + b + 1 - c) := by
  simp only [indicialOne, indicialZero]; congr 3; ring

/-- [proved-standard; formal-checked] The exponents at `0` are `0, 1 − c`. -/
theorem roots_indicialZero (c : K) : (indicialZero c).roots = {0, 1 - c} := by
  rw [indicialZero, Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X, Polynomial.roots_X_sub_C]; rfl

/-- [proved-standard; formal-checked] The exponents at `1` are `0, c − a − b`. -/
theorem roots_indicialOne (a b c : K) : (indicialOne a b c).roots = {0, c - a - b} := by
  rw [indicialOne, Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X, Polynomial.roots_X_sub_C]; rfl

/-- [proved-standard; formal-checked] The exponents at `∞` are `a, b`. -/
theorem roots_indicialInf (a b : K) : (indicialInf a b).roots = {a, b} := by
  rw [indicialInf, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.X_sub_C_ne_zero _)), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]; rfl

/-- [proved-standard; formal-checked] **Fuchs' relation**: the six exponents sum to `1`. -/
theorem fuchs (a b c : K) :
    ((indicialZero c).roots + (indicialOne a b c).roots + (indicialInf a b).roots).sum = 1 := by
  rw [roots_indicialZero, roots_indicialOne, roots_indicialInf]
  simp only [Multiset.sum_add, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]; ring

/-- [proved-standard; formal-checked] Legendre's scheme (`a = b = ½`, `c = 1`): `(0, 0)`, `(0, 0)`, `(½, ½)`. -/
theorem legendre_exponents [CharZero K] :
    (indicialZero (1 : K)).roots = {0, 0} ∧ (indicialOne (1 / 2 : K) (1 / 2) 1).roots = {0, 0} ∧
      (indicialInf (1 / 2 : K) (1 / 2)).roots = {1 / 2, 1 / 2} := by
  refine ⟨?_, ?_, roots_indicialInf _ _⟩
  · rw [roots_indicialZero]; norm_num
  · rw [roots_indicialOne]; norm_num

/-- [proved-standard; formal-checked] Legendre's operator is invariant under `λ ↦ 1 − λ`. -/
theorem legendre_comp_one_sub [CharZero K] (p : K[X]) :
    opPoly (1 / 2 : K) (1 / 2) 1 (p.comp (1 - Polynomial.X)) =
      (opPoly (1 / 2 : K) (1 / 2) 1 p).comp (1 - Polynomial.X) := by
  rw [opPoly_comp_one_sub]; norm_num

/-- [proved-standard; formal-checked] The `(½, ⅓, 0)` triangle, `a = b = 1/12`, `c = ½`: exponents `(0, ½)` at `0`,
`(0, ⅓)` at `1`, `(1/12, 1/12)` at `∞`, so the exponent differences are `½`, `⅓`, `0`. -/
theorem triangle_exponents [CharZero K] :
    (indicialZero (1 / 2 : K)).roots = {0, 1 / 2} ∧
      (indicialOne (1 / 12 : K) (1 / 12) (1 / 2)).roots = {0, 1 / 3} ∧
      (indicialInf (1 / 12 : K) (1 / 12)).roots = {1 / 12, 1 / 12} := by
  refine ⟨?_, ?_, roots_indicialInf _ _⟩
  · rw [roots_indicialZero]; norm_num
  · rw [roots_indicialOne]; norm_num

/-- [proved-standard; formal-checked] The record's chart of the triangle, `(a, b; c) = (1/12, 5/12; 1)`: exponent
differences `0` at `0` (the cusp), `½` at `1`, `⅓` at `∞`. -/
theorem triangle_exponents_cusp_at_zero [CharZero K] :
    (indicialZero (1 : K)).roots = {0, 0} ∧ (indicialOne (1 / 12 : K) (5 / 12) 1).roots = {0, 1 / 2} ∧
      (indicialInf (1 / 12 : K) (5 / 12)).roots = {1 / 12, 5 / 12} := by
  refine ⟨?_, ?_, roots_indicialInf _ _⟩
  · rw [roots_indicialZero]; norm_num
  · rw [roots_indicialOne]; norm_num

/-! ## 2. Frobenius at a double exponent: Legendre's solutions at `0` -/

/-- [definition] The hypergeometric series `₂F₁(a, b; c; λ)` as a formal power series, with Mathlib's coefficient. -/
def hyperSeries (a b c : K) : K⟦X⟧ := mk (ordinaryHypergeometricCoefficient a b c)

/-- [proved-standard; formal-checked] The ratio of consecutive coefficients:
`f_(n+1) = fₙ (n + a)(n + b)/((n + 1)(n + c))`. -/
theorem coeff_hyperSeries_succ (a b c : K) (n : ℕ) :
    coeff (n + 1) (hyperSeries a b c) =
      coeff n (hyperSeries a b c) * (((n : K) + a) * (n + b) / (((n : K) + 1) * (n + c))) := by
  simp only [hyperSeries, coeff_mk, ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv, div_eq_mul_inv]
  ring

/-- [proved-standard; formal-checked] **`₂F₁` solves Gauss's equation** at the exponent `0`, when `c` is not a
nonpositive integer: `L ₂F₁(a, b; c; ·) = 0` in `K⟦X⟧`. -/
theorem op_hyperSeries [CharZero K] (a b c : K) (hc : ∀ n : ℕ, (n : K) + c ≠ 0) :
    op a b c (hyperSeries a b c) = 0 := by
  ext n
  have h1 : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h2 := hc n
  rw [coeff_op, coeff_hyperSeries_succ, map_zero]
  field_simp
  ring

/-- [definition] Legendre's series `F = ₂F₁(½, ½; 1; λ) = Σ ((½)ₙ/n!)² λⁿ`. -/
def legendreF : K⟦X⟧ := hyperSeries (1 / 2) (1 / 2) 1

/-- [proved-standard; formal-checked] `F(0) = 1`. -/
theorem coeff_zero_legendreF : coeff 0 (legendreF : K⟦X⟧) = 1 := by
  simp [legendreF, hyperSeries, ordinaryHypergeometricCoefficient, -coeff_zero_eq_constantCoeff]

/-- [proved-standard; formal-checked] Legendre's recursion `(n + 1)² f_(n+1) = (n + ½)² fₙ`. -/
theorem coeff_legendreF_succ [CharZero K] (n : ℕ) :
    ((n : K) + 1) ^ 2 * coeff (n + 1) (legendreF : K⟦X⟧) = ((n : K) + 1 / 2) ^ 2 * coeff n legendreF := by
  have h1 : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [legendreF, coeff_hyperSeries_succ]
  field_simp

/-- [proved-standard; formal-checked] Over `ℝ`, `fₙ = wₙ²`, the coefficient of `K(√λ) = (π/2) F(λ)`
(`CompleteEllipticSeries.hypergeometric_coefficient`). -/
theorem coeff_legendreF_real (n : ℕ) : coeff n (legendreF : ℝ⟦X⟧) = CompleteEllipticSeries.wallis n ^ 2 := by
  rw [legendreF, hyperSeries, coeff_mk, CompleteEllipticSeries.hypergeometric_coefficient]

/-- [proved-standard; formal-checked] **`L F = 0`**: Legendre's series solves Legendre's equation. -/
theorem op_legendreF [CharZero K] : op (1 / 2 : K) (1 / 2) 1 legendreF = 0 :=
  op_hyperSeries _ _ _ fun n => Nat.cast_add_one_ne_zero n

/-- [proved-standard; formal-checked] Legendre's operator on coefficients:
`[λᵐ] L G = (m + 1)² g_(m+1) − (m + ½)² gₘ`. -/
theorem coeff_op_legendre (G : K⟦X⟧) (m : ℕ) :
    coeff m (op (1 / 2 : K) (1 / 2) 1 G) = ((m : K) + 1) ^ 2 * coeff (m + 1) G - ((m : K) + 1 / 2) ^ 2 * coeff m G := by
  rw [coeff_op]; ring

/-- [definition] `θ + s` on `A + Bℓ` with a formal logarithm `ℓ` (`θℓ = 1`, that is `ℓ′ = 1/λ`), carried as
the pair `(A, B)`: `(θ + s)(A + Bℓ) = ((θ + s)A + B) + ((θ + s)B) ℓ`. -/
def eulerL (s : K) (p : K⟦X⟧ × K⟦X⟧) : K⟦X⟧ × K⟦X⟧ := (euler s p.1 + p.2, euler s p.2)

/-- [definition] `λ` times a pair. -/
def mulXL (p : K⟦X⟧ × K⟦X⟧) : K⟦X⟧ × K⟦X⟧ := (X * p.1, X * p.2)

/-- [definition] `λ L` on `A + Bℓ` in Euler form, `θ(θ + c − 1) − λ(θ + a)(θ + b)`, by the Leibniz rule. -/
def opL (a b c : K) (p : K⟦X⟧ × K⟦X⟧) : K⟦X⟧ × K⟦X⟧ :=
  eulerL 0 (eulerL (c - 1) p) - mulXL (eulerL a (eulerL b p))

/-- [proved-standard; formal-checked] `λL(A + Bℓ) = (λ L A + (2θ + c − 1)B − λ(2θ + a + b)B) + (λ L B) ℓ`. -/
theorem opL_pair (a b c : K) (A B : K⟦X⟧) :
    opL a b c (A, B) =
      (X * op a b c A + (euler 0 B + euler (c - 1) B) - X * (euler a B + euler b B), X * op a b c B) := by
  rw [X_mul_op, X_mul_op]
  refine Prod.ext ?_ ?_ <;> ext n <;> rcases n with _ | n <;>
    simp [opL, eulerL, mulXL, twisted, coeff_succ_X_mul, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff]
  ring

/-- [proved-standard; formal-checked] **Legendre's operator on `Fℓ + G`**:
`L(Fℓ + G) = ℓ · L F + (2(1 − λ)F′ − F + L G)`, multiplied through by `λ`. -/
theorem legendre_opL [CharZero K] (G F : K⟦X⟧) :
    opL (1 / 2 : K) (1 / 2) 1 (G, F) =
      (X * (op (1 / 2) (1 / 2) 1 G + 2 * (1 - X) * d⁄dX K F - F), X * op (1 / 2) (1 / 2) 1 F) := by
  have hC : C (1 / 2 : K) + C (1 / 2) = 1 := by rw [← map_add]; norm_num
  rw [opL_pair]
  simp only [euler_eq, sub_self, map_zero, zero_mul, add_zero]
  refine Prod.ext ?_ rfl
  linear_combination (-X * F) * hC

/-- [proved-standard; formal-checked] `Fℓ + G` solves Legendre's equation iff `L G = F − 2(1 − λ)F′`. -/
theorem legendre_log_iff [CharZero K] (G : K⟦X⟧) :
    opL (1 / 2 : K) (1 / 2) 1 (G, legendreF) = 0 ↔
      op (1 / 2 : K) (1 / 2) 1 G = legendreF - 2 * (1 - X) * d⁄dX K legendreF := by
  rw [legendre_opL, op_legendreF, mul_zero, Prod.mk_eq_zero]
  simp only [mul_eq_zero, X_ne_zero, false_or, and_true]
  constructor <;> intro h <;> linear_combination h

/-- [proved-standard; formal-checked] `L 0 = 0`. -/
theorem op_zero (a b c : K) : op a b c 0 = 0 := by simp [op]

/-- [definition] The coefficients of the solution `G` of `L G = R` with `G(0) = g₀`, by the recursion
`(n + 1)(n + c) g_(n+1) = rₙ + (n + a)(n + b) gₙ`. -/
def solveCoeff (a b c : K) (R : K⟦X⟧) (g₀ : K) : ℕ → K
  | 0 => g₀
  | n + 1 => (coeff n R + ((n : K) + a) * (n + b) * solveCoeff a b c R g₀ n) / (((n : K) + 1) * (n + c))

/-- [proved-standard; formal-checked] **The inhomogeneous equation** `L G = R` has one solution in `K⟦X⟧` with
`G(0) = g₀`, when `c` is not a nonpositive integer. -/
theorem existsUnique_op_eq [CharZero K] (a b c : K) (hc : ∀ n : ℕ, (n : K) + c ≠ 0) (R : K⟦X⟧) (g₀ : K) :
    ∃! G : K⟦X⟧, coeff 0 G = g₀ ∧ op a b c G = R := by
  refine ⟨mk (solveCoeff a b c R g₀), ⟨by simp [solveCoeff, -coeff_zero_eq_constantCoeff], ?_⟩, ?_⟩
  · ext n
    have h1 : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 := hc n
    rw [coeff_op]
    simp only [coeff_mk, solveCoeff]
    field_simp
    ring
  · rintro G ⟨h0, hG⟩
    ext n
    induction n with
    | zero => simpa [solveCoeff, -coeff_zero_eq_constantCoeff] using h0
    | succ n ih =>
      have h1 : (n : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      have h2 := hc n
      have e := congrArg (coeff n) hG
      rw [coeff_op] at e
      simp only [coeff_mk, solveCoeff] at ih ⊢
      rw [← ih]
      field_simp
      linear_combination e

/-- [proved-standard; formal-checked] **Frobenius at the double exponent**: there is one `G` with `G(0) = 0` such
that `Fℓ + G` solves Legendre's equation. -/
theorem legendre_log_solution [CharZero K] :
    ∃! G : K⟦X⟧, coeff 0 G = 0 ∧ opL (1 / 2 : K) (1 / 2) 1 (G, legendreF) = 0 := by
  simpa only [legendre_log_iff] using existsUnique_op_eq (1 / 2 : K) (1 / 2) 1
    (fun n => Nat.cast_add_one_ne_zero n) (legendreF - 2 * (1 - X) * d⁄dX K legendreF) 0

/-- [definition] The continuation `ℓ ↦ ℓ + κ` on `A + Bℓ`. -/
def shiftLog (κ : K) (p : K⟦X⟧ × K⟦X⟧) : K⟦X⟧ × K⟦X⟧ := (p.1 + κ • p.2, p.2)

/-- [proved-standard; formal-checked] **`ℓ ↦ ℓ + κ` commutes with `L`**, so it carries solutions to solutions. -/
theorem opL_shiftLog (a b c κ : K) (p : K⟦X⟧ × K⟦X⟧) : opL a b c (shiftLog κ p) = shiftLog κ (opL a b c p) := by
  obtain ⟨A, B⟩ := p
  refine Prod.ext ?_ ?_ <;> ext n <;> rcases n with _ | n <;>
    simp [opL, eulerL, mulXL, shiftLog, coeff_succ_X_mul, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff]
  ring

/-- [proved-standard; formal-checked] `L` is `K`-linear on pairs. -/
theorem opL_smul (a b c κ : K) (p : K⟦X⟧ × K⟦X⟧) : opL a b c (κ • p) = κ • opL a b c p := by
  obtain ⟨A, B⟩ := p
  refine Prod.ext ?_ ?_ <;> ext n <;> rcases n with _ | n <;>
    simp [opL, eulerL, mulXL, coeff_succ_X_mul, coeff_zero_X_mul, -coeff_zero_eq_constantCoeff] <;>
    ring

/-- [definition] The basis `(F, (Fℓ + G)/κ)` at `0` (over `ℂ`, `κ = πi`). -/
def legendreBasis (κ : K) (G : K⟦X⟧) : Fin 2 → K⟦X⟧ × K⟦X⟧ := ![(legendreF, 0), κ⁻¹ • (G, legendreF)]

/-- [proved-standard; formal-checked] Both members of the basis solve Legendre's equation when `G` is Frobenius's. -/
theorem opL_legendreBasis [CharZero K] (κ : K) {G : K⟦X⟧} (hG : opL (1 / 2 : K) (1 / 2) 1 (G, legendreF) = 0)
    (i : Fin 2) : opL (1 / 2 : K) (1 / 2) 1 (legendreBasis κ G i) = 0 := by
  fin_cases i
  · simp only [legendreBasis, Fin.zero_eta, Matrix.cons_val_zero]
    rw [opL_pair, op_legendreF, op_zero]
    simp [euler_eq]
  · simp only [legendreBasis, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [opL_smul, hG, smul_zero]

/-- [proved-standard; formal-checked] The basis is linearly independent over `K` (`F(0) = 1`). -/
theorem legendreBasis_linearIndependent {κ : K} (hκ : κ ≠ 0) (G : K⟦X⟧) :
    LinearIndependent K (legendreBasis κ G) := by
  rw [legendreBasis, LinearIndependent.pair_iff]
  intro s t h
  have h2 := congrArg (fun p => coeff 0 p.2) h
  have hF := coeff_zero_legendreF (K := K)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, zero_add, map_smul, smul_eq_mul, Prod.snd_zero,
    map_zero, hF, mul_one] at h2
  have ht : t = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (inv_ne_zero hκ)
  subst ht
  have h1 := congrArg (fun p => coeff 0 p.1) h
  simp only [Prod.smul_mk, zero_smul, add_zero, map_smul, smul_eq_mul, Prod.fst_zero,
    map_zero, hF, mul_one] at h1
  exact ⟨h1, rfl⟩

/-- [proved-standard; formal-checked] **The continuation round `λ = 0` acts on the basis by `A = [[1, 2], [0, 1]]`**:
with `ℓ ↦ ℓ + 2κ`, the move sends the `j`-th member to `Σᵢ Aᵢⱼ eᵢ` (column convention), `LegendreLevelTwo.A`. -/
theorem shiftLog_legendreBasis {κ : K} (hκ : κ ≠ 0) (G : K⟦X⟧) (j : Fin 2) :
    shiftLog (2 * κ) (legendreBasis κ G j) =
      ∑ i, (((LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : K) • legendreBasis κ G i := by
  rw [Fin.sum_univ_two, LegendreLevelTwo.coe_A]
  fin_cases j
  · simp [legendreBasis, shiftLog]
  · simp only [legendreBasis, shiftLog, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Prod.smul_mk, Prod.mk_add_mk, smul_zero,
      Int.cast_ofNat, Int.cast_one, one_smul]
    refine Prod.ext ?_ (by simp)
    simp only [smul_smul, mul_assoc, mul_inv_cancel₀ hκ, mul_one]
    abel

/-- [proved-standard; formal-checked] Over `ℂ`, the continuation `ℓ ↦ ℓ + 2πi` round `λ = 0` acts on
`(F, (Fℓ + G)/(πi))` by `[[1, 2], [0, 1]]`. -/
theorem continuation_round_zero (G : ℂ⟦X⟧) (j : Fin 2) :
    shiftLog (2 * Real.pi * Complex.I) (legendreBasis (Real.pi * Complex.I) G j) =
      ∑ i, (((LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) •
        legendreBasis (Real.pi * Complex.I) G i := by
  rw [show (2 : ℂ) * Real.pi * Complex.I = 2 * (Real.pi * Complex.I) by ring]
  exact shiftLog_legendreBasis (mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero) G j

open Matrix (trace)

/-! ## 3. Rigidity: the local monodromies fix the group -/

/-- [definition] The integer moves read over `K`. -/
def toK : SL(2, ℤ) →* SL(2, K) := Matrix.SpecialLinearGroup.map (Int.castRingHom K)

/-- [proved-standard; formal-checked] The entries of a move read over `K`. -/
theorem coe_toK_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((toK g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j = ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : K) := rfl

/-- [proved-standard; formal-checked] Two moves of `SL(2, K)` agree iff their matrices do. -/
theorem sl_eq_iff (g h : SL(2, K)) : g = h ↔ (g : Matrix (Fin 2) (Fin 2) K) = h := by
  rw [Matrix.SpecialLinearGroup.ext_iff, Matrix.ext_iff]

/-- [definition] Conjugation `g ↦ P g P⁻¹` by `P ∈ GL(2, K)`. -/
def conjBy (P : GL (Fin 2) K) : SL(2, K) →* SL(2, K) where
  toFun g := ⟨(P : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
      ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, ← Matrix.det_mul,
      Units.mul_inv, Matrix.det_one]⟩
  map_one' := by
    refine Subtype.ext ?_
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Units.mul_inv]
  map_mul' g h := by
    refine Subtype.ext ?_
    change (P : Matrix (Fin 2) (Fin 2) K) * (g * h) * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((P : Matrix (Fin 2) (Fin 2) K) * g * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        ((P : Matrix (Fin 2) (Fin 2) K) * h * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

/-- [proved-standard; formal-checked] The matrix of a conjugate. -/
theorem coe_conjBy (P : GL (Fin 2) K) (g : SL(2, K)) :
    (conjBy P g : Matrix (Fin 2) (Fin 2) K) = (P : Matrix (Fin 2) (Fin 2) K) * g * ((P⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) := rfl

/-- [proved-standard; formal-checked] `P g P⁻¹ = h` iff `P g = h P`. -/
theorem conjBy_eq_iff (P : GL (Fin 2) K) (g h : SL(2, K)) :
    conjBy P g = h ↔ (P : Matrix (Fin 2) (Fin 2) K) * g = h * P := by
  rw [sl_eq_iff, coe_conjBy]
  constructor
  · intro e
    rw [← e, Matrix.mul_assoc _ _ (P : Matrix (Fin 2) (Fin 2) K), Units.inv_mul, Matrix.mul_one]
  · intro e
    rw [e, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- [proved-standard; formal-checked] Conjugations compose. -/
theorem conjBy_mul (Q P : GL (Fin 2) K) (g : SL(2, K)) : conjBy (Q * P) g = conjBy Q (conjBy P g) := by
  rw [sl_eq_iff]
  simp only [coe_conjBy, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] The trace is a class function. -/
theorem trace_conjBy (P : GL (Fin 2) K) (g : SL(2, K)) :
    trace (conjBy P g : Matrix (Fin 2) (Fin 2) K) = trace (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_conjBy, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]

/-- [proved-standard; formal-checked] In `SL(2)` a move and its inverse have one trace. -/
theorem trace_inv (g : SL(2, K)) :
    trace ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = trace (g : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two_of, Matrix.trace_fin_two,
    add_comm]

/-- [proved-standard; formal-checked] **A unipotent move other than `1` is a shear**: `tr g = 2`, `g ≠ 1` give
`P g P⁻¹ = [[1, 1], [0, 1]]`. -/
theorem exists_conj_shear (g : SL(2, K)) (ht : trace (g : Matrix (Fin 2) (Fin 2) K) = 2) (h1 : g ≠ 1) :
    ∃ P : GL (Fin 2) K, conjBy P g = toK ModularGroup.T := by
  obtain ⟨p, q, r, t, hg⟩ : ∃ p q r t : K, (g : Matrix (Fin 2) (Fin 2) K) = !![p, q; r, t] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [hg, Matrix.det_fin_two_of] at hdet
  rw [hg, Matrix.trace_fin_two_of] at ht
  have hT : ((toK ModularGroup.T : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [coe_toK_apply, ModularGroup.coe_T]
  by_cases hq : q = 0
  · subst hq
    have hp : (p - 1) ^ 2 = 0 := by linear_combination p * ht - hdet
    have hp1 : p = 1 := by linear_combination pow_eq_zero_iff (two_ne_zero) |>.1 hp
    have ht1 : t = 1 := by linear_combination ht - hp1
    have hr : r ≠ 0 := by
      rintro rfl
      apply h1
      ext i j
      rw [hg, hp1, ht1]
      fin_cases i <;> fin_cases j <;> simp
    have hd : (!![0, 1; r, 0] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simpa using hr
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
    rw [conjBy_eq_iff, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hg, hT, hp1, ht1, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_] <;> ring
  · have hd : (!![1, 0; p - 1, q] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simpa using hq
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
    rw [conjBy_eq_iff, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hg, hT, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_]
    · ring
    · ring
    · linear_combination -hdet + p * ht
    · linear_combination q * ht

/-- [proved-standard; formal-checked] `A = [[1, 2], [0, 1]]` over `K`. -/
theorem coe_toK_A : ((toK LegendreLevelTwo.A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 2; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coe_toK_apply, LegendreLevelTwo.coe_A]

/-- [proved-standard; formal-checked] `B⁻¹ = [[1, 0], [−2, 1]]` over `K`. -/
theorem coe_toK_B_inv :
    ((toK LegendreLevelTwo.B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; -2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_toK_apply, LegendreLevelTwo.coe_B, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- [proved-standard; formal-checked] `−T = [[−1, −1], [0, −1]]` over `K`. -/
theorem coe_toK_neg_T :
    ((toK (-ModularGroup.T) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![-1, -1; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coe_toK_apply, ModularGroup.coe_T]

/-- [proved-standard; formal-checked] `S = [[0, −1], [1, 0]]` over `K`. -/
theorem coe_toK_S : ((toK ModularGroup.S : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coe_toK_apply, ModularGroup.coe_S]

/-- [proved-standard; formal-checked] `2 ≠ −2` when `2 ≠ 0`. -/
theorem two_ne_neg_two (h2 : (2 : K) ≠ 0) : (2 : K) ≠ -2 := by
  intro h
  apply mul_ne_zero h2 h2
  linear_combination h

/-- [proved-standard; formal-checked] **Rigidity of Legendre's local data**: over a field with `2 ≠ 0`, two moves
`X, Y ∈ SL(2, K)` of trace `2` whose product has trace `−2` are conjugate in `GL(2, K)` to `(A, B⁻¹)`,
`A = [[1, 2], [0, 1]]`, `B⁻¹ = [[1, 0], [−2, 1]]`. -/
theorem legendre_rigidity (h2 : (2 : K) ≠ 0) (X Y : SL(2, K))
    (hX : trace (X : Matrix (Fin 2) (Fin 2) K) = 2) (hY : trace (Y : Matrix (Fin 2) (Fin 2) K) = 2)
    (hXY : trace ((X * Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -2) :
    ∃ P : GL (Fin 2) K, conjBy P X = toK LegendreLevelTwo.A ∧ conjBy P Y = toK LegendreLevelTwo.B⁻¹ := by
  have hX1 : X ≠ 1 := by
    rintro rfl
    rw [one_mul, hY] at hXY
    exact two_ne_neg_two h2 hXY
  obtain ⟨P₁, hP₁⟩ := exists_conj_shear X hX hX1
  have hY₁ := trace_conjBy P₁ Y
  have hXY₁ := trace_conjBy P₁ (X * Y)
  rw [hY] at hY₁
  rw [hXY, map_mul, hP₁, Matrix.SpecialLinearGroup.coe_mul] at hXY₁
  obtain ⟨p, q, r, t, hg⟩ : ∃ p q r t : K, (conjBy P₁ Y : Matrix (Fin 2) (Fin 2) K) = !![p, q; r, t] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe (conjBy P₁ Y)
  have hT : ((toK ModularGroup.T : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [coe_toK_apply, ModularGroup.coe_T]
  rw [hg, Matrix.det_fin_two_of] at hdet
  rw [hg, Matrix.trace_fin_two_of] at hY₁
  rw [hg, hT, Matrix.mul_fin_two, Matrix.trace_fin_two_of] at hXY₁
  have hr : r = -4 := by linear_combination hXY₁ - hY₁
  have hd : (!![8, 2 * (p - 1); 0, 4] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have : (8 : K) * 4 - 2 * (p - 1) * 0 = 2 * 2 * 2 * 2 * 2 := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd * P₁, ?_, ?_⟩
  · rw [conjBy_mul, hP₁, conjBy_eq_iff, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hT, coe_toK_A,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_] <;> ring
  · rw [conjBy_mul, conjBy_eq_iff, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hg, coe_toK_B_inv,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_]
    · linear_combination 2 * (p - 1) * hr
    · linear_combination 2 * hdet + 2 * q * hr - 2 * hY₁
    · linear_combination 4 * hr
    · linear_combination 4 * hY₁

/-- [proved-standard; formal-checked] In the `(2, 3, ∞)` data the product is not the whole turn: `XY = −1` would give
`Y = −X⁻¹` and `tr Y = −tr X = 0`. -/
theorem triangle_mul_ne_neg_one (X Y : SL(2, K)) (hX : trace (X : Matrix (Fin 2) (Fin 2) K) = 0)
    (hY : trace (Y : Matrix (Fin 2) (Fin 2) K) = 1) : X * Y ≠ -1 := by
  intro h
  have hY' : Y = -X⁻¹ := by rw [← inv_mul_cancel_left X Y, h, mul_neg, mul_one]
  rw [hY', Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, trace_inv, hX, neg_zero] at hY
  exact zero_ne_one hY

/-- [proved-standard; formal-checked] **Rigidity of the `(2, 3, ∞)` data**: over any field, `X, Y ∈ SL(2, K)` with
`tr X = 0`, `tr Y = 1` and `tr XY = −2` are conjugate in `GL(2, K)` to `(S, U)`, `S = [[0, −1], [1, 0]]`,
`U = S T = [[0, −1], [1, 1]]` (`ModularFreeProduct`). -/
theorem triangle_rigidity (X Y : SL(2, K)) (hX : trace (X : Matrix (Fin 2) (Fin 2) K) = 0)
    (hY : trace (Y : Matrix (Fin 2) (Fin 2) K) = 1)
    (hXY : trace ((X * Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -2) :
    ∃ P : GL (Fin 2) K, conjBy P X = toK ModularGroup.S ∧ conjBy P Y = toK ModularFreeProduct.U := by
  have hZ : -(X * Y) ≠ 1 := by
    intro h
    exact triangle_mul_ne_neg_one X Y hX hY (by rw [← neg_neg (X * Y), h])
  have htZ : trace ((-(X * Y) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 2 := by
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, hXY, neg_neg]
  obtain ⟨P₁, hP₁⟩ := exists_conj_shear _ htZ hZ
  have hT : ((toK ModularGroup.T : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [coe_toK_apply, ModularGroup.coe_T]
  have hW : conjBy P₁ (X * Y) = toK (-ModularGroup.T) := by
    rw [sl_eq_iff, coe_toK_neg_T]
    have e := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) hP₁
    simp only [coe_conjBy, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_neg, Matrix.neg_mul, hT] at e
    rw [coe_conjBy, ← neg_neg (_ * _ * _), e]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨a, b, c, d, hx⟩ : ∃ a b c d : K, (conjBy P₁ X : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨e, f, g, h, hy⟩ : ∃ e f g h : K, (conjBy P₁ Y : Matrix (Fin 2) (Fin 2) K) = !![e, f; g, h] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe (conjBy P₁ X)
  rw [hx, Matrix.det_fin_two_of] at hdet
  have htr := trace_conjBy P₁ X
  rw [hX, hx, Matrix.trace_fin_two_of] at htr
  have hty := trace_conjBy P₁ Y
  rw [hY, hy, Matrix.trace_fin_two_of] at hty
  have hm := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) hW
  simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy, coe_toK_neg_T, Matrix.mul_fin_two] at hm
  have h1 : a * e + b * g = -1 := congrFun (congrFun hm 0) 0
  have h2 : a * f + b * h = -1 := congrFun (congrFun hm 0) 1
  have h3 : c * e + d * g = 0 := congrFun (congrFun hm 1) 0
  have h4 : c * f + d * h = -1 := congrFun (congrFun hm 1) 1
  have hc : c = 1 := by
    linear_combination (e + h - 1) * hdet + hdet + hty + htr - d * h1 + b * h3 - a * h4 + c * h2
  have hQ : (!![1, -a; 0, 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; norm_num
  set Q := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hQ with hQdef
  have hQX : conjBy Q (conjBy P₁ X) = toK ModularGroup.S := by
    rw [conjBy_eq_iff, hQdef, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hx, coe_toK_S, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_]
    · linear_combination (-a) * hc
    · linear_combination -hdet - b * hc
    · linear_combination hc
    · linear_combination htr
  have hQW : conjBy Q (toK (-ModularGroup.T)) = toK (-ModularGroup.T) := by
    rw [conjBy_eq_iff, hQdef, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, coe_toK_neg_T, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_] <;> ring
  refine ⟨Q * P₁, by rw [conjBy_mul, hQX], ?_⟩
  have hY₁ : conjBy P₁ Y = (conjBy P₁ X)⁻¹ * conjBy P₁ (X * Y) := by rw [map_mul, inv_mul_cancel_left]
  rw [conjBy_mul, hY₁, hW, map_mul, map_inv, hQX, hQW, ← map_inv, ← map_mul]
  congr 1
  decide

/-- [proved-standard; formal-checked] A pair generates what it generates with its second member inverted. -/
theorem closure_pair_inv {G : Type*} [Group G] (x y : G) :
    Subgroup.closure ({x, y⁻¹} : Set G) = Subgroup.closure {x, y} := by
  apply le_antisymm <;> rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff] <;>
    refine ⟨Subgroup.subset_closure (Set.mem_insert _ _), ?_⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · have h := Subgroup.inv_mem (Subgroup.closure ({x, y⁻¹} : Set G))
      (Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y⁻¹)))
    rwa [inv_inv] at h

/-- [proved-standard; formal-checked] The range of Sanov's word map is the group generated by `A` and `B`. -/
theorem range_sanov :
    LegendreLevelTwo.sanov.range = Subgroup.closure {LegendreLevelTwo.A, LegendreLevelTwo.B} := by
  rw [LegendreLevelTwo.sanov, FreeGroup.range_lift_eq_closure]
  congr 1
  ext g
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor <;> rintro (h | h) <;> simp [h]

/-- [proved-standard; formal-checked] The image of Sanov's range in `PSL(2, ℤ)` is `Γ(2)/±1`
(`LegendreLevelTwo.map_Gamma_two_eq_range`). -/
theorem range_sanov_map_proj :
    LegendreLevelTwo.sanov.range.map ModularFreeProduct.proj =
      (CongruenceSubgroup.Gamma 2).map ModularFreeProduct.proj := by
  rw [← MonoidHom.range_comp, LegendreLevelTwo.map_Gamma_two_eq_range]

/-- [proved-standard; formal-checked] **Legendre's monodromy group**: under the local data of
`legendre_rigidity`, one conjugation carries `X`, `Y` to `A`, `B⁻¹` and the group they generate onto the image
over `K` of Sanov's range, whose image in `PSL(2, ℤ)` is `Γ(2)/±1` (`range_sanov_map_proj`). -/
theorem legendre_monodromy_group (h2 : (2 : K) ≠ 0) (X Y : SL(2, K))
    (hX : trace (X : Matrix (Fin 2) (Fin 2) K) = 2) (hY : trace (Y : Matrix (Fin 2) (Fin 2) K) = 2)
    (hXY : trace ((X * Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -2) :
    ∃ P : GL (Fin 2) K, conjBy P X = toK LegendreLevelTwo.A ∧ conjBy P Y = toK LegendreLevelTwo.B⁻¹ ∧
      (Subgroup.closure {X, Y}).map (conjBy P) = LegendreLevelTwo.sanov.range.map toK := by
  obtain ⟨P, hPX, hPY⟩ := legendre_rigidity h2 X Y hX hY hXY
  refine ⟨P, hPX, hPY, ?_⟩
  rw [MonoidHom.map_closure, Set.image_pair, hPX, hPY, range_sanov, MonoidHom.map_closure, Set.image_pair,
    map_inv, closure_pair_inv]

/-- [proved-standard; formal-checked] Legendre's local data force nontrivial local moves: `X ≠ 1`, `Y ≠ 1`,
`XY ≠ −1` follow from the traces when `2 ≠ 0`. -/
theorem legendre_nontrivial (h2 : (2 : K) ≠ 0) (X Y : SL(2, K))
    (hX : trace (X : Matrix (Fin 2) (Fin 2) K) = 2) (hY : trace (Y : Matrix (Fin 2) (Fin 2) K) = 2)
    (hXY : trace ((X * Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -2) :
    X ≠ 1 ∧ Y ≠ 1 ∧ X * Y ≠ -1 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    rw [one_mul, hY] at hXY
    exact two_ne_neg_two h2 hXY
  · rintro rfl
    rw [mul_one, hX] at hXY
    exact two_ne_neg_two h2 hXY
  · intro h
    have hY' : Y = -X⁻¹ := by rw [← inv_mul_cancel_left X Y, h, mul_neg, mul_one]
    rw [hY', Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, trace_inv, hX] at hY
    exact two_ne_neg_two h2 hY.symm

/-- [proved-standard; formal-checked] `S` and `U = S T` generate `SL(2, ℤ)` (Mathlib's `SL2Z_generators`). -/
theorem closure_S_U :
    Subgroup.closure ({ModularGroup.S, ModularFreeProduct.U} : Set SL(2, ℤ)) = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  have hS : ModularGroup.S ∈ Subgroup.closure ({ModularGroup.S, ModularFreeProduct.U} : Set SL(2, ℤ)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hU : ModularFreeProduct.U ∈ Subgroup.closure ({ModularGroup.S, ModularFreeProduct.U} : Set SL(2, ℤ)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨hS, ?_⟩
  have hT : ModularGroup.T = ModularGroup.S⁻¹ * ModularFreeProduct.U := by
    rw [ModularFreeProduct.U, inv_mul_cancel_left]
  rw [hT]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hS) hU

/-- [proved-standard; formal-checked] The half-turn `s` and the third of a turn `u` generate `PSL(2, ℤ)`. -/
theorem closure_s_u :
    Subgroup.closure ({ModularFreeProduct.s, ModularFreeProduct.u} : Set PSL(2, ℤ)) = ⊤ := by
  rw [ModularFreeProduct.s, ModularFreeProduct.u, ← Set.image_pair, ← MonoidHom.map_closure, closure_S_U]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- [proved-standard; formal-checked] **The triangle's monodromy group is the modular group**: under the local data
of `triangle_rigidity`, one conjugation carries `X`, `Y` to `S`, `U` and the group they generate onto the image of
`SL(2, ℤ)` over `K`; projectively the images `s`, `u` have orders `2`, `3` and generate `PSL(2, ℤ)`. -/
theorem triangle_monodromy_group (X Y : SL(2, K)) (hX : trace (X : Matrix (Fin 2) (Fin 2) K) = 0)
    (hY : trace (Y : Matrix (Fin 2) (Fin 2) K) = 1)
    (hXY : trace ((X * Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -2) :
    ∃ P : GL (Fin 2) K, conjBy P X = toK ModularGroup.S ∧ conjBy P Y = toK ModularFreeProduct.U ∧
      (Subgroup.closure {X, Y}).map (conjBy P) = (toK : SL(2, ℤ) →* SL(2, K)).range := by
  obtain ⟨P, hPX, hPY⟩ := triangle_rigidity X Y hX hY hXY
  refine ⟨P, hPX, hPY, ?_⟩
  rw [MonoidHom.map_closure, Set.image_pair, hPX, hPY, ← Set.image_pair, ← MonoidHom.map_closure, closure_S_U,
    MonoidHom.range_eq_map]

/-! ## 4. Witnesses -/

/-- [proved-standard; formal-checked] Legendre's model meets its local data: `tr A = tr B⁻¹ = 2`,
`tr(A B⁻¹) = −2`, and `A B⁻¹ = [[−3, 2], [−2, 1]] ≠ −1`. -/
theorem legendre_witness :
    trace (LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) = 2 ∧
      trace ((LegendreLevelTwo.B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 2 ∧
      trace ((LegendreLevelTwo.A * LegendreLevelTwo.B⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -2 ∧
      LegendreLevelTwo.A * LegendreLevelTwo.B⁻¹ ≠ -1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- [proved-standard; formal-checked] The modular model meets the triangle's local data: `tr S = 0`, `tr U = 1`,
`S U = −T`, of trace `−2`. -/
theorem triangle_witness :
    trace (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) = 0 ∧
      trace (ModularFreeProduct.U : Matrix (Fin 2) (Fin 2) ℤ) = 1 ∧
      ModularGroup.S * ModularFreeProduct.U = -ModularGroup.T ∧
      trace ((ModularGroup.S * ModularFreeProduct.U : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -2 := by
  refine ⟨by decide, by decide, ModularFreeProduct.S_mul_U, by decide⟩

/-- [proved-standard; formal-checked] The `SL(2)` traces `2 cos(π d)` of the exponent differences `d = ½, ⅓, 0`. -/
theorem two_cos_exponent_differences :
    2 * Real.cos (Real.pi * (1 / 2)) = 0 ∧ 2 * Real.cos (Real.pi * (1 / 3)) = 1 ∧
      2 * Real.cos (Real.pi * 0) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_one_div, Real.cos_pi_div_two, mul_zero]
  · rw [mul_one_div, Real.cos_pi_div_three]; norm_num
  · rw [mul_zero, Real.cos_zero, mul_one]

end Holonics.Geometry.HypergeometricMonodromy
