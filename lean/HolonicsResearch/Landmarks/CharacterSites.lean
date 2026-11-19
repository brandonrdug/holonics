import HolonicsResearch.Landmarks.PrimeCycles
import HolonicsResearch.Landmarks.ZeroPairSite
import Holonics.Geometry.Motion
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Per-site clocks carry a Dirichlet `L`-function, and a zero paired with its conjugate is a real site

The box of #410: "Per-site clocks for L-functions, and the Foster tank chart off the real locus
(`Landmarks/{PrimeCycles,ZeroPairSite}`)." The box carries no more text, and its reading here is
`agent-inferred`:
- *per-site clocks*: the cycle machine of `Landmarks/PrimeCycles` puts every site on the one
  complex clock `s`; here each site also carries its own clock, a phase of finite order, so that
  the machine's transfer determinant is the Euler product of a Dirichlet `L`-function;
- *the tank chart off the real locus*: `Landmarks/ZeroPairSite` reads a centred zero `ρ′ = ρ − ½`
  as the tank site `companion(0, −ρ′²)`, whose faces are real only on the seam or on the real axis
  (`tank_seam_iff`, `tank_reflection_iff`, `off_seam_tank_not_real`); here the zero is paired
  with its conjugate (the zeros of `ξ` come in quadruples `ρ, 1 − ρ, ρ̄, 1 − ρ̄`), and the pair
  is a real site for every `ρ′`.

Sources: the box above; the owners' opening paragraphs (`Landmarks/PrimeCycles`: "A cycle machine
has one site per primitive cycle `i`, of length `ℓ_i`, carrying the material `exp(−s·ℓ_i)` at the
complex clock `s`"; `Landmarks/ZeroPairSite`: the three charts, advance, tank and heat, and "the
ordered trichotomy cannot be applied to the tank chart without the seam"); the null-cone record
`research/records/2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md`
§4 and §5; `Zeta/FosterReturn` (`witness_off_seam`); `Geometry/Motion` (`complex_rate_split`);
the atlas rows `landmark.cycle-machine`, `rh.prime-cycle-machine`, `rh.primes-primitive-cycles`,
`trace.abelian-cover-artin` (a character's twist `diag(ψ(kσ))·B` of a dart operator),
`rh.foster-tank-site`, `rh.foster-tank-kinds`, `rh.foster-tank-real-locus-counterexample`,
`rh.pair-heat-chart` and `rh.foster-return-one-port`.

## What is proved

1. **The clocked machine.** [definition] `clockedMachine ℓ θ s = diag(θ_i exp(−s ℓ_i))`: the owner's
   cycle machine with each site carrying its own clock `θ_i` beside the common clock `s`; it is
   `diag(θ) · cycleMachine ℓ s` (`clockedMachine_eq_mul`) and the owner's machine at `θ ≡ 1`
   (`clockedMachine_one`). [proved-derived; formal-checked] Its transfer determinant is
   `∏_i (1 − θ_i e^{−s ℓ_i})` (`clockedMachine_det`) and its closed-word faces are
   `tr(Mᵏ) = Σ_i θ_iᵏ e^{−s ℓ_i k}` (`clockedMachine_trace_pow`).
2. **The character machine.** [definition] For a Dirichlet character `χ` mod `N`, the clocked
   machine on the primes below `M` with lengths `log p` and clocks `χ(p)` (`characterMachine`).
   [proved-standard; formal-checked] Its transfer determinant is the truncated Euler product
   `∏_(p<M) (1 − χ(p) p^(−s))` (`characterMachine_det`), and its inverse tends to `L(χ, s)` for
   `Re s > 1` (`characterMachine_tendsto_L`, Mathlib's `DirichletCharacter.LSeries_eulerProduct`).
   [proved-derived; formal-checked] Its closed-word faces are `Σ_(p<M) χ(p)ᵏ p^(−ks)`
   (`characterMachine_trace_pow`), the `L`-series' summands `χ(pᵏ)(pᵏ)^(−s)` at the prime powers
   (`characterMachine_trace_pow_term`). Mod `1` it is the owner's `primeMachine`
   (`characterMachine_modOne`), and its limit is `ζ(s) = L(χ₁, s)`
   (`characterMachine_modOne_tendsto_zeta`).
3. **The site's clock is a turn of finite order.** [proved-standard; formal-checked] For `p ∣ N`
   the site is silent, `χ(p) = 0` (`site_silent`). For `p ∤ N`, with `u` the class of `p` in
   `(ZMod N)ˣ`: `‖χ(p)‖ = 1`, `χ(p)^(ord u) = 1`, `ord u ∣ φ(N)`, and the clock closes after
   `orderOf χ(p)` ticks, `χ(p)^(orderOf χ(p)) = 1`, with `orderOf χ(p) ∣ ord u`
   (`site_clock_closes`). [proved-derived; formal-checked] The site's material is a boost times a
   turn, `χ(p) p^(−s) = p^(−Re s) · (χ(p) p^(−i Im s))`, with `‖χ(p) p^(−s)‖ = p^(−Re s)` and a turn
   of norm one (`site_boost_turn`).
4. **The logarithmic derivative per site.** [proved-derived; formal-checked] The twisted von
   Mangoldt summand at `p^(k+1)` is the site's closed-word face weighted by its length,
   `Λ(p^(k+1)) χ(p^(k+1)) (p^(k+1))^(−s) = log p · (χ(p) p^(−s))^(k+1)` (`site_vonMangoldt_term`),
   and the machine's length-weighted face `tr(diag(log p) · M^(k+1))` is the sum of those summands
   over the sites below `M` (`characterMachine_weighted_trace`). [proved-standard; formal-checked]
   For `Re s > 1`, `−L′/L(χ, s) = Σ_p Σ_(k≥0) log p · (χ(p) p^(−s))^(k+1)`
   (`neg_logDeriv_eq_sum_sites`: Mathlib's `LSeries_twist_vonMangoldt_eq`, its series carried onto
   the sites and the word lengths through `(p, k) ↦ p^(k+1)`).
5. **The conjugate chart.** [definition] For `ρ′ = σ′ + iγ`, the pair site
   `S(ρ′) = companion(2σ′, σ′² + γ²)` over `ℝ` (`pairSite`). [proved-derived; formal-checked] Its
   characteristic polynomial over `ℂ` is `(X − ρ′)(X − ρ̄′)` (`pairSite_charpoly_map`); its faces
   are real for every `ρ′`: trace `2σ′`, zero exactly on the seam; determinant `|ρ′|² ≥ 0`,
   positive exactly for `ρ′ ≠ 0`; discriminant `−4γ² ≤ 0`, negative exactly off the axis
   (`pairSite_trace`, `pairSite_det`, `pairSite_discriminant`, `pairSite_faces`). Its kind
   (`pairSite_kind`): a **rotation** for `γ ≠ 0`, on the seam or off it; null for `γ = 0 ≠ σ′`;
   degenerate at `ρ′ = 0`. So the chart classifies the off-seam, off-axis zeros where the owner's
   tank has no real faces.
6. **The quadruple.** [proved-derived; formal-checked] The real quartic
   `Q = X⁴ − 2(σ′² − γ²)X² + (σ′² + γ²)²` (`quadrupleQuartic`) is the product of the pair sites of
   `ρ′` and `−ρ′` (`quadrupleQuartic_eq_pairSites`), and over `ℂ` the product of the owner's tank
   sites of `ρ′` and `ρ̄′` (`quadrupleQuartic_map`). Conjugation carries one tank to the other,
   `conj tank(ρ′, w) = tank(ρ̄′, w̄)` (`tank_conj`), so `tank(ρ′, w) + tank(ρ̄′, w)` has zero
   imaginary part at every real `w` (`quadruple_tank_real`); off the poles that sum is `Q′/Q`
   (`quadruple_tank_logDeriv`), and at a real `w` with `Q(w) ≠ 0` it is the real number
   `Q′(w)/Q(w)` (`quadruple_impedance_real`): the quadruple's impedance is a real rational function.
7. **Boost and turn.** [definition] `realify z = [[Re z, −Im z], [Im z, Re z]]` and the turn
   `J = [[0, −1], [1, 0]]`. [proved-derived; formal-checked] `realify z = Re z · 1 + Im z · J`
   (`realify_eq`), multiplicative (`realify_mul`), acting on `ℝ² ≅ ℂ` as multiplication by `z`
   (`realify_mulVec`). The matrix `P = [[1, −σ′], [0, γ]]` of determinant `γ` intertwines,
   `P · S = realify(ρ′) · P` (`pairSite_intertwines`), so for `γ ≠ 0` the pair site is similar to
   `σ′ · 1 + γ · J` (`pairSite_similar`), whose turn against the unit metric is `γ · J` and whose
   boost is `σ′ · 1` (`realify_turn_boost`, from `Motion.complex_rate_split`): the boost is the
   zero's distance from the seam and the turn its height. Its flow is
   `realify(e^(tρ′)) = e^(σ′t)(cos(γt) · 1 + sin(γt) · J)` (`realify_flow`), and along
   `v(t) = e^(tρ′)`, `v̇ = v ρ′`, so `v⁻¹v̇ = ρ′` is boost rate `σ′` plus `i` times turn rate `γ`,
   with `‖v(t)‖ = e^(σ′t)` (`flow_rate`).
8. **The quarter turn to the heat chart.** [proved-derived; formal-checked] `−iρ′ = γ − iσ′`, its
   conjugate is `iρ̄′ = γ + iσ′`, and `S(−iρ′) = companion(2γ, γ² + σ′²)` (`heat_is_quarter_turn`);
   with `ρ′ = (σ − ½) + iγ` its characteristic polynomial is the owner's `pairQuadratic σ γ`
   (`heat_charpoly`). The quarter turn exchanges the seam and the axis: the heat site is a rotation
   exactly off the seam (`heat_kind`).
9. **Seam and axis.** [proved-derived; formal-checked] On the seam `σ′ = 0` the pair site is the pure
   turn `companion(0, γ²)`, its image over `ℂ` is the owner's tank site, and it is a rotation for
   `γ ≠ 0` (`pairSite_seam`). On the axis `γ = 0` it is `companion(2σ′, σ′²)`, the double root
   `σ′` with discriminant zero, and `S − σ′ · 1 ≠ 0` (`pairSite_axis`).
   [counterexample; formal-checked] So on the axis the similarity of item 7 fails: no invertible
   `P` has `P · S = (σ′ · 1) · P` (`pairSite_axis_not_similar`); the double root is a shear (the
   null kind), not the scalar boost `σ′ · 1`, and the hypothesis `γ ≠ 0` of `pairSite_similar` is
   load-bearing.
10. **Witnesses.** [proved-derived; formal-checked] The trivial character's machine below `3` has the
    one site `2` and transfer determinant `1 − 2^(−s)` (`witness_trivial_machine`). The character
    `χ₄` mod `4` (`chi4`) silences the site `2` and turns the site `3` by a half-turn, `χ₄(3) = −1`
    of order `2` (`chi4_values`); below `4` its transfer determinant is `1 + 3^(−s)` and its
    closed-word face `tr(M²)` is `3^(−2s)` (`witness_chi4_machine`). The owner's off-axis witness
    `ρ′ = ½ + i`, whose tank has no real determinant face, has the real chart
    `S = companion(1, 5/4)`: trace `1`, determinant `5/4`, discriminant `−4`, a rotation
    (`witness_real_chart`).

## What is not claimed

Hecke and Artin `L`-functions, the analytic continuation of `L(χ, s)` and its zeros, the
generalized Riemann hypothesis and the explicit formula. The conjugation symmetry of the zeros of
`ξ` is the lens's premise and is not proved here: every statement on the conjugate chart is about
one centred zero `ρ′` and its conjugate, and nothing here locates a zero. No realization of the
quadruple's impedance as a real RLC network is built: off the seam two of its poles `±ρ′, ±ρ̄′`
lie in the right half-plane, so the real rational function `Q′/Q` is not positive real there, the
impedance of an active one-port (the reading of `FosterReturn.witness_off_seam`). The order of a
site's clock is `orderOf` in the multiplicative monoid of `ℂ`; nothing is claimed about the
primitive characters or the conductor.

## The computational object

The computational object is the helical pair interaction, read on the sites. A prime site of the
character machine is a helix on two clocks: the common clock `s` scales it by the boost `p^(−Re s)`
and advances its phase by `Im s · log p`, and its own clock `χ(p)` turns it by a root of unity
whose winding closes after `orderOf χ(p)` ticks; a closed word of length `k` is the face
`χ(p)ᵏ p^(−ks)`, and the log-derivative weighs it by the site's length `log p`. In the zero chart
the pair is the conjugate pairing `(ρ′, ρ̄′)`, a real site that boosts at the zero's distance from
the seam and turns at its height. Of the winding guide's six general objects this touches the
helix (a site's two clocks, the flow `e^(tρ′)`), the pair (the conjugate pairing and the quadruple
of tanks) and faces and placement (trace, determinant and discriminant faces, closed-word faces,
the receiver's real impedance at a real `w`); the cell holonomy is touched in reading only (the
site's clock as the holonomy of the character around its primitive cycle, the twist of
`trace.abelian-cover-artin`), and the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Landmarks.CharacterSites

open Finset Filter Topology Complex
open scoped LSeries.notation
open Holonics.Landmarks.PrimeCycles

/-! ## 1. The clocked machine -/

section Clocked

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] **The clocked machine**: the cycle machine whose site `i` carries its own clock `θ i`
beside the common clock `s`. -/
def clockedMachine (ℓ : ι → ℝ) (θ : ι → ℂ) (s : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => θ i * Complex.exp (-s * (ℓ i : ℂ))

/-- [proved-derived; formal-checked] The clocked machine is `diag(θ)` times the owner's cycle machine. -/
theorem clockedMachine_eq_mul (ℓ : ι → ℝ) (θ : ι → ℂ) (s : ℂ) :
    clockedMachine ℓ θ s = Matrix.diagonal θ * cycleMachine ℓ s := by
  rw [clockedMachine, cycleMachine, Matrix.diagonal_mul_diagonal]

omit [Fintype ι] in
/-- [proved-derived; formal-checked] With every clock `1` the clocked machine is the owner's. -/
theorem clockedMachine_one (ℓ : ι → ℝ) (s : ℂ) : clockedMachine ℓ 1 s = cycleMachine ℓ s := by
  simp [clockedMachine, cycleMachine]

/-- [proved-derived; formal-checked] **The transfer determinant is the clocked Euler product.** -/
theorem clockedMachine_det (ℓ : ι → ℝ) (θ : ι → ℂ) (s : ℂ) :
    (1 - clockedMachine ℓ θ s).det = ∏ i, (1 - θ i * Complex.exp (-s * (ℓ i : ℂ))) := by
  rw [clockedMachine, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.det_diagonal]

/-- [proved-derived; formal-checked] **The closed-word faces** `tr(Mᵏ) = Σ_i θ_iᵏ e^(−s ℓ_i k)`. -/
theorem clockedMachine_trace_pow (ℓ : ι → ℝ) (θ : ι → ℂ) (s : ℂ) (k : ℕ) :
    ((clockedMachine ℓ θ s) ^ k).trace = ∑ i, θ i ^ k * Complex.exp (-s * (ℓ i : ℂ)) ^ k := by
  rw [clockedMachine, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Pi.pow_apply, mul_pow]

end Clocked

/-! ## 2. The character machine -/

section CharacterMachine

variable {N : ℕ}

/-- [definition] **The character machine below `M`**: one site per prime `p < M`, of length `log p`,
carrying its own clock `χ(p)`. -/
def characterMachine (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) :
    Matrix (Nat.primesBelow M) (Nat.primesBelow M) ℂ :=
  clockedMachine (fun p : Nat.primesBelow M => Real.log (p : ℕ)) (fun p => χ ((p : ℕ) : ZMod N)) s

/-- [proved-standard; formal-checked] `(pᵏ)^s = p^(k s)` for a natural base. -/
theorem natCast_pow_cpow (p k : ℕ) (s : ℂ) : (((p ^ k : ℕ) : ℂ)) ^ s = (p : ℂ) ^ ((k : ℂ) * s) := by
  rw [natCast_cpow_natCast_mul, Nat.cast_pow]

/-- [proved-standard; formal-checked] **The character machine's transfer determinant is the
truncated Euler product** `∏_(p<M) (1 − χ(p) p^(−s))`. -/
theorem characterMachine_det (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) :
    (1 - characterMachine χ s M).det = ∏ p ∈ Nat.primesBelow M, (1 - χ p * (p : ℂ) ^ (-s)) := by
  rw [characterMachine, clockedMachine_det]
  rw [← Finset.prod_coe_sort (Nat.primesBelow M) (fun p => 1 - χ p * (p : ℂ) ^ (-s))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : 0 < (p : ℕ) := (Nat.prime_of_mem_primesBelow p.2).pos
  rw [exp_neg_log_eq_cpow hp]

/-- [proved-standard; formal-checked] **The inverse transfer determinants tend to `L(χ, s)`** for
`Re s > 1` (Mathlib's `DirichletCharacter.LSeries_eulerProduct`). -/
theorem characterMachine_tendsto_L (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun M : ℕ => ((1 - characterMachine χ s M).det)⁻¹) atTop (𝓝 (L ↗χ s)) := by
  refine (DirichletCharacter.LSeries_eulerProduct χ hs).congr fun M => ?_
  rw [characterMachine_det, Finset.prod_inv_distrib]

/-- [proved-derived; formal-checked] **The closed-word faces** `tr(Mᵏ) = Σ_(p<M) χ(p)ᵏ p^(−ks)`. -/
theorem characterMachine_trace_pow (χ : DirichletCharacter ℂ N) (s : ℂ) (M k : ℕ) :
    ((characterMachine χ s M) ^ k).trace =
      ∑ p ∈ Nat.primesBelow M, χ p ^ k * (p : ℂ) ^ (-((k : ℂ) * s)) := by
  rw [characterMachine, clockedMachine_trace_pow]
  rw [← Finset.sum_coe_sort (Nat.primesBelow M) (fun p => χ p ^ k * (p : ℂ) ^ (-((k : ℂ) * s)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp : 0 < (p : ℕ) := (Nat.prime_of_mem_primesBelow p.2).pos
  rw [exp_neg_log_eq_cpow hp, ← mul_neg, cpow_nat_mul]

/-- [proved-derived; formal-checked] The closed-word faces are the `L`-series' summands at `pᵏ`. -/
theorem characterMachine_trace_pow_term (χ : DirichletCharacter ℂ N) (s : ℂ) (M k : ℕ) :
    ((characterMachine χ s M) ^ k).trace =
      ∑ p ∈ Nat.primesBelow M, χ ((p ^ k : ℕ) : ZMod N) * (((p ^ k : ℕ) : ℂ)) ^ (-s) := by
  rw [characterMachine_trace_pow]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [natCast_pow_cpow, Nat.cast_pow, map_pow, mul_neg]

/-- [proved-derived; formal-checked] **Mod `1` the character machine is the owner's prime machine.** -/
theorem characterMachine_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) (M : ℕ) :
    characterMachine χ s M = primeMachine s M := by
  rw [characterMachine, primeMachine, ← clockedMachine_one]
  congr 1
  funext p
  rw [χ.level_one, Pi.one_apply]
  exact MulChar.one_apply (isUnit_of_subsingleton _)

/-- [proved-standard; formal-checked] Mod `1` the limit is `ζ(s)`, which is `L(χ₁, s)`, for `Re s > 1`. -/
theorem characterMachine_modOne_tendsto_zeta (χ : DirichletCharacter ℂ 1) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun M : ℕ => ((1 - characterMachine χ s M).det)⁻¹) atTop (𝓝 (riemannZeta s)) ∧
      L ↗χ s = riemannZeta s := by
  refine ⟨?_, ?_⟩
  · simp_rw [characterMachine_modOne]
    exact primeMachine_tendsto_zeta hs
  · rw [χ.level_one, DirichletCharacter.LSeries_modOne_eq, LSeries_one_eq_riemannZeta hs]

end CharacterMachine

/-! ## 3. The site's clock -/

section SiteClock

variable {N : ℕ}

/-- [proved-standard; formal-checked] **A site dividing the modulus is silent**: `χ(p) = 0`. -/
theorem site_silent (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    χ p = 0 :=
  χ.map_nonunit fun h => ((ZMod.isUnit_prime_iff_not_dvd hp).mp h) hpN

/-- [proved-standard; formal-checked] **The site's clock closes**: `χ(p)` is a root of unity whose
order divides the order of `p` in `(ZMod N)ˣ`, which divides `φ(N)`. -/
theorem site_clock_closes (χ : DirichletCharacter ℂ N) [NeZero N] {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N) = p ∧ ‖χ p‖ = 1 ∧ χ p ^ orderOf u = 1 ∧ orderOf u ∣ N.totient ∧
      0 < orderOf (χ p) ∧ χ p ^ orderOf (χ p) = 1 ∧ orderOf (χ p) ∣ orderOf u := by
  have hc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hu : ((ZMod.unitOfCoprime p hc : (ZMod N)ˣ) : ZMod N) = p := ZMod.coe_unitOfCoprime p hc
  have h1 : χ p ^ orderOf (ZMod.unitOfCoprime p hc) = 1 := by
    rw [← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  have hpos : 0 < orderOf (ZMod.unitOfCoprime p hc) := orderOf_pos _
  have hfin : IsOfFinOrder (χ p) := isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hpos, h1⟩
  refine ⟨ZMod.unitOfCoprime p hc, hu, ?_, h1, ?_, hfin.orderOf_pos, pow_orderOf_eq_one _,
    orderOf_dvd_of_pow_eq_one h1⟩
  · rw [← hu]
    exact χ.unit_norm_eq_one _
  · rw [← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card

/-- [proved-derived; formal-checked] **A site's material is a boost times a turn**:
`χ(p) p^(−s) = p^(−Re s) · (χ(p) p^(−i Im s))`, the turn of norm one. -/
theorem site_boost_turn (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (s : ℂ) :
    χ p * (p : ℂ) ^ (-s) = (((p : ℝ) ^ (-s.re) : ℝ) : ℂ) * (χ p * (p : ℂ) ^ (-((s.im : ℂ) * I))) ∧
      ‖χ p * (p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) ∧
      ‖χ p * (p : ℂ) ^ (-((s.im : ℂ) * I))‖ = 1 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : 0 < p := hp.pos
  have hunit : ‖χ p‖ = 1 := by
    have hc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    rw [← ZMod.coe_unitOfCoprime p hc]
    exact χ.unit_norm_eq_one _
  refine ⟨?_, ?_, ?_⟩
  · have hs : -s = -(s.re : ℂ) + -((s.im : ℂ) * I) := by
      conv_lhs => rw [← Complex.re_add_im s]
      ring
    rw [hs, cpow_add _ _ hp0, Complex.ofReal_cpow (Nat.cast_nonneg p), Complex.ofReal_natCast,
      Complex.ofReal_neg]
    ring
  · rw [norm_mul, hunit, one_mul, norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  · rw [norm_mul, hunit, one_mul, norm_natCast_cpow_of_pos hpos]
    simp

end SiteClock

/-! ## 4. The logarithmic derivative per site -/

section LogDeriv

variable {N : ℕ}

/-- [proved-derived; formal-checked] **The twisted von Mangoldt summand at `p^(k+1)` is the site's
closed-word face weighted by its length** `log p`. -/
theorem site_vonMangoldt_term (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) (s : ℂ) :
    LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s (p ^ (k + 1)) =
      (Real.log p : ℂ) * (χ p * (p : ℂ) ^ (-s)) ^ (k + 1) := by
  have hn : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hn, Pi.mul_apply, ArithmeticFunction.vonMangoldt_apply_pow k.succ_ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime hp, div_eq_mul_inv, ← Complex.cpow_neg,
    natCast_pow_cpow, Nat.cast_pow, map_pow, mul_pow, ← cpow_nat_mul, mul_neg]
  ring

/-- [proved-derived; formal-checked] **The length-weighted closed-word face** `tr(diag(log p)·M^(k+1))`
is the sum of the twisted von Mangoldt summands at the `p^(k+1)`, `p < M`. -/
theorem characterMachine_weighted_trace (χ : DirichletCharacter ℂ N) (s : ℂ) (M k : ℕ) :
    (Matrix.diagonal (fun p : Nat.primesBelow M => (Real.log (p : ℕ) : ℂ)) *
        (characterMachine χ s M) ^ (k + 1)).trace =
      ∑ p ∈ Nat.primesBelow M, LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s (p ^ (k + 1)) := by
  rw [characterMachine, clockedMachine, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  rw [← Finset.sum_coe_sort (Nat.primesBelow M)
    (fun p => LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s (p ^ (k + 1)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := Nat.prime_of_mem_primesBelow p.2
  rw [site_vonMangoldt_term χ hp, Pi.pow_apply, exp_neg_log_eq_cpow hp.pos]

/-- [proved-standard; formal-checked] **`−L′/L(χ, s)` is the sum over sites and word lengths** of
`log p · (χ(p) p^(−s))^(k+1)`, for `Re s > 1`. -/
theorem neg_logDeriv_eq_sum_sites (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    -deriv (L ↗χ) s / L ↗χ s =
      ∑' p : Nat.Primes, ∑' k : ℕ, (Real.log p : ℂ) * (χ p * (p : ℂ) ^ (-s)) ^ (k + 1) := by
  rw [← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, LSeries]
  set f := LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s with hf
  let g : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 1)
  have hg : Function.Injective g := by
    rintro ⟨p, k⟩ ⟨q, m⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 h
    exact Prod.ext (Subtype.ext h1) h2
  have hsupp : Function.support f ⊆ Set.range g := by
    intro n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (by simp [hf])
    have hΛ : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro h0
      apply hn
      simp [hf, LSeries.term_of_ne_zero hn0, h0]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    refine ⟨(⟨p, hp⟩, k - 1), ?_⟩
    simp only [g]
    congr 1
    omega
  have hsum : Summable f := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  rw [← hg.tsum_eq hsupp]
  refine ((hsum.comp_injective hg).tsum_prod).trans ?_
  refine tsum_congr fun p => tsum_congr fun k => ?_
  exact site_vonMangoldt_term χ p.2 k s

end LogDeriv

/-! ## 5. The conjugate chart: a zero paired with its conjugate is a real site -/

section PairSite

open Polynomial
open Holonics.Geometry.LocalFactor
open Holonics.Landmarks.ZeroPairSite
open Holonics.Compression.Landmark.SiteKind (discriminant siteKind siteKind_eq_rotation_iff
  siteKind_eq_null_iff siteKind_eq_degenerate_iff companion_traceless_ne_zero)
open Holonics.Zeta.FosterTanks (tank)

/-- [definition] **The pair site** of `ρ′ = σ′ + iγ`: the real site whose roots are `ρ′` and `ρ̄′`. -/
def pairSite (ρ' : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := companion (2 * ρ'.re) (ρ'.re ^ 2 + ρ'.im ^ 2)

/-- [proved-derived; formal-checked] The pair site's trace face is `2σ′`. -/
theorem pairSite_trace (ρ' : ℂ) : (pairSite ρ').trace = 2 * ρ'.re :=
  (theCompanionHasTraceAndDeterminant _ _).1

/-- [proved-derived; formal-checked] The pair site's determinant face is `σ′² + γ² = |ρ′|²`. -/
theorem pairSite_det (ρ' : ℂ) : (pairSite ρ').det = ρ'.re ^ 2 + ρ'.im ^ 2 :=
  (theCompanionHasTraceAndDeterminant _ _).2

/-- [proved-derived; formal-checked] The pair site's discriminant face is `−4γ²`. -/
theorem pairSite_discriminant (ρ' : ℂ) :
    discriminant (pairSite ρ').trace (pairSite ρ').det = -4 * ρ'.im ^ 2 := by
  rw [pairSite_trace, pairSite_det, discriminant]
  ring

/-- [proved-derived; formal-checked] **Over `ℂ` the pair site splits at `ρ′` and `ρ̄′`.** -/
theorem pairSite_charpoly_map (ρ' : ℂ) :
    (pairSite ρ').charpoly.map (algebraMap ℝ ℂ) = (X - C ρ') * (X - C ((starRingEnd ℂ) ρ')) := by
  rw [Matrix.charpoly_fin_two, pairSite_trace, pairSite_det]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C]
  have e1 : algebraMap ℝ ℂ (2 * ρ'.re) = ρ' + (starRingEnd ℂ) ρ' := by
    rw [Complex.add_conj, Complex.coe_algebraMap]
  have e2 : algebraMap ℝ ℂ (ρ'.re ^ 2 + ρ'.im ^ 2) = ρ' * (starRingEnd ℂ) ρ' := by
    rw [Complex.mul_conj, Complex.normSq_apply, Complex.coe_algebraMap]
    congr 1
    ring
  rw [e1, e2, C_add, C_mul]
  ring

/-- [proved-derived; formal-checked] **The pair site's faces are real for every zero**: the trace
vanishes on the seam, the determinant is positive off the centre, the discriminant negative off
the axis. -/
theorem pairSite_faces (ρ' : ℂ) :
    ((pairSite ρ').trace = 0 ↔ ρ'.re = 0) ∧ 0 ≤ (pairSite ρ').det ∧
      (0 < (pairSite ρ').det ↔ ρ' ≠ 0) ∧
      discriminant (pairSite ρ').trace (pairSite ρ').det ≤ 0 ∧
      (discriminant (pairSite ρ').trace (pairSite ρ').det < 0 ↔ ρ'.im ≠ 0) := by
  rw [pairSite_discriminant, pairSite_trace, pairSite_det]
  refine ⟨by constructor <;> intro h <;> linarith, by positivity, ?_, by nlinarith [sq_nonneg ρ'.im], ?_⟩
  · constructor
    · rintro h rfl
      simp at h
    · intro h
      have : ρ'.re ≠ 0 ∨ ρ'.im ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h (Complex.ext hc.1 hc.2)
      rcases this with h1 | h1
      · have := sq_pos_of_ne_zero h1
        positivity
      · have := sq_pos_of_ne_zero h1
        positivity
  · constructor
    · intro h h0
      rw [h0] at h
      simp at h
    · intro h
      have := sq_pos_of_ne_zero h
      linarith

/-- [proved-derived; formal-checked] **The pair site's kind**: a rotation off the axis, null on the
axis off the centre, degenerate at the centre. -/
theorem pairSite_kind (ρ' : ℂ) :
    (ρ'.im ≠ 0 → siteKind (pairSite ρ').trace (pairSite ρ').det = .rotation) ∧
      (ρ'.im = 0 → ρ'.re ≠ 0 → siteKind (pairSite ρ').trace (pairSite ρ').det = .null) ∧
      (ρ' = 0 → siteKind (pairSite ρ').trace (pairSite ρ').det = .degenerate) := by
  rw [pairSite_trace, pairSite_det]
  refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [siteKind_eq_rotation_iff]
    have := sq_pos_of_ne_zero h
    nlinarith
  · rw [siteKind_eq_null_iff, h]
    have := sq_pos_of_ne_zero h'
    constructor
    · linarith
    · ring
  · rw [siteKind_eq_degenerate_iff, h]
    simp

/-! ## 6. The quadruple -/

/-- [definition] **The quadruple's real quartic** `X⁴ − 2(σ′² − γ²)X² + (σ′² + γ²)²`, whose roots are
`±ρ′, ±ρ̄′`. -/
def quadrupleQuartic (ρ' : ℂ) : ℝ[X] :=
  X ^ 4 - C (2 * (ρ'.re ^ 2 - ρ'.im ^ 2)) * X ^ 2 + C ((ρ'.re ^ 2 + ρ'.im ^ 2) ^ 2)

/-- [proved-derived; formal-checked] The quartic is the product of the pair sites of `ρ′` and `−ρ′`. -/
theorem quadrupleQuartic_eq_pairSites (ρ' : ℂ) :
    quadrupleQuartic ρ' = (pairSite ρ').charpoly * (pairSite (-ρ')).charpoly := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, pairSite_trace, pairSite_det, pairSite_trace,
    pairSite_det, quadrupleQuartic]
  simp only [Complex.neg_re, Complex.neg_im, map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat]
  ring

/-- [proved-derived; formal-checked] **Over `ℂ` the quartic is the product of the tank sites of `ρ′`
and `ρ̄′`.** -/
theorem quadrupleQuartic_map (ρ' : ℂ) :
    (quadrupleQuartic ρ').map (algebraMap ℝ ℂ) =
      (tankSite ρ').charpoly * (tankSite ((starRingEnd ℂ) ρ')).charpoly := by
  rw [quadrupleQuartic_eq_pairSites, Polynomial.map_mul, pairSite_charpoly_map, pairSite_charpoly_map,
    tankSite_charpoly, tankSite_charpoly]
  simp only [map_neg, C_pow]
  ring

/-- [proved-derived; formal-checked] Conjugation carries the tank of `ρ′` to the tank of `ρ̄′`. -/
theorem tank_conj (ρ' w : ℂ) :
    (starRingEnd ℂ) (tank ρ' w) = tank ((starRingEnd ℂ) ρ') ((starRingEnd ℂ) w) := by
  simp [Holonics.Zeta.FosterTanks.tank, map_div₀, map_ofNat (starRingEnd ℂ) 2]

/-- [proved-derived; formal-checked] **At a real `w` the conjugate pair of tanks reads a real
impedance.** -/
theorem quadruple_tank_real (ρ' : ℂ) (w : ℝ) :
    (tank ρ' w + tank ((starRingEnd ℂ) ρ') w).im = 0 := by
  have h := tank_conj ρ' w
  rw [Complex.conj_ofReal] at h
  rw [← h, Complex.add_im, Complex.conj_im]
  ring

/-- [proved-derived; formal-checked] Off the poles the conjugate pair of tanks is the logarithmic
derivative `Q′/Q` of the quartic. -/
theorem quadruple_tank_logDeriv (ρ' w : ℂ) (h1 : w ^ 2 - ρ' ^ 2 ≠ 0)
    (h2 : w ^ 2 - (starRingEnd ℂ) ρ' ^ 2 ≠ 0) :
    tank ρ' w + tank ((starRingEnd ℂ) ρ') w =
      (derivative ((quadrupleQuartic ρ').map (algebraMap ℝ ℂ))).eval w /
        ((quadrupleQuartic ρ').map (algebraMap ℝ ℂ)).eval w := by
  rw [quadrupleQuartic_map, tankSite_charpoly, tankSite_charpoly, derivative_mul]
  simp only [derivative_sub, derivative_C, derivative_X_pow, eval_mul, eval_add, eval_sub, eval_pow,
    eval_X, eval_C, sub_zero]
  simp only [Holonics.Zeta.FosterTanks.tank]
  field_simp
  push_cast
  ring

/-- [proved-derived; formal-checked] **The quadruple's impedance is a real rational function**: at a
real `w` with `Q(w) ≠ 0` it is the real number `Q′(w)/Q(w)`. -/
theorem quadruple_impedance_real (ρ' : ℂ) (w : ℝ) (hQ : (quadrupleQuartic ρ').eval w ≠ 0) :
    tank ρ' w + tank ((starRingEnd ℂ) ρ') w =
      (((derivative (quadrupleQuartic ρ')).eval w / (quadrupleQuartic ρ').eval w : ℝ) : ℂ) := by
  have hev : ∀ P : ℝ[X], (P.map (algebraMap ℝ ℂ)).eval (w : ℂ) = ((P.eval w : ℝ) : ℂ) := by
    intro P
    rw [eval_map, ← Complex.coe_algebraMap, eval₂_at_apply]
  have hQc : ((quadrupleQuartic ρ').map (algebraMap ℝ ℂ)).eval (w : ℂ) ≠ 0 := by
    rw [hev]
    exact_mod_cast hQ
  rw [quadrupleQuartic_map, tankSite_charpoly, tankSite_charpoly, eval_mul] at hQc
  simp only [eval_sub, eval_pow, eval_X, eval_C] at hQc
  rw [quadruple_tank_logDeriv ρ' w (left_ne_zero_of_mul hQc) (right_ne_zero_of_mul hQc),
    Polynomial.derivative_map, hev, hev]
  push_cast
  rfl

/-! ## 7. Boost and turn -/

/-- [definition] **The turn** `J = [[0, −1], [1, 0]]`, the quarter-turn generator of `Geometry/Motion`. -/
def turnJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- [definition] **The realification of `z`**: multiplication by `z` on `ℝ² ≅ ℂ`. -/
def realify (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![z.re, -z.im; z.im, z.re]

/-- [proved-standard; formal-checked] `realify z = Re z · 1 + Im z · J`. -/
theorem realify_eq (z : ℂ) : realify z = z.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) + z.im • turnJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realify, turnJ]

/-- [proved-standard; formal-checked] The realification is multiplicative. -/
theorem realify_mul (z w : ℂ) : realify (z * w) = realify z * realify w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [realify, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [proved-standard; formal-checked] The realification acts on `(Re x, Im x)` as multiplication by `z`. -/
theorem realify_mulVec (z x : ℂ) :
    (realify z).mulVec ![x.re, x.im] = ![(z * x).re, (z * x).im] := by
  ext i
  fin_cases i <;> simp [realify, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- [definition] The intertwiner `P = [[1, −σ′], [0, γ]]` of the pair site with the realification. -/
def intertwiner (ρ' : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -ρ'.re; 0, ρ'.im]

/-- [proved-derived; formal-checked] `P · S(ρ′) = realify(ρ′) · P`, with `det P = γ`. -/
theorem pairSite_intertwines (ρ' : ℂ) :
    intertwiner ρ' * pairSite ρ' = realify ρ' * intertwiner ρ' ∧ (intertwiner ρ').det = ρ'.im := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [intertwiner, pairSite, realify, companion, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [intertwiner, Matrix.det_fin_two]

/-- [proved-derived; formal-checked] **Off the axis the pair site is similar to `σ′ · 1 + γ · J`.** -/
theorem pairSite_similar (ρ' : ℂ) (hγ : ρ'.im ≠ 0) :
    pairSite ρ' = (intertwiner ρ')⁻¹ * realify ρ' * intertwiner ρ' := by
  obtain ⟨h, hdet⟩ := pairSite_intertwines ρ'
  have hu : IsUnit (intertwiner ρ').det := by rw [hdet]; exact hγ.isUnit
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- [proved-derived; formal-checked] **The turn of `realify ρ′` is `γ · J` and its boost is `σ′ · 1`**
(`Motion.complex_rate_split`). -/
theorem realify_turn_boost (ρ' : ℂ) :
    Holonics.Geometry.Motion.turn 1 (realify ρ') = ρ'.im • turnJ ∧
      Holonics.Geometry.Motion.boost 1 (realify ρ') = ρ'.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨h1, h2⟩ := Holonics.Geometry.Motion.complex_rate_split (K := ℝ) ρ'.re ρ'.im
  refine ⟨?_, ?_⟩
  · rw [realify, h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [turnJ]
  · rw [realify, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- [proved-standard; formal-checked] **The flow** `realify(e^(tρ′)) = e^(σ′t)(cos(γt) · 1 + sin(γt) · J)`. -/
theorem realify_flow (ρ' : ℂ) (t : ℝ) :
    realify (Complex.exp (t * ρ')) =
      Real.exp (ρ'.re * t) • (Real.cos (ρ'.im * t) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        Real.sin (ρ'.im * t) • turnJ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realify, turnJ, Complex.exp_re, Complex.exp_im, mul_comm]

/-- [proved-standard; formal-checked] **Along `v = e^(tρ′)`, `v⁻¹v̇ = ρ′`** (boost rate `σ′`, turn rate
`γ`), and `‖v‖ = e^(σ′t)`. -/
theorem flow_rate (ρ' : ℂ) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => Complex.exp (τ * ρ')) (Complex.exp (t * ρ') * ρ') t ∧
      (Complex.exp (t * ρ'))⁻¹ * (Complex.exp (t * ρ') * ρ') = ρ' ∧
      ‖Complex.exp (t * ρ')‖ = Real.exp (ρ'.re * t) := by
  refine ⟨?_, inv_mul_cancel_left₀ (Complex.exp_ne_zero _) ρ', ?_⟩
  · have h := (((hasDerivAt_id (t : ℂ)).mul_const ρ').cexp).comp_ofReal
    refine h.congr_deriv ?_
    simp
  · rw [Complex.norm_exp]
    simp [mul_comm]

/-! ## 8. The quarter turn to the heat chart -/

/-- [proved-derived; formal-checked] **The heat chart is the pair site of the quarter-turned zero**:
`−iρ′ = γ − iσ′`, its conjugate `iρ̄′ = γ + iσ′`, and `S(−iρ′) = companion(2γ, γ² + σ′²)`. -/
theorem heat_is_quarter_turn (ρ' : ℂ) :
    -I * ρ' = ρ'.im - ρ'.re * I ∧ (starRingEnd ℂ) (-I * ρ') = I * (starRingEnd ℂ) ρ' ∧
      (starRingEnd ℂ) (-I * ρ') = ρ'.im + ρ'.re * I ∧
      pairSite (-I * ρ') = companion (2 * ρ'.im) (ρ'.im ^ 2 + ρ'.re ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Complex.ext <;> simp
  · apply Complex.ext <;> simp
  · apply Complex.ext <;> simp
  · have h1 : (-I * ρ').re = ρ'.im := by simp
    have h2 : (-I * ρ').im = -ρ'.re := by simp
    rw [pairSite, h1, h2, neg_sq]

/-- [proved-derived; formal-checked] With `ρ′ = (σ − ½) + iγ` the quarter-turned pair site has the
owner's heat quadratic `pairQuadratic σ γ` as its characteristic polynomial. -/
theorem heat_charpoly (σ γ : ℚ) :
    (pairSite (-I * ((((σ : ℝ) - 1 / 2 : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I))).charpoly =
      pairQuadratic σ γ := by
  have h1 : (-I * ((((σ : ℝ) - 1 / 2 : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I)).re = (γ : ℝ) := by simp
  have h2 : (-I * ((((σ : ℝ) - 1 / 2 : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I)).im = -((σ : ℝ) - 1 / 2) := by
    simp
  rw [Matrix.charpoly_fin_two, pairSite_trace, pairSite_det, h1, h2, neg_sq, pairQuadratic, quad]

/-- [proved-derived; formal-checked] **The quarter turn exchanges seam and axis**: the heat site is a
rotation off the seam. -/
theorem heat_kind (ρ' : ℂ) (h : ρ'.re ≠ 0) :
    siteKind (pairSite (-I * ρ')).trace (pairSite (-I * ρ')).det = .rotation :=
  (pairSite_kind _).1 (by simpa using h)

/-! ## 9. Seam and axis -/

/-- [proved-derived; formal-checked] **On the seam the pair site is the pure turn `companion(0, γ²)`**,
the owner's tank site over `ℂ`, a rotation for `γ ≠ 0`. -/
theorem pairSite_seam (ρ' : ℂ) (h : ρ'.re = 0) :
    pairSite ρ' = companion 0 (ρ'.im ^ 2) ∧ (pairSite ρ').map (algebraMap ℝ ℂ) = tankSite ρ' ∧
      (ρ'.im ≠ 0 → siteKind (pairSite ρ').trace (pairSite ρ').det = .rotation) := by
  refine ⟨by simp [pairSite, h], ?_, (pairSite_kind ρ').1⟩
  have hsq : ρ' ^ 2 = -((ρ'.im : ℂ) ^ 2) := by
    apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairSite, tankSite, companion, h, hsq]

/-- [proved-derived; formal-checked] **On the axis the pair site is the double root
`companion(2σ′, σ′²)`**: discriminant zero, and not the scalar `σ′ · 1`. -/
theorem pairSite_axis (ρ' : ℂ) (h : ρ'.im = 0) :
    pairSite ρ' = companion (2 * ρ'.re) (ρ'.re ^ 2) ∧
      discriminant (pairSite ρ').trace (pairSite ρ').det = 0 ∧
      pairSite ρ' - ρ'.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  refine ⟨by simp [pairSite, h], by rw [pairSite_discriminant, h]; ring, ?_⟩
  have := companion_traceless_ne_zero (2 * ρ'.re) (ρ'.re ^ 2 + ρ'.im ^ 2)
  rwa [show 2 * ρ'.re / 2 = ρ'.re by ring] at this

/-- [counterexample; formal-checked] **On the axis the pair site is not similar to `σ′ · 1`**: the
height hypothesis of `pairSite_similar` is load-bearing. -/
theorem pairSite_axis_not_similar (ρ' : ℂ) (h : ρ'.im = 0) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsUnit P.det) : P * pairSite ρ' ≠ realify ρ' * P := by
  intro hPS
  apply (pairSite_axis ρ' h).2.2
  have hr : realify ρ' = ρ'.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [realify_eq, h, zero_smul, add_zero]
  rw [hr, Matrix.smul_mul, Matrix.one_mul] at hPS
  have hS : pairSite ρ' = ρ'.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    calc pairSite ρ' = P⁻¹ * (P * pairSite ρ') := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
      _ = ρ'.re • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
          rw [hPS, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hP]
  rw [hS, sub_self]

/-! ## 10. Witnesses -/

/-- [definition] **The character `χ₄` mod `4`** with complex values. -/
def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- [proved-standard; formal-checked] `chi4` reads Mathlib's integer `χ₄`. -/
theorem chi4_apply (n : ℕ) : chi4 n = ((ZMod.χ₄ n : ℤ) : ℂ) := rfl

/-- [proved-standard; formal-checked] The primes below `3`. -/
theorem primesBelow_three : Nat.primesBelow 3 = {2} := by decide

/-- [proved-standard; formal-checked] The primes below `4`. -/
theorem primesBelow_four : Nat.primesBelow 4 = {2, 3} := by decide

/-- [proved-standard; formal-checked] **`χ₄` silences the site `2` and turns the site `3` by a
half-turn of order `2`.** -/
theorem chi4_values : chi4 (2 : ℕ) = 0 ∧ chi4 (3 : ℕ) = -1 ∧ orderOf (chi4 (3 : ℕ)) = 2 := by
  have h3 : chi4 (3 : ℕ) = -1 := by
    rw [chi4_apply, ZMod.χ₄_nat_three_mod_four (by norm_num)]
    simp
  refine ⟨?_, h3, ?_⟩
  · rw [chi4_apply, ZMod.χ₄_nat_eq_if_mod_four]
    simp
  · rw [h3, orderOf_neg_one, ringChar.eq_zero]
    simp

/-- [proved-derived; formal-checked] **The trivial character's machine below `3`** has transfer
determinant `1 − 2^(−s)`. -/
theorem witness_trivial_machine (s : ℂ) :
    (1 - characterMachine (1 : DirichletCharacter ℂ 1) s 3).det = 1 - (2 : ℂ) ^ (-s) := by
  rw [characterMachine_det, primesBelow_three, Finset.prod_singleton,
    MulChar.one_apply (isUnit_of_subsingleton _)]
  simp

/-- [proved-derived; formal-checked] **`χ₄`'s machine below `4`**: transfer determinant `1 + 3^(−s)`
and closed-word face `tr(M²) = 3^(−2s)`. -/
theorem witness_chi4_machine (s : ℂ) :
    (1 - characterMachine chi4 s 4).det = 1 + (3 : ℂ) ^ (-s) ∧
      ((characterMachine chi4 s 4) ^ 2).trace = (3 : ℂ) ^ (-(2 * s)) := by
  obtain ⟨h2, h3, -⟩ := chi4_values
  refine ⟨?_, ?_⟩
  · rw [characterMachine_det, primesBelow_four, Finset.prod_insert (by decide),
      Finset.prod_singleton, h2, h3]
    push_cast
    ring
  · rw [characterMachine_trace_pow, primesBelow_four, Finset.sum_insert (by decide),
      Finset.sum_singleton, h2, h3]
    push_cast
    ring

/-- [proved-derived; formal-checked] **The real chart of `ρ′ = ½ + i`**, whose tank has no real
determinant face, is the rotation `companion(1, 5/4)`: trace `1`, determinant `5/4`,
discriminant `−4`. -/
theorem witness_real_chart :
    pairSite (1 / 2 + I) = companion 1 (5 / 4) ∧ (pairSite (1 / 2 + I)).trace = 1 ∧
      (pairSite (1 / 2 + I)).det = 5 / 4 ∧
      discriminant (pairSite (1 / 2 + I)).trace (pairSite (1 / 2 + I)).det = -4 ∧
      siteKind (pairSite (1 / 2 + I)).trace (pairSite (1 / 2 + I)).det = .rotation ∧
      ¬ ∃ q : ℝ, (tankSite (1 / 2 + I)).det = (q : ℂ) := by
  have hre : (1 / 2 + I : ℂ).re = 1 / 2 := by norm_num
  have him : (1 / 2 + I : ℂ).im = 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, (pairSite_kind _).1 (by rw [him]; norm_num), tank_off_axis_not_real⟩
  · rw [pairSite, hre, him]
    norm_num
  · rw [pairSite_trace, hre]
    norm_num
  · rw [pairSite_det, hre, him]
    norm_num
  · rw [pairSite_discriminant, him]
    norm_num

end PairSite

end Holonics.Landmarks.CharacterSites
