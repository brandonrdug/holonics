import HolonicsResearch.Coupling.LeeYangIsing
import HolonicsResearch.Zeta.HeatFlowEntire

/-!
# The lock's uniform coupling is the heat clock: every zero in the field stays on the imaginary axis for every forward time

Sources: `Coupling/LeeYangIsing`, `Coupling/LeeYangCircle` (atlas `thermal.ising-lee-yang`,
`parametron.coupled-locks-lee-yang`); `Zeta/HeatFlowEntire`, `Zeta/ForwardPreservation`,
`Zeta/DeBruijnNewmanPolynomial` (atlas `rh.heat-flow-polynomial`,
`rh.forward-preservation-polynomial`, `rh.dbn-polynomial-threshold`); `Coupling/HeatArrow` (the
sign of the cross coupling, stated there as a reading); an outside reader's reply of November 19
(its blueprint "finite-lock heat-clock zero flow", whose polynomial statements the tree already
held); Lee and Yang 1952, de Bruijn 1950, Newman 1976.

[definition] A finite set `V` of locks (spins `±1`); a configuration is its set `S` of up locks,
and `mag S = ∑ i, spin S i` is its magnetization.  With one exchange `c` between every ordered pair
(the diagonal included, which only adds a constant), `∑ i, ∑ j, c sᵢ sⱼ = c · (mag S)²`, so the
uniformly coupled partition function is

  `flow V t h = ∑ S, exp (t · (mag S)² + h · mag S)`,  `t = β c / 2`,

the law of the magnetization of free locks reweighed by `e^(t M²)`: the heat clock of the zeta lane.

**What is proved.**

1. `isingZ_uniform`: the Ising partition function with the uniform exchange `c` is
   `flow V (β c / 2) (β h)`.
2. `flow_zero`: at `t = 0` the locks are free, `flow V 0 h = (exp h + exp (−h)) ^ |V|`.
3. `flow_ne_zero_of_re_ne_zero`: for `t ≥ 0` and `Re h ≠ 0`, `flow V t h ≠ 0` (Lee–Yang through
   item 1): at every forward time of the clock every zero in the field lies on the imaginary axis.
4. Two locks: `flow_two` (`flow (Fin 2) t h = 2 + exp (4t) (exp (2h) + exp (−2h))`);
   `flow_two_zero_on_axis` (`flow (Fin 2) t (iθ/2) = 0 ↔ cos θ = −exp (−4t)`, for every real `t`);
   `flow_two_off_axis` (for `t < 0` a zero leaves the axis, from `antiferromagnet_zero_off_axis`);
   `seamTimes_two` (the times at which every zero lies on the axis are `[0, ∞)`);
   `zeroAngle_zero`, `zeroAngle_strictAntiOn`, `zeroAngle_mem`, `flow_two_zeroAngle` (the angle
   `arccos (−exp (−4t))` starts at `π` and falls strictly toward `π/2` on `t ≥ 0`, where the flow
   vanishes at the field `i · zeroAngle t / 2`; the bound `π/2 < zeroAngle t ≤ π` holds at every
   real `t`).
5. The heat equation: `hasDerivAt_flow_time` (`∂_t flow = ∑ S, (mag S)² · e^(…)`) and
   `deriv_deriv_flow_field` (the second derivative in the field is the same sum), so
   `heat_equation`: `∂_t flow = ∂_h² flow`.
6. The tree's heat operator (`heatE_free`): with the free locks read on the seam chart,
   `free z = flow V 0 (i z)`, `heatE t free z = flow V t (i z)` for every real `t` and complex `z`
   (each term is an exponential, `iteratedDeriv_sum_exp`, and the series in `k` is the exponential
   series of `t (mag S)²`).

[interpretation] The heat clock's sharpening is a ferromagnetic coupling of every lock to the
family's total (a mean field): forward time is cooling or a stronger exchange, backward time is an
antiferromagnetic one, and free locks sit at the threshold `0`.

**Limits.**  The uniform coupling only (the complete graph).  The set of times at which every zero
lies on the axis is computed for two locks only; for more locks `t ≥ 0` is contained in it by
item 3, and the converse is not proved.  The palette of `ξ` in place of the binomial law is the
zeta lane's and nothing here bears on it.  No limit over growing `V`.

Computational object: the helical pair interaction; touches the pair (the exchange), faces and
placement (a configuration is a face, the zeros' placement on the axis) and the tube (the clock);
the helix, the cell holonomy and the tower thread stay attached.

**Consumers.**  The atlas row `thermal.mean-field-heat-clock`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Coupling.MeanFieldHeatClock

open Finset Complex Holonics.Coupling.LeeYangIsing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [definition] The magnetization of the configuration whose up locks are `S`. -/
def mag (S : Finset V) : ℝ := ∑ i, spin S i

variable (V) in
/-- [definition] **The heat-clock flow**: the uniformly coupled partition function
`∑ S, exp (t · (mag S)² + h · mag S)` at clock time `t` and complex field `h`. -/
def flow (t : ℝ) (h : ℂ) : ℂ :=
  ∑ S : Finset V, Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + h * (mag S : ℂ))

/-- [proved-derived; formal-checked] **The uniform Ising partition function is the flow.**
`isingZ (fun _ _ => c) β (fun _ => h) = flow V (β c / 2) (β h)`. -/
theorem isingZ_uniform (c β : ℝ) (h : ℂ) :
    isingZ (fun _ _ : V => c) β (fun _ => h) = flow V (β * c / 2) (β * h) := by
  unfold isingZ flow
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [exponent]
  have h1 : ∑ i, ∑ j, c * spin S i * spin S j = c * mag S ^ 2 := by
    rw [mag, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, h * (spin S i : ℂ) = h * (mag S : ℂ) := by
    rw [mag, Complex.ofReal_sum, Finset.mul_sum]
  rw [h1, h2]
  push_cast
  ring

/-- [proved-standard; formal-checked] The weight of one configuration of free locks is the product of the locks' weights. -/
theorem exp_mul_mag (h : ℂ) (S : Finset V) :
    Complex.exp (h * (mag S : ℂ)) = (∏ _i ∈ S, Complex.exp h) * ∏ _i ∈ univ \ S, Complex.exp (-h) := by
  have hsum : h * (mag S : ℂ) = ∑ i, h * (spin S i : ℂ) := by
    rw [mag, Complex.ofReal_sum, Finset.mul_sum]
  rw [hsum, Complex.exp_sum, ← Finset.prod_mul_prod_compl S, Finset.compl_eq_univ_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun _ hi => by rw [spin_of_mem hi]; simp
  · refine Finset.prod_congr rfl fun _ hi => ?_
    rw [← Finset.compl_eq_univ_sdiff] at hi
    rw [spin_of_mem_compl hi]
    simp

/-- [proved-standard; formal-checked] **Free locks.**  At clock time `0` the flow is the product
of the locks' own sums, `flow V 0 h = (exp h + exp (−h)) ^ |V|`. -/
theorem flow_zero (h : ℂ) :
    flow V 0 h = (Complex.exp h + Complex.exp (-h)) ^ Fintype.card V := by
  rw [← Finset.card_univ, ← Finset.prod_const, Finset.prod_add, Finset.powerset_univ, flow]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← exp_mul_mag]
  congr 1
  simp

/-- [proved-derived; formal-checked] **Lee–Yang along the forward clock.**  For `t ≥ 0`, the flow
has no zero in a field with nonzero real part. -/
theorem flow_ne_zero_of_re_ne_zero {t : ℝ} (ht : 0 ≤ t) {h : ℂ} (hh : h.re ≠ 0) :
    flow V t h ≠ 0 := by
  intro hz
  have hu := isingZ_uniform (V := V) (2 * t) 1 h
  have hflow : flow V (1 * (2 * t) / 2) ((1 : ℝ) * h) = flow V t h := by
    congr 1 <;> push_cast <;> ring
  rw [hflow, hz] at hu
  exact hh (lee_yang_ising (fun _ _ : V => 2 * t) (fun _ _ => rfl) (fun _ _ => by linarith)
    one_pos h hu)

/-! ## Two locks -/

/-- [proved-standard; formal-checked] The magnetization of two locks. -/
theorem mag_fin_two (S : Finset (Fin 2)) : mag S = spin S 0 + spin S 1 := by
  rw [mag, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **Two locks.**
`flow (Fin 2) t h = 2 + exp (4t) (exp (2h) + exp (−2h))`. -/
theorem flow_two (t : ℝ) (h : ℂ) :
    flow (Fin 2) t h = 2 + Complex.exp (4 * t) * (Complex.exp (2 * h) + Complex.exp (-2 * h)) := by
  rw [flow]
  have hS : (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hS]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [mag_fin_two, spin]
  simp
  rw [mul_add (Complex.exp (4 * t)), ← Complex.exp_add, ← Complex.exp_add]
  ring_nf

/-- [proved-standard; formal-checked] **The two locks' zeros on the axis.**  For every real `t`
and `θ`, `flow (Fin 2) t (iθ/2) = 0` exactly when `cos θ = −exp (−4t)`. -/
theorem flow_two_zero_on_axis (t θ : ℝ) :
    flow (Fin 2) t (I * θ / 2) = 0 ↔ Real.cos θ = -Real.exp (-4 * t) := by
  have hc : flow (Fin 2) t (I * θ / 2) =
      ((2 + Real.exp (4 * t) * (2 * Real.cos θ) : ℝ) : ℂ) := by
    rw [flow_two]
    have e1 : 2 * (I * θ / 2) = (θ : ℂ) * I := by ring
    have e2 : -2 * (I * θ / 2) = -(θ : ℂ) * I := by ring
    rw [e1, e2, ← Complex.two_cos]
    push_cast
    ring
  have hinv : Real.exp (-4 * t) = (Real.exp (4 * t))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [hc, Complex.ofReal_eq_zero, hinv]
  have hpos := Real.exp_pos (4 * t)
  constructor
  · intro h0
    field_simp
    linarith
  · intro h0
    rw [h0]
    field_simp
    ring

/-- [counterexample; formal-checked] **Backward time leaves the axis.**  For `t < 0` the two
locks' flow has a zero in a field with nonzero real part (the antiferromagnet with exchange
`2t < 0`). -/
theorem flow_two_off_axis {t : ℝ} (ht : t < 0) :
    ∃ h : ℂ, h.re ≠ 0 ∧ flow (Fin 2) t h = 0 := by
  obtain ⟨h, hre, hz⟩ := antiferromagnet_zero_off_axis (K := -2 * t) (by linarith) one_pos
  refine ⟨h, hre, ?_⟩
  rw [isingZ_uniform] at hz
  have hflow : flow (Fin 2) (1 * -(-2 * t) / 2) ((1 : ℝ) * h) = flow (Fin 2) t h := by
    congr 1 <;> push_cast <;> ring
  rw [← hflow]
  exact hz

/-- [proved-derived; formal-checked] **The threshold of the clock for two locks is `0`.**  The
times at which every zero of the two locks' flow lies on the imaginary axis are `[0, ∞)`. -/
theorem seamTimes_two :
    {t : ℝ | ∀ h : ℂ, flow (Fin 2) t h = 0 → h.re = 0} = Set.Ici 0 := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_Ici]
  constructor
  · intro H
    by_contra hlt
    obtain ⟨h, hre, hz⟩ := flow_two_off_axis (not_le.mp hlt)
    exact hre (H h hz)
  · intro ht h hz
    by_contra hre
    exact flow_ne_zero_of_re_ne_zero ht hre hz

/-- [definition] The angle of the two locks' zero on the axis, `arccos (−exp (−4t))`. -/
def zeroAngle (t : ℝ) : ℝ := Real.arccos (-Real.exp (-4 * t))

/-- [proved-derived; formal-checked] At `t = 0` the two zeros coincide at the angle `π`. -/
theorem zeroAngle_zero : zeroAngle 0 = Real.pi := by
  simp [zeroAngle]

/-- [proved-derived; formal-checked] **Cooling moves the zero.**  On `t ≥ 0` the angle falls
strictly. -/
theorem zeroAngle_strictAntiOn : StrictAntiOn zeroAngle (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hmem : ∀ x : ℝ, 0 ≤ x → -Real.exp (-4 * x) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have h1 : Real.exp (-4 * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 := Real.exp_pos (-4 * x)
    constructor <;> linarith
  refine Real.strictAntiOn_arccos (hmem a ha) (hmem b hb) ?_
  have : Real.exp (-4 * b) < Real.exp (-4 * a) := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- [proved-derived; formal-checked] The angle lies in `(π/2, π]` at every real `t` (the
argument `−exp (−4t)` is negative for every `t`; only on `t ≥ 0` is it the angle of a zero on the
axis, by `flow_two_zero_on_axis` and `−exp (−4t) ≥ −1`). -/
theorem zeroAngle_mem (t : ℝ) : Real.pi / 2 < zeroAngle t ∧ zeroAngle t ≤ Real.pi := by
  refine ⟨?_, Real.arccos_le_pi _⟩
  rw [zeroAngle, lt_iff_not_ge, Real.arccos_le_pi_div_two]
  have := Real.exp_pos (-4 * t)
  linarith

/-- [proved-derived; formal-checked] **The angle is the zero's.**  For `t ≥ 0` the two locks' flow
vanishes at the field `i · zeroAngle t / 2`. -/
theorem flow_two_zeroAngle {t : ℝ} (ht : 0 ≤ t) :
    flow (Fin 2) t (I * (zeroAngle t : ℂ) / 2) = 0 := by
  have hpos := Real.exp_pos (-4 * t)
  have hle : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [flow_two_zero_on_axis, zeroAngle, Real.cos_arccos (by linarith) (by linarith)]

/-! ## The heat equation -/

/-- [proved-standard; formal-checked] **The clock derivative.**
`∂_t flow V t h = ∑ S, (mag S)² · exp (t (mag S)² + h mag S)`. -/
theorem hasDerivAt_flow_time (t : ℝ) (h : ℂ) :
    HasDerivAt (fun s : ℝ => flow V s h)
      (∑ S : Finset V, (mag S : ℂ) ^ 2 *
        Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + h * (mag S : ℂ))) t := by
  unfold flow
  refine HasDerivAt.fun_sum fun S _ => ?_
  have hin : HasDerivAt (fun s : ℝ => ((s * mag S ^ 2 : ℝ) : ℂ) + h * (mag S : ℂ))
      ((1 * mag S ^ 2 : ℝ) : ℂ) t :=
    (((hasDerivAt_id t).mul_const (mag S ^ 2)).ofReal_comp).add_const _
  exact hin.cexp.congr_deriv (by push_cast; ring)

/-- [proved-standard; formal-checked] The first derivative in the field. -/
theorem hasDerivAt_flow_field (t : ℝ) (h : ℂ) :
    HasDerivAt (fun k : ℂ => flow V t k)
      (∑ S : Finset V, (mag S : ℂ) *
        Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + h * (mag S : ℂ))) h := by
  unfold flow
  refine HasDerivAt.fun_sum fun S _ => ?_
  have hin : HasDerivAt (fun k : ℂ => ((t * mag S ^ 2 : ℝ) : ℂ) + k * (mag S : ℂ))
      (1 * (mag S : ℂ)) h :=
    ((hasDerivAt_id h).mul_const _).const_add _
  exact hin.cexp.congr_deriv (by ring)

/-- [proved-standard; formal-checked] The derivative in the field of the first derivative. -/
theorem hasDerivAt_flow_field_two (t : ℝ) (h : ℂ) :
    HasDerivAt (fun k : ℂ => ∑ S : Finset V, (mag S : ℂ) *
        Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + k * (mag S : ℂ)))
      (∑ S : Finset V, (mag S : ℂ) ^ 2 *
        Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + h * (mag S : ℂ))) h := by
  refine HasDerivAt.fun_sum fun S _ => ?_
  have hin : HasDerivAt (fun k : ℂ => ((t * mag S ^ 2 : ℝ) : ℂ) + k * (mag S : ℂ))
      (1 * (mag S : ℂ)) h :=
    ((hasDerivAt_id h).mul_const _).const_add _
  exact (hin.cexp.const_mul (mag S : ℂ)).congr_deriv (by ring)

/-- [proved-standard; formal-checked] **The second derivative in the field** is the same sum,
`∂_h² flow V t h = ∑ S, (mag S)² · exp (t (mag S)² + h mag S)`. -/
theorem deriv_deriv_flow_field (t : ℝ) (h : ℂ) :
    deriv (deriv fun k : ℂ => flow V t k) h =
      ∑ S : Finset V, (mag S : ℂ) ^ 2 *
        Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + h * (mag S : ℂ)) := by
  have hd : deriv (fun k : ℂ => flow V t k) = fun k => ∑ S : Finset V, (mag S : ℂ) *
      Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ) + k * (mag S : ℂ)) :=
    funext fun k => (hasDerivAt_flow_field t k).deriv
  rw [hd]
  exact (hasDerivAt_flow_field_two t h).deriv

/-- [proved-standard; formal-checked] **The heat equation.**  The clock derivative of the flow is
its second derivative in the field, `∂_t flow = ∂_h² flow`. -/
theorem heat_equation (t : ℝ) (h : ℂ) :
    deriv (fun s : ℝ => flow V s h) t = deriv (deriv fun k : ℂ => flow V t k) h := by
  rw [(hasDerivAt_flow_time t h).deriv, deriv_deriv_flow_field]

/-! ## The tree's heat operator -/

omit [DecidableEq V] in
/-- [proved-standard; formal-checked] The iterated derivatives of a finite sum of exponentials. -/
theorem iteratedDeriv_sum_exp (c : Finset V → ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => ∑ S : Finset V, Complex.exp (c S * z)) =
      fun z => ∑ S : Finset V, c S ^ n * Complex.exp (c S * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      refine (HasDerivAt.fun_sum fun S _ => ?_).deriv
      have hin : HasDerivAt (fun z : ℂ => c S * z) (c S * 1) z := (hasDerivAt_id z).const_mul _
      exact (hin.cexp.const_mul (c S ^ n)).congr_deriv (by ring)

/-- [proved-standard; formal-checked] The flow on the seam chart `h = i z` is a finite sum of exponentials. -/
theorem flow_seam (t : ℝ) (z : ℂ) :
    flow V t (I * z) = ∑ S : Finset V, Complex.exp (((t * mag S ^ 2 : ℝ) : ℂ)) *
      Complex.exp ((I * (mag S : ℂ)) * z) := by
  unfold flow
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Complex.exp_add]
  congr 1
  ring

open Holonics.Zeta.HeatFlowEntire Holonics.Zeta.EntireDerivativeGrowth in
/-- [proved-derived; formal-checked] **The tree's heat operator runs the clock.**  With the free
locks read on the seam chart, `free z = flow V 0 (i z)`, the derivative-series heat flow of
`Zeta/HeatFlowEntire` is the flow at time `t`: `heatE t free z = flow V t (i z)` for every real `t`
and complex `z`. -/
theorem heatE_free (t : ℝ) (z : ℂ) :
    heatE t (fun w => flow V 0 (I * w)) z = flow V t (I * z) := by
  have hfree : (fun w => flow V 0 (I * w)) =
      fun w : ℂ => ∑ S : Finset V, Complex.exp ((I * (mag S : ℂ)) * w) := by
    funext w
    rw [flow_seam]
    simp
  have hterm : ∀ k, heatTerm t (fun w => flow V 0 (I * w)) z k =
      ∑ S : Finset V, ((t * mag S ^ 2 : ℝ) : ℂ) ^ k / (k.factorial : ℂ) *
        Complex.exp ((I * (mag S : ℂ)) * z) := by
    intro k
    rw [heatTerm, hfree, iteratedDeriv_sum_exp (fun S => I * (mag S : ℂ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hI : (I * (mag S : ℂ)) ^ (2 * k) = (-(mag S : ℂ) ^ 2) ^ k := by
      rw [pow_mul, mul_pow, Complex.I_sq]
      ring
    rw [hI]
    push_cast
    rw [mul_pow, neg_pow (t : ℂ), neg_pow ((mag S : ℂ) ^ 2)]
    ring_nf
    rw [show ((-1 : ℂ) ^ (k * 2)) = 1 by rw [pow_mul']; simp]
    ring
  rw [heatE, tsum_congr hterm, flow_seam]
  refine (hasSum_sum fun S _ => ?_).tsum_eq
  have he := NormedSpace.expSeries_div_hasSum_exp (((t * mag S ^ 2 : ℝ) : ℂ))
  rw [← Complex.exp_eq_exp_ℂ] at he
  exact he.mul_right _

end Holonics.Coupling.MeanFieldHeatClock

section Audit

open Holonics.Coupling.MeanFieldHeatClock

#print axioms isingZ_uniform
#print axioms flow_zero
#print axioms flow_ne_zero_of_re_ne_zero
#print axioms flow_two
#print axioms flow_two_zero_on_axis
#print axioms flow_two_off_axis
#print axioms seamTimes_two
#print axioms zeroAngle_strictAntiOn
#print axioms zeroAngle_mem
#print axioms flow_two_zeroAngle
#print axioms heat_equation
#print axioms heatE_free

end Audit
