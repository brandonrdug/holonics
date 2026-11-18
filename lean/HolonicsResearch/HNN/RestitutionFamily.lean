import HolonicsResearch.HNN.CarriedRate
import Mathlib

/-!
# The junction's restitution family: the anchor passes, the differences return shortened

#410 (box "The junction's restitution family"); the junction record of November 13 on the tick's
return, §6 and §7
(`research/records/2026-11-13_THE_TICK_HOLDS_THE_JUNCTIONS_ANCHOR_WITHOUT_ITS_RETURN_THE_RETURN_IS_THE_SWING_OF_THE_STATE_TWO_TICKS_BACK_ABOUT_THE_PRESENT_ANCHOR_THE_TREES_OWN_ECHO_TERM_AND_A_MERGE_LOSES_WHICH_NEVER_HOW_MUCH.md`);
atlas `junction.restitution-family`, `tower.field-tick-return`.

At a junction whose ports carry arrivals `a_b` with weights `π_b` summing to one, the anchor is
`v = Σ_b π_b a_b` (`anchor`). For a restitution `Γ` the junction returns

```text
S(Γ) = P + Γ(P − I),        (S a)_b = v + Γ (v − a_b)
```

(`restitution`): the Swing of each arrival about the anchor, shortened by `Γ`.

[proved-derived; formal-checked] What is proved.

1. **The anchor passes, the differences return times `−Γ`** (`restitution_sub_anchor`,
   `restitution_const`, `restitution_of_anchor_zero`, `restitution_split`): `S` is the identity on
   the constant arrivals and `−Γ` on the arrivals of zero anchor, and every arrival splits into the
   two. The power splits the same way, `Σ_b π_b (S a)_b² = v² + Γ² Σ_b π_b (a_b − v)²`
   (`restitution_power`).
2. **A port's own return is `(1 + Γ)π_b − Γ`** (`restitutionMatrix`, `restitution_eq_mulVec`,
   `restitutionMatrix_diag`); at `d` equal ports it is `1/d` at `Γ = 0` (the broadcast anchor), `0`
   at `Γ = 1/(d − 1)` (the matched splitter) and `(2 − d)/d` at `Γ = 1` (the half-turn `2P − I`)
   (`ownReturn_equal_ports`).
3. **With one tick of transit the family closes on the sites** (`siteAnchor`, `unit_transit`,
   `unit_transit_swing`): waves that cross a contact in one tick,
   `a_(j←i)^(k+1) = (1 + Γ) v_i^k − Γ a_(i←j)^k`, on reciprocal contacts with weights `π_ij`
   standing over the ticks and summing to one at each site, give
   `v_i^(k+2) = (1 + Γ)(A v^(k+1))_i − Γ v_i^k`, that is `v^(k+2) − Av^(k+1) = −Γ(v^k − Av^(k+1))`.
4. **The modes** (`mode_recurrence`, `turning_root_normSq`, `turning_root_norm`): a mode of the mean
   with value `λ` and a root `z` of `z² − (1 + Γ)λ z + Γ` give the solution `zᵏ`; where
   `(1 + Γ)²λ² ≤ 4Γ` every root has modulus `√Γ`, through `HNN/CarriedRate.root_normSq`, the
   carried rate's own modulus.
5. **The slow root** (`slowRoot`, `slowRoot_zero`, `slowRoot_isRoot`, `hasDerivAt_slowRoot`,
   `slowRoot_first_order`): at `λ = 1 − ε` the root `((1 + Γ)λ + √((1 + Γ)²λ² − 4Γ))/2` is `1` at
   `ε = 0` and has derivative `−ρ`, `ρ = (1 + Γ)/(1 − Γ)`, so it is `1 − ρε + o(ε)`; at `ε = 0` the
   other root is `Γ` (`charPoly_at_one`).
6. **The constitution's value** (`echoShare_equal`, `echo_restitution_equal`,
   `echo_restitution_matches_splitter`): for `d` equal reciprocal partners the echo share is
   `B = 1/d`, `B/(1 − B) = 1/(d − 1)`, the matched splitter's `Γ` of item 2, so the two
   derivations agree.
7. **The chart** (`rho_of_gamma`, `gamma_of_rho`, `gamma_abs_lt_one`, `telegraph_rho`):
   `Γ = (ρ − 1)/(ρ + 1)` inverts `ρ = (1 + Γ)/(1 − Γ)`, `|Γ| < 1` at every `ρ > 0`, and the
   telegraph step's `Γ = (2τ − 1)/(2τ + 1)` has `ρ = 2τ`.
8. **The two-tick map loses nothing while `Γ ≠ 0`** (`twoTick`, `twoTick_bijective`):
   `(x⁻, x) ↦ (x, (1 + Γ)F(x) − Γx⁻)` is a bijection for every `F`.

[agent-inferred] **Limits.** Real values on the ports; the complex chart of the same family is the
same algebra with `|·|²`. One `Γ` for the whole junction network (the record asks one `Γ` among a
site's partners; a `Γ` per site needs it constant across each site's partners and is not stated).
The slow root's expansion is the derivative at `ε = 0`; the second-order term is not computed. No
three-port statement (the record's microwave remark) is made. The built tick of the November tower
adds where this family sets (the record's §13.1), so this file is the law's junction, not the
built tick.

The computational object is the helical pair interaction: the junction's return is the Swing of each
arrival about the anchor (a half-turn shortened by `Γ`), and read on the sites with one tick of
transit it is the Swing of the state two ticks back about the present anchor, the carried rate.
Of the winding guide's six general objects this touches the pair (the junction's contacts and
their reflection) and the tube (the two-tick clocked span); the helix, faces and placement, the
cell holonomy and the tower thread stay attached.

Consumers: the atlas rows `junction.restitution-family` and `tower.field-tick-return`;
`HNN/CarriedRate` holds the modulus.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.RestitutionFamily

open Filter Topology Matrix

/-! ## 1. The family at one junction -/

section Junction

variable {ι : Type*} [Fintype ι]

/-- [definition] **The anchor** `v = Σ_b π_b a_b`. -/
def anchor (π a : ι → ℝ) : ℝ := ∑ b, π b * a b

/-- [definition] **The restitution about the anchor**, `S(Γ) = P + Γ(P − I)`:
`(S a)_b = v + Γ(v − a_b)`. -/
def restitution (Γ : ℝ) (π a : ι → ℝ) : ι → ℝ := fun b => anchor π a + Γ * (anchor π a - a b)

/-- [proved-derived; formal-checked] **Each arrival's departure returns half-turned and
shortened**: `(S a)_b − v = −Γ(a_b − v)`. -/
theorem restitution_sub_anchor (Γ : ℝ) (π a : ι → ℝ) (b : ι) :
    restitution Γ π a b - anchor π a = -Γ * (a b - anchor π a) := by
  simp only [restitution]; ring

/-- [proved-derived; formal-checked] The anchor of a constant arrival is that constant. -/
theorem anchor_const {π : ι → ℝ} (hπ : ∑ b, π b = 1) (c : ℝ) : anchor π (fun _ => c) = c := by
  simp only [anchor, ← Finset.sum_mul, hπ, one_mul]

/-- [proved-derived; formal-checked] **The anchor passes whole**: `S` is the identity on the
constant arrivals, at every `Γ`. -/
theorem restitution_const {π : ι → ℝ} (hπ : ∑ b, π b = 1) (Γ c : ℝ) :
    restitution Γ π (fun _ => c) = fun _ => c := by
  funext b
  simp only [restitution, anchor_const hπ]; ring

/-- [proved-derived; formal-checked] **The differences return times `−Γ`**: on an arrival of zero
anchor, `S a = −Γ a`. -/
theorem restitution_of_anchor_zero (Γ : ℝ) (π a : ι → ℝ) (ha : anchor π a = 0) :
    restitution Γ π a = fun b => -Γ * a b := by
  funext b
  simp only [restitution, ha]; ring

/-- [proved-derived; formal-checked] **The split**: an arrival is its anchor plus its differences,
the anchor passing and the differences returning times `−Γ`. -/
theorem restitution_split {π : ι → ℝ} (hπ : ∑ b, π b = 1) (Γ : ℝ) (a : ι → ℝ) :
    anchor π (fun b => a b - anchor π a) = 0 ∧
      restitution Γ π (fun b => a b - anchor π a) = (fun b => -Γ * (a b - anchor π a)) ∧
      restitution Γ π a = fun b => anchor π a + -Γ * (a b - anchor π a) := by
  have h0 : anchor π (fun b => a b - anchor π a) = 0 := by
    simp only [anchor, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ, one_mul, sub_self]
  refine ⟨h0, restitution_of_anchor_zero Γ π _ h0, ?_⟩
  funext b
  simp only [restitution]; ring

/-- [proved-derived; formal-checked] **The power splits as the arrivals do**:
`Σ_b π_b (S a)_b² = v² + Γ² Σ_b π_b (a_b − v)²`. -/
theorem restitution_power {π : ι → ℝ} (hπ : ∑ b, π b = 1) (Γ : ℝ) (a : ι → ℝ) :
    ∑ b, π b * restitution Γ π a b ^ 2 =
      anchor π a ^ 2 + Γ ^ 2 * ∑ b, π b * (a b - anchor π a) ^ 2 := by
  set v := anchor π a with hv
  have hdev : ∑ b, π b * (a b - v) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ, one_mul]
    rw [hv, anchor]; ring
  have hexp : ∀ b, π b * restitution Γ π a b ^ 2 =
      v ^ 2 * π b + (-2 * Γ * v) * (π b * (a b - v)) + Γ ^ 2 * (π b * (a b - v) ^ 2) := by
    intro b; simp only [restitution, ← hv]; ring
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hπ, hdev]
  ring

variable [DecidableEq ι]

/-- [definition] **The restitution as a matrix**: `S_bc = (1 + Γ)π_c − Γ[b = c]`. -/
def restitutionMatrix (Γ : ℝ) (π : ι → ℝ) : Matrix ι ι ℝ :=
  fun b c => (1 + Γ) * π c - Γ * (if b = c then 1 else 0)

/-- [proved-derived; formal-checked] The restitution is the matrix's action. -/
theorem restitution_eq_mulVec (Γ : ℝ) (π a : ι → ℝ) :
    restitution Γ π a = restitutionMatrix Γ π *ᵥ a := by
  funext b
  simp only [restitution, anchor, restitutionMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

omit [Fintype ι] in
/-- [proved-derived; formal-checked] **A port's own return is `(1 + Γ)π_b − Γ`.** -/
theorem restitutionMatrix_diag (Γ : ℝ) (π : ι → ℝ) (b : ι) :
    restitutionMatrix Γ π b b = (1 + Γ) * π b - Γ := by
  simp [restitutionMatrix]

end Junction

/-- [definition] The own return at one port of share `p`. -/
def ownReturn (Γ p : ℝ) : ℝ := (1 + Γ) * p - Γ

/-- [proved-derived; formal-checked] **The three named junctions at `d` equal ports**: own return
`1/d` at `Γ = 0`, `0` at `Γ = 1/(d − 1)`, `(2 − d)/d` at `Γ = 1`; the differences' power factor
`Γ²` at the splitter is `1/(d − 1)²`. -/
theorem ownReturn_equal_ports {d : ℝ} (hd : 1 < d) :
    ownReturn 0 (1 / d) = 1 / d ∧ ownReturn (1 / (d - 1)) (1 / d) = 0 ∧
      ownReturn 1 (1 / d) = (2 - d) / d ∧ (1 / (d - 1)) ^ 2 = 1 / (d - 1) ^ 2 := by
  have hd0 : d ≠ 0 := by linarith
  have hd1 : d - 1 ≠ 0 := by linarith
  refine ⟨by simp [ownReturn], ?_, ?_, by rw [div_pow, one_pow]⟩
  · unfold ownReturn; field_simp; ring
  · unfold ownReturn; field_simp; ring

/-! ## 2. One tick of transit closes the family on the sites -/

section Transit

variable {σ : Type*} [Fintype σ]

/-- [definition] **A site's anchor at tick `k`**, `v_i^k = Σ_j π_ij a_(i←j)^k`, with
`w k i j = a_(i←j)^k` the wave arriving at `i` from `j`. -/
def siteAnchor (π : σ → σ → ℝ) (w : ℕ → σ → σ → ℝ) (k : ℕ) (i : σ) : ℝ :=
  ∑ j, π i j * w k i j

/-- [definition] **One tick of transit on reciprocal contacts**: the wave reaching `i` from `j` at
`k + 1` is `j`'s restitution toward `i`, `(1 + Γ) v_j^k − Γ a_(j←i)^k`. -/
def UnitTransit (Γ : ℝ) (π : σ → σ → ℝ) (w : ℕ → σ → σ → ℝ) : Prop :=
  ∀ k i j, w (k + 1) i j = (1 + Γ) * siteAnchor π w k j - Γ * w k j i

/-- [proved-derived; formal-checked] **The site step**: with weights summing to one at each site
and standing over the ticks, `v_i^(k+2) = (1 + Γ)(A v^(k+1))_i − Γ v_i^k`. -/
theorem unit_transit {Γ : ℝ} {π : σ → σ → ℝ} (hπ : ∀ i, ∑ j, π i j = 1)
    {w : ℕ → σ → σ → ℝ} (hw : UnitTransit Γ π w) (k : ℕ) (i : σ) :
    siteAnchor π w (k + 2) i =
      (1 + Γ) * ∑ j, π i j * siteAnchor π w (k + 1) j - Γ * siteAnchor π w k i := by
  have hecho : ∑ j, π i j * w (k + 1) j i = siteAnchor π w k i := by
    have hj : ∀ j, π i j * w (k + 1) j i =
        (1 + Γ) * siteAnchor π w k i * π i j - Γ * (π i j * w k i j) := by
      intro j; rw [hw k j i]; ring
    simp only [hj, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ i, mul_one]
    rw [siteAnchor]; ring
  have hstep : siteAnchor π w (k + 2) i =
      ∑ j, π i j * ((1 + Γ) * siteAnchor π w (k + 1) j - Γ * w (k + 1) j i) := by
    simp only [siteAnchor]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw (k + 1) i j, siteAnchor]
  rw [hstep]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← hecho, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_; ring
  · refine Finset.sum_congr rfl fun j _ => ?_; ring

/-- [proved-derived; formal-checked] **The site step is a Swing two ticks back**:
`v^(k+2) − Av^(k+1) = −Γ(v^k − Av^(k+1))`. -/
theorem unit_transit_swing {Γ : ℝ} {π : σ → σ → ℝ} (hπ : ∀ i, ∑ j, π i j = 1)
    {w : ℕ → σ → σ → ℝ} (hw : UnitTransit Γ π w) (k : ℕ) (i : σ) :
    siteAnchor π w (k + 2) i - ∑ j, π i j * siteAnchor π w (k + 1) j =
      -Γ * (siteAnchor π w k i - ∑ j, π i j * siteAnchor π w (k + 1) j) := by
  rw [unit_transit hπ hw k i]; ring

end Transit

/-! ## 3. The modes and the slow root -/

/-- [proved-derived; formal-checked] **A root gives a mode's solution**: if
`z² − (1 + Γ)λz + Γ = 0`, then `c_k = zᵏ` obeys `c_(k+2) = (1 + Γ)λ c_(k+1) − Γ c_k`. -/
theorem mode_recurrence {Γ l : ℝ} {z : ℂ}
    (hz : z * z - (((1 + Γ) * l : ℝ) : ℂ) * z + (Γ : ℂ) = 0) (k : ℕ) :
    z ^ (k + 2) = (((1 + Γ) * l : ℝ) : ℂ) * z ^ (k + 1) - (Γ : ℂ) * z ^ k := by
  have : z ^ (k + 2) - ((((1 + Γ) * l : ℝ) : ℂ) * z ^ (k + 1) - (Γ : ℂ) * z ^ k) =
      z ^ k * (z * z - (((1 + Γ) * l : ℝ) : ℂ) * z + (Γ : ℂ)) := by ring
  rw [hz, mul_zero] at this
  exact sub_eq_zero.mp this

/-- [proved-standard; formal-checked] **Where the mode turns, its roots have modulus squared `Γ`**:
`(1 + Γ)²λ² ≤ 4Γ` gives `|z|² = Γ` (`HNN/CarriedRate.root_normSq`). -/
theorem turning_root_normSq {Γ l : ℝ} (hdisc : ((1 + Γ) * l) ^ 2 ≤ 4 * Γ) {z : ℂ}
    (hz : z * z - (((1 + Γ) * l : ℝ) : ℂ) * z + (Γ : ℂ) = 0) : Complex.normSq z = Γ :=
  Holonics.HNN.CarriedRate.root_normSq hdisc hz

/-- [proved-standard; formal-checked] **The turning roots have modulus `√Γ`.** -/
theorem turning_root_norm {Γ l : ℝ} (hdisc : ((1 + Γ) * l) ^ 2 ≤ 4 * Γ) {z : ℂ}
    (hz : z * z - (((1 + Γ) * l : ℝ) : ℂ) * z + (Γ : ℂ) = 0) : ‖z‖ = Real.sqrt Γ := by
  have h := turning_root_normSq hdisc hz
  rw [Complex.normSq_eq_norm_sq] at h
  rw [← h, Real.sqrt_sq (norm_nonneg z)]

/-- [proved-derived; formal-checked] At the conserved mode the roots are `1` and `Γ`:
`z² − (1 + Γ)z + Γ = (z − 1)(z − Γ)`. -/
theorem charPoly_at_one (Γ z : ℝ) : z * z - (1 + Γ) * z + Γ = (z - 1) * (z - Γ) := by ring

/-- [definition] The discriminant at `λ = 1 − ε`. -/
def disc (Γ ε : ℝ) : ℝ := ((1 + Γ) * (1 - ε)) ^ 2 - 4 * Γ

/-- [definition] **The slow root** at `λ = 1 − ε`, `((1 + Γ)λ + √((1 + Γ)²λ² − 4Γ))/2`. -/
def slowRoot (Γ ε : ℝ) : ℝ := ((1 + Γ) * (1 - ε) + Real.sqrt (disc Γ ε)) / 2

/-- [proved-derived; formal-checked] The slow root is a root wherever the discriminant is
nonnegative. -/
theorem slowRoot_isRoot {Γ ε : ℝ} (hD : 0 ≤ disc Γ ε) :
    slowRoot Γ ε * slowRoot Γ ε - (1 + Γ) * (1 - ε) * slowRoot Γ ε + Γ = 0 := by
  have hs := Real.sq_sqrt hD
  have hd : disc Γ ε = ((1 + Γ) * (1 - ε)) ^ 2 - 4 * Γ := rfl
  unfold slowRoot
  linear_combination (1 / 4 : ℝ) * hs + (1 / 4 : ℝ) * hd

/-- [proved-derived; formal-checked] **At `ε = 0` the slow root is the conserved mode, `1`.** -/
theorem slowRoot_zero {Γ : ℝ} (hΓ : Γ ≤ 1) : slowRoot Γ 0 = 1 := by
  have : disc Γ 0 = (1 - Γ) ^ 2 := by unfold disc; ring
  unfold slowRoot
  rw [this, Real.sqrt_sq (by linarith)]
  ring

/-- [proved-derived; formal-checked] **The slow root settles `ρ` times sooner**: for `Γ < 1`,
`d/dε slowRoot = −ρ` at `ε = 0`, `ρ = (1 + Γ)/(1 − Γ)`. -/
theorem hasDerivAt_slowRoot {Γ : ℝ} (hΓ : Γ < 1) :
    HasDerivAt (slowRoot Γ) (-((1 + Γ) / (1 - Γ))) 0 := by
  have h1 : (1 - Γ) ≠ 0 := by linarith
  have hD0 : disc Γ 0 = (1 - Γ) ^ 2 := by unfold disc; ring
  have hDne : disc Γ 0 ≠ 0 := by rw [hD0]; positivity
  have hl : HasDerivAt (fun ε : ℝ => (1 + Γ) * (1 - ε)) ((1 + Γ) * (-1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_sub 1).const_mul (1 + Γ)
  have hdD : HasDerivAt (disc Γ) (-(2 * (1 + Γ) ^ 2)) 0 := by
    have := (hl.pow 2).sub (hasDerivAt_const (0 : ℝ) (4 * Γ))
    unfold disc
    refine this.congr_deriv ?_
    norm_num
    ring
  have hsq := hdD.sqrt hDne
  have hall : HasDerivAt (fun ε => ((1 + Γ) * (1 - ε) + Real.sqrt (disc Γ ε)) / 2)
      (((1 + Γ) * (-1) + -(2 * (1 + Γ) ^ 2) / (2 * Real.sqrt (disc Γ 0))) / 2) 0 :=
    (hl.add hsq).div_const 2
  have hsqrt0 : Real.sqrt (disc Γ 0) = 1 - Γ := by rw [hD0, Real.sqrt_sq (by linarith)]
  refine hall.congr_deriv ?_
  rw [hsqrt0]
  field_simp
  ring

/-- [proved-derived; formal-checked] **To first order the slow root is `1 − ρε`**:
`slowRoot ε − (1 − ρε) = o(ε)`. -/
theorem slowRoot_first_order {Γ : ℝ} (hΓ : Γ < 1) :
    (fun ε => slowRoot Γ ε - (1 - (1 + Γ) / (1 - Γ) * ε)) =o[𝓝 0] fun ε => ε := by
  have h := (hasDerivAt_slowRoot hΓ).isLittleO
  rw [slowRoot_zero hΓ.le] at h
  refine h.congr (fun ε => ?_) (fun ε => sub_zero ε)
  simp only [sub_zero, smul_eq_mul]
  ring

/-! ## 4. The value the constitution names, and the chart -/

section Echo

variable {σ : Type*}

/-- [definition] **The echo share** of a site: `B_i = Σ_(j ∈ partners) p_ij p_ji`, the share of
its state two ticks before that returns to it. -/
def echoShare (s : Finset σ) (p : σ → σ → ℝ) (i : σ) : ℝ := ∑ j ∈ s, p i j * p j i

/-- [proved-derived; formal-checked] **At `d` equal reciprocal partners the echo is `1/d`.** -/
theorem echoShare_equal {s : Finset σ} {p : σ → σ → ℝ} {i : σ} {d : ℕ} (hs : s.card = d)
    (hd : 0 < d) (hp : ∀ j ∈ s, p i j = 1 / d ∧ p j i = 1 / d) :
    echoShare s p i = 1 / d := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [echoShare, Finset.sum_congr rfl fun j hj => by rw [(hp j hj).1, (hp j hj).2],
    Finset.sum_const, hs, nsmul_eq_mul]
  field_simp

end Echo

/-- [proved-derived; formal-checked] **The constitution's restitution at `d` equal shares**:
`B = 1/d` gives `B/(1 − B) = 1/(d − 1)`. -/
theorem echo_restitution_equal {d : ℝ} (hd : 1 < d) : (1 / d) / (1 - 1 / d) = 1 / (d - 1) := by
  have hd0 : d ≠ 0 := by linarith
  have hd1 : d - 1 ≠ 0 := by linarith
  field_simp

/-- [proved-derived; formal-checked] **The two derivations agree**: the echo's `Γ* = B/(1 − B)`
at `d` equal shares is the matched splitter, the restitution with no own return. -/
theorem echo_restitution_matches_splitter {d : ℝ} (hd : 1 < d) :
    ownReturn ((1 / d) / (1 - 1 / d)) (1 / d) = 0 := by
  rw [echo_restitution_equal hd]
  exact (ownReturn_equal_ports hd).2.1

/-- [proved-derived; formal-checked] `ρ = (1 + Γ)/(1 − Γ)` at `Γ = (ρ − 1)/(ρ + 1)`. -/
theorem rho_of_gamma {ρ : ℝ} (hρ : 0 < ρ) :
    (1 + (ρ - 1) / (ρ + 1)) / (1 - (ρ - 1) / (ρ + 1)) = ρ := by
  have h1 : ρ + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- [proved-derived; formal-checked] `Γ = (ρ − 1)/(ρ + 1)` at `ρ = (1 + Γ)/(1 − Γ)`. -/
theorem gamma_of_rho {Γ : ℝ} (hΓ : Γ < 1) :
    ((1 + Γ) / (1 - Γ) - 1) / ((1 + Γ) / (1 - Γ) + 1) = Γ := by
  have h1 : 1 - Γ ≠ 0 := by linarith
  field_simp
  ring

/-- [proved-derived; formal-checked] **A finite load reflects less than whole**: `|Γ| < 1` at every
`ρ > 0`, so the step is passive by its form. -/
theorem gamma_abs_lt_one {ρ : ℝ} (hρ : 0 < ρ) : |(ρ - 1) / (ρ + 1)| < 1 := by
  have h1 : 0 < ρ + 1 := by linarith
  rw [abs_div, abs_of_pos h1, div_lt_one h1, abs_lt]
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The telegraph step**: `Γ = (2τ − 1)/(2τ + 1)` has
`ρ = 2τ`, twice the relaxation time in ticks. -/
theorem telegraph_rho {τ : ℝ} (hτ : 0 < τ) :
    (1 + (2 * τ - 1) / (2 * τ + 1)) / (1 - (2 * τ - 1) / (2 * τ + 1)) = 2 * τ := by
  have := rho_of_gamma (ρ := 2 * τ) (by linarith)
  exact this

/-! ## 5. The two-tick map -/

section TwoTick

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- [definition] **The two-tick map** `(x⁻, x) ↦ (x, (1 + Γ)F(x) − Γx⁻)`. -/
def twoTick (Γ : ℝ) (F : V → V) (p : V × V) : V × V :=
  (p.2, (1 + Γ) • F p.2 - Γ • p.1)

/-- [definition] Its inverse while `Γ ≠ 0`. -/
def twoTickInv (Γ : ℝ) (F : V → V) (p : V × V) : V × V :=
  (Γ⁻¹ • ((1 + Γ) • F p.1 - p.2), p.1)

/-- [proved-derived; formal-checked] **The two-tick map merges nothing while `Γ ≠ 0`**, for every
`F`. -/
theorem twoTick_bijective {Γ : ℝ} (hΓ : Γ ≠ 0) (F : V → V) : Function.Bijective (twoTick Γ F) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨twoTickInv Γ F, ?_, ?_⟩
  · intro p
    simp only [twoTick, twoTickInv]
    ext
    · simp only [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hΓ, one_smul]
    · rfl
  · intro p
    simp only [twoTick, twoTickInv]
    ext
    · rfl
    · simp only [smul_smul, mul_inv_cancel₀ hΓ, one_smul, sub_sub_cancel]

end TwoTick

end Holonics.HNN.RestitutionFamily
