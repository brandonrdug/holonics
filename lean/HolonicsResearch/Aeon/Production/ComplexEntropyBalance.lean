import Holonics.Aeon.Production.PathReversal
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The entropy balance on a complex: a density, its current, and a nonnegative production

[definition] The record of October 22 (order is torsion, §5.4 and §8) reads entropy as a density with a current and a
nonnegative production, `∂ₜ s + d*J_s = σ ≥ 0` with `σ = Σ_c J_c A_c` (each flux times its affinity), read by a
receiver over a partition. On a finite complex with incidence `B e v` (edge `e` at vertex `v`) the **divergence**
of a current is `(∂J)_v = Σ_e B e v J_e` (`divergence`), the **production** of currents against affinities is
`Σ_e J_e A_e` (`production`), and a constitution is **passive** when every edge's term is nonnegative (`Passive`).
For a finite Markov law `p > 0` moving under rates `W` (`ṗ_x = −Σ_y j(x,y)`, the master equation) the record's
quantities are, per state `x` and ordered pair `(x, y)`:

```text
j(x,y)   = p_x W_xy − p_y W_yx                                    (edgeCurrent, the net current)
A(x,y)   = log (p_x W_xy) − log (p_y W_yx)                        (edgeAffinity)
s_x      = −p_x log p_x                                           (density)
J_s(x,y) = −j(x,y) (½ (log p_x + log p_y) + 1)                    (entropyCurrent)
φ_x      = ½ Σ_y j(x,y) (log W_xy − log W_yx)                     (bathFlux, the entropy given to the medium)
σ_x      = ½ Σ_y j(x,y) A(x,y)                                    (localProduction)
```

[proved-derived; formal-checked] What is proved.

1. **Stokes on a complex.** `Σ_v f_v (∂J)_v = Σ_e (d f)_e J_e` (`stokes`), so when every edge's incidence sums to
   zero (a closed complex, `d 1 = 0`) the divergence sums to zero (`sum_divergence_eq_zero`), and a density obeying
   `ṡ_v + (∂J_s)_v = σ_v` has total rate `Σ_v σ_v` (`hasDerivAt_total`); against a passive constitution that rate is
   the production and is nonnegative (`hasDerivAt_total_production`, `production_nonneg`), zero exactly when every
   edge's term vanishes (`production_eq_zero_iff`).
2. **The passive constitutions.** A linear constitution `J_e = g_e A_e` with `g ≥ 0` is passive
   (`passive_linear`), its production is `Σ g_e A_e²` (`production_linear`), and for `g > 0` it vanishes exactly
   when every affinity does (`linear_production_eq_zero_iff`). The master equation's constitution
   `j = p_x W_xy − p_y W_yx` against `A = log (p_x W_xy) − log (p_y W_yx)` is passive for a positive law and rates
   with symmetric support (`edge_term_nonneg`, `passive_pairs`): each term is `(u − v)(log u − log v) ≥ 0`
   (`sub_mul_log_sub_nonneg`), zero exactly when `u = v` (`sub_mul_log_sub_eq_zero_iff`).
3. **The pair complex.** The ordered pairs of states, with `B (x,y) v = [v = x] − [v = y]` (`pairIncidence`), are a
   closed complex (`sum_pairIncidence`), the divergence of a current there is its outflow less its inflow
   (`divergence_pairIncidence`), and for an antisymmetric current carried as halves on the two orientations it is
   the outflow `Σ_y J(x,y)` (`divergence_pairIncidence_half`). Stokes reads `Σ_x Σ_y J(x,y) = 0`
   (`sum_outflow_eq_zero`).
4. **The local balance of the master equation.** Along any path with `ṗ_x = −Σ_y j(x,y)` at a positive law,
   `ṡ_x + Σ_y J_s(x,y) + φ_x = σ_x` (`hasDerivAt_density`, from the edgewise identity `balance_identity`), with
   `J_s` antisymmetric (`entropyCurrent_swap`), and on the pair complex `ṡ_x + (∂J_s)_x + φ_x = σ_x`
   (`hasDerivAt_density_complex`). Each local production is nonnegative (`localProduction_nonneg`).
5. **The summed balance and the join to `PathReversal`.** `dH/dt = σ − Σ_x φ_x` (`hasDerivAt_entropy`), and the
   total production is `PathReversal`'s epoch production of the law `p` under the rates `W`,
   `Σ_x σ_x = Σ_(x,y) p_x W_xy log (p_x W_xy / p_y W_yx)` (`totalProduction_eq_epochProduction`), so it is
   nonnegative and vanishes exactly under detailed balance (`totalProduction_nonneg`,
   `totalProduction_eq_zero_iff`); it is the production of the pair complex's half currents against their
   affinities (`totalProduction_eq_production`). The bath flux reads `PathReversal`'s affinity clock
   `log (W_xy / W_yx)` against the current (`bathFlux_eq_affinity`). When every bath flux vanishes and the law moves
   for all time, the entropy is monotone (`entropy_monotone_of_bath_zero`).

The rates `W` are a fixed constitution and the law `p` moves; the diagonal of `W` enters no term (`j(x,x) = 0`).
The production is read in the real chart: the law and the rates are reals, as in `PathReversal.RealChart`, and the
exact rational chart of that owner is not restated here.

The computational object is the helical pair interaction: each ordered pair of states is a pair contact whose slip
is the net current `j`, its affinity `A` is the log of the contact's flow ratio, and the production is the contact
material `Σ j A`, dissipated at each contact, never negative; the entropy current carries the density across the
contact and Stokes cancels it on the closed complex. Of the winding guide's six general objects this touches the
pair (each contact's current and affinity) and the cell holonomy (the affinity clock `log (W_xy / W_yx)` whose cycle
readings `PathReversal` owns); the helix, faces and placement, the tube and the tower thread stay attached.

What stands beside it: `Aeon/Production/PathReversal` owns the epoch production and its vanishing under detailed
balance, which item 5 joins; `Physics/Thermal/Schnakenberg` splits that production across a neck and holds the
rational sign certificate of one junction; `Physics/TwoCellEntropyTransport` is the two-cell instance with
symmetric rates; `Aeon/Production/PartitionDeBruijn` reads the symmetric case as de Bruijn's identity on a
partition. The continuum balance `∂ₜ s + ∇·J_s = σ` on a manifold, and the Schnakenberg cycle decomposition of `σ`
over a cycle basis, are not stated.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.ComplexEntropyBalance

open Finset Holonics.Aeon.Production.PathReversal

/-! ## 1. Stokes and passivity on a complex -/

section Complex

variable {V E : Type*} [Fintype V] [Fintype E]

/-- [definition] **The divergence** of a current `J` through the incidence `B e v`: `(∂J)_v = Σ_e B e v J_e`. -/
def divergence (B : E → V → ℝ) (J : E → ℝ) (v : V) : ℝ := ∑ e, B e v * J e

/-- [definition] **The coboundary** of a potential: `(d f)_e = Σ_v B e v f_v`. -/
def coboundary (B : E → V → ℝ) (f : V → ℝ) (e : E) : ℝ := ∑ v, B e v * f v

/-- [proved-standard; formal-checked] **Stokes on a complex**: `⟨f, ∂J⟩ = ⟨d f, J⟩`. -/
theorem stokes (B : E → V → ℝ) (J : E → ℝ) (f : V → ℝ) :
    ∑ v, f v * divergence B J v = ∑ e, coboundary B f e * J e := by
  unfold divergence coboundary
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun e _ => sum_congr rfl fun v _ => by ring

/-- [proved-standard; formal-checked] **On a closed complex the divergence sums to zero.** -/
theorem sum_divergence_eq_zero {B : E → V → ℝ} (hB : ∀ e, ∑ v, B e v = 0) (J : E → ℝ) :
    ∑ v, divergence B J v = 0 := by
  have h := stokes B J fun _ => 1
  simp only [one_mul] at h
  rw [h]
  simp [coboundary, hB]

/-- [definition] **The production** of currents against affinities: `Σ_e J_e A_e`. -/
def production (J A : E → ℝ) : ℝ := ∑ e, J e * A e

/-- [definition] **A passive constitution**: every edge's flux times its affinity is nonnegative. -/
def Passive (J A : E → ℝ) : Prop := ∀ e, 0 ≤ J e * A e

/-- [proved-standard; formal-checked] A passive constitution produces nonnegatively. -/
theorem production_nonneg {J A : E → ℝ} (h : Passive J A) : 0 ≤ production J A :=
  sum_nonneg fun e _ => h e

/-- [proved-standard; formal-checked] A passive production vanishes exactly when every edge's term does. -/
theorem production_eq_zero_iff {J A : E → ℝ} (h : Passive J A) :
    production J A = 0 ↔ ∀ e, J e * A e = 0 := by
  unfold production
  rw [sum_eq_zero_iff_of_nonneg fun e _ => h e]
  simp

omit [Fintype E] in
/-- [proved-standard; formal-checked] **A linear constitution `J = g A` with `g ≥ 0` is passive.** -/
theorem passive_linear {g A : E → ℝ} (hg : ∀ e, 0 ≤ g e) : Passive (fun e => g e * A e) A :=
  fun e => by rw [mul_assoc]; exact mul_nonneg (hg e) (mul_self_nonneg _)

/-- [proved-standard; formal-checked] The linear production is `Σ g_e A_e²`. -/
theorem production_linear (g A : E → ℝ) :
    production (fun e => g e * A e) A = ∑ e, g e * A e ^ 2 :=
  sum_congr rfl fun e _ => by ring

/-- [proved-standard; formal-checked] For `g > 0` the linear production vanishes exactly at zero affinity. -/
theorem linear_production_eq_zero_iff {g A : E → ℝ} (hg : ∀ e, 0 < g e) :
    production (fun e => g e * A e) A = 0 ↔ ∀ e, A e = 0 := by
  rw [production_eq_zero_iff (passive_linear fun e => (hg e).le)]
  refine forall_congr' fun e => ?_
  rw [mul_assoc, mul_eq_zero, or_iff_right (hg e).ne', mul_self_eq_zero]

/-- [proved-standard; formal-checked] **The summed balance.** If the density obeys `ṡ_v + (∂J_s)_v = σ_v` on a
closed complex, its total moves at `Σ_v σ_v`. -/
theorem hasDerivAt_total {B : E → V → ℝ} (hB : ∀ e, ∑ v, B e v = 0) {s : ℝ → V → ℝ} {Js : E → ℝ}
    {σ : V → ℝ} {t : ℝ} (hs : ∀ v, HasDerivAt (fun τ => s τ v) (σ v - divergence B Js v) t) :
    HasDerivAt (fun τ => ∑ v, s τ v) (∑ v, σ v) t := by
  have h := HasDerivAt.fun_sum (u := univ) fun v _ => hs v
  rwa [sum_sub_distrib, sum_divergence_eq_zero hB, sub_zero] at h

/-- [proved-derived; formal-checked] **The balance against a passive constitution**: when the local productions
sum to `Σ_c J_c A_c` of a passive constitution, the total density rises at that nonnegative production. -/
theorem hasDerivAt_total_production {B : E → V → ℝ} (hB : ∀ e, ∑ v, B e v = 0) {s : ℝ → V → ℝ}
    {Js J A : E → ℝ} {σ : V → ℝ} {t : ℝ} (hσ : ∑ v, σ v = production J A) (hP : Passive J A)
    (hs : ∀ v, HasDerivAt (fun τ => s τ v) (σ v - divergence B Js v) t) :
    HasDerivAt (fun τ => ∑ v, s τ v) (production J A) t ∧ 0 ≤ production J A :=
  ⟨hσ ▸ hasDerivAt_total hB hs, production_nonneg hP⟩

end Complex

/-! ## 2. One contact: `(u − v)(log u − log v) ≥ 0` -/

/-- [proved-standard; formal-checked] **A contact's production is nonnegative.** -/
theorem sub_mul_log_sub_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ (u - v) * (Real.log u - Real.log v) := by
  rcases le_total u v with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [Real.log_le_log hu h])
  · exact mul_nonneg (by linarith) (by linarith [Real.log_le_log hv h])

/-- [proved-standard; formal-checked] **It vanishes exactly on a balanced contact.** -/
theorem sub_mul_log_sub_eq_zero_iff {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (u - v) * (Real.log u - Real.log v) = 0 ↔ u = v := by
  rw [mul_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact Real.log_injOn_pos (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hv) h
  · exact Or.inl

/-! ## 3. The pair complex -/

section Pairs

variable {S : Type*} [Fintype S]

/-- [definition] **The outflow** of a current on ordered pairs: `Σ_y J(x,y)`. -/
def outflow (J : S → S → ℝ) (x : S) : ℝ := ∑ y, J x y

/-- [proved-standard; formal-checked] **Stokes on the pairs**: an antisymmetric current's outflows sum to zero. -/
theorem sum_outflow_eq_zero {J : S → S → ℝ} (h : ∀ x y, J y x = -J x y) : ∑ x, outflow J x = 0 := by
  unfold outflow
  have h1 : ∑ x, ∑ y, J x y = ∑ x, ∑ y, -J x y := by
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => h x y
  simp only [sum_neg_distrib] at h1
  linarith

variable [DecidableEq S]

/-- [definition] **The incidence of the pair complex**: `B (x,y) v = [v = x] − [v = y]`. -/
def pairIncidence (e : S × S) (v : S) : ℝ := (if v = e.1 then 1 else 0) - (if v = e.2 then 1 else 0)

/-- [proved-standard; formal-checked] The pair complex is closed. -/
theorem sum_pairIncidence (e : S × S) : ∑ v, pairIncidence e v = 0 := by
  simp [pairIncidence, sum_sub_distrib]

/-- [proved-standard; formal-checked] On the pair complex the divergence is outflow less inflow. -/
theorem divergence_pairIncidence (J : S → S → ℝ) (v : S) :
    divergence pairIncidence (fun e => J e.1 e.2) v = ∑ y, J v y - ∑ x, J x v := by
  unfold divergence pairIncidence
  rw [Fintype.sum_prod_type]
  simp only [sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  · rw [sum_eq_single v (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp
  · rw [sum_comm, sum_eq_single v (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
    simp

/-- [proved-standard; formal-checked] **An antisymmetric current carried as halves on the two orientations has
divergence its outflow.** -/
theorem divergence_pairIncidence_half {J : S → S → ℝ} (h : ∀ x y, J y x = -J x y) (v : S) :
    divergence pairIncidence (fun e => J e.1 e.2 / 2) v = outflow J v := by
  rw [divergence_pairIncidence (fun x y => J x y / 2)]
  unfold outflow
  simp_rw [h _ v]
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun y _ => by ring

end Pairs

/-! ## 4. The master equation: currents, affinities, the density and its local balance -/

section Master

variable {S : Type*} [Fintype S]

/-- [definition] **The net current** of the law `p` under the rates `W` from `x` to `y`. -/
def edgeCurrent (p : S → ℝ) (W : S → S → ℝ) (x y : S) : ℝ := flow p W x y - flow p W y x

/-- [definition] **The affinity** of the contact `(x, y)`: the log of its flow ratio. -/
def edgeAffinity (p : S → ℝ) (W : S → S → ℝ) (x y : S) : ℝ :=
  Real.log (flow p W x y) - Real.log (flow p W y x)

/-- [definition] **The entropy density** of a state: `−p_x log p_x`. -/
def density (p : S → ℝ) (x : S) : ℝ := Real.negMulLog (p x)

/-- [definition] **The entropy** of the law: `H(p) = Σ_x s_x`. -/
def entropy (p : S → ℝ) : ℝ := ∑ x, density p x

/-- [definition] **The entropy current** across the contact `(x, y)`. -/
def entropyCurrent (p : S → ℝ) (W : S → S → ℝ) (x y : S) : ℝ :=
  -(edgeCurrent p W x y * ((Real.log (p x) + Real.log (p y)) / 2 + 1))

/-- [definition] **The bath flux** at a state: the entropy its contacts give to the medium. -/
def bathFlux (p : S → ℝ) (W : S → S → ℝ) (x : S) : ℝ :=
  ∑ y, edgeCurrent p W x y * (Real.log (W x y) - Real.log (W y x)) / 2

/-- [definition] **The local production** at a state: half its contacts' currents times their affinities. -/
def localProduction (p : S → ℝ) (W : S → S → ℝ) (x : S) : ℝ :=
  ∑ y, edgeCurrent p W x y * edgeAffinity p W x y / 2

/-- [definition] **The total production**: `σ = Σ_x σ_x`. -/
def totalProduction (p : S → ℝ) (W : S → S → ℝ) : ℝ := ∑ x, localProduction p W x

variable {p : S → ℝ} {W : S → S → ℝ}

omit [Fintype S] in
theorem edgeCurrent_swap (p : S → ℝ) (W : S → S → ℝ) (x y : S) :
    edgeCurrent p W y x = -edgeCurrent p W x y := by
  unfold edgeCurrent; ring

omit [Fintype S] in
/-- [proved-derived; formal-checked] The entropy current is antisymmetric. -/
theorem entropyCurrent_swap (p : S → ℝ) (W : S → S → ℝ) (x y : S) :
    entropyCurrent p W y x = -entropyCurrent p W x y := by
  unfold entropyCurrent; rw [edgeCurrent_swap]; ring

omit [Fintype S] in
/-- [proved-derived; formal-checked] **The affinity splits into the law's log ratio and the rates' log ratio**,
read against the current (off the support both sides vanish). -/
theorem current_mul_affinity (hA : Admissible p W) (x y : S) :
    edgeCurrent p W x y * edgeAffinity p W x y =
      edgeCurrent p W x y * (Real.log (p x) - Real.log (p y) + (Real.log (W x y) - Real.log (W y x))) := by
  rcases (hA.nonneg x y).eq_or_lt with h0 | hpos
  · have h0' : W y x = 0 := by
      rcases (hA.nonneg y x).eq_or_lt with h | h
      · exact h.symm
      · exfalso; linarith [hA.support y x h]
    simp [edgeCurrent, flow, ← h0, h0']
  · have hback := hA.support x y hpos
    unfold edgeAffinity flow
    rw [Real.log_mul (hA.pos x).ne' hpos.ne', Real.log_mul (hA.pos y).ne' hback.ne']
    ring

omit [Fintype S] in
/-- [proved-derived; formal-checked] **Each contact is passive**: `j(x,y) A(x,y) ≥ 0`. -/
theorem edge_term_nonneg (hA : Admissible p W) (x y : S) :
    0 ≤ edgeCurrent p W x y * edgeAffinity p W x y := by
  unfold edgeCurrent edgeAffinity
  rcases (flow_nonneg hA x y).eq_or_lt with h0 | hpos
  · rw [← h0, flow_zero_of_zero hA h0.symm]; simp
  · exact sub_mul_log_sub_nonneg hpos (flow_support hA hpos)

omit [Fintype S] in
/-- [proved-derived; formal-checked] The master equation's constitution is passive on the pair complex. -/
theorem passive_pairs (hA : Admissible p W) :
    Passive (fun e : S × S => edgeCurrent p W e.1 e.2 / 2) (fun e => edgeAffinity p W e.1 e.2) :=
  fun e => by rw [div_mul_eq_mul_div]; exact div_nonneg (edge_term_nonneg hA e.1 e.2) (by norm_num)

/-- [proved-derived; formal-checked] Each local production is nonnegative. -/
theorem localProduction_nonneg (hA : Admissible p W) (x : S) : 0 ≤ localProduction p W x :=
  sum_nonneg fun y _ => div_nonneg (edge_term_nonneg hA x y) (by norm_num)

/-- [proved-derived; formal-checked] **The edgewise balance**: `σ_x − Σ_y J_s(x,y) − φ_x = (log p_x + 1) Σ_y j(x,y)`.
-/
theorem balance_identity (hA : Admissible p W) (x : S) :
    localProduction p W x - outflow (entropyCurrent p W) x - bathFlux p W x =
      (Real.log (p x) + 1) * outflow (edgeCurrent p W) x := by
  unfold localProduction outflow entropyCurrent bathFlux
  rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [current_mul_affinity hA x y]
  ring

/-- [proved-derived; formal-checked] **The local balance of the master equation**:
`ṡ_x + Σ_y J_s(x,y) + φ_x = σ_x` along any path with `ṗ_x = −Σ_y j(x,y)` at a positive law. -/
theorem hasDerivAt_density {p : ℝ → S → ℝ} {t : ℝ} (hA : Admissible (p t) W) {x : S}
    (hp : HasDerivAt (fun τ => p τ x) (-outflow (edgeCurrent (p t) W) x) t) :
    HasDerivAt (fun τ => density (p τ) x)
      (localProduction (p t) W x - outflow (entropyCurrent (p t) W) x - bathFlux (p t) W x) t := by
  have h := (Real.hasDerivAt_negMulLog (hA.pos x).ne').comp t hp
  rw [balance_identity hA x]
  exact h.congr_deriv (by ring)

/-- [proved-derived; formal-checked] **The local balance on the pair complex**: `ṡ_x + (∂J_s)_x + φ_x = σ_x`, with
the entropy current carried as halves on the two orientations. -/
theorem hasDerivAt_density_complex [DecidableEq S] {p : ℝ → S → ℝ} {t : ℝ} (hA : Admissible (p t) W) {x : S}
    (hp : HasDerivAt (fun τ => p τ x) (-outflow (edgeCurrent (p t) W) x) t) :
    HasDerivAt (fun τ => density (p τ) x)
      (localProduction (p t) W x -
        divergence pairIncidence (fun e => entropyCurrent (p t) W e.1 e.2 / 2) x - bathFlux (p t) W x) t := by
  rw [divergence_pairIncidence_half (entropyCurrent_swap (p t) W)]
  exact hasDerivAt_density hA hp

/-- [proved-derived; formal-checked] **The summed balance**: `dH/dt = σ − Σ_x φ_x`. -/
theorem hasDerivAt_entropy {p : ℝ → S → ℝ} {t : ℝ} (hA : Admissible (p t) W)
    (hp : ∀ x, HasDerivAt (fun τ => p τ x) (-outflow (edgeCurrent (p t) W) x) t) :
    HasDerivAt (fun τ => entropy (p τ)) (totalProduction (p t) W - ∑ x, bathFlux (p t) W x) t := by
  have h := HasDerivAt.fun_sum (u := univ) fun x _ => hasDerivAt_density hA (hp x)
  rw [sum_sub_distrib, sum_sub_distrib,
    sum_outflow_eq_zero (entropyCurrent_swap (p t) W), sub_zero] at h
  exact h

/-! ## 5. The join to `PathReversal` -/

/-- [proved-standard; formal-checked] Against an antisymmetric `D`, `Σ (J_xy − J_yx) D_xy = 2 Σ J_xy D_xy`. -/
theorem sum_sub_swap_mul (J D : S → S → ℝ) (hD : ∀ x y, D y x = -D x y) :
    ∑ x, ∑ y, (J x y - J y x) * D x y = 2 * ∑ x, ∑ y, J x y * D x y := by
  have h : ∑ x, ∑ y, J y x * D x y = -∑ x, ∑ y, J x y * D x y := by
    rw [sum_comm, ← sum_neg_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun y _ => by rw [hD x y]; ring
  simp only [sub_mul, sum_sub_distrib, h]
  ring

/-- [proved-derived; formal-checked] **The total production is `PathReversal`'s epoch production**:
`Σ_x σ_x = Σ_(x,y) p_x W_xy log (p_x W_xy / p_y W_yx)`. -/
theorem totalProduction_eq_epochProduction (hA : Admissible p W) :
    totalProduction p W = RealChart.epochProduction p W := by
  unfold totalProduction localProduction edgeCurrent edgeAffinity RealChart.epochProduction
  simp_rw [RealChart.log_flow_div hA]
  simp_rw [← sum_div]
  rw [sum_sub_swap_mul (flow p W) (fun x y => Real.log (flow p W x y) - Real.log (flow p W y x))
    fun x y => by ring]
  ring

/-- [proved-derived; formal-checked] `σ ≥ 0`. -/
theorem totalProduction_nonneg (hA : Admissible p W) : 0 ≤ totalProduction p W := by
  rw [totalProduction_eq_epochProduction hA]; exact RealChart.epochProduction_nonneg hA

/-- [proved-derived; formal-checked] **`σ = 0` exactly under detailed balance**, `p_x W_xy = p_y W_yx`. -/
theorem totalProduction_eq_zero_iff (hA : Admissible p W) :
    totalProduction p W = 0 ↔ DetailedBalance p W := by
  rw [totalProduction_eq_epochProduction hA]; exact RealChart.epochProduction_eq_zero_iff hA

/-- [proved-derived; formal-checked] **The total production is the pair complex's production** of the half
currents against their affinities. -/
theorem totalProduction_eq_production :
    totalProduction p W =
      production (fun e : S × S => edgeCurrent p W e.1 e.2 / 2) (fun e => edgeAffinity p W e.1 e.2) := by
  unfold totalProduction localProduction production
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

omit [Fintype S] in
/-- [proved-derived; formal-checked] Under nonnegative rates with symmetric support, `log (W_xy / W_yx)` is
`log W_xy − log W_yx`. -/
theorem affinity_eq_log_sub (hW : ∀ x y, 0 ≤ W x y) (hs : ∀ x y, 0 < W x y → 0 < W y x) (x y : S) :
    RealChart.affinity W x y = Real.log (W x y) - Real.log (W y x) := by
  unfold RealChart.affinity
  rcases (hW x y).eq_or_lt with h0 | hpos
  · have h0' : W y x = 0 := by
      rcases (hW y x).eq_or_lt with h | h
      · exact h.symm
      · exfalso; linarith [hs y x h]
    rw [← h0, h0']; simp
  · exact Real.log_div hpos.ne' (hs x y hpos).ne'

/-- [proved-derived; formal-checked] **The bath flux reads `PathReversal`'s affinity clock against the current.** -/
theorem bathFlux_eq_affinity (hA : Admissible p W) (x : S) :
    bathFlux p W x = ∑ y, edgeCurrent p W x y * RealChart.affinity W x y / 2 := by
  unfold bathFlux
  exact sum_congr rfl fun y _ => by rw [affinity_eq_log_sub hA.nonneg hA.support]

/-- [proved-derived; formal-checked] **With no bath flux the entropy is monotone**: a law that moves by the master
equation at every time, positive throughout, with every bath flux zero, has nondecreasing entropy. -/
theorem entropy_monotone_of_bath_zero {p : ℝ → S → ℝ} (hA : ∀ t, Admissible (p t) W)
    (hp : ∀ t x, HasDerivAt (fun τ => p τ x) (-outflow (edgeCurrent (p t) W) x) t)
    (hφ : ∀ t x, bathFlux (p t) W x = 0) : Monotone fun t => entropy (p t) := by
  refine monotone_of_hasDerivAt_nonneg (f' := fun t => totalProduction (p t) W) (fun t => ?_)
    fun t => totalProduction_nonneg (hA t)
  have h := hasDerivAt_entropy (hA t) (hp t)
  simp only [hφ t, sum_const_zero, sub_zero] at h
  exact h

end Master

end Holonics.Aeon.Production.ComplexEntropyBalance
