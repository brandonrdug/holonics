import Mathlib
import Holonics.Physics.Wave.Telegrapher

/-!
# The chain's two ticks are the telegrapher's central scheme, and the scheme is consistent

Source: #410's box "The light cone on a general graph and the scheme's continuum limit", its second clause.
`Physics/Wave/Telegrapher` says that eliminating `I` gives `LC ∂²V + LG ∂V = ∂²_x V` "in the continuum limit (not
formalized here)", and atlas `wave.lc-chain-tick` scopes itself "continuum consistency not formalized". The first
clause, the cone on a general graph, is `Physics/Wave/GraphCone`.

[proved-derived; formal-checked] What is proved.

1. **Two ticks eliminate the current** (§1). For any material, two consecutive ticks of `Telegrapher.step`
   (sources `s`, then `s′`) satisfy, over `ℚ` and under the module's own hypotheses at node `i`,
   `C_i(V² − 2V¹ + V⁰) + (hG_i/2)(V² − V⁰) = h²((V¹_(i+1) − V¹_i)/L_i − (V¹_i − V¹_(i−1))/L_(i−1))
   + h(s′ − s)[i = 0]` (`two_ticks`), from `step_is_the_telegrapher` and the current update.
2. **The uniform chain is the centred scheme** (§1). With `C = εk`, `G = σk` and `L = μk` (cell `k`), two ticks are
   `εμ D²_t V + σμ D⁰_t V − D²_x V = μ(s′ − s)[i = 0]/(kh)` (`uniform_chain_scheme`; `schemeOp` is the centred
   scheme over any field), homogeneous when the source is held over both ticks (`uniform_chain_scheme_held`). The
   midpoint leakage makes the loss term the centred difference `(V² − V⁰)/(2h)`, so the scheme is centred in time
   throughout.
3. **Centred differences converge** (§2). `(f(a + h) − f(a − h))/(2h) → f′(a)` (`central_first`) and
   `(f(a + h) − 2f(a) + f(a − h))/h² → f″(a)` (`central_second`, by L'Hôpital) on the punctured neighbourhood of
   `0`.
4. **Consistency** (§3). For a field `u(t, x)` whose time slice is twice differentiable at `t` and whose space slice
   is twice differentiable at `x`, the scheme on its grid samples (`sample`) tends to `a u_tt + b u_t − u_xx` as
   `(h, k) → (0, 0)` with `h, k ≠ 0`, the two independently, with no ratio of `h` to `k` asked
   (`scheme_consistent`); a solution of `a u_tt + b u_t = u_xx` leaves a residual that tends to zero
   (`scheme_residual_tendsto_zero`). With `a = εμ`, `b = σμ` and item 2, the chain is consistent with
   `εμ u_tt + σμ u_t − u_xx`.

Limits. The bound is `o(1)`, not `O(h² + k²)`: the second-order rate (truncation errors `h² f‴/6` and `h² f⁗/12`
of the two centred differences, under bounded third and fourth derivatives) is not stated. Consistency is not
convergence: the chain's solutions approach the telegrapher's when the scheme is also stable (Lax), the stability
statement is `Physics/Wave/Energy` under the Courant bound `h² < LC`, that is `h < √(εμ) k`, and the Lax
equivalence is not proved here. Only the uniform chain is read as a constant-coefficient scheme; the continuum
reading of `two_ticks` for a varying material, `ε ∂²_t u + σ ∂_t u = ∂_x(μ⁻¹ ∂_x u)`, is not stated.

The computational object is the helical pair interaction: the nodes are the chain's storing cells (capacitance and
leakage), the junctions its pair contacts (inductance), and eliminating the contacts' current leaves the cells'
two-tick law, whose continuum face is the telegrapher's. Of the winding guide's six general objects this touches
the tube (the clocked chain with its tick and cell) and the pair (the junction whose current is eliminated); the
helix, faces and placement, the cell holonomy and the tower thread stay attached.

Consumers: the #410 box "The light cone on a general graph and the scheme's continuum limit", and the atlas rows
`wave.lc-chain-tick` (whose scope "continuum consistency not formalized" this answers) and
`em.telegrapher-constitution`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Wave.TelegrapherLimit

open Filter Topology
open Holonics.Physics.Wave.Telegrapher

/-! ## §1 The scheme the chain implements -/

/-- [definition] **The central scheme** of `a ∂²_t u + b ∂_t u − ∂²_x u` on three time levels `V0`, `V1`, `V2`
(ticks `n − 1`, `n`, `n + 1`) at node `i`, with tick `h` and cell `k`: the centred second difference in time, the
centred first difference in time, and the centred second difference in space at the middle level. Stated over any
field, so the chain (over `ℚ`) and a sampled smooth field (over `ℝ`) read the same operator. -/
def schemeOp {𝕜 : Type*} [Field 𝕜] (a b h k : 𝕜) (V0 V1 V2 : ℤ → 𝕜) (i : ℤ) : 𝕜 :=
  a * ((V2 i - 2 * V1 i + V0 i) / h ^ 2) + b * ((V2 i - V0 i) / (2 * h)) -
    (V1 (i + 1) - 2 * V1 i + V1 (i - 1)) / k ^ 2

/-- [proved-derived; formal-checked] **Two ticks eliminate the current.** For any material, two consecutive ticks
of `Telegrapher.step` (sources `s`, then `s'`) satisfy, at every node `i`,
`C(V² − 2V¹ + V⁰) + (hG/2)(V² − V⁰) = h²((V¹_(i+1) − V¹_i)/L_i − (V¹_i − V¹_(i−1))/L_(i−1))
+ h(s'[i=0] − s[i=0])`: the current is gone, and what is left is the telegrapher's operator in divergence form with the junctions'
inductances inside the space difference. -/
theorem two_ticks (m : Material) (h s s' : ℚ) (x x1 x2 : State) (h1 : x1 = step m h s x)
    (h2 : x2 = step m h s' x1) (i : ℤ) (hden : 2 * m.C i + h * m.G i ≠ 0) (hL : m.L i ≠ 0) :
    m.C i * (x2.V i - 2 * x1.V i + x.V i) + h * m.G i / 2 * (x2.V i - x.V i) =
      h ^ 2 * ((x1.V (i + 1) - x1.V i) / m.L i - (x1.V i - x1.V (i - 1)) / m.L (i - 1)) +
        h * (inject s' i - inject s i) := by
  have hA := (step_is_the_telegrapher m h s' x1 i i hden hL).1
  have hC := (step_is_the_telegrapher m h s x i i hden hL).1
  rw [← h2] at hA
  rw [← h1] at hC
  have hI : ∀ e, x2.I e = x1.I e - h / m.L e * (x1.V (e + 1) - x1.V e) := by
    intro e; rw [h2]; rfl
  rw [hI i, hI (i - 1), sub_add_cancel] at hA
  have hdA : m.C i * (x2.V i - x1.V i) =
      h * (x1.I (i - 1) - h / m.L (i - 1) * (x1.V i - x1.V (i - 1)) -
      (x1.I i - h / m.L i * (x1.V (i + 1) - x1.V i)) + inject s' i) -
      h * m.G i * (x2.V i + x1.V i) / 2 := hA
  linear_combination hdA - hC

/-- [proved-derived; formal-checked] **The uniform chain is the central scheme.** On the uniform chain with
`C = εk`, `G = σk` and `L = μk` (cell `k`, so `ε`, `σ`, `μ` are per unit length), two consecutive ticks satisfy
`εμ D²_t V + σμ D⁰_t V − D²_x V = μ(s' − s)[i = 0]/(kh)` at every node: the chain is exactly the centred scheme of
`εμ ∂²_t u + σμ ∂_t u − ∂²_x u`, and a source held over the two ticks (or none) leaves it homogeneous. -/
theorem uniform_chain_scheme (ε σ μ k h s s' : ℚ) (x x1 x2 : State)
    (h1 : x1 = step (Material.uniform (ε * k) (σ * k) (μ * k)) h s x)
    (h2 : x2 = step (Material.uniform (ε * k) (σ * k) (μ * k)) h s' x1) (i : ℤ)
    (hk : k ≠ 0) (hh : h ≠ 0) (hμ : μ ≠ 0) (hden : 2 * (ε * k) + h * (σ * k) ≠ 0) :
    schemeOp (ε * μ) (σ * μ) h k x.V x1.V x2.V i = μ * (inject s' i - inject s i) / (k * h) := by
  have hL : μ * k ≠ 0 := mul_ne_zero hμ hk
  have hid := two_ticks (Material.uniform (ε * k) (σ * k) (μ * k)) h s s' x x1 x2 h1 h2 i hden hL
  simp only [Material.uniform] at hid
  unfold schemeOp
  linear_combination (norm := (field_simp; ring)) (μ / (k * h ^ 2)) * hid

/-- [proved-derived; formal-checked] With a source held over the two ticks the uniform chain's scheme is
homogeneous. -/
theorem uniform_chain_scheme_held (ε σ μ k h s : ℚ) (x x1 x2 : State)
    (h1 : x1 = step (Material.uniform (ε * k) (σ * k) (μ * k)) h s x)
    (h2 : x2 = step (Material.uniform (ε * k) (σ * k) (μ * k)) h s x1) (i : ℤ)
    (hk : k ≠ 0) (hh : h ≠ 0) (hμ : μ ≠ 0) (hden : 2 * (ε * k) + h * (σ * k) ≠ 0) :
    schemeOp (ε * μ) (σ * μ) h k x.V x1.V x2.V i = 0 := by
  rw [uniform_chain_scheme ε σ μ k h s s x x1 x2 h1 h2 i hk hh hμ hden]
  simp

/-! ## §2 Centred differences converge -/

/-- [proved-standard; formal-checked] Negation keeps the punctured neighbourhood of `0`. -/
theorem tendsto_neg_nhdsNE_zero : Tendsto (fun h : ℝ => -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((continuous_neg (G := ℝ)).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh

/-- [proved-standard; formal-checked] **The centred first difference** `(f(a + h) − f(a − h))/(2h)` tends to
`f′(a)` wherever `f` is differentiable at `a`. -/
theorem central_first {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) :
    Tendsto (fun h => (f (a + h) - f (a - h)) / (2 * h)) (𝓝[≠] 0) (𝓝 f') := by
  have h1 := hasDerivAt_iff_tendsto_slope_zero.mp hf
  have h2 := h1.comp tendsto_neg_nhdsNE_zero
  have h3 := (h1.add h2).div_const 2
  rw [show f' = (f' + f') / 2 by ring]
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := hh
  simp only [Function.comp_def, smul_eq_mul, ← sub_eq_add_neg]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The centred second difference** `(f(a + h) − 2f(a) + f(a − h))/h²` tends
to `f″(a)` where `f` is differentiable near `a` and `f′` at `a` (L'Hôpital, then the centred first difference of
`f′`). -/
theorem central_second {f f' : ℝ → ℝ} {f'' a : ℝ} (hf : ∀ᶠ y in 𝓝 a, HasDerivAt f (f' y) y)
    (hf' : HasDerivAt f' f'' a) :
    Tendsto (fun h => (f (a + h) - 2 * f a + f (a - h)) / h ^ 2) (𝓝[≠] 0) (𝓝 f'') := by
  have hp : Tendsto (fun h : ℝ => a + h) (𝓝 0) (𝓝 a) := by
    simpa using (continuous_const_add a).tendsto 0
  have hm : Tendsto (fun h : ℝ => a - h) (𝓝 0) (𝓝 a) := by
    simpa using (continuous_sub_left a).tendsto 0
  have hF : ∀ᶠ h in 𝓝[≠] (0 : ℝ), HasDerivAt (fun h => f (a + h) - 2 * f a + f (a - h))
      (f' (a + h) - f' (a - h)) h := by
    have e1 := hp.eventually hf
    have e2 := hm.eventually hf
    filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2] with h d1 d2
    have k1 : HasDerivAt (fun h => f (a + h)) (f' (a + h)) h := HasDerivAt.comp_const_add a h d1
    have k2 : HasDerivAt (fun h => f (a - h)) (-(f' (a - h))) h := HasDerivAt.comp_const_sub a h d2
    have := (k1.sub_const (2 * f a)).add k2
    rw [← sub_eq_add_neg] at this
    exact this
  have hG : ∀ᶠ h in 𝓝[≠] (0 : ℝ), HasDerivAt (fun h : ℝ => h ^ 2) (2 * h) h :=
    Eventually.of_forall fun h => by simpa using hasDerivAt_pow 2 h
  have hG' : ∀ᶠ h in 𝓝[≠] (0 : ℝ), 2 * h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero two_ne_zero hh
  have hFa : Tendsto (fun h => f (a + h) - 2 * f a + f (a - h)) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt f a := hf.self_of_nhds.continuousAt
    have := (((hc.tendsto.comp hp).sub_const (2 * f a)).add (hc.tendsto.comp hm)).mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [show f a - 2 * f a + f a = 0 by ring] at this
    exact this
  have hGa : Tendsto (fun h : ℝ => h ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  exact HasDerivAt.lhopital_zero_nhdsNE hF hG hG' hFa hGa (central_first hf')

/-! ## §3 Consistency -/

/-- [definition] A field `u(t, x)` sampled on the grid round `(t, x)`: level `n`, node `i` reads
`u(t + nh, x + ik)`. -/
def sample (u : ℝ → ℝ → ℝ) (t x h k : ℝ) (n : ℤ) : ℤ → ℝ := fun i => u (t + n * h) (x + i * k)

/-- [proved-standard; formal-checked] The scheme on a sampled field, written out. -/
theorem schemeOp_sample (a b : ℝ) (u : ℝ → ℝ → ℝ) (t x h k : ℝ) :
    schemeOp a b h k (sample u t x h k (-1)) (sample u t x h k 0) (sample u t x h k 1) 0 =
      a * ((u (t + h) x - 2 * u t x + u (t - h) x) / h ^ 2) +
        b * ((u (t + h) x - u (t - h) x) / (2 * h)) -
        (u t (x + k) - 2 * u t x + u t (x - k)) / k ^ 2 := by
  simp [schemeOp, sample, ← sub_eq_add_neg]

/-- [proved-standard; formal-checked] **Consistency.** Where the time slice `s ↦ u(s, x)` has a derivative `u_t`
near `t` and `u_t` one at `t`, and the space slice `y ↦ u(t, y)` a derivative `u_x` near `x` and `u_x` one at `x`,
the scheme on the sampled field tends to `a u_tt + b u_t − u_xx` at `(t, x)` as the tick and the cell go to zero
independently (no ratio of `h` to `k` is asked). -/
theorem scheme_consistent (a b : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) {ut ux : ℝ → ℝ} {utt uxx : ℝ}
    (hT : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => u s x) (ut s) s) (hT2 : HasDerivAt ut utt t)
    (hX : ∀ᶠ y in 𝓝 x, HasDerivAt (u t) (ux y) y) (hX2 : HasDerivAt ux uxx x) :
    Tendsto (fun p : ℝ × ℝ => schemeOp a b p.1 p.2 (sample u t x p.1 p.2 (-1))
        (sample u t x p.1 p.2 0) (sample u t x p.1 p.2 1) 0)
      ((𝓝[≠] 0) ×ˢ (𝓝[≠] 0)) (𝓝 (a * utt + b * ut t - uxx)) := by
  have T2 := (central_second hT hT2).comp (tendsto_fst (g := 𝓝[≠] (0 : ℝ)))
  have T1 := (central_first hT.self_of_nhds).comp (tendsto_fst (g := 𝓝[≠] (0 : ℝ)))
  have X2 := (central_second hX hX2).comp (tendsto_snd (f := 𝓝[≠] (0 : ℝ)))
  have := ((T2.const_mul a).add (T1.const_mul b)).sub X2
  refine this.congr fun p => ?_
  rw [schemeOp_sample]
  rfl

/-- [proved-standard; formal-checked] **A solution leaves a vanishing residual.** If `u` solves
`a u_tt + b u_t = u_xx` at `(t, x)`, the scheme's residual on its samples tends to zero. With `a = εμ`, `b = σμ`
this is the uniform chain's scheme (`uniform_chain_scheme`): the chain is consistent with the telegrapher
equation. -/
theorem scheme_residual_tendsto_zero (a b : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) {ut ux : ℝ → ℝ}
    {utt uxx : ℝ}
    (hT : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => u s x) (ut s) s) (hT2 : HasDerivAt ut utt t)
    (hX : ∀ᶠ y in 𝓝 x, HasDerivAt (u t) (ux y) y) (hX2 : HasDerivAt ux uxx x)
    (hsol : a * utt + b * ut t = uxx) :
    Tendsto (fun p : ℝ × ℝ => schemeOp a b p.1 p.2 (sample u t x p.1 p.2 (-1))
        (sample u t x p.1 p.2 0) (sample u t x p.1 p.2 1) 0)
      ((𝓝[≠] 0) ×ˢ (𝓝[≠] 0)) (𝓝 0) := by
  have := scheme_consistent a b u t x hT hT2 hX hX2
  rwa [hsol, sub_self] at this

end Holonics.Physics.Wave.TelegrapherLimit
