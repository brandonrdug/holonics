# RT3: every flowed integer event is its steepest-descent main term on three ranges, with the defect exhibited

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** RT3 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../archive/plans/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owners:** under `soma/formal/elementary-holonics/ElementaryHolonics/RH/`: `FlowedGamma.lean`,
`FlowedGammaContour.lean`, `GammaPhase.lean`, `EventSaddle.lean`, `EventMain.lean`,
`EventBounds.lean`, `EventGaussian.lean`, `EventWindow.lean`, `EventPieces.lean`,
`EventTail.lean`, `EventAssembly.lean`, `EventDefect.lean`, `EventHorizontal.lean`,
`EventExplicit.lean`, `EventMainRange.lean`, `EventMedium.lean`, `EventLarge.lean`, all
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] Repository `t > 0` (standard `τ = −t < 0`, Dobner's `|t| = 4t`); `L = log |n|`;
`s = x + iy`; the flowed `n = 1` event `Γ_t(w) = ∫ e^{−tu²} e^{(w−½)u} φ(u) du`;
`γ₁(s) = ½ (s − 1) π^{−s/2} Γ(s/2 + 1)` (pole-free); the phase
`g(s) = ¼ s(s−1) e^{−s log π /2} √(2π) exp((s/2 − ½) Log(s/2) − s/2)` with
`ℓ(s) = 1/(2s) + 1/(s−1) − ½ log π + ½ Log(s/2)` and `ℓ'(s) = 1/(2s) − 1/(2s²) − 1/(s−1)²`;
the shift `J_t(s) = s + t Λ(s)`, `Λ(s) = Log(s/2) − log π`; the main coefficient
`γ_t'(s) = g(s) e^{tΛ(s)²/4}`; the window `Y = y^{2/3}/20`; the relative defect
`r = rdef t s L Y`.

[proved-derived; formal-checked]

- **The comb is a family of shifted `n = 1` events.** `FlowedGamma.integral_flowedTerm_eq_shift`:
  `∫ flowedTerm t z n = e^{−tL²} e^{−zL} Γ_t(z + 2tL)` for every `n ≠ 0`.
- **The event is a Gaussian line integral of `γ₁` on any vertical line `Re z = c > −2`.**
  `FlowedGammaContour.T_eq_γ₁`: the transform `∫ lapTerm (−1) s 1` converges on `Re s > −2` and
  equals `γ₁(s)` there (analytic continuation off `Re s > 1`); `Γt_eq_contour`:
  `Γ_t(w) = (4πt)^{−1/2} ∫ e^{(c+iy−w)²/(4t)} γ₁(c+iy) dy`, by the complex-shifted Gaussian pair
  and Fubini, no Cauchy theorem.
- **Stirling becomes a phase expansion.** `GammaPhase.g_expansion`: on `GoodSeg w ζ`
  (`Re w ≥ 2` or `4|Re w| ≤ Im w ≥ 2`, `‖ζ‖ ≤ ‖w‖/8`),
  `g(w+ζ) = g(w) exp(ζ ℓ(w) + ζ² ℓ'(w)/2 + R)` with `‖R‖ ≤ 402 ‖ζ‖³/‖w‖²`, by the fundamental
  theorem along the segment twice, from RT2's `gamma_eq_sqrt`.
- **The saddle window by rectangle Cauchy.** `EventSaddle.Γt_window`: the line `Re z = c`
  through the saddle is exchanged, on `|Im z − y₀| ≤ Y`, for the window integral plus the two
  horizontal sides and the tails on `Re z = 2`
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).
- **The exact event decomposition.** `EventMain.event_decomp` and
  `EventAssembly.event_eq_main_mul`: for `t > 0`, `g(s) ≠ 0`, `‖s‖ ≥ max(2, 12t)`, `0 < Y < y`,
  `∫ flowedTerm t (J_t s) n = γ_t'(s) e^{−sL} e^{−tL²} (1 + r)`, with
  `r = F₁ G₀ (I_W/G) − 1 + R'`: `F₁ = e^{2tLε₁ + 2t²L²ℓ'}` (`ε₁ = ℓ − Λ/2 = 1/(2s) + 1/(s−1)`),
  `G = ∫ e^{−Av² + iqv}`, `G₀ = (4πt)^{−1/2} G`, `I_W = ∫_{−Y}^{Y} gauss (1 + D)`, `D` the
  window defect of the phase expansion, `R'` the horizontal and tail pieces over `γ_t'`.
- **Every piece bounded explicitly.** `EventDefect.norm_rdef_le`:
  `‖r‖ ≤ (a(1+b)+b)(1+d)+d+e`; `EventExplicit.norm_rdef_le_explicit` exhibits
  `a = 2(6tL + 6t²L²)/‖s‖`, `b = 36t/‖s‖ + 4t‖q‖²`, `d = (β₃ + β₄)/(√(2πt) e^{−2t‖q‖²})`,
  `e = epiece`, under the listed side conditions, from `EventGaussian.norm_sqrt_G_sub_one_le`,
  `EventWindow.norm_window_defect_le`, `EventWindow.norm_G_sub_window_le`,
  `EventHorizontal.norm_Rpiece_le` (with `EventPieces.norm_γ₁_le_g`, `norm_g_le`,
  `norm_γt'_ge`, `EventTail.norm_tail_le`).
- **The main range `L ≤ y^{1/3}`.** `EventMainRange`: with `y = u³`, `Y = u²/20`, `L ≤ u`,
  `|x| ≤ X ≤ u³`: `norm_rdef_le_Bmaj`, **`‖r‖ ≤ Bmaj t X u`**, a function of `u` alone with
  every coefficient exhibited (`Amaj`, `Bmaj'`, `Dmaj`, `Emaj`); **`tendsto_Bmaj`:
  `Bmaj t X u → 0` as `u → ∞`** (each piece dominated by `exp` of a quartic with negative
  leading coefficient); **`event_main`: for `u ≥ u₀(t, X)` (explicit), the decomposition holds
  with `‖r‖ ≤ Bmaj t X u`.** The dominant piece is `Amaj = (12t + 12t²)/u`, so the relative
  defect is `O(y^{−1/3})`.
- **The medium range `L ≤ y^{7/12}`.** `EventMedium`: with `y = w¹²`, `Y = w⁸/20`, `L ≤ w⁷`,
  `F₁` is no longer near `1`, and `norm_one_add_rdef_le_explicit` bounds
  `‖1 + r‖ ≤ ‖F₁‖(1+b)(1+d) + e` with `‖F₁‖ ≤ e^{(6tL + 6t²L²)/‖s‖}`; the majorants `Bmaj'`,
  `Dmed`, `Emed` vanish in `w`; **`event_medium`: eventually in `w`,
  `‖∫ flowedTerm t (J_t s) n‖ ≤ 12 ‖γ_t'(s)‖ e^{−xL} e^{−tL²/2}`**, half the Gaussian decay kept.
- **The large range `L ≥ y^{7/12}`.** `EventLarge`: RT1's absolute bound
  `∫ ‖flowedTerm‖ ≤ K₂ e^{−cL²}`, `c = min(t,1)/8`, relative to `γlow ≤ ‖γ_t'(s)‖`;
  **`event_large`: eventually in `w`,
  `‖∫ flowedTerm t (J_t s) n‖ ≤ ‖γ_t'(s)‖ e^{−xL} e^{−(c/2)L²}`**, since `K₂ e^{−c w¹⁴/4}`
  times `Γmaj` (the reciprocal of `γlow`) is `exp` of a polynomial of degree 14 with negative
  leading coefficient.

At one height the three ranges meet: `y = w¹² = (w⁴)³`, `u = w⁴`; main `L ≤ w⁴`, medium
`w⁴ < L ≤ w⁷`, large `L > w⁷`. All three are uniform on `|x| ≤ X` for each fixed `X ≥ 0`.

`#print axioms` on `event_main`, `tendsto_Bmaj`, `event_medium`, and `event_large` returns
`propext`, `Classical.choice`, `Quot.sound`. `EventMainRange`, `EventMedium`, and `EventLarge`
build alone (8,769, 8,770, 8,771 jobs) and inside the root umbrella (9,831 jobs).

## The scope, corrected in place

[definition] The contract named one owner `RH/DescentEvent.lean`; the return is the family of
owners listed above, one per organ of the argument, and the contract's RT3 text is corrected to
say so. Dobner's split is `|t| log n ≤ y^{1/3}` and `≤ y^{3/5}`; the return uses `L ≤ y^{1/3}`
and `L ≤ y^{7/12}`. The medium exponent `7/12` lies in `(1/2, 2/3)`, the interval on which the
cubic phase remainder `(2tL)³/y²` vanishes and the large-range Gaussian `e^{−cL²}` beats
`e^{−πy/2}`; it is chosen so that every threshold is an integer power of `w = y^{1/12}`. The
main-range rate is `O(y^{−1/3})`, sharper than Dobner's `O(y^{−1/5})`, and the strip is
`|x| ≤ X` fixed rather than `|x| ≤ C y^{1/4}`; RT5 places the zeros of `F_t` in a fixed strip and
RT6 transfers on bounded discs, so the fixed strip is what the seal uses. RT4 will state its
uniform remainder in these terms.

[counterexample; source-inspected] The first route for the tails, the asymptotic of the
vertical-line Gaussian integral through `w` itself, is invalid: the integrand carries the
oscillation `e^{iy · ½ log|w|}` and its Gaussian weight has no decay in the phase. It was replaced
by the saddle contour `Re z = Re s + 2tL`, on which the phase is exactly removed, with the
rectangle exchange to `Re z = 2` for the tails. The lossy lower bound `γlow ~ e^{−π‖s‖/2}` (the
true decay is `e^{−πy/4}`) is what makes the medium range need the saddle machinery rather than
the trivial line bound; both facts are recorded so the choice is not re-derived.

## Pass RT3

The per-event identity with its remainder bound on all three ranges, formal-checked. **RT3
passes** at the corrected scope. Falsifier: `t > 0`, `X ≥ 0`, `u ≥ u₀(t, X)`, `s = x + iu³`
with `|x| ≤ X`, and `n` with `log|n| ≤ u` at which `‖r‖ > Bmaj t X u`; or a height beyond the
medium or large threshold at which the stated absolute bound fails.

## Boundaries

- No claim of movement on `0 ≤ Λ_DN`; the port `RodgersTaoNonneg` stands until RT6.
- The main term `γ_t'(s) e^{−sL} e^{−tL²}` is the `n`-th term of Dobner's `F_t` times
  `γ_t'(s)`; the sum over `n` on the three ranges is RT4's.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.EventMainRange
timeout 180s lake build ElementaryHolonics.RH.EventMedium
timeout 180s lake build ElementaryHolonics.RH.EventLarge
timeout 180s lake build ElementaryHolonics
```
