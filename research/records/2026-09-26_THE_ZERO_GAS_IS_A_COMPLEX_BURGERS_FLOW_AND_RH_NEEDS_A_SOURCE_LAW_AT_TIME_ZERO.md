# The zero gas is a complex Burgers flow, and RH needs a source law at time zero

**Date:** 2026-09-26. **Status:** derivation with Sol's grading (#62, step 6 targets).
**Occasion:** Brandon asked whether to make another attempt on RH, with Hodge and complex
Navier–Stokes (not the Clay statement). He asked for the reasoning in the elementary objects, with
the toroidal and helical geometry explicit (winding, areas, volumes, tubes), not Weil positivity or
height, and with compression as the solving method.

## 1. Where the line stands

[proved-derived; formal-checked] In the tree chart:
- `RiemannHypothesis ↔ Λ_DN = 0`;
- `Λ_DN ∈ [0, 1/8]` (standard `Λstd = 4Λ_DN ∈ [0, ½]`);
- every negative time has an off-seam zero;
- the flow never creates a pair;
- a lone off-seam pair among real zeros collides within half its height squared.

Owners: `HolonicsResearch/Zeta/{DeBruijnSeal, DescentZeros, CriticalChart, ThresholdReturn}`.

The gap is `Λ_DN ≤ 0`, which is RH. Upper bounds from zero-free regions are circular: de Bruijn's
bound is half the square of the greatest off-seam height.

## 2. Four exact readings in the objects

1. **The ear and its blur** [derived at the symbol and bounded-truncation levels;
   the unbounded-operator construction and its Bochner identity are open, as §5 states;
   direction corrected the same day].
   - The seam times use `heatE(−τ) ξ = ∫ e^(τu²) e^((s−½)u) Φ(u) du` (`DeBruijnSeal`). The proposed unbounded-operator reading
     at seam time `τ` is `G_τ(∂_c) = ∫ e^(τu²) Φ(u) e^((∂_c − ½)u) du`: the palette of scale
     shifts `Φ`, reweighted by a Gaussian.
   - Along the seam (`s = ½ + iz`), weighting the palette by `e^(τu²)` is the Gaussian
     un-convolution of `ξ` in frequency (`e^(−τ∂_z²)`).
     - `τ > 0` sharpens the ear: the palette's far scales are raised.
     - `τ < 0` blurs it: frequencies are smeared with a Gaussian of variance `−2τ`, the forward heat
       flow along the seam.
   - `Λ_DN = inf{τ : G_τ(∂_c)` is quasi-invertible for every real `c ≠ ½}`: the least sharpening at
     which the ear hears every dimension except ½. Rodgers–Tao says every blur (`τ < 0`) leaves it
     deaf somewhere off ½, and RH says the unsharpened ear (`τ = 0`) already hears. The quantifier
     is over all real `c`, because the flowed zeros leave the strip.
   - [open] Which fractal strings the ear hears after the flow needs a new law: the flowed symbol is
     no Dirichlet series of the holes' windings, so Lapidus–Maier's theorem does not carry over.
2. **The zero gas is a complex Burgers flow** [derived].
   - `u = −2∂ log F_t` solves `∂_t u − u ∂u = −∂²u` (Cole–Hopf). The zeros are its poles, and they
     move by `ż_k = F″/F′ (z_k)`, which is `2Σ_(j≠k) 1/(z_k − z_j)` on a finite comb.
   - For the pair inertia `A = Σ y_k²` (with `m` pairs, simple zeros), the exact rate is
     `Ȧ = −2m − 4Σ(y_k − y_j)²/|z_k − z_j|² − 4Σ(y_k + y_j)²/|z_k − z̄_j|² − 4Σ y_k²/|z_k − r_a|²
     ≤ −2m`.
   - This is the same object as complex fluid flow: Burgers' complex singularities are a heat
     solution's zeros.
   - [open obstruction] Every monotone of this gas (inertia, energy, winding, gyro-area,
     capacity) says that pairs collide *later*, not that none exist at `t = 0`. RH needs
     `A(0) = 0` from an independent source law. The entire comb also needs a cutoff with its tail
     flux.
3. **Carry and ticks** [proved-standard; corrects the first statement].
   - `RH ⟺ N(T) = Σ_(on-line zeros ≤ T) order` for every admissible `T`.
   - Hardy's `Z` changes sign only at odd orders. A sign-change count therefore also needs
     simplicity.
   - In the Aeon objects, the rectangle's argument carry and the section's order-weighted ticks
     are two receivers of one Aeon. `S(T)` is unbounded, so no fixed neck correction bounds their
     defect.
4. **Recurrence on the prime torus** [proved-standard: Bagchi].
   - The prime rings rotate at `log p`, rationally independent, so they follow a Kronecker line
     that never locks.
   - RH is equivalent to strong recurrence of ζ in `½ < σ < 1`: approximate return at a
     receiver's grain with positive lower density.
   - The Euler product supplies the independent ring phases. Davenport–Heilbronn, which lacks one,
     has off-seam zeros; it is the negative control.
   - Bagchi's theorem is not yet formalized.

## 3. Hodge and complex Navier–Stokes

- **Hodge** [proved-standard; open].
  - Poincaré–Lelong: `dd^c log|f| = [div f]`, so a navigator's section sources a divisor. That
    settles codimension one (Lefschetz (1,1)) and `c_p` for sections of rank-`p` bundles.
  - The projective higher-codimension case is the open cycle-source term of
    `Hodge/HodgeConjecture`. It fails for compact Kähler manifolds (Voisin).
  - The zeta divisor models the mechanism and adds no higher-codimension source.
- **Complex Navier–Stokes** [proved-standard; open].
  - Li–Sinai (2008): complex-valued 3D solutions blow up in finite real time. Global existence for
    all complex data is false.
  - The proposition worth testing [open]: for a stated class of analytic divergence-free initial
    Holons, the complex-time germ continues along paths outside a locally finite singular set, on
    a covering. Each singular neck has finite local monodromy, a Laurent or Puiseux chart, and a
    closing flux balance across its tube sections. Li–Sinai is allowed by it.
  - It may be false: singularities may accumulate, form a natural boundary, or have nonalgebraic
    monodromy.
  - The first step is a local analytic mild-solution Holon, unique on overlapping complex-time
    charts.

## 4. The campaign: source to neck

[agent-inferred, with Sol] **The objects.**
- **Holon:** the flowed ξ, with the prime phase rings as its proposed source constitution.
- **Aeon:** heat time and the argument lift.
- **Epochs:** the critical-line crossings and the pair-collision sections.
- **Holarchy:** the prime rings, the helical pair contacts, the zero tubes, and a receiver that
  compares the rectangle carry with the order-weighted ticks.

Hodge's cycle-source receiver and the complex-fluid neck receiver are separate test instances.

**The Lean, by name:**
- `Zeta.Hearing.{quasiInvertible_iff_verticalZeroFree, threshold_eq_sharpenedHearingInf}`;
- `Zeta.ZeroTube.{finitePairInertia_rate, windowPairInertia_balance}`;
- `Zeta.CarryTick.defect_eq_offSeamCount_addMultiplicityDefect`;
- the proposed new law `Zeta.PrimeRing.sourceNeckSquare`, which relates a prime-ring source face,
  through a tube, to a pair or carry defect with its explicit residual.

**The first falsifiable landmark** is `windowPairInertia_balance`. On an expanding zero window,
does a source-qualified boundary residual have a controlled sign, or vanish once its tail is kept?
Three tests could reject a proposed source law before any RH claim:
- a finite Euler-product surrogate;
- a flowed `F_t`;
- the Davenport–Heilbronn negative control.

**Compression as the method.** Candidate prime-ring words and contact locks are compared by their
code-length pair: the description of the source law against the residual it leaves at the zero
face. A landmark is a face where navigator paths meet and a decoder-preserving pivot shrinks the
residual. Only a proved source-to-receiver identity forcing the residual pair population to vanish
would be a solution.

## 5. The first returns and the falsifier (same day, `cf6f70f4`, `114963ab`)

[proved-derived; formal-checked] New owners in `HolonicsResearch/Zeta`:
- **`ZeroTube`**:
  - the finite pair inertia's exact rate, `Ȧ ≤ −2m`, and `A(T) + 2mT ≤ A(0)`;
  - the window balance for `heatE t ξ` at every time, with the exterior's tail flux `T_k`;
  - a seam-lying exterior gives `Re T_k ≥ 0`, and a non-lifting tail with a non-falling window
    inertia forces no pairs. That hypothesis is RH outside the window, so the step is circular.
- **`CarryTick`**: `2πi N(T) = ∮ ξ′/ξ`; `N − parityTicks = offSeam + Σ_seam(ord − ord mod 2)`;
  **RH ⟺ the carry equals the order-weighted seam ticks**; a seam tick is a sign change exactly at
  odd order.
- **`Hearing`**: `Λ_DN` as the least sharpening at which every `c ≠ ½` is heard. The spectral
  truncations are invertible exactly when the symbol has no zero on their segment (a unital
  C⋆-algebra model).
- **`PaletteLaw`** [counterexample]: no law of the palette that is closed under Gaussian damping
  can force the seam. `e^(−u²)Φ` satisfies every such law, yet `heatE 1 ξ` has an off-seam zero.
  Positivity and log-concavity of the palette are therefore ruled out as source laws.

[counterexample; certified exactly] The falsifier (`research/notebook/zeta_tube/falsifier.py`)
was run on three tests: a flowed polynomial comb, a finite primon gas over `{2, 3}` (the Euler
surrogate), and Davenport–Heilbronn, whose off-seam zeros sit in four certified Rouché discs.

| Candidate source law | Verdict |
|---|---|
| The tail does not lift the window (`B_W ≤ 0`) | Rejected: the control's pairs satisfy it |
| The tail does not lift, and the window inertia is stationary | Forces emptiness, but equivalent to RH by construction |
| The prime part `Re P ≤ 0` at a zero puts that zero on the seam | Rejected by the control's first off-seam zero |
| **The prime part `Re P ≤ 0` at every zero** | **Survives.** ξ satisfies it at its first five zeros; the control violates it at three of its four. It is not circular, and it is not yet shown to force emptiness |
| The Euler product together with the functional equation | Not rejected and separates the control, but it is RH for the Selberg class |
| Palette positivity or log-concavity | Rejected, by the control's positive palette and by `PaletteLaw` |
| The Lee–Yang property of `Φ(u)du` | Equivalent to RH by construction |

**The surviving landmark.** The zero's velocity splits into a prime part `P` and an archimedean
part. At every ξ zero checked, the prime part's real flux points toward the seam, balancing the
archimedean part. The control's off-seam zeros have it pointing away. The open theorem is whether
`Re P ≤ 0` at every zero forces an empty pair population.

[open] Owed in #62:
- the operator-level ear (`∂_c` on `L²(ℝ, e^(−2cx)dx)` and its Mellin–Plancherel unitary);
- a source law for the tail that forces `A(0) = 0`;
- the tail's boundary (Cauchy-transform) form;
- a window-tracking owner;
- simplicity of the lower zeros in `CarryTick`;
- the finite primon gas's threshold being exactly zero for every prime set;
- whether the global prime-part sign forces emptiness;
- Bagchi's theorem.
