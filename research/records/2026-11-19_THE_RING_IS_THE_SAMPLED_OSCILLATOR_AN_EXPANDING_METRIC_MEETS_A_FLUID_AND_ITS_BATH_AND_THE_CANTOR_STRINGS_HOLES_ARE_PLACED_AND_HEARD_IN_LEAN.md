# The ring is the sampled oscillator, an expanding metric meets a fluid and its bath, and the Cantor string's holes are placed and heard, in Lean

November 19, 12:09 UTC. The twenty-first formalization pass over #410, its twenty-second set, after [the
twenty-first](2026-11-19_LEGENDRES_LOCAL_MOVES_FIX_GAMMA_TWO_BY_RIGIDITY_TWO_BUNDLES_IN_SERIES_RETAIN_THE_PRODUCT_A_TRIANGLE_RETAINS_ITS_WHOLE_CONSTITUTION_AND_A_RING_CHAIN_IS_HARPERS_OPERATOR_IN_LEAN.md)
(#1033). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Objects/ContinuousCrossing` | The charge `x = A cos(ωt + φ)` (`A, ω > 0`) has an upward zero `{x = 0, ẋ > 0}` exactly where its lifted phase `θ(t) = (ωt + φ + π/2)/2π` is an integer, each transversal with rate `Aω` (`isUpwardZero_iff`, `isUpwardZero_iff_liftedPhase`, `hasDerivAt_of_isUpwardZero`), the crest being the quarter-turn shift (`isCrest_iff_isUpwardZero_shift`); the zeros in `(t₀, t₁]` number `⌊θ(t₁)⌋ − ⌊θ(t₀)⌋`, the completed windings (`upwardZerosIn_finite_ncard`, `upwardZerosIn_ncard_eq_windings`); sampled `d` times a period from any start, with ring start `r = ⌊d·openPhase θ(t₀)⌋` and sub-step offset `δ`, the zeros over `N` micro-steps number the owner's `ringCrossings d r N = (r + N)/d` whatever `δ` (`upwardZeros_sampled_ncard`, `sampled_ncard_eq_of_ringStart_eq`), a micro-step holds one zero exactly when the ring's micro-step from `r + k` lands on its section, the owner's `Crossing` for `d ≥ 2` (`microStep_ncard`, `microStep_crossing_iff_ownerCrossing`); over `n·k` micro-steps of a clock passage the count is `targetTicks r k` and the carrier is the residue phase advanced by `2πδ/d` (`sampled_crossings_eq_targetTicks`, `sampled_carrier_eq_residuePhase`); the three-quarter passage read from the oscillator at `δ = 0` and `δ = ½` (`threeQuarter_continuous_witness`, `threeQuarter_offset_witness`) | #410's box "Continuous crossing as the micro-step ring" (ticked); `Objects/Parametron`'s `[open]` paragraph and `docs/ELEMENTARY_OBJECTS.md` §5 | `parametron.continuous-crossing-is-ring` (new) |
| `Physics/Spacetime/FriedmannFluid` | The flat Friedmann–Lemaître–Robertson–Walker field `g = diag(−1, a², a², a²)` has its first and second jets read by Mathlib's derivatives along every coordinate line, the first jet nonzero (`hasDerivAt_frwField`, `hasDerivAt_frwFirstJetField`, `frwSecondJet_symm`, `frwFirstJet_ne_zero`); for any diagonal metric with a diagonal jet the Christoffel symbols and their rates are closed forms (`christoffel_diagonal`, `christoffelJet_diagonal`), and through `CurvatureJets`' `ricci` this jet has `R₀₀ = −3a″/a`, `R_ij = (aa″ + 2a′²)δ_ij`, `R = 6(a″/a + H²)`, `G₀₀ = 3H²`, `G_ij = −(2aa″ + a′²)δ_ij` and the tide `−aa″δ_ij` (`frw_ricci`, `frw_scalar`, `frw_einstein`, `frw_tide`); the comoving perfect fluid reads `perfectFluidTensor ρ p` in the orthonormal frame (`frwFrame_fluid`), and the owner's `einsteinResidual` vanishes iff Friedmann's two equations hold (`friedmann_iff`, `friedmann_accel`); the fluid's balance `ρ′ = −3H(ρ + p)` follows (`continuity`), a barotropic fluid keeps `ρa^(3(1+w))` (`barotropic_const`), and a Stefan–Boltzmann bath keeps `𝒯a` and `sa³` (`bath_cools`, `entropy_conserved`); de Sitter and the radiation solution `a = √t` with its bath are built fields solving the equation (`deSitter_field`, `radiation_field`, `radiation_bath`); on the comoving congruence the deviation `J = a·1` obeys `J″ = −R̂J` at the built tide, so `Raychaudhuri`'s equation holds with its deviation proved (`comoving_deviation`, `comoving_raychaudhuri`) | #410's boxes "Einstein: the continuum realization" and "Curvature's strain and rotation" (part); `Physics/Spacetime/Einstein`'s `[open]` paragraph | `gr.flrw-fluid-bath` (new); `coupling.curvature-jets` (scope) |
| `Foundation/CantorStringSpectrum` | Each address `w` of `FractalPacking` has its cell `[c_w, c_w + 3^(−|w|)]`, the owner's `descend w root` with the Cantor reader's moment as its lower end, and its hole, the open middle third between the cell's two children (`cell_eq_descend`, `hole_eq_descend`, `cellLower_eq_moment`, `cellLower_eq_sum`); Mathlib's `preCantorSet n` is the union of the depth-`n` cells (`preCantorSet_eq_iUnion_cell`), the holes are pairwise disjoint, lie in `[0, 1]` with their ends in the Cantor set, and exhaust its complement (`pairwise_disjoint_hole`, `hole_ends_mem_cantorSet`, `unitInterval_diff_cantorSet`), with lengths `cantorLength n = cantorGap w`, so the set is null (`volume_cantorSet`) and the string's tube `V(ε)` is the measure of the set's inner `ε`-neighbourhood in its complement (`volume_innerTube`); the spectral count `N(x) = Σ_n 2^n ⌊x·3^(−(n+1))⌋₊` is the owner's `spectralCount` (`cantorCount_eq_spectralCount`), with `N(3x) = 2N(x) + ⌊x⌋₊` (`cantorCount_three_mul`), the Weyl term `N(x) ≤ x`, `N(x)/x → 1`, and `x^D ≤ x − N(x) < 2x^D` for `x ≥ 1` (`cantorCount_le`, `tendsto_cantorCount_div`, `rpow_cantorDim_le_sub_cantorCount`, `sub_cantorCount_lt`); the ratio `R = (x − N(x))/x^D` is `1` at `3^k` and `2^(1−D)` at `2·3^k`, invariant under `x ↦ 3x` on the natural numbers, and has no limit, beside the tube's `normalizedTube_not_tendsto` (`spectralRatio_three_mul_natCast`, `spectralRatio_not_tendsto`, `cantorString_counts_oscillate`) | #410's box "Fractal strings" (part); `FractalStringTube`'s "What is not claimed" | `fractal.cantor-holes-placed`, `fractal.cantor-spectral-count` (new); `fractal.cantor-gap-zeta`, `fractal.cantor-tube-content` (scope, owners), `fractal.minkowski-spectral-asymptotic` (scope) |

The boxes these answer, by their opening words: "Continuous crossing as the micro-step ring" (ticked); "Einstein: the
continuum realization" and "Curvature's strain and rotation" (each part done, by the same module); and "Fractal strings"
(part done).

## 2. What the pass corrected

1. The open item of `docs/ELEMENTARY_OBJECTS.md` §5 reads the continuous crossing "as the micro-step ring" without a
   range of `d`: the count `(r + N)/d` of continuous crossings holds at every `d ≥ 1`, but at `d = 1` the owner's ring
   marks every state on its section and records no `Crossing` (`no_crossing_of_denominator_one`), so the identification
   with the owner's records holds for `d ≥ 2`. The brief named the ring's state `(r + k) % d`; the owner's
   `ringOscillator` carries the unreduced potential `r + k`, and the statement is made there (the reduced state gives
   the same condition).
2. `Physics/Spacetime/Einstein`'s `[open]` paragraph named the continuum realization and the Regge construction as owed
   in #62, which closed on October 22 and resolves to #410; the paragraph now points to this module and names #410.
   `Physics/Spacetime`'s `[open]` list still carried the weak static limit `R₀₀ = ∇²Φ` after #1032 had proved it; it now
   points to both owners. `StressEnergy` said the source map "is exactly" the perfect fluid; the word is gone. The
   brief's barotropic law `ρa^(3(1+w))` needs `a > 0` for the real exponent; it is a hypothesis. The continuity equation
   is derived from the two Friedmann equations: no covariant divergence of tensor fields is built, so it is the content
   of `conservation_return` on this metric, not an instance of that theorem.
3. The brief called the Cantor string's spectral second term "the lattice case of Lapidus–Pomerance": their direct
   theorem of 1993 assumes Minkowski measurability, which the Cantor string lacks (`normalizedTube_not_tendsto`), so the
   string lies outside its hypothesis; its two-term count with an oscillating second term is Fleckinger–Vassiliev's
   example (Trans. AMS 337, 1993), and the atlas row `fractal.minkowski-spectral-asymptotic` now says so beside its
   scope. The brief wrote the cell's lower end `c_w = Σ_i 2w_i 3^(−(i+1))` with the hands read coarsest first, while the
   owner's words put the finest hand at the head; the proved form reads `w.reverse`. `N(x) ≤ x` needs `x ≥ 0`.

## 3. What each statement stands on, and what is left

- `Objects/ContinuousCrossing` identifies the free oscillator's section crossings with the micro-step ring's, sampled at
  any start and any `d ≥ 1`, joined to the owner's clock passage and its residue phase. A damped, pumped or driven
  oscillator (the parametron's Mathieu equation, a time-varying `ω`, Floquet growth), a nonuniform sampling clock and
  sections other than the upward zero and the crest are not stated. The box is ticked.
- `Physics/Spacetime/FriedmannFluid` builds the first metric field in the tree whose first jet does not vanish, reads
  its Ricci and Einstein tensors and its tide, and solves the field equation with a perfect fluid and its radiation
  bath, with de Sitter and a radiation solution as witnesses. Spatial curvature, perturbations, viscous or
  heat-conducting fluids on this metric, the Bianchi identity in general (the 3-jet), a change of coordinates, the
  deviation equation along a general geodesic and the Regge construction are not stated. Both boxes stay part done.
- `Foundation/CantorStringSpectrum` places the holes, proves the set null and the tube a Lebesgue measure, and computes
  the Cantor string's spectral count with its Weyl term and its oscillating second term of order `x^D`. The Tauberian
  theorem in general, Lapidus–Pomerance's criterion for a general string, the nonlattice case, `R`'s periodic profile
  and its limits beyond `1 ≤ R < 2`, Lapidus–Maier's inverse problem and its counterexample at `½`, Herichi–Lapidus and
  Makarov are not stated, and no Dirichlet Laplacian is built. The box stays part done.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owners that named these statements as unstated or owed (`Objects/Parametron`'s `[open]` paragraph and `docs/ELEMENTARY_OBJECTS.md` §5 on the continuous crossing; `Physics/Spacetime/Einstein`'s and `Physics/Spacetime`'s `[open]` paragraphs and `CurvatureJets`' "What is not claimed" on the continuum realization and the deviation equation; `FractalStringTube`'s "What is not claimed" on the holes placed, the tube as a measure and the Cantor string's spectral count), dropped the word "exact" from a docstring of `Objects/Parametron` and two of `Physics/Spacetime/StressEnergy`, and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3920 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10632 jobs)`, exit 0; `Holonics`, with `Objects/Parametron`, `Physics/Spacetime`, `Physics/Spacetime/Einstein`, `Physics/Spacetime/StressEnergy` and their importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new or edited file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
