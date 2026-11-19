# The hand's saving is sandwiched by its square, a map and its dual share one Ihara factor, the repair's patches are a prefix code, differences are jets at any step, and founding obeys Ville at every horizon, in Lean

November 19, 01:20 UTC. The seventh formalization pass over #410, its fifth set, after
[the fourth](2026-11-19_THE_STRANDS_HOLD_THE_SUM_ONLY_IN_THEIR_COMPARISON_EACH_POLYNOMIAL_KERNEL_IS_THE_IMAGE_BEFORE_IT_A_NUMBER_KEEPS_ITS_LOWER_LEVEL_AND_A_READING_IS_BOUNDED_BY_ITS_LEVERAGE_IN_LEAN.md)
(#1014). Six new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #404, #398, #366, #33, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Zeta/HandCountDeficit` | The equation of state `w = −V L′/L` is `−d ln L/d ln V` (`eos_eq_neg_deriv_log_log`), and an excess `C = L − hV` concave on `[0, ∞)` with `C(0) = 0` gives `w ≥ −1` (`eos_ge_neg_one`). In nats `ln 2 − H((1 + y)/2) = Σ_(k≥1) y^(2k)/(2k(2k − 1))` (`hasSum_gap`), between `y²/2` and `y² ln 2` for `|y| ≤ 1` (`gap_bounds`), so `L²/(2N ln 2) ≤ D(N) ≤ L²/N` (`deficit_sandwich`); `|L(N)| ≤ N` on the primes' hand (`abs_runningHandSum_le`), and `Hand.TheHandCancelsToSquareRoot` holds exactly when `D(N) ≤ C N^ε` for every `ε > 0`, with no hypothesis (`hand_iff_deficit`). | the record of October 23 on code length as a field, §1 and §5 | `code.equation-of-state`, `rh.hand-count-deficit` (now `formal-checked`) |
| `Landmarks/IharaTwoFrames` | A combinatorial map `(σ, α)`, `α` a fixed-point-free involution, and its face dual `(σα, α)` on one set of darts: the dual's dual is the map (`dual_dual`), its vertices are the faces (`faceCount_dual`), the darts are two copies of the edges (`dartOf_bijective`, `card_darts`), and the face frame is the dual's own source frame (`face_frame_eq_dual_frame`), so `Landmarks/IharaBass.ihara_bass` read in the vertex frame and in the face frame shares the factor `(1 − u²)^E` (`two_frames_ihara_bass`). With Euler's relation, `b₁ + b₁* = E`, `b₁ = F − 1` and `b₁* = V − 1` (`cycleRank_add_dual`, `cycleRank_eq`, `dual_cycleRank_eq`); a diagram's `c` crossings add `c` to the source's cycle rank, so the source pairs with the dual exactly when `c = 0` (`diagram_cycleRank`, `source_pairs_with_dual_iff`). | #410's box `trace.ihara-two-frames`; the Rust owner `geometry/receiver_topology.rs` at `13f8c734` | `trace.ihara-two-frames` (now `formal-checked`) |
| `Transport/RepairCodec` | A repair codec (damage, key, patches, and a decoder that reads no further than its patches, `decode(damage x, key, patches x ++ r) = (x, r)`) reopens every passage (`reopen_damage`) and is a `Foundation/ContinuingTower` transition whose residual is the key and the patches (`toTransition`, `toTransition_reopen_apply`). Over one fibre the patches are a prefix code (`prefixFree_patches`), injective in every universe (`injOn_fibre`), obey Kraft's inequality (`kraft_on_fibre`, proved directly), and the longest has at least `⌈log₂ N⌉` bits (`exists_long_patch`). | #410's box "The repair codec is a Fold transition" (#366); the repair record of October 5 | `compression.pair-repair` |
| `Transport/JetAtStep` | The staircase's `Δ` iterated on the samples `m ↦ g(x₀ + mh)` is the step-`h` difference `Δ_[h]` iterated on `g` (`delta_iterate_sample`), so no second difference operator is founded. The jet `toJet_h(D)(u) = Σ_(k≤r) (D_k/k!)·(u/h)_k` has the matrix `[tⁱ](t)_k/(k! hⁱ)` (`coeff_toJetAtStep`), upper triangular (`entry_eq_zero_of_lt`, `coeff_toJetAtStep_triangular`) with diagonal `1/(k! hᵏ)` (`entry_diag`). For `deg p ≤ r` and `h ≠ 0` the jet of `p`'s step-`h` differences at `x₀` is its Taylor expansion at `x₀` (`toJetAtStep_differences`, by Gregory–Newton and `differences_eq_zero_of_lt`); any differences read back from the jet return for every `k ≤ r` (`differences_toJetAtStep`, through `JetStaircase.coefficient_eq_iteratedDelta_at_zero`); the jet holds exactly the first `r + 1` (`toJetAtStep_eq_iff`). | #410's box `toJet_atStep` (#33); the Rust owner `to_jet` in `jet_staircase.rs` at `13f8c734` | `jet.to-jet-at-step` (new) |
| `HNN/FoundingVille` | Ville's inequality at every finite horizon on a finite alphabet: for a law and a test whose conditionals sum to at most one, the chance that `Q/P` reaches `λ` by horizon `N` is at most `1/λ` (`ville`), nondecreasing in `N` (`chance_mono_horizon`). A node law with a subprobability kernel is dominated by its node maximum likelihood (`countedProb_le_nodeML`), so a family founds by `N` with chance at most `Σ 2^(−cost)` (`founding_ville`). The helical instance, the KT split law on `(k mod ℓ, y_(k−offset))` against a null that is a node law on `(k mod gcd(ℓ, L), y_(k−offset))` at every candidate (`ktTest_eq` is the Rust's `(2·seen + 1)/(2·total + |A|)`), is `founding_universal_inference`; one `g` dividing every `gcd(ℓ, L)` meets its hypothesis (`founding_universal_inference_of_dvd`), and the supremum over horizons stays below one when the family bound does (`founding_below_one`). | #410's box "Founding (#398)"; the Rust owner `hnn/founding.rs` at `d5ed4adc1` | `hnn.founding-universal-inference` (now `formal-checked`) |
| `HNN/FinestGrain` | A receiver's grain `L_R = ⌈1/ε⌉`, refused typed where `ε ≤ 0` or `L_R` passes the `u64` carrier (`receiverGrain_isSome_iff`, `receiverGrain_spec`), the least denominator that resolves `ε` (`one_div_grain_le`, `grain_le_of_resolves`); the finest grain is the Rust's fold (`finestGrain_eq_foldlM`), read without refusal exactly when every receiver has a grain (`finestGrain_isSome_iff`), and `declare` refuses exactly there (`declare_isSome_iff`), so on a declared field it is a total read with `1/max_R L_R ≤ ε_R` for every receiver (`Declared.finestGrain_eq`, `Declared.finest_resolves`). The lattice exponent `size(2 L_R max(X, 1) − 1)` is the least `L` with `2 L_R X ≤ 2^L` (`latticeExponent_le_of_reach_le`), which discharges `HNN/LatticeDeposit.remainder_below_grain`'s hypothesis: a remainder of one unit an entry moves every receiver's read by at most `ε_R/2` (`remainder_below_every_tolerance`). | #410's box "Every receiver of a declared field has a grain"; the Rust owner `hnn/field.rs` at `d5ed4adc1` | `hnn.receiving-precision-at-grain` |

The boxes these answer, by their opening words: "The code length's equation of state and the count lens on the primes'
hand" (whole); `trace.ihara-zeta`, `trace.ihara-two-frames` (whole, its first half done in #1000); "The repair codec is
a Fold transition" (whole, as corrected in §2); "The change of basis from differences to jets at an arbitrary rational
step" (whole); "Founding (#398)" (whole, at every finite horizon and on their supremum); "Every receiver of a declared
field has a grain" (whole).

## 2. What the pass corrected

1. **The sandwich's upper constant needs the series.** The record of October 23, §7, says the equivalence's upper side
   needs only `log z ≤ z − 1`. For the equivalence it does, since a constant factor leaves `O(N^ε)` as it is; but that
   inequality gives `D(N) ≤ L²/(N ln 2)`, and the sandwich's stated `L²/N` follows from the series: each term over `y²`
   increases in `|y|`, and their sum at `|y| = 1` is `ln 2` (`gap_mono`, `gap_bounds`).
2. **The equation of state's hypotheses.** `code.equation-of-state` asked for `L` positive and differentiable. The
   bound `w ≥ −1` uses the excess's concavity on `[0, ∞)` with `C(0) = 0`, `V > 0`, `L(V) > 0` and `C` differentiable
   at `V`; the row's scope now says so.
3. **The repair's bound needs a decoder that reads no further than its patches, and it bounds the longest patch.**
   With reopening and injectivity alone, `N = 3` passages in one fibre can carry the patches `[]`, `[0]`, `[1]`, none of
   length `⌈log₂ 3⌉ = 2`. The box and the row said "of length at least `⌈log₂ N⌉`" of every residual; the module takes
   the decoder's law as the codec's definition and proves the bound for the longest word, and the box is reworded.
4. **`E − V + 1` is the first Betti number only for a connected map,** and the two-frame identities take Euler's
   relation `V − E + F = 2` as a hypothesis; neither connectivity nor planarity is derived.
5. **The founding null is a node law at every candidate's node.** `g = gcd(ℓ, L)` changes with the candidate, so "the
   null where `y_k` depends on the past only through `(k mod g, y_(k−offset))`" names one null per candidate, and the
   union bound needs it at each; one `g` dividing every `gcd(ℓ, L)` suffices. The Rust's module doc calls `Q/P` a
   martingale of mean one: the martingale is `Q_counted/P_counted`, `Q` extended by `P` on the opening cells, and Ville
   needs only `ΣQ ≤ 1`. The bound needs no positivity of the law and holds at any offset, zero included.
6. **The grain had no Lean owner.** `hnn.receiving-precision-at-grain` cited `LatticeDeposit.remainder_below_grain`,
   which takes `L_R` as a bare positive natural. The ceiling, its `u64` refusal and the finest grain are now
   `HNN/FinestGrain`'s, which also discharges that theorem's hypothesis from the lattice exponent.
7. **The jet at a step stands beside the staircase.** The box named `Transport/JetStaircase` as the owner; the change of
   basis at step `h` is `Transport/JetAtStep`, joined to it through `delta_iterate_sample`, and the step-one case is the
   staircase's own Newton jet (`toJetAtStep_one_eval`). The atlas had no row for it; `jet.to-jet-at-step` is new.
8. **A history owner read at the wrong commit.** A worker read `trace.ihara-two-frames`'s unpinned owner
   `crates/holonics/src/geometry/receiver_topology.rs` as broken at `d5ed4adc1`. An unpinned `H:` owner names the
   pre-reset tree `13f8c734`, where the file stands, so the owner stays as it is.

## 3. What each statement stands on

- **The hand's saving** stands on Mathlib's binary entropy and its series; its RH reading passes through the classical
  equivalence of `TheHandCancelsToSquareRoot` with the Riemann hypothesis, named by `Zeta/Seam` and not formalized. The
  Stirling form of `KT(N)` and the octave form of `w` stand beside it.
- **The two frames** stand on `Landmarks/IharaBass`, instantiated twice on one dart set; the Euler product side in two
  frames is not restated.
- **The repair codec** stands on `Transport/Fold` and `Foundation/ContinuingTower`; the restriction to the fixed point
  (arc consistency, the repair record's §8 item 1) and the count of one patch a held chain are left to the record's
  receipts.
- **The jet at a step** stands on Mathlib's `fwdDiff` (Gregory–Newton, the vanishing above the degree) and on the
  staircase's change of basis; the Rust's order ceiling and its refusal past the sample count are bounds of the
  realization.
- **Founding** is read at every finite horizon. No measure on infinite streams is built, so equating the supremum with
  the chance of ever founding needs continuity from below, which is not formalized; `reopen` as a fresh e-process, the
  description ceiling and the read's interval enclosure stay in the Rust record.
- **The grain** models `Field::declare`'s first refusal; the `u128` saturation of the lattice exponent and the fan-in's
  `ℓ1` bound stay the consumer's hypotheses, as in `LatticeDeposit`.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the six modules: `Build completed successfully (8867 jobs)`, exit 0, 102 s, no
declaration elaborated with `sorry`; projected under 10 minutes, deadline 20 minutes, peak resident set not read.
Single-file checks of each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision on
a cloud host, read by exit status (each `EXIT 0` with no output), for the reason the first pass's record gives
(`agent-inferred`). The research library's aggregator imports the six modules, and `tools/lean_census.py` reads
`unbuilt=0 unrooted=0`.

Three workers on disjoint owner paths wrote five of the modules; the lead wrote `Transport/JetAtStep`, re-checked each
file from the tree, and read every `L:` owner added to the atlas against its module's declarations by
`tools/link_check.py atlas` (`broken=0`).
