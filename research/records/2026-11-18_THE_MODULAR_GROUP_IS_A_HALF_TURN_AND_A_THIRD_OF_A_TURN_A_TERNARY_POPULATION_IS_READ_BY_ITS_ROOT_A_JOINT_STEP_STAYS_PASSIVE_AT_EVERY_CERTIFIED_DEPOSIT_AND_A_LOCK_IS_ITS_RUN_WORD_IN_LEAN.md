# The modular group is a half-turn and a third of a turn, a ternary population is read by its root, a joint step stays passive at every certified deposit, and a lock is its run word, in Lean

November 18, 23:50 UTC. The fifth formalization pass of the day, over boxes of #410. Seven modules of
`lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no `axiom` and no
`native_decide`, and the last seven proofs of the libraries that closed by `native_decide` moved to the kernel.
Nothing here touches the engine, a state or a run. The passes before it are
[the first](2026-11-18_THE_THEORYS_CORE_STATED_IN_LEAN_RINGS_CLOSE_AT_THEIR_LCM_AND_CARRIES_AT_THEIR_PRODUCT_IDENTITY_IS_THE_MODES_SHARED_READINGS_AND_A_PROOF_IS_THE_ORBIT_OF_A_FINITE_MAP.md),
[the second](2026-11-18_A_NUMBER_IS_THE_HOMOLOGY_OF_ITS_PLACES_A_LAW_OF_COMPOSITION_IS_ITS_CHARACTERS_A_SYMBOLS_WORD_OBEYS_KRAFT_AND_A_RETURN_MAPS_NECKLACES_ARE_COUNTED_IN_LEAN.md),
[the third](2026-11-18_TWO_N_MARKOV_PARAMETERS_SEPARATE_SOURCES_A_SHIFTS_RATE_IS_ITS_SPECTRAL_RADIUS_A_PAIRS_MOVE_IS_A_PROPER_LORENTZ_MAP_READ_TWICE_AND_A_CHANGE_MOVES_ONE_CONTACT_A_TICK_IN_LEAN.md)
and [the fourth](2026-11-18_EVERY_PROPER_LORENTZ_MAP_IS_A_PAIRS_MOVE_THREE_DISTANCES_HOLD_AT_EVERY_REAL_RATE_RECURRENCE_IS_A_LEDGER_WITH_A_DEADLINE_AND_A_LEVELS_SITES_ARE_READ_FROM_ISOLATION_IN_LEAN.md).

Refs #410, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `EllipticCurve/TernaryReducedCount` | The four populations of the Tunnell carrier, filters of the cube `[-B, B]³`, `B = ⌊√n⌋`, are double sums of square fibres: the `z` with `c z² = m` in a box number `0`, `1` at `m = 0`, or `2` when `m/c` is a square whose root is in the box (`card_filter_sq`, read by `Nat.sqrt`, which the kernel reduces), so a filter of a product is the sum of its fibres (`card_filter_triple`, `card_diagonal`). For `a x² + y² + c z²` the outer sums need only `\|x\| ≤ ⌊√(n/a)⌋` and `\|z\| ≤ ⌊√(n/c)⌋` (`card_tight`). Every coefficient of the carrier is its double sum at every `n` (`fullTunnellThetaCoefficient_eq_reduced`, and on odd `n` the thin and thick counts alone), and the kernel reads `2, 0, 2, 0, −6, 0, 2, 0` at `1, 4, …, 64`, `−6` at `81`, `2` at `625`, `−6` at `729` and `26` at `15625` (thin `250`, thick `138`, over `177 · 89` and `177 · 45` pairs). | #998's record, §2 item 8 | `bsd.tunnell-reduced-count` (new), `bsd.shimura-lift-coefficients`, `bsd.shimura-local-recurrence` |
| `Geometry/ModularFreeProduct` | `S = [[0, −1], [1, 0]]` and `U = S T = [[0, −1], [1, 1]]` have `S² = U³ = −1`, so their classes in `PSL(2, ℤ)` have orders two and three; the Möbius action on `ℍ` kills the centre `±1`, `S` exchanges the halves `Re z > 0` and `Re z < 0`, and `U`, `U²` send the right half into the left, so Mathlib's ping-pong lemma makes `ℤ/2 ∗ ℤ/3 → PSL(2, ℤ)` injective; it is onto because `S` and `T` generate (`psl2zEquiv`, through the binary coproduct of the two factors, which Mathlib lists as a TODO). The Stern–Brocot moves are words in it: `[R] = s u`, `[L] = s u²` (`proj_sbRMove`, `proj_sbLMove`), and `s u = [T]` has infinite order, the `(2, 3, ∞)` signature. Legendre's `Γ(2)` holds `−1` and has index six (`index_Gamma_two`). | #410's box on monodromy as a group of moves; `Geometry/Farey` | `lock.modular-free-product`, `lock.stern-brocot-moves-as-words`, `lock.gamma-two-index` (all new) |
| `Geometry/LockAddress` | The retired Rust `LockAddress` on the positive chart: a run of `k` letters is `Rᵏ` or `Lᵏ`, `X Rᵏ X = Lᵏ` and `cfMatrix t = Rᵗ X`, so `Geometry/Farey.cfProd` is the run word up to one exchange (`cfProd_eq_runWord`), of determinant one, whose columns are consecutive convergents (`runWord_convergents`) and whose node `(1, 1) ↦ (h_(n+1) + h_n, k_(n+1) + k_n)` is their mediant, the last convergent with its last quotient one longer (`runWord_node`). The mediant stands `1/(k(k + k′))` and `1/(k′(k + k′))` from its unimodular neighbours (`lock_tolerance`); the denominator is the horizon, `q ∣ t p ⇔ q ∣ t` for `p/q` in lowest terms (`lock_horizon`); a pair with rates `u, v ≠ 0` locks at `(p, q)` exactly on the multiples of `(u/g, v/g)`, a stationary clock only at `p = 0`, opposite rates only at ratios of opposite sign (`lock_kernel`, `lock_kernel_stationary`, `lock_kernel_signed`). | #410's lock-address box; `Compression/SternBrocotCode` | `lock.run-word-address` (new), `contact.lock-address` |
| `Holon/LoopCurvature` | Over `ℚ`, `b₁ = \|E\| − rank d₀ − rank d₁` for a two-term cochain complex, and `\|E\| − \|V\| − \|F\| + 2` where the vertex and face kernels are each one line. On the owner's connection incidence at the trivial connection: the square-celled torus `C_m × C_n` for every `m, n ≥ 1` has `b₁ = 2`, its column cochain closed and not exact (`torus_betti1`, `torus_column_not_exact`); the cube's surface has `b₁ = 0` (`cube_betti1`). The zero-reduced-cost lemma: a feasible potential's reduced cost is nonnegative and telescopes, a walk of zero reduced cost is least and every edge of a least walk has zero reduced cost, while the least-potential neighbour is not least (`zero_reduced_walk_is_least`, `least_h_neighbour_counterexample`). Metric dimensions as kernel checks with Bellman-certified distances: `P₃` 1, `K_(1,3)` 2, `P₄ □ P₄` 2, `C₅ □ P₂` 2, `C₆ □ P₂` 3, `C₇ □ P₂` 2, `C₃ □ C₄` 3. | the loop-curvature record of September 28, §6 and §10 | `cell.first-betti-torus-sphere`, `landmark.zero-reduced-cost`, `landmark.small-metric-dimensions` (all new) |
| `Compression/KTNodeSplit` | Every Krichevsky–Trofimov face moves toward an arrival by `([c = y] − k(c))/(N + \|A\|/2 + 1)` (`ktFace_bump_sub`); at `\|A\| = 2` the split `a = (n₀ + ½)/(N + 1)` moves by `(y − a)/(N + 2)` and stays inside the unit interval (`nodeSplit_arrive`); the recursion from one half returns the split, uniquely (`splitOf_unique`); a face cell's `−log₂` width is the sum of its digits' code lengths (`faceCell_code_length`), and the KT code adds its conditionals' (`ktCode_snoc`). | the egg record of September 27, §3 | `hnn.landmark-kt-node-split` (new), `hnn.landmark-kt-sequential` |
| `HNN/JointStepCovector` | For the implicit-midpoint joint step `M x′ = A x + h B u`: the adjoint state `λ = M⁻ᵀ g′`; the covectors `Aᵀλ` on the opening state and `h Bᵀλ` on the supply, with no remainder; a change `R ↦ R + E` moves the next state by exactly `−h M_E⁻¹ E ē`, `ē = Q x̄`, so the derivative along a symmetric direction pairs `E` with `G_R = −h sym(λ ēᵀ)`. Passivity is proved: for `J` skew, `Q` symmetric, `R ⪰ 0`, `h ≥ 0` the energy rises by no more than the supply; a deposit `R′ = R − η G_R` keeps `R′ ⪰ 0` when `R ⪰ c I` and `η h (\|λ\|² + \|ē\|²)/2 ≤ c`, so the next step is passive, and it descends, `⟨G_R, R′ − R⟩ = −η ‖G_R‖²`. The reception owner's step is this step (`stepMatrix_eq`, `solveStep_after_eq`). | #410's joint-step box; the mutual-contact record of October 29, §3 | `holarchy.joint-step-covector` (new), `tower.mutual-contact` |
| `HNN/RestitutionFamily` | `S(Γ) = P + Γ(P − I)` passes the anchor and returns each difference times `−Γ`, with the power split `v² + Γ² Σ π_b (a_b − v)²`; a port's own return is `(1 + Γ)π_b − Γ`, `1/d`, `0` and `(2 − d)/d` at `Γ = 0`, `1/(d − 1)`, `1` for `d` equal ports; one tick of transit on reciprocal contacts gives `v^(k+2) = (1 + Γ) A v^(k+1) − Γ v^k`; the turning roots have modulus `√Γ` through `HNN/CarriedRate`; the slow root at `λ = 1 − ε` is `1` with derivative `−ρ`, `ρ = (1 + Γ)/(1 − Γ)`; the echo share `B = 1/d` gives `B/(1 − B) = 1/(d − 1)`, the matched splitter's `Γ`; the telegraph step's `Γ = (2τ − 1)/(2τ + 1)` has `ρ = 2τ`; the two-tick map is a bijection while `Γ ≠ 0`. | #410's restitution box; the junction record of November 13, §6 and §7 | `junction.restitution-family` |

The boxes of #410 these answer, by their opening words: "The exact owner's covector for the joint step" (whole);
"The junction's restitution family" (whole); "The lock address" (whole, with the signed case read as in §2);
"Krichevsky–Trofimov" (whole: the node split and the log-width sum, beside the binary bound done before); of
"Loop curvature" the first Betti numbers and the zero-reduced-cost lemma, with the metric dimensions short of
the tori `C₄ □ C₄` and `C₅ □ C₅`; of "Monodromy as a group of moves" the free product and the index of `Γ(2)`.

## 2. What the pass corrected

1. **No proof in the libraries rests on the compiler any longer.** The seven `native_decide` closures the fourth
   pass left, all lattice counts of the elliptic-curve family over boxes of up to `251³` points, now read the
   reduced count: `FamilyTunnellShimuraLift.tunnellThetaCoefficient_one` and
   `shimuraHeckeDifference_zero_through_sturm_aperture`, the two first-orbit Hecke defects of
   `FamilyTunnellHeckeIntertwining` at `p = 3` on `{1, 9, 81}` and `p = 5` on `{1, 25, 625}`, and the three
   checks of `FamilyWaldspurgerGate`. `bsd.shimura-lift-coefficients` rests on the kernel alone. The first
   reduction summed the fibre over the whole square `[-B, B]²` and a check of the value at `15625` was killed for
   memory beside three other Lean processes; the tight boxes take it to under a minute for the module.
2. **The gate's three checks were anonymous.** `FamilyWaldspurgerGate`'s `example`s are now the theorems
   `canonicalBranchCount_three`, `_eleven` and `_fortyThree` (`c₃ = 1`, `c₁₁ = −1`, `c₄₃ = 3`), so the row
   `bsd.waldspurger-gate-count` can own them. They are decided over the gate's own definitions, because the
   reduced count imports the carrier that imports the gate.
3. **A pointer to a closed issue.** `Geometry/EggModular` named its analytic obligations "in #62"; #62 closed on
   October 22 into #410, and the line now names #410's box and the free product beside it.
4. **The restitution row's slow root.** `junction.restitution-family` wrote the slow root as
   `1 − ρε + O(ε²)`; what is proved is its derivative at `ε = 0`, the first-order term the box asks for. The
   row moves from `proved-derived` to `formal-checked` with its scope saying so.
5. **The KT rate at any alphabet.** The egg record's `(y − a)/(N + 2)` is the binary case of
   `([c = y] − k(c))/(N + |A|/2 + 1)`; the general form is stated and the binary one derived from it.
6. **The box's "signed kernel"** is read as the lock relation `q u = p v` over signed rates (`agent-inferred`).
   If it meant words of `SL(2, ℤ)` with negative entries, that chart is the free product of
   `Geometry/ModularFreeProduct`, and the run word's signed form is not stated.

## 3. What each statement stands on, and the constructions beside it

- **The reduced count.** It is a reduction of counting, not of the forms: nothing here is a theorem about the
  Shimura lift or the Hecke operators, which consume the values. The level corrections are still read over the
  whole square and so only at small `n`; a tight box for `4x² + 2y² + c z²` is the same lemma with the middle
  coefficient two.
- **The free product.** The ping-pong is played on the open halves of `ℍ` by real part. The Schwarz map of the
  `(½, ⅓, 0)` triangle, `Γ(2)` as the monodromy of Legendre's family and its freeness on `[[1, 2], [0, 1]]`
  and `[[1, 0], [2, 1]]`, and `K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)` stand in the box. The construction for the
  freeness is a ping-pong of the same kind on `ℍ`, with the translation by two and its conjugate by `S`.
- **The lock address.** The Euclidean descent that builds the runs is `SternBrocotCode.path` read letter by
  letter; the cheapest lock strictly between neighbours is `PairResonance`'s.
- **Loop curvature.** The faces are signed matrices joined to `Holon/Complex` through `∂² = 0` against its
  incidence, because the owner reads a cell as a closed walk of forward edges. The two tori of the notebook
  need a refusal over every triple (560 at `C₄ □ C₄`), which an enumeration by `powersetCard` ran out of
  memory on; the construction is the refusal read up to the torus's own translations, which fix one landmark.
- **The joint step.** The certificate is one sufficient bound against a floor of `R`; the least step that
  breaks `R′ ⪰ 0` is the least eigenvalue of a rank-two update. The covectors on `J` and `Q` are the same
  variation with `E` in their place.
- **The restitution family.** One `Γ` for the whole network and real port values; a `Γ` per site needs it
  constant across each site's partners.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the seven modules by name with the four this change edits
(`FamilyTunnellShimuraLift`, `FamilyTunnellHeckeIntertwining`, `FamilyWaldspurgerGate`, `EggModular`): RESULT.
Single-file checks of each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision on a cloud host, for the reason the first pass's record gives (`agent-inferred`), each read by its exit
status. The research library's aggregator imports the seven modules.

Three workers on disjoint owner paths wrote six of the modules (the free product; the loop curvature and the KT
split; the joint step, the restitution family and the lock address), and the lead wrote the reduced count and
the seven replacements. A restart of the host stopped the workers at 23:32; their files were re-checked by the
lead from the tree, and every `L:` owner added to the atlas was read against its module's declarations.
