# A pool's best face is its leading eigenvectors, level two is free on two carries, a softmax release falls by the entropy two passes apart, and a conserved face is a congruence, in Lean

November 19, 00:35 UTC. The seventh formalization pass over #410, its second set, after
[the first](2026-11-19_A_LOAD_MOVES_A_LINE_BY_ITS_WEIGHT_ON_THE_MODE_THE_MAGNITUDE_CANNOT_SEE_THE_BASINS_IT_REFLECTS_THE_STABLE_CORE_IS_THE_FIRST_ROUND_AND_A_LOSSLESS_PERIOD_READS_HILLS_KINDS_BY_ITS_TRACE_IN_LEAN.md)
(#1006). Eight new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`,
no `axiom` and no `native_decide`, and two docstrings brought current. Nothing here touches the engine, a state or a
run.

Refs #410, #404, #405, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `HNN/PoolFaceKyFan` | The Ky Fan maximum principle and its pencil: for a symmetric `A`, `tr WᵀAW ≤ λ₁ + … + λ_k` on every orthonormal `k`-frame, attained at the leading eigenvectors (`trace_le_leadingSum`, `isGreatest_trace`), through frame weights in `[0, 1]` summing to `k`; with `R = Q^(1/2)`, `det(B − λQ) = det Q · det(R⁻¹BR⁻¹ − λ)` and the bound under `WᵀQW = 1` (`det_sub_smul`, `trace_le_gen`, `exists_trace_eq_gen`). Joined to `EffectiveTension.tension_fromRows_pool`: no rank-`k` pool face removes more than the sum of the `k` leading generalized eigenvalues of `(MᵀM, Q)`, the leading generalized eigenvectors remove exactly that for every generalized inverse of the joint Gram, and the whole pool removes `tr M Q⁻¹ Mᵀ` (`pool_face_removal_le`, `exists_pool_face_removal_eq`, `whole_pool_sum`). | #410's box on the effective tension; the record of October 24 on what a contact cannot bridge, §6 | `contact.pool-founding`, `contact.tension-founds-face`, `contact.ky-fan-pencil` (new) |
| `Geometry/LegendreLevelTwo` | Sanov's theorem: `A = [[1, 2], [0, 1]]` and `B = [[1, 0], [2, 1]]` generate a free group by ping-pong on the integer plane's two cones (`sanov_injective`), no word is `−1` (every word is `≡ 1` modulo four on the diagonal), so the word map stays injective into `PSL(2, ℤ)` (`sanov_psl_injective`); every `g ∈ Γ(2)` is `±` a word by descent on `|c|` (`exists_sanov_eq`); and `F₂ ≃* Γ(2)/±1` (`gammaTwoFree`). | #410's box "Monodromy as a group of moves", its clause on Legendre's `Γ(2)` | `lock.gamma-two-index` |
| `Geometry/CompleteEllipticSeries` | `K(√λ) = ∫₀^(π/2)(1 − λ sin²θ)^(−1/2) dθ = Σ (π/2) w_n² λⁿ = (π/2) ₂F₁(½, ½; 1; λ)` for `0 ≤ λ < 1`, with `w_n = C(2n, n)/4ⁿ = (½)_n/n!` the Wallis weight, the binomial series of `(1 − x)^(−1/2)` and the Wallis integral, integrated term by term under the bound `λⁿ` (`ellipticK_eq_hypergeometric`, `hasSum_ellipticK`). | the same box, its clause `K(√λ)` | `egg.period-coefficients` |
| `Physics/Wave/TelegrapherLimit` | Two ticks of the LC chain eliminate the current exactly over `ℚ` for any material (`two_ticks`); on a uniform chain they are the centred scheme of `εμ∂²_t + σμ∂_t − ∂²_x` (`uniform_chain_scheme`); and the scheme on samples of a function whose slices are twice differentiable tends to `εμ u_tt + σμ u_t − u_xx` as `(h, k) → (0, 0)` with no ratio of the steps assumed (`scheme_consistent`). | #410's box on the light cone and the scheme's continuum limit | `wave.lc-chain-tick` |
| `HNN/SoftmaxTwoCycle` | A place hearing its own softmax release in step: the release is a law; for a symmetric coupling the pair energy `E(s, t) = −⟨t, Ws⟩ − ⟨b, s + t⟩ + T(Σ s log s + Σ t log t)` obeys `E(s, t) = E(t, F t) + T·D(s ‖ F t)` (`energy_identity`, through Gibbs's variational principle), so it falls in step and stands exactly on a fixed point or a two-cycle (`energy_orbit_eq_iff`); the fall telescopes, the energy is bounded below on laws, and `Σ_k D(x_k ‖ x_(k+2))` is summable (`energy_telescope`, `kl_two_apart_summable`). | #410's box on the synchronous two-cycle, its softmax clause | `tower.field-echo`, `motion.relaxed-step-three-kinds` |
| `HNN/HalfPumpMonodromy` | The October founded ring's Half pump: on the harmonic in-phase pair the period map is the shear `[[1, 0], [−8hp/(a − b), 1]]`, determinant one and trace two, for `a ≠ b` and `a + b ≠ 0` (`half_pump_harmonic_monodromy`, `_matrix`); its signed form certifies exactly when `p ≤ d/h`, singular at the edge (`half_pump_edge_certifies`, `half_pump_edge_singular`); both on any incidence with `B·1 = 0` and nonnegative weights, the cyclic ring among them; and the Rust test's entries `−8, −8/3, −4, −4/3` and refused strengths (`declared_entries`, `declared_edges`). | #410's box `half_pump_harmonic_monodromy` and `half_pump_edge_certifies` (comment c6249536068, item 5) | `hnn.half-pump-harmonic-monodromy` (now `formal-checked`) |
| `HNN/SheetConjunction` | A reading of a stream's (symbol, lag residue) counts is additive over cells, so no count reading equals the conjunction of the last two symbols, and no sign of one reads their agreement; two locks moving by `σ′ = sign(h_s + J_s σ)`, the second gated by the first, read the conjunction or the agreement at every cell from any opening sheets, so the sheets' state is no count reading (`no_countReading_reads_conjunction`, `no_countThreshold_reads_agreement`, `conjunction_sheet_reads`, `agreement_sheet_reads`). | #410's box "The locked sheets make conjunctions"; the torsion record of October 22, §6 | `parametron.sheets-make-conjunctions` (new) |
| `Compression/OneFaceLaw` | For an operation of any arity, conservation of a face, the respect of `T` on equal faces, `q ∘ T = T_q ∘ (q ∘ ·)` and the fibre being one point are one condition; on a product its kernel is a `Con` and `q` factors through the quotient by an injective map carrying the product to `T_q`; jointly injective conserved faces read `T` on a window. Over `{t, h, a}`, "contains `th`" is not conserved, the seam face is, and the syntactic congruence has six classes and the right congruence three, with four contexts and two suffixes separating them; the syntactic congruence is the coarsest conserved refinement. The jet is a monoid map into the dual numbers and the derivative alone is not conserved; `det` is conserved and the trace is not, even beside `det`, while `tr(AB) = ⟨A, Bᵀ⟩`; the sign is conserved and the cycle type is not. | #410's box "One face law across operations" and the fibre clause of "Association is evaluation"; the record of October 24 on one face law, §§1 to 3 and 5 | `face.conserved-is-congruence`, `lang.seam-state-carry`, `face.algebra-census`, `arith.association-is-evaluation` |

The boxes these answer, by their opening words: "The effective tension at a contact" (whole, with #571); "The light
cone on a general graph and the scheme's continuum limit" (whole, with #996, at consistency);
"`half_pump_harmonic_monodromy` and `half_pump_edge_certifies`" (whole); "The locked sheets make conjunctions"
(whole); "One face law across operations" (whole); "Monodromy as a group of moves" (`Γ(2)`'s freeness and `K(√λ)`;
the Schwarz map with its monodromy and `Γ(2)` as Legendre's monodromy stay); "The synchronous two-cycle" (the
softmax release, with the period doubling of a pumped period read in `HNN/HillFloquetKinds` of #1006; the softmax
orbit's convergence stays); "Association is evaluation" (its fibre clause and the closure).

## 2. What the pass corrected

1. **Ky Fan was named missing from Mathlib, and the row said so.** `contact.pool-founding` gave the rank-`k` maximum
   and the whole-pool trace as not formal, and `HNN/EffectiveTension`'s docstring as not proved here; both now point
   to `HNN/PoolFaceKyFan`.
2. **The Half pump's row was narrower than its law.** `hnn.half-pump-harmonic-monodromy` held the statements on unit
   weights and `a > b`; they hold on any incidence with `B·1 = 0` and nonnegative weights, and the shear needs
   `a + b ≠ 0` beside `a ≠ b`. Its "owed #62" is retired.
3. **A threshold of a count reading reads the conjunction.** The record's §6 says the sheets' transitions make
   conjunctions that no readout linear in the counts reads; that holds for linear readouts, as the box says, but a
   threshold of one separates "both `a`" (`x + y > 3/2` is linearly separable). The threshold refusal holds for the
   agreement, and `SheetConjunction` proves that one beside the box's.
4. **The ring record states no softmax energy.** The one proved is the pair energy with the entropy terms, which turns
   the sign chart's sum of field terms into the relative entropy two passes apart.
5. **Two hypotheses of the telegrapher chain are not needed.** `two_ticks` needs no `L ≠ 0`, the current update being
   the definition, and `Telegrapher.step_is_the_telegrapher` asks for it where its first conjunct does not use it. The
   foundation's docstring ("in the continuum limit (not formalized here)") is true of its own file and was left, so
   that the framework closure is not rebuilt for a sentence; the atlas row carries the new owner.
6. **`deriving Fintype` fails on an enumeration at this toolchain.** On an inductive of constructors without fields
   the handler's `enumList` proof meets a coercion mismatch; `OneFaceLaw` writes the instance by hand, and a structured
   inductive (`SynClass`) derives it.

## 3. What each statement stands on

- **The pool's face** compares removals by trace, not in the Loewner order, with `Q` positive definite; the singular
  `Q` read on its range, the code savings and the worked numbers stand in the record's receipts.
- **Level two** is free as a group of moves; that it is the monodromy of Legendre's family `y² = x(x − 1)(x − λ)`,
  the periods continued round `0` and `1`, is the construction to make next, with the Schwarz map of the
  `(½, ⅓, 0)` triangle.
- **The period** is read on `0 ≤ λ < 1`; negative `λ`, `K′` and Legendre's relation stand beside it.
- **The scheme's limit** is consistency at `o(1)`; the `O(h² + k²)` rate needs bounded third and fourth derivatives,
  and convergence of solutions joins it to the stability of `Physics/Wave/Energy` under `h < √(εμ) k` (Lax).
- **The softmax two-cycle** is approached: the relative entropy two passes apart is summable; convergence of the orbit
  needs Łojasiewicz's inequality or isolated critical points.
- **The face law's census** (784 of 3,025 rectangles, 81 face pairs, 218 of 256 plural trace pairs) is the record's
  receipts; the module proves each law and one witness of each failure.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the eight modules and the two whose docstrings changed:
`Build completed successfully (8719 jobs)`, exit 0, 34 s, no declaration elaborated with `sorry`; projected under 10
minutes, deadline 20 minutes, peak resident set not read. Single-file checks of each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision on a cloud host, read by exit status (each `EXIT 0` with no output, 2 to 7 s), for the reason the first pass's
record gives (`agent-inferred`). The research library's aggregator imports the eight modules.

Three workers on disjoint owner paths wrote seven of the modules; the lead wrote `Compression/OneFaceLaw`, re-checked
each file from the tree, and read every `L:` owner added to the atlas against its module's declarations by
`tools/link_check.py atlas` (`broken=0`).
