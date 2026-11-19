# The strands hold the sum only in their comparison, each polynomial kernel is the image before it, a number keeps its lower level, and a reading is bounded by its leverage, in Lean

November 19, 01:00 UTC. The seventh formalization pass over #410, its fourth set, after
[the third](2026-11-19_TWO_COUPLED_PLANES_TURNS_ARE_FREE_THE_CARRY_IS_A_CLASS_OF_ORDER_N_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART_IN_LEAN.md)
(#1009). Eight new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #404, #405, #386, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `HNN/StrandsComparisonChart` | Three strands under the rotor's laws (`A` held, `G` stepped, `H` turned on the sheet `o`), with the keys `H ← 0, o ← +1` before the first numeral, `A ← H, H ← 0, o ← e` at the operator and `G ← H, H ← −A, o ← +1` at the equals: a numeral moves them to `(A, μⁿG, μⁿH + o·value, o)` (`read_eq`); after `x ∘ y =` and `k` digits of the result, `A = x`, `G = μᵏ e y`, `H = p_k − μᵏ x` from any opening strands (`chart_eq`), so the comparison is `p_k − μᵏ(x + e y)` (`chart_comparison`) and no strand holds the sum; a written digit moves the conjugate face by `t ↦ μt − d` (`face_step`); where `μᴸ = 1` the comparison is `−μᵏ s_k` (`chart_comparison_on_ring`) and closes at `k = L` exactly where `z ≡ x + e y` (`chart_closes_iff`); on `ZMod q`, `q + 1 = bᴸ`, it discharges `RadixItinerary.strand_digit`'s hypothesis, so the `b`-th of the conjugate face is the next digit (`chart_digit`); the comparison's face is `face(H)·conj(face(G))` (`face_comparison_coe`) and the two hands differ by `2μᵏy` (`hands_differ`). The hand theorem: without the sheet, any linear operator keys and a shared equals key leave `y`'s coefficient `K_= h` the same, so two hands' difference never sees `y` (`hand_unread_without_sheet`). | #410's boxes "The strands' comparison chart" and "The strands' hand theorem"; the strands record of October 26, §2 and §4 | `hnn.tower-strands` |
| `Mathematics/PolynomialDeRham` | On homogeneous polynomials of three variables over any field of characteristic zero, `P_(n+1) → P_n³ → P_(n−1)³ → P_(n−2)` by gradient, curl and divergence: partial derivatives commute (`pderiv_comm`, which Mathlib does not state), so the chain is a complex (`curl_grad`, `div_curl`); the position's contraction is Koszul's homotopy, `x·∇f = nf`, `∇(x·F) − x × (∇ × F) = (n + 1)F`, `x(∇·G) − ∇ × (x × G) = (n + 2)G`, `∇·(xh) = (n + 3)h`; so each kernel is the image before it (`grad_eq_zero_iff`, `curl_eq_zero_iff`, `div_eq_zero_iff`, `div_surjective`, each with its witness); `dim P_d = C(d + 2, 2)` (`finrank_homogeneous`, through the `d`-multisets of three variables) and the curl leaves `C(n + 3, 2)` free (`curlFree_eq_range`, `finrank_curlFree`); `3C(n+2, 2) − 3C(n+1, 2) + C(n, 2) = C(n+3, 2)` and the chain's alternating count is zero (`free_count`, `alternating_count`). | #410's box "Gradient, curl and divergence on homogeneous polynomials"; the Einstein record of November 11, §14.4 and §14.12 | `gr.strength-alternating-count` (now `formal-checked`) |
| `Mathematics/LevelLaws` | The level of `n ≠ 0` in base `b ≥ 2` and its face (`level_eq_of_chart`, `chart`); a product adds the levels and climbs by its words' product, never at a prime base (`level_mul`, `level_mul_prime`); a sum or difference keeps the lower level when the levels differ and can only climb when they agree (`level_add_of_lt`, `level_sub_of_lt`, `level_sub_of_gt`, `le_level_add`, `le_level_sub`), with the record's examples; numbers agreeing from place `m` up differ by less than `bᵐ` (`sub_lt_of_div_eq`, `sub_lt_of_leading_digits`); `x ↦ mx` on `ℤ/q` takes `q/gcd(q, m)` values, a coprime factor permutes, a factor `≡ −1` is the half-turn, `9x ≡ −x` and `x⁵ ≡ x (mod 10)` (`card_range_mul`, `mul_bijective_of_coprime`, `nine_mul_mod_ten`, `pow_five_modEq_ten`); the trailing digit law as the product's fibre, factored over any splitting `R ≃* S × T`, `2q − 1` and `q − 1` on a finite field, and base ten's `27, 4, 12, …` as the product of `ℤ/2`'s and `ℤ/5`'s laws through the Chinese remainder theorem (`pairCount_prod`, `pairCount_zero_field`, `pairCount_unit_field`, `pairCount_ten_factors`); `tr(A^p) ≡ tr(A) (mod p)` for every integer matrix (`trace_pow_prime_modEq`); `b` of the `b²` digit pairs propagate a carry and an unread carry after `m` places has chance `b^(−m)` (`card_propagate`, `unread_carry_prob`); and the clock cast `w′ = w · logRate V/logRate V′`, a constant cast keeping `w` and a slower unit clock reading the byte floor as phantom (`clock_cast`, `clock_cast_const`, `clock_cast_phantom`). | #410's box "Association is evaluation, and a number is a word at a level of the base's tower", its clauses after the fibre law; the record of October 23 on association, §§1, 2, 4, 6 and 7 | `radix.level-laws`, `radix.difference-leading-cancellation`, `radix.product-digit-law-factors`, `code.clock-cast` (now `formal-checked`); `radix.multiplier-face-action`, `arith.fermat-ring-partition`, `radix.carry-chain-eulerian` |
| `Compression/KTPartitionInvariant` | A KT code on any keying of the counted cells, its face `(2N_y + 1)/(2n + |A|)` (`cellFace_eq`); two keyings that group the earlier cells alike give the same faces and code (`keyedCode_eq_of_agree`); the split keying `(k mod ℓ, a k)` and the node keying `(k mod g, a k)` agree when the context with the node phase fixes `k mod ℓ` (`kt_code_partition_invariant`), the box's reading at `g = gcd(ℓ, L)` (`kt_code_partition_invariant_of_context`), with surplus zero; the Rust fixture's equality at every length (`fixture_codes_equal`); and with a constant context the split's face is `3/4` where the node's is `1/2` (`phase_not_carried_parts_faces`). | #410's box `kt_code_partition_invariant` (comment c6249536068, item 2) | `code.kt-partition-invariant` (now `formal-checked`) |
| `HNN/FoundingCapacityPeriod` | The founded count `N_ℓ(n) = F(n)·(n + ℓ)·(the founded source's binomials)` (`foundCount_eq`), nondecreasing in the period (`foundCount_mono`), with `C(t+k−1, k−1) ≤ C(n+k−1, k−1)` for an Own population `t ≤ n` (`own_population_le`); the admitted periods form an initial segment (`founding_admits_initial_segment`), the crossover is monotone in the period (`capacity_crossover_monotone_in_period`), the one-count test holds exactly when `n* ≤ P` (`founding_admits_iff`), and the late-source states lie in a box of at most the founded source's factor (`late_source_bridge`). | #410's box `capacity_crossover_monotone_in_period` (the same comment, item 3) | `hnn.capacity-crossover-monotone-in-period` (now `formal-checked`) |
| `Aeon/Clock/OwnClockCarry` | An Own ring ticks one a cell with carry zero in and out (`own_tick_ignores_carry`); an Own ring anywhere in the chain leaves the rest of it (`chain_insert_own`), so each Lock tick and the final Lock carry equal those of the field without its Own suffix (`own_clock_leaves_the_carry_chain`), and the aeon closes at the same cells over a passage (`carryWord_append_owns`); the Lock chain is `HNN/Moment.SelectiveDecl`'s step with ones appended (`founded_chain_eq_selective`). | #410's box `own_clock_leaves_the_carry_chain` (the same comment, item 4) | `hnn.own-clock-leaves-the-carry-chain` (now `formal-checked`) |
| `HNN/ReadingLeverage` | In a pivot chart `K` of a positive semidefinite Gram, `v = v_s + ρ` with `v_s ∈ range G`, `ρ_K = 0` and `ρ = 0 ↔ v ∈ range G` (`supported_mem_range`, `openPart_comp`, `openPart_eq_zero_iff`); `|wᵀv_s|² ≤ (wᵀGw)·h_K` for every form, attained (`sq_dotProduct_supported_le`, `supported_bound_attained`); forms equal on the cells share `wᵀv_s` and differ on `v` by `(w − w′)ᵀρ`; in range `h_K = vᵀG⁻v` for every generalized inverse, in every pivot chart and under a rebase (`chartLeverage_eq_ginv`, `chartLeverage_chart_free`, `chartLeverage_rebase`); the bordered corner `−Δ h_K` and a passed pivot's entry `Δ ρ_p` (`det_bordered_corner`, `det_bordered_passed`); `Π(1 + h_t) = det G_N/det G_0` and the prequential identity for any positive definite prior (`prod_one_add_lev`, `prequential_isLeast`, `prequential_unit_prior`); and GPT-6's example, the chart's bound attained where a pseudo-inverse's reading gives `1/4` (`witness_bound`). | #410's box "The leverage of a new reading"; the record of October 24 on what a contact cannot bridge, §§9 and 10 | `contact.reading-leverage` (now `formal-checked`), `release.leverage-probe` |
| `HNN/LapsByComposition` | The tension is read off `(H, B, T)` alone, so a reread at one constitution leaves it (`tension_eq_of_moments`); founding never raises it, its drop `M G_Q Mᵀ ⪰ 0` for every generalized inverse (`founding_le`, `founding_drop_posSemidef`); a candidate with `M = 0` founds nothing while the founded set stands (`founds_nothing_of_crossRemainder_eq_zero`, `founds_nothing_until_added`); the lap tension is antitone in the founded set and a lap that founds nothing is a lasting fixed point (`lapTension_antitone`, `lap_fixed_point`, `lapTension_fixed`); and the foundings number at most `(L₀ − L_floor)/c_min` (`foundings_card_le`, `foundings_finite`). | #410's box "Laps found by composition"; the record of October 25 on laps over the same text | `contact.lap-founds-reachable` |

The boxes these answer, by their opening words: "The strands' comparison chart" (whole); "The strands' hand theorem"
(whole); "Gradient, curl and divergence on homogeneous polynomials" (whole); `kt_code_partition_invariant` (whole);
`capacity_crossover_monotone_in_period` (whole, the bridge as a count); `own_clock_leaves_the_carry_chain` (whole);
"Laps found by composition" (whole); "Association is evaluation" (all but the carry chain's Eulerian stationary law);
"The leverage of a new reading" (all but the corner's `Γ_k` series and the error `σ²(1 + h)`).

## 2. What the pass corrected

1. **A prime power's trailing law has a third kind of pair.** `radix.product-digit-law-factors` said that on each
   prime's cycle a pair either collapses to `0` or turns among the units, with `2p − 1` and `p − 1`; that holds at
   exponent one. On `ℤ/4`, `2 · 1 = 2` is neither, and `0` has 8 pairs; the row now says so.
2. **The leading face's cancellation needs no equal lengths**, and its example read "lengths (5, 4), (5, 4)" for two
   numbers of length 4: the row now gives the shared leading digit 5 and length 4, and the scope says that agreeing from
   place `m` up is enough.
3. **Fermat on a ring holds for every integer matrix.** `arith.fermat-ring-partition` scoped its Lean to nonnegative
   entries, which is the necklace count's; the congruence `tr(A^p) ≡ tr(A)` is now proved without it.
4. **The clock cast needs nonzero log-rates, not positivity**, which only reads them as `d ln`.
5. **The KT split's hypothesis is weaker than the box's.** The context need fix `c mod ℓ` only together with the node
   phase.
6. **The crossover box's formula is the crossover of `F + ℓ`.** The box wrote `n·(F + ℓ)`, a product, where the atlas
   writes `n*(F+ell)`, the crossover of `F` with an Own ring of period `ℓ`; the box is corrected when ticked, and the
   row gains the count `N_ℓ(n) = F(n)·(n + ℓ)·…` that the monotonicity is read on.
7. **The leverage's sequence identities hold for every positive definite prior**, the unit prior one case; and the
   probe's ball is proved as an inclusion (Cauchy–Schwarz), its other half beside it.
8. **GPT-6's outside module need not be carried in.** The box asked to carry in its proof of the main inequality for a
   factor `L·diag(d)·Lᵀ`; `sq_dotProduct_supported_le` holds on any positive semidefinite Gram, which covers it.
9. **Partial derivatives commute on `MvPolynomial` is not in Mathlib** at the pinned revision; `PolynomialDeRham`
   proves it on monomials.

## 3. What each statement stands on

- **The strands** are stated for every `x`, `y` and hand, which replaces the record's census of 1,496,496 calculations;
  the keys' location (§3) is the October machine's reading and stands beside it.
- **The polynomial chain** is read in three variables; Einstein's strength in four (§5.6) is the same alternating count
  with its identity term, and Hilbert's syzygy theorem, which bounds the chain at `n` steps in `n` variables, stands
  beside it.
- **The level laws** are on `ℕ` (a difference with `y < x`); the carry chain's Eulerian stationary law and spectrum,
  the discrete-log phases of `(ℤ/10)ˣ`, the base-12 instance and Benford's law stand beside them.
- **The crossover's bridge** is a count: the stream statement that a late source's persisting state lies in its box
  is read on a common opening (`HNN/Moment.persist_mem_box`).
- **The leverage** leaves the corner's `Γ_k` series (Sylvester's identity for the stored minors), the off-range limit,
  the error `σ²(1 + h)` and the charge `½ log₂(1 + h)`.
- **The laps** take the founding rule as a function of the founded set and the code's fall per founding as a
  hypothesis (the founding test); the pool of products and the reach's doubling stand beside them.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the eight modules: `Build completed successfully (8859 jobs)`, exit 0, 42 s, no
declaration elaborated with `sorry`; projected under 10 minutes, deadline 20 minutes, peak resident set not read.
Single-file checks of each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision
on a cloud host, read by exit status (each `EXIT 0` with no output, 2 to 6 s), for the reason the first pass's record
gives (`agent-inferred`). The research library's aggregator imports the eight modules, and `tools/lean_census.py` reads
`unbuilt=0 unrooted=0`.

Three workers on disjoint owner paths wrote six of the modules; the lead wrote `HNN/StrandsComparisonChart` and
`Mathematics/PolynomialDeRham`, re-checked each file from the tree, and read every `L:` owner added to the atlas
against its module's declarations by `tools/link_check.py atlas` (`broken=0`).
