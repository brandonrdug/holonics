# The strength is three times the free functions of three variables, sheets do not coarsen where a word crosses back, the survivors are the cycle fibre, and a key's move is the derivative of the code, in Lean

November 19, 01:55 UTC. The seventh formalization pass over #410, its sixth set, after
[the fifth](2026-11-19_THE_HANDS_SAVING_IS_SANDWICHED_BY_ITS_SQUARE_A_MAP_AND_ITS_DUAL_SHARE_ONE_IHARA_FACTOR_THE_REPAIRS_PATCHES_ARE_A_PREFIX_CODE_DIFFERENCES_ARE_JETS_AT_ANY_STEP_AND_FOUNDING_OBEYS_VILLE_AT_EVERY_HORIZON_IN_LEAN.md)
(#1015). Twelve new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`, and two module headers whose open paragraphs those modules answer. Nothing here touches
the engine, a state or a run.

Refs #410, #404, #405, #393, #399, #374, #359, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Spacetime/StrengthFreeData` | A system of terms `(m_j, s_j)` leaves `z(n) = Σ_j m_j C(n + 3 + s_j, 3)` coefficients free at order `n`, a cubic with `6z = M₀n³ + 3M₁n² + (3M₂ − M₀)n + M₃ − M₁`, `M_k = Σ_j m_j (2 + s_j)ᵏ` (`freeCount_eq`); `z(n)/C(n + 3, 3) → M₀`, so no function of four variables is free exactly when the terms balance (`tendsto_free_four`); then `z(n)/C(n + 2, 2) → M₁`, the free functions of three variables (`tendsto_free_three`), and the strength `n z(n)/C(n + 3, 3) → 3M₁` (`tendsto_strength`, `strength_eq_three_mul`). The wave, Maxwell's strengths and potentials and gravitation count `(n + 1)²`, `2(n + 1)(n + 3)`, `2n(n + 2)` and `2(n − 1)(n + 3)` at every order, the record's 121, 286, 240, 234 at `n = 10` among them, with strengths 6, 12, 12, 12 (`free_functions`, `strengths`). | the Einstein record of November 11, §5.6 and §11 | `gr.strength-free-data` (now `formal-checked`) |
| `Aeon/Clock/SheetCoarsening` | A micro-state's sheet is the flux of its prefix (`sheet_eq_crossings`). Under a sub-cut `Σ′ ⊂ Σ` the epochs coarsen on every word (`crossingTicks_subset_of_subCut`, `epochs_coarsen`), the sheets do not: on two edges with `Σ` cutting both and `Σ′` the second, the word "first forward, second back" returns to fine sheet 0 while the coarse sheet reads `−1`, its epochs coarsening `0 ↦ 0, 1 ↦ 0, 2 ↦ 1` (`sheets_do_not_coarsen`); on a word that never crosses `Σ` back the sheets coarsen under every sub-cut (`sheetsCoarsen_of_forward`). | #410's box on the oriented coarsening (Rust `EpochTower`, `aeon/epoch.rs` at `d5ed4adc1`) | `aeon.oriented-coarsen-refusal` |
| `HNN/SurvivorsCycleFibre` | The traversal tree of an edge list (`treeChain`, prefix-closed); a survivor is the tree's reading, so its image does not depend on the walk that reads it (`survivor_eq_treeReading`, `survivor_path_independent`); propagation survives exactly when every fundamental cycle closes at the seed and the tree's readings are injective (`propagate_eq_some_iff`, `survives_iff_fundamental`); as loops of the Bombe, over a truth that fits every edge the survivors are the fundamental-cycle fibre cut by the tree's injectivity (`cycleLoop_closes_iff`, `holds_iff_tree_and_fundamental`, `plugboard_survives_iff`, `survivors_eq_cycle_fibre`). | #410's box "Survivors are the cycle fibre"; the record of October 5 on located keys, §8 item 1 | `hnn.propagation-edge-fibre` |
| `HNN/TurnMenuFibre` | A relation a turn fits is a partial injection whose consequences are unique, its cycles have length `ord(c)` and its paths are shorter (`partialInj_of_fits`, `consequence_unique`, `cycle_order_eq`, `path_length_lt`); a turn survives a menu given by its components exactly when every cycle has length `ord(c)`, every path fewer than `ord(c)` edges, and the pieces pack into disjoint cosets of `⟨c⟩` (`TurnMenu.survives_iff`, `TurnMenu.cycle_takes_coset`, `TurnMenu.card_le_of_survives`); on `ℤ/d`, `ord(c) = d/gcd(d, c)` with `gcd(d, c)` cosets (`addOrderOf_zmod`, `card_cosets_zmod`, `TurnMenu.zmod_survives_iff`), and the record's cycle `(0 1 2 3)` on `ℤ/60` survives exactly 15 and 45 (`ring60_survives_iff`). | #410's box on the turn menu's fibre law (#359) | `hnn.turn-menu-fibre` (now `formal-checked`) |
| `HNN/ResidentPairFace` | The resident face `W`, `R`, `L`, its populations and `S = ΣC²` as functions of the counts and the port (`faceW`, `faceR`, `faceL`, `sumSquares`); the comparison `Φ = Σ_c ⟨h_c, ν̂ Σ_ρ W_c[ρ] e_ρ⟩` moves by exactly `t` times each gradient entry when one read moves by `t` (`pairing_shiftOutput`, `pairing_shiftCurrent`, `pairing_shiftEarlier`; derivatives over ℝ, `hasDerivAt_shift*`), and the three gradients and the energy `ν̂²S` equal the sums over occupied bindings (`whole_pair_gradient`); a binding moves `W`, `R`, `L`, the populations and `S` by `a[x]b[y]`, `b[y]`, `a[x]`, 1, 1 and `2C_old + 1`, the occupied count by one exactly when `C_old = 0` (`bind_laws`), joined to `Encoding.pair_read_counts_bind` through the port's form (`pairRead_eq_face`, `pairRead_bind_face`). | #410's boxes 218 and 219 (#399); `hnn/moment/resident_pair_face.rs` at `d5ed4adc1` | `hnn.resident-pair-face` (now `formal-checked`), `hnn.resident-pair-face-gradient` (new) |
| `Landmarks/SmithCokernel` | For any Smith form of a submodule over a commutative ring, the ledger reads each coordinate modulo its invariant, its kernel is the submodule, and the cokernel is `Π_j R/(d_j)` (`ledger`, `ker_ledger`, `ledger_surjective`, `cokernelEquiv`); a vector is reached, or reached in the multiple `c`, by divisibility coordinate by coordinate (`reached_iff`, `reached_in_multiple_iff`); over ℤ the cokernel is `Π_j ZMod |d_j|` with rank `n` and `m − n` free coordinates (`int_cokernelAddEquivZMod`, `int_finrank_range`, `int_card_free`), and a face is reachable only in the multiple `c` exactly when `c ≠ 0`, every `d_j ∣ c y_j` and some `d_j ∤ y_j` (`reachableOnlyInMultiple_iff_ledger`). The `𝔽₂` ledger of `E/2E` is `IntegralCokernel`'s §5. | #410's box 103 | `linalg.smith-normal-form` (now `formal-checked`) |
| `Compression/KeyMove` | With rows `F_j` and higher terms `G`, moving `u`'s residue on ring `j` to `v` moves the encodings by `Δ = (F_j[v] − F_j[r_j(u)]) + (G(κ[j ↦ v]) − G(κ))` at `u`'s places and by zero elsewhere (`moved_sub`); the code on the segment to the moved encodings has derivative `Σ_(k : x_k = u) c_k(Δ)` at the start (`hasDerivAt_move`); with no higher term reading ring `j` that is the record's `g_j(u, v) = Σ_(k : x_k = u) ⟨γ_k, F_j[v] − F_j[r_j(u)]⟩` (`key_move_first_order`, `key_move_first_order_inner`); a term reading ring `j` with another enters (`second_order_enters`). | the symbol record of November 12, §8.3 | `code.key-move-first-order` (new), `code.symbol-word-located-rings` |
| `HNN/ReceivingPrecision` | The ledger's steps (arrive, deposit, publish, release) and its close keep the partition, inclusive deposition = deposited + published, and once a step is taken exchange + deposited + published is the change widened by the interior widths (`inv_run`, `deposition_eq_deposited_plus_published`, `partition_telescopes`; on code lengths through `FirstLaw.ledger_telescopes`, `exact_partition_telescopes`); publication moves the ledger as a deposit does with no arrival (`publish_spec`, `publish_deposition_class`, `arrivals_step`); the arrived reread keeps the sealed score and counts (`publishPrecision_seals`, `publishPrecision_reread`); the same-moment ingest and close keep the published ledger (`ingest_after_publish`, `close_after_publish`); a refused ingest or close returns the resident and a bounded crib and releases no view (`observeCellPublic_ingest_refused`, `observeCellPublic_close_refused`, `observeCellPublic_bounded`); a saved partitioned balance restores to itself (`restore_save`, `restore_partitioned`). | #410's boxes 209 to 214 (#393); the records of October 16 and 17; `aeon/first_law.rs`, `hnn/reference.rs`, `observed.rs`, `passage.rs` at `5cc91c7b` and `d5ed4adc1` | `hnn.receiving-precision-publication` (new), `hnn.boundary-first-law` |
| `HNN/SoftmaxTwoCycleSettles` | `D(s ‖ u) ≥ H²(s, u) = Σ(√s − √u)²` for laws, from `log y ≤ y − 1` (`kl_ge_hellinger`); on laws `Σ(s − u)² ≤ 4H²` (`sumSq_le_hellinger`); so along the softmax orbit the squared departure from a two-cycle is summable (`departure_summable`) and `‖x_(k+2) − x_k‖ → 0` (`tendsto_entry_two_apart`, `tendsto_norm_two_apart`). | #410's box on the synchronous two-cycle; the ring record of November 13 | `tower.field-echo` |
| `Compression/LocatedRelabelling` | The located route's survivors on `π∘x` are those on `x` relabelled by `π` (`survivors_relabel`, from `locate_relabel` and its steps); the gauge class, the located advance `A_(π∘x) = A_x∘π⁻¹` and the labels `π∘λ_x` follow (`gaugeClasses_relabel`, `locatedAdvance_relabel`, `locatedLabel_relabel`), so the advance coder is `Relabelling.Carried` (`advanceCoder_carried`) and the navigator code's length is invariant (`navigatorCodeLength_relabel`), while its bits are not (`patchIndex_moves`). Any run of prunings inside the passage keeps every orbit regenerating a passage that fits the damage, so the truth's member is kept and a class released alone is the truth's (`orbit_mem_restrict`, `truth_member_kept`, `release_sound`). | #410's boxes 228 and 229 (#374); `compression/keys/transport.rs` at `d5ed4adc1` | `compression.transport-relabelling` (now `formal-checked`), `hnn.encoded-located-relabelling`, `compression.located-transport`, `compression.transport-repair` |
| `HNN/FoundedUnitsPrice` | The sequential KT mass is `Π_c Γ(n_c + ½)/Γ(½) / (Γ(n + A/2)/Γ(A/2))` (`ktSeq_eq_gamma`), so `−log₂ W` is the box's sum in `L(k) = log₂ Γ(k/2)` with `L(k + 2) = L(k) + log₂ k − 1` (`neg_logb_orderOneMass`, `L_add_two`); the Rust's price is the complete code's change (`price_eq_change`, `merge_price_eq_change`), accepted exactly when `2A²·W < W′` (`price_neg_iff_ratio`, through `Merge.merge_cost_mass_iff`); the parse decodes (`founded_decode_parse`), and the lattice's code is at most the parse's, equal exactly when no other segmentation carries mass (`lattice_code_le_parse`, `lattice_code_eq_iff`). | #410's boxes 256 and 257 (#405); the record of October 23 on founded units; `crates/engine/src/units.rs` | `hnn.founded-units` (now `formal-checked`), `receiver.merge-segmentation-mass` |

The boxes these answer, by their opening words: "The refusal of an oriented (sheet) coarsening"; "The integral cokernel
ledger over ℤ"; "The first-order identity of a key's move"; "Survivors are the cycle fibre" (as reworded, §2 item 3);
"The synchronous two-cycle of a place hearing its own release" (its last owed part); "The count of free data `z(n)`";
the six boxes of receiving precision (#393); the two of the resident pair face (#399); "The located route's survivors
carried under relabelling"; "The release over a union of fibre members is sound"; "The turn menu's fibre law"; "The
founded units' price"; "The units' lattice read". Eighteen boxes in all.

## 2. What the pass corrected

1. **The strength, not the count, does not depend on the chart.** The Einstein record's §11 says the count is
   chart-independent, reading Maxwell both ways; the counts differ at every order, `2(n + 1)(n + 3)` against
   `2n(n + 2)`, and both strengths are 12. The row's scope now says so.
2. **The sheets' refusal needs only one crossing back.** `aeon.oriented-coarsen-refusal` named the cause as a
   backward crossing of `Σ′` falling between forward ones; the counterexample has one forward crossing of `Σ` and then
   one backward crossing of `Σ′`. The epochs coarsen along every sub-section, and the sheets on every word that never
   crosses the fine section back. The row's expression, meaning and scope are rewritten; its grade stays
   `counterexample`.
3. **The survivors are the cycle fibre cut by the tree's injectivity.** The box said the survivors equal the
   fundamental-cycle fibre. The cycles do not see the diagonal board's injectivity, which is a condition of its own:
   over a truth that fits every edge the survivors are the fibre meeting the tree-injective candidates. The box is
   reworded, and `HNN/Keys`' open paragraph, which the module answers, now points to it.
4. **The turn menu's record instance names the elements of order four.** The row's "order-2" names the record's
   passage; the turns 15 and 45 that the cycle `(0 1 2 3)` admits on `ℤ/60` are the elements of order four, the cycle's
   length.
5. **The resident pair face had no Lean owner for the face.** Its one `L:` owner was the count read. The Rust's `bind`
   trusts the old count it is passed, and its `S` and occupied laws hold because `bind_pair_count` reads the count
   before it adds; the Lean states the law with the old count read from the table. The skip of empty phases in the
   gradient is sound because counts are never negative.
6. **The Smith row's divisibility chain is not stated.** Mathlib's `Basis.SmithNormalForm` carries no chain
   `d₁ ∣ d₂ ∣ ⋯` and no uniqueness up to units, so the invariants are those of the chosen form; every reachability read
   stands without the chain.
7. **The record's sum is the derivative only where no higher term reads the moved ring,** and it is the derivative
   along the segment to the moved encodings, not the code's change at the moved key. "With the rows held" names every
   row of every order; a term reading the moved ring with another enters the step (`second_order_enters`).
8. **The passage reader checks the partition and not the telescoping.** Version 4's `read_balance` restores a balance
   with no step and a nonzero exchange (`restore_accepts_untelescoped`), so the box on a close and a cold restore holds
   for balances the resident saved, not for every file the reader accepts. The box on the same-moment ingest holds
   because the ingest writes neither the ledger nor the arrived operand; no commutation of the two is claimed, since the
   moment's fields change. The box's "sample count" is read as the ledger's cell and arrival counts. One refusal branch
   of `publish_receiving_precision` after the occurrence check cannot be reached.
9. **The located route carries its code's length, not its bits.** The survivors are equal as lists before the Rust's
   sort, which leaves them a permutation of each other; a patch's class index moves under a relabelling. The release's
   "whenever the truth's member is kept" holds without condition, since the truth's member is never refused, and the
   soundness needs no certificate; a kept member that is not the truth's can release a class the truth lacks.
   `Compression/Relabelling`'s owed paragraph now points to the discharge of its hypothesis.
10. **The founded units had no Lean owner.** `hnn.founded-units` was graded `definition` while its scope claimed the
    price is the code's change exactly. The Lean reads the after-merge counts as the merged word's own; the Rust's
    incremental changes agreeing with them is its test on one passage. Neither the Rust nor the Lean counts the founding
    list's stop bit, and `units.rs`'s header names only `Merge` as its Lean.

## 3. What each statement stands on

- **The strength** is a count; the shift each term carries is the ruler's convention and is not derived, and
  Einstein's own table is not quoted.
- **The sheets** read words of steps by cut cochains (`Aeon/Clock/Epoch`); the arrival form of a non-coarsening, a
  section the motion lingers on, is a different cause and stands apart.
- **The survivors** stand on `Compression/Core/Keys`' loops and `HNN/Keys`' propagation; the turn menu takes a
  relation's cycles and paths as data, and deciding the packing is a search the law states and does not run.
- **The resident pair face** is held at unit modulus over any commutative ring; the integer charts, the leaky path and
  the founded Own ring are not modelled.
- **The Smith ledger** takes a form as given; computing one for a matrix is Mathlib's existence over a principal ideal
  domain, and the worked instance is built by hand.
- **A key's move** holds for any code differentiable at the passage's encodings; the key's discrete carry at a declared
  grain is the record's design and not a theorem.
- **Receiving precision** abstracts the event's selection, its tolerance and the rebase's lattice; the card's
  publication and the collapse at close are not modelled.
- **The softmax orbit** draws together two passes apart; the orbit's own convergence needs Łojasiewicz's inequality or
  isolated critical points and is not claimed.
- **The located route** takes the cell reflection and the key order as data; the chart's equality with the founded
  encoding and the fixed point's equality with the projection stay where they were.
- **The founded units' price** is stated with the true `L`, not the `2^(−32)` table and its enclosure.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the twelve modules, `Compression/Relabelling`, `Holonics.HNN.Keys` and
`Holonics.HNN`: `Build completed successfully (8985 jobs)`, exit 0, 141 s, no declaration elaborated with `sorry`;
projected under 10 minutes, deadline 30 minutes, peak resident set not read. Single-file checks of each module at the
package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision on a cloud host, read by exit status (each
`EXIT 0` with no output), for the reason the first pass's record gives (`agent-inferred`). The research library's
aggregator imports the twelve modules, and `tools/lean_census.py` reads `unbuilt=0 unrooted=0`.

Six workers on disjoint owner paths, at most three at once, wrote eight of the modules; the lead wrote
`Physics/Spacetime/StrengthFreeData`, `Aeon/Clock/SheetCoarsening`, `Compression/KeyMove` and
`HNN/SoftmaxTwoCycleSettles`, re-checked each file from the tree, and read every `L:` owner added to the atlas against
its module's declarations by `tools/link_check.py atlas` (`broken=0`).
