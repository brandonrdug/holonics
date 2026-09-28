//! **The receiving tree: the shift navigator's landmarks, executed on a declared dyadic lattice,
//! addressed by typed bundles, weighing every face locally, stored at the faces where paths part**
//! (Lean `Compression/Landmark/Context`; campaign 1's repair; campaign 2's receiving letters; #73).
//! The HNN reads it as the receiving parametron's storage (`hnn::receiving`).
//!
//! [definition; agent-inferred, the unity audit of September 27, §2] **The receiving tree is the
//! shift navigator's landmarks.** A source read cell by cell is a passage of the shift navigator:
//! each tick pushes its letter onto the address. A node is a context, the face where every path
//! ending in that context converges, which is the elementary objects' definition of a landmark and
//! the same object this module's siblings locate for other navigators (site kinds, fixed points,
//! identities, constraint identities, primitive cycles). Its joins to the framework:
//! - [proved-derived; formal-checked] **Each pruned tree is a candidate standing, and the tree is
//!   their mixture** (Lean `Compression/Landmark/Context/Standing`). For a tree source over a pruned
//!   tree `S`, whose next-symbol face reads only the leaf context `S` reaches, the address at the
//!   declared depth is a `Foundation/Standing.StandingLaw` on the shift navigator's words
//!   (`address_standing`, through `standingLaw_exists_iff_future_factors`), and so is the
//!   leaf-context map itself when `S`'s leaves are closed under the shift (`leaf_standing`). The
//!   tree's weight is the stop prior's weighted sum over `S` of the tree sources' likelihoods
//!   (`mixture_over_leaf_standings`, `Tree.own_mixture_over_trees` read through
//!   `tree_source_likelihood`), and its dominance bound (`Tree.own_kraft_and_dominance`) is the code
//!   cost of choosing among the candidate standings.
//! - [counterexample; formal-checked] A leaf map that is not closed under the shift is not a
//!   standing (`unclosed_leaf_is_not_a_standing`): the address at the declared depth is then the
//!   standing, and the leaf map only its present face.
//! - [proved-derived; formal-checked] **A node's arrivals are the epochs of its section** (Lean
//!   `Compression/Landmark/Context/Epoch`): the node's ticks form a certified section of the
//!   passage's aeon, its arrival count after `k` cells is `Aeon/Clock/Epoch.epochOf` of those ticks
//!   at micro-state `k` (`arrivals_are_epochs`), and its register ([`Capacity`]'s carry included)
//!   is the node law's run of its epoch history, whose total never passes the epoch index
//!   (`node_register_on_epochs`, `capped_register_on_epochs`).
//!
//! [definition; agent-inferred] **The tree depends on library owners only.** Its refusals are its
//! own ([`ContextError`]); its enclosures and their grid are `ratio::algebraic`'s
//! ([`LOG_OCTAVES`], `interval_sum`); a face's grain exponent is the receiver's face read at the
//! grain (`receiver::face::grain_exponent`); its letters are addresses over a declared family of
//! slot alphabets ([`LetterFamily`]), whose readers are the HNN's (`hnn::receiving::Feature`: a
//! ring's phase class, a contact's reading); its online baselines are codes of fixed context order
//! ([`baseline`]). The HNN reads the tree: it builds the addresses it passes in, runs a window's
//! phases together on its cores (`hnn::receiving::window_faces`), and measures the tree
//! prequentially on the exposure's cut (`hnn::reference::prequential`).
//!
//! [definition; Brandon, September 25; the tree's form agent-inferred] **The receiving face
//! compresses landmarks.** Brandon: the compression "is of landmarks connecting generators … when
//! relevant they expand and are open for a time"; a cache is "more like a cocycle in a natural
//! autogradient"; tokenizers and BPE are "partials without complete mathematics". The law, derived
//! with Sol (`research/records/2026-09-25_THE_COMPRESSION_IS_OF_LANDMARKS_A_TREE_COCYCLE_AND_MERGES_PRICED_BY_THEIR_CODE_LENGTH_PAIR.md`):
//! landmarks are nodes of the tree of typed address words, founded at first arrival; each holds KT
//! masses, and the face is the tree's weighting along the one path the current address opens
//! (Willems–Shtarkov–Tjalkens), exact in ℚ and read at the grain; the path's edge log ratios are an
//! additive cochain, a deposit is local to the path, and its covector is the log-derivative of the
//! edge ratios, with no pullback through a network; release is the retention law's future
//! quotient, never a budget alone; and the wave earns its computation by supplying address letters
//! the tree weights in, any wave correction measured against the count-only face. The tree's form
//! (context-tree weighting) and the build order are agent-inferred; merges (tokenizers) belong to
//! campaign 5. The measurements are in the dated records of September 26 and 27
//! (`2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md`,
//! `2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md`,
//! `2026-09-27_A_LANDMARKS_STORAGE_HAS_A_CAPACITY_AT_ITS_CEILING_IT_CARRIES.md`).
//!
//! [definition] The computational object is the helical pair interaction; this owner is the
//! receiving parametron's storage, read as a tree of landmarks. Of the winding guide's six general
//! objects it touches four: **faces and placement** (the receiving face, read at the receiver's
//! grain), the **tower thread** (the bundle restriction: an address restricts by dropping its oldest
//! whole bundle, and a cell's odometer digits descend its dyadic cell), the **pair** (each edge of an
//! opened path compares a node's face with its child's, `R_(d→d+1) = q_(d+1)/q_d`) and the
//! **helix** (a ring's phase class is the phase of a circle-plus-carry read at its grain; the β
//! chart's exponent is a carry and its mantissa the phase within the octave). A tree has no
//! two-cells, so no **cell holonomy** is claimed, and the **tube** is the passage itself, one cell
//! per tick.
//!
//! ```text
//! bundle     b_i = (x_i, f_i)   the tick of cell i: its cell and its declared features' letters, read
//!                              from the retained state after the tick (Lean Compression/Landmark/Context/Address)
//! address    a_j = [b_(j−1), …, b_(j−D)]  newest bundle first,  b_i = Boundary for i < 0      per cell
//! branches   cells:   [x_(j−1), …, x_(j−D)]                                     D letters
//!            bundles: [x_(j−1), f¹_(j−1), …, f^r_(j−1), x_(j−2), …]               D(1 + r) letters
//! digits     a cell c emits its B = ⌈log₂|A|⌉ odometer digits; digit i is read in the trees of its
//!            dyadic cell h (its digit prefix), a forced digit (empty upper half) opens nothing
//! KT         k_s(b) = (2n_s(b) + 1)/(2n_s + 2) in half-units, b ∈ {0, 1}
//! lattice    q̂_D = ⟦k_D(0)⟧ ;  q̂_d = ⟦λ̂_d k_d(0) + (1 − λ̂_d) q̂_(d+1)⟧ ;  λ̂_d = ⟦β_d/(1 + β_d)⟧₀¹
//!            ⟦x⟧ = nearest multiple of 2^(−M_p) (ties up) inside [2^(−M_p), 1 − 2^(−M_p)]
//! join       q̂_h = ⟦λ̂_h q̂_cells + (1 − λ̂_h) q̂_bundles⟧ ,  λ̂_h = ⟦β_h/(1 + β_h)⟧,  β_h = W_cells/W_bundles
//! split      (q̂, 1 − q̂) at each opened digit;  cell face = ∏ of its digits' splits
//! deposit    β'_d = β_d k_d(b)/q̂_(d+1)(b) bottom-up on each branch, β'_h = β_h q̂_cells(b)/q̂_bundles(b),
//!            then n_d(b) += 1, and at the ceiling (n_d(0) + n_d(1) = 2^c) n_d(·) ← ⌈n_d(·)/2⌉
//! ```
//!
//! [definition] **Typed address letters** ([`Letter`]): `Boundary` (before the cut's first cell),
//! `Cell(code)` (a tick of the cell-only family) and `Bundle` (a tick's cell with its declared
//! features' letters, [`Bundle`]). The address of cell `j` is its preceding `D` bundles, newest
//! first, read per cell: causal, with no window pooling ([`address`], [`letter_address`]). A
//! bundle's code is `0` for the boundary and `1 + x + |A| · f` for a cell `x` with the features'
//! mixed-radix code `f` ([`LetterFamily::bundle_code`], injective: Lean
//! `Compression/Landmark/Context/Address.bundle_code_injective`); in a tree each typed letter is a child's key under
//! its parent, `0` for the boundary and `1 + value` otherwise.
//!
//! [definition; agent-inferred] **A section's slots, read once** ([`sections`]): on a curated
//! stream whose section letters open its parts (`B + C·k + c`), a tick's bundle carries the slots of
//! the part it lies in, the channel (and optionally the kind), read at the part's letter and carried
//! by every bundle of the part ([`Sections`]); the curated source's typed address.
//!
//! [definition; agent-inferred] **A span located from a reading part** ([`spans`]): the joint
//! address across two ports, the longest suffix of a part (a response) that recurs in a closed span
//! on another port (its request) and the span's cell after it ([`SpanReading`], [`Located`]); the
//! admitted receivers read it (`receiver::population::admitted`).
//!
//! [definition; agent-inferred] **The declared family and its finite partitions** ([`LetterFamily`],
//! the slots' alphabets; the HNN's readers of them, `hnn::receiving::{Feature, FeatureFamily}`),
//! each derived from a declaration, never a literal:
//! - a ring's **phase class** `⌊g·phase⌋ mod g` at the ring's declared grain `g` (its period `d_g`,
//!   the ring's own port chart, where the fibre is empty; or `g = 2`, the half of the rotor's cycle
//!   its clock phase `λ_g/d_g` is in), `g ≥ 2` letters (Lean `phase_partition_finite`). The grain-2
//!   letter reads the rotor's clock, not the parametron's half-turn sheets (`hnn::ring::sheets`,
//!   the sides of its mode amplitude against the pump's axis), which the letters do not read;
//! - a contact's **reading** (its owner's, `hnn::contact::ContactReading`, read by
//!   `hnn::receiving::LetterReader` from the retained clock and constitution): its **lock address**,
//!   `Unlocked` at the declared tolerance or a reduced `(p, q)`, `1 ≤ p ≤ P`, `1 ≤ q ≤ Q`, with `Q`
//!   the greatest denominator whose first return (`q` turns of the contact's second ring, Lean
//!   `Aeon/Clock/Lock.cycle_iff_period_dvd`) is observable within the aeon and `P` the first ring's
//!   bound alike (`hnn::contact::LockDeclaration::derived`; Lean `lock_partition_finite`), times
//!   its **site kind** over the proved `SiteKind` cases (`navigator::trace::SiteKind`, five). The
//!   slot's letter is the contact owner's (`ContactReading::letter`), so the partition and its rank
//!   have one owner. A boost needs a declared signature (`ConstitutionRead::
//!   contact_stiffness_signature`): a stiffness `K = b bᵀ ⪰ 0` reads rotations and null shears only,
//!   whatever the data deposit.
//!
//! [definition; agent-inferred] **A slot carries at least two letters** ([`LetterFamily::new`]): a
//! slot of one letter carries nothing, so no family declares one and none is charged for one. The
//! development harness's constant-slot control (`r` slots of one letter each, the enlarged tree's
//! own reweighting) is [`LetterFamily::constant_control`], a control and never a declared family.
//!
//! [definition; agent-inferred, Sol's review §2] **The enlarged tree keeps the cell-only branch.**
//! With no features declared the tree is campaign 1's cell tree, unchanged. With `r ≥ 1` features
//! each dyadic cell `h` carries two branches, the cell tree over `[x_(j−1), …]` and the bundle tree
//! over the flattened bundle word, joined at `h` by a two-face mixture weighed by its own
//! likelihood ratio (Lean `Compression/Landmark/Context/Tree.sequential_mixture`): the join's weight is
//! `½ W_cells + ½ W_bundles`, so the enlarged code length is at most the cell tree's plus one bit a
//! dyadic cell, and for every cell-only pruned tree `S` at most `Γ(S) + 1` plus its leaves' code
//! (Lean `Compression/Landmark/Context/Address.cell_only_dominance_with_feature_charge`), before the features'
//! description and the certified drift. The bundle tree restricts by whole bundles
//! (`bundle_restrict`): its node at `d(1 + r)` letters is the address restricted to `d` bundles.
//!
//! [definition] **The emission is the cell's odometer digits.** Digit `i` of class `c` is read at
//! its joint address: its digit prefix (the dyadic cell it descends) as a forced split, then the
//! context letters mixed by the trees of that dyadic cell, each node holding binary KT masses in
//! half-units. A dyadic cell whose upper half holds no class of the chart forces its digit with
//! face 1 and stores nothing, so every `|A| ≥ 2` is normalized. The whole-cell emission
//! (`|A|`-ary masses at each node) is retired: on the standing cut it never earned a split (the
//! record of September 26). Its depth-one forced case is the region table (order-1's
//! `|A|`-ary KT face), whose law is kept in Lean only (`Compression/Landmark/Context/Tree.depth_one_is_the_whole_cell_table`).
//!
//! [definition; agent-inferred, the primary's law] **Every quantity on the hot path is a
//! fixed-width integer on a declared dyadic lattice, with certified residuals, and the executed
//! face stays exactly normalized.** Each path face is a numerator of `2^(−M_p)` (`u64`), each stop
//! weight `λ̂` likewise, each count a half-unit integer (`u32`), each `β` an odd/odd ratio of `W`
//! bits with a binary exponent, and every product and quotient is formed in `u128`. The face is
//! positive and normalized for any `λ̂ ∈ [0, 1]` (`path_face_normalized`, `lattice_path_laws`): the
//! digit's executed split is `(q̂, 1 − q̂)`, and a cell's face is the width of its descended interval
//! (`cell_faces_partition`), a dyadic of at most `B · M_p` bits.
//!
//! [proved-derived; agent-inferred] **The widths**, derived from the passage `n*`, the grain `L_R`,
//! the digits `B` and the path depth `P` (no literal is tuned): `P = D` for the cell tree, and
//! `P = D + D(1 + r) + 2` for the enlarged tree, whose join adds both branches' residuals (the
//! drift terms `D² + (D(1 + r))² + 2(D + D(1 + r)) + 2 ≤ P²` and the rounding terms
//! `2D + 1 + 2D(1 + r) + 1 + 2 ≤ 2P + 1`). Write `K = 2n* + 2` (a binary KT face is at least
//! `1/K`, `digit_face_ge`), `ε = 2^(−M_p−1)` and `μ̂ = ⌊2^(M_p)/K⌋/2^(M_p)` (every lattice face is at
//! least `μ̂`, `lattice_path_floor`). Let `ρ_d` be `|ln q̂_d − ln q_d|` for the ideal tree
//! weighting `q`, `Δ_d = |ln β̂_d − ln β_d|` the chart's drift at the node, and `θ_d` a level's
//! rounding in `ln` (the stop weight's and the face's, at most `2^(−M_p)/min(q̂_d, k_d, q̂_(d+1))`,
//! the leaf's `ε/min(q̂_D, k_D)`, the join's `2^(−M_p)/min(q̂_h, q̂_cells, q̂_bundles)`).
//! - **Down the path**, `ρ_d ≤ Δ_d + ρ_(d+1) + θ_d` (`mix_ratio_bound`), so
//!   `ρ_0 ≤ Σ_(d<P) Δ_d + (2P + 1) ε/μ̂`; in absolute terms `|q̂_0 − q_0| ≤ (P + 1)ε + Σ|λ̂ − λ|`
//!   (`lattice_path_deviation`).
//! - **Over the passage**, `β̂ = E/P̂` with `P̂` the executed child's sequential probability, so the
//!   node's step telescopes (`lattice_step_telescope`) and its weight is 1-Lipschitz in `ln P̂`
//!   (`weight_log_lipschitz`): the drift is bounded by the rounding and rebases **summed over the
//!   subtree**, never compounded, `Δ_d ≤ n_s (2(P − d) − 1)(ε/μ̂ + 2^(1−W) + ρ_c)` with `n_s ≤ n*`
//!   the node's arrivals, `2^(1−W)` a mantissa rebase's `|ln(1 − r)|` (`rebase_log_residual`) and
//!   `ρ_c` a carrier rebase's (below).
//! - **A cell** has at most `B` opened digits and `Σ_(d<P) (2(P − d) − 1) = P²`, and each split of
//!   a stored chain (stored where paths part, below) rounds once more at `W` bits: an arrival splits at most one
//!   chain in each digit tree it opens and a lineage at most `D ≤ P` times, so the mantissa units
//!   number at most `(2n* + 1) P²` a digit, and
//!   `|log₂ q̂ − log₂ q| ≤ (3/2) B [(n* P² + 2P + 1) ε/μ̂ + (2n* + 1) P² 2^(1−W) + n* P² ρ_c]`
//!   (`log₂ e < 3/2`). Each source is held within a quarter grain:
//!   - `M_p` is the least `M` with `2^M ≥ 3 B L_R K (n* P² + 2P + 1)` ([`face_bits`]);
//!   - `W` is the least width with `2^W ≥ 12 B L_R (2n* + 1) P²` ([`carrier_width`]);
//!   - the carrier rebase keeps a denominator of `R = 126 − W ≥ W` bits, so `ρ_c < 2^(1−R)` and its
//!     share is below a quarter grain too (the rebase is taken only when its product can overflow;
//!     otherwise `ρ_c = 0` and the rule is campaign 1's);
//!   - the certificates are summed on the grid `2^(−C)`, `C = M_p + W`: every rounding term is at
//!     least `2^(−M_p)` and every rebase term at least `2^(−W)`, so rounding each up on the grid
//!     inflates it by at most `1 + 2^(−min(M_p, W))`.
//!
//!   So the rule ([`Landmarks::face_rule`]) is at most `(1 + 2^(−min(M_p, W))) · 3/4` of a grain,
//!   and `(1 + 2^(−min(M_p, W))) · 1/2` without the carrier's rebase. [established-bounded;
//!   checked] It lies below half a grain, exactly, with or without the carrier's rebase, at
//!   `n* ∈ {64, 6148, 2^14, 2^17, 2^20}`, `L_R = 16`, `B = 8` and `P ∈ {1, …, 6, 8, 12, 24, 48, 73}`
//!   (the test `landmark_rule_lies_below_half_a_grain`). [historical] Before the splits were
//!   counted in `W` (`2^W ≥ 12 B L_R n* P²`, at commit `89460425`), the rule passed half a grain,
//!   first at `n* = 6148`, `D = 5` (`M_p = 40`, `W = 28`).
//!
//!   At the standing cut (`n* = 6,148 = 2²·29·53`, `L_R = 16`, `B = 8`, `D = 4`, cells only):
//!   `M_p = 39`, `W = 29`, `C = 68`.
//!
//! [definition; agent-inferred, Sol's review §4] **The carrier rebases past `u128`.** The β step's
//! carrier `(N, D) = (β_n k_n, β_d k_d x)` (odd parts of `β`, the KT face `k = k_n/k_d` in half-units,
//! the child's lattice numerator `x`) is carried exactly while its mantissa's division fits `u128`.
//! Before it can overflow (`2W + κ + M_p + 1 > 128`, `κ` the bits of `K`), the carrier rebases by a
//! common power of two, `N 2^s = 2^e N̂` exactly and `D = 2^e D̂ + r_D` with `D̂` of `R` bits, and the
//! remainder `r_D` is released: the ratio lies in `(N̂/(D̂ + 1), N̂/D̂]`, whose logarithmic width is
//! below `1/D̂` (Lean `Compression/Landmark/Context/Carrier.{rebase_decode, rebase_ratio_enclosed}`). That width is
//! added to the node's drift and excess certificates, the same terms that carry a mantissa rebase
//! through every later KT, path and mixture step (`rebase_step_enclosed`, `rebase_log_residual_sum`,
//! `width_or_rebase_total`). The widths are never reduced to fit the carrier: `M_p` and `W` stay the
//! rule's. The declaration is refused only when a lattice product itself passes `u128`
//! (`max(2M_p + 2, M_p + κ + 3)`, `M_p + W + 3` or `W + κ + M_p` above 128 bits, `M_p > 62`, or
//! `R < W`). Campaign 1's `|A| = 256`, `D = 4` tree was refused from 87,382 cells, then from
//! 605,395 cells (`2^19` admitted), and now declares to 19,372,659 cells (`2^24`).
//!
//! [definition; agent-inferred] **The lattice mixture and the stop weight read split operands**
//! (the wide cut: at the wide cut's `2^20` cells the single division's `2M_p + κ + 3` reached 133
//! bits). A mixing node's face `⟦λ̂ u/v + (1 − λ̂) x⟧` has the lattice numerator
//! `λ̂u/v + (2^M − λ̂)x/2^M`; each part is divided with its remainder, `λ̂u = q_a v + r_a` and
//! `(2^M − λ̂)x = q_b 2^M + r_b`, and the rounding reads
//! `q_a + q_b + ⌊(2r_a 2^M + 2r_b v + v 2^M)/(2v 2^M)⌋`, the same integer as the single division of
//! the sum (`⌊N/D + ½⌋` with its integer part taken out), in `max(2M_p, M_p + κ + 3)` bits. The stop
//! weight `⟦β/(1 + β)⟧` is decided before its division whenever one side of `1 + β` passes the other
//! by `2^(M+1)` (the other side's share is then below half a lattice step), which bounds its operands
//! by `M_p + W + 3` bits. Both return exactly the integers the single divisions return (the test
//! `landmark_split_operands_are_the_single_division`).
//!
//! [definition] **The certificate is carried, not recomputed** (the per-cell residual without the
//! ideal). Each node and each join carries two bounds on the grid `2^(−C)`: `drift` ≥ `Δ` and
//! `excess` ≥ `|L̂ − L|`, its routed subsequence's executed code length against the ideal in `ln`. A
//! deposit adds, bottom-up along each opened path, the read's `θ_d` plus twice the rebases' units
//! to the node's excess and the child's excess increment plus the rebases' units to its drift
//! (`|ln(1 − r)| ≤ r/(1 − r) < 1/m'` for the kept mantissa `m' ∈ [2^(W−1), 2^W)`, and `1/D̂` for a
//! carrier release); a join adds both branch roots' increments. A read's residual is
//! `ρ ≤ Σ drift + Σ θ` per opened digit over both branches and the join, and a cell's
//! ([`CellReading::residual`]) is the digits' sum in `log₂` (times `3/2`), never above the rule.
//!
//! [definition; agent-inferred] **Stored at the faces where paths part** (Lean
//! `Compression/Landmark/Context/Compaction`; the one storage). Every address runs to the declared
//! depth (padded with `Boundary`), so a chain of nodes each with one reached child routes the same
//! arrivals and holds the same counts: with `ρ = P_w/P_e`, `1 − ρ_j = (1 − w_j)(1 − ρ_(j+1))`, and on
//! the dyadic rungs `1 − ρ_top = 2^(−S)(1 − ρ_bottom)`, `S = Σ j_i` (`chain_ratio`,
//! `chain_ratio_dyadic`). So a chain with the node below it is one KT node at the summed
//! rung, `P_w(top) = W E + (1 − W) X`, `1 − W = 2^(−S)`, founded at `β₀ = 2^S − 1` and stepped by the
//! unchanged law (`compacted_is_the_full_tree`); a chain ending at `D` is one KT node
//! (`leaf_chain_is_one_node`); a forced depth has rung `0`. A stored node is a chain: its bottom
//! depth, its counts, its chart at the chain's summed rung (read from
//! the branch's summed rungs, never stored), and its **label**, the letters from its parent's face to
//! its bottom (a leaf's to `D`). A read walks each label letter by letter (exact comparison, no
//! hash); where the address parts from a label at depth `k` the chain splits (`chain_split`,
//! `Law::part`): above a leaf the upper part reads `β_u = 2^(S_up) − 1`, above an internal bottom
//! `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)` and `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low) − 1) + 2^S − 1)`,
//! and the path stops at the prior below `k`. The deposit founds the upper part with the chain's
//! counts and its stepped chart, keeps the lower part's counts at `β_ℓ`, relinks the parent, and
//! founds the arrival's leaf. [proved-derived; agent-inferred] **The split's rounding**: each
//! ratio is formed exactly (`BigUint`, [`Beta::split`]) and carried once at `W` bits, one mantissa
//! rebase at most,
//! the ratio's carry `m' ∈ [2^(W−1), 2^W)` below the exact one by a relative `[0, 1/m')`; the map
//! `β ↦ β_u` is 1-Lipschitz in `ln β` and `β ↦ β_ℓ` an exact shift, so
//! `|ln β̂_u − ln β_u|, |ln β̂_ℓ − ln β_ℓ| ≤ Δ + 1/m' < Δ + 2^(1−W)` with `Δ` the chain's drift: each part
//! carries its unit `⌈2^C/m'⌉` in its drift, and the split's two units enter the deposit's increment
//! once, by the rule the rebases use; a founding ratio `2^S − 1` past `W` bits is carried as
//! `(2^W − 1) 2^(S − W)` with its unit alike. An arrival splits at most one chain in each digit tree
//! it opens, and a lineage at most `D ≤ P` times, so the rule's rebase term reads
//! `(2n* + 1) P² 2^(1−W)` ([`Landmarks::face_rule`]), which the derived `W` holds within a quarter
//! grain ([`carrier_width`]). **The labels are the tree's own paths**: a cell that founds leaves
//! holds, in each branch, one run of its address's letters below the shallowest leaf it founds (the
//! label pool, `u32` letters), and each of its leaves ends in that run; every letter of a run lies
//! on a stored node's edge, interned per founding cell, never a record of arrivals or a pointer into
//! the source. The pool holds the tree's labels and, after each split, one letter more: the letter
//! at the parting depth `k + 1` becomes the lower part's child letter in the table and stays in the
//! pool where the chain held it (still on a stored edge; [`Landmarks::bits`] counts it twice). The
//! root folds into its chain: a tree nothing has reached stores nothing and reads the prior, and
//! its first arrival stores one leaf chain from the root to `D`. [proved-derived] A tree of `ℓ`
//! leaves stores at most `2ℓ − 1` chains, so a tree
//! reached by `n` arrivals stores at most `2n − 1` nodes at every depth (`compacted_node_bound`),
//! and a passage of `n` cells at most `2 n B` nodes and `n D` label letters a branch.
//!
//! [definition; agent-inferred] **A landmark's storage has a capacity** (Lean
//! `Compression/Landmark/Context/Capacity`; [`Capacity`], declared in [`LandmarkDeclaration::capacity`]). A node's
//! counts are a register on the node's own clock, its arrivals: the deposit counts the digit, and
//! when that brings `n_0 + n_1` to the ceiling `L = 2^c` both counts carry, `n_b ← ⌈n_b/2⌉`, so the
//! face read before the next arrival is KT's on the carried counts. The register is then a function
//! of the sequence of digits that reached the node, never of the counts alone (it is not
//! exchangeable), and its face is positive and normalized (Lean `cap_face_pos`, `cap_face_sum`).
//! The tree weighting, its Kraft form and dominance, the step `β' = β k/q̂'` and the compaction hold
//! for any node law whose state is a function of what reached the node (Lean
//! `Context/Tree.{NodeLaw, own_mixture_over_trees, own_kraft_and_dominance, own_weight_step₀,
//! law_standing_is_routed}`, `Context/Compaction.compacted_node_law`): a chain's nodes route the
//! same arrivals, so a stored
//! chain is one register, and a split's upper part takes the chain's register (`Law::part`
//! unchanged). `Unbounded` (`c = ∞`) is the KT node, as is every ceiling no node reaches
//! (`cap_below_ceiling_is_kt`). The carry only lowers counts, so every node's total stays at most
//! its arrivals: KT's floor `1/(2n* + 2)`, the widths, the certificates and the rule are
//! unchanged. The card's mirror (`holonics-cuda`, `kernels/tree.cu`) carries the same register at
//! the same ceiling in its deposit ([`Capacity::ceiling_halves`] uploaded with the law).
//!
//! [historical; measured] **The full arena of one node a depth is retired** (its realization,
//! `Storage::Full`, is at commit `89460425`): it declared the same prior and read the same face in
//! ℚ at every arrival, and on the wide cut's development cells at `D = 6` the two codes were equal
//! within their certificates while the full arena held 4,620,707 nodes against 2,784,875 (commit
//! `2fb0c1c0`). The tests keep an ideal full tree in ℚ as the independent reference
//! (`compression/landmark/context/tests/full.rs`).
//!
//! [historical; measured] **Founding where paths converge (second-arrival founding) is measured and retired**
//! (commit `d137e8a6`; Lean `Compression/Landmark/Context/ConvergenceFounding` stays as the law of absent children and
//! stopping rules). A node founded at its second arrival, its first arrival held as a pending record
//! in the child table, declared a different prior; on the wide cut's development cells it coded
//! above the first-arrival tree at `D = 6` (`1827190 + 13/16 + ε` bits at its chosen
//! `D = 19`, charged 6, against `1822006 + 1/16 + ε`, charged 4), so the development cells kept the
//! first arrival (held out, disclosed and choosing nothing, it read `−490 + 11/16 + ε` below: its
//! paths grew one depth a recurrence, so its early cells read shallow and its late cells deep); its
//! memory saving is had without changing the prior by the storage where paths part.
//!
//! [definition; agent-inferred] **The arena** (the layout the card ports, [`ArenaView`]). Nodes are
//! numbered in founding order, `u32`; every per-node value is a flat vector indexed by the node:
//! its depth word (its bottom depth, with its branch in the top bit), its two half-unit masses
//! `2C_0, 2C_1` (their sum is the total; the arena the oracle shares), its label end (one past its
//! bottom's letter in the label pool, `u32` letters), and its chart: `β`, the cached stop weight
//! `λ̂`, its rebases and its two certificates. `roots[t]` is the root of tree `t = branch · 2^B + h`
//! (the heap index `h = 2^i + prefix` of the dyadic cell), `children` a hash table from
//! `(parent << 32) | letter` to the child, and `joins[h]` each dyadic cell's join chart (enlarged
//! trees only). A read past the stored nodes reads the prior: a path read stops where the address
//! leaves the stored labels, whose face is exactly `1/2`. `Clone` copies the arena, linear in the
//! stored nodes: 96 bytes a node in the flat vectors on x86-64 (the chart 80, the masses 8, the depth
//! word 4, the label end 4), a 16-byte table entry with its control byte, and 4 bytes a label
//! letter; `PartialEq` compares the table as a map (std's `HashMap`). The reads and the deposit are
//! one law (`Law`) acting on any standing (`Standing`): the tree's own, or a window's working
//! overlay (below). The card (`holonics-cuda`, `hnn::tree`) mirrors the same arena without the
//! certificates: 48 bytes a node (the depth word, the label end, the masses and the chart's `β` and
//! `λ̂`), a 12-byte table slot at twice the nodes, and 4 bytes a label letter.
//!
//! [definition; agent-inferred] **A window in cell order** ([`Landmarks::window`], [`Window`],
//! prequential scoring within a window; run on the host's cores by `hnn::receiving::window_faces`
//! and consumed by `hnn::receiving::ReceivingPhases::tree_faces`). A receiving window
//! compares `A` cells at once, and phase `j` reads the tree at the standing after the window's
//! earlier phases' deposits: their targets are known at compare, so those deposits are applied, in
//! cell order, to a working overlay (`Working`). The nodes and joins a deposit writes are copied
//! from the tree at their first write, the nodes it founds are numbered after the tree's, the links
//! a compacted split changes and the label runs it holds are the overlay's own, and every other
//! node reads through to the tree, which is never written. The deposit then applies the same
//! steps to the published tree in the same order, by the same law, so each overlay's face is the
//! face the deposited tree reads (the test
//! `landmark_window_faces_read_each_phase_after_the_earlier_deposits`). [established-bounded;
//! measured] On the standing cut's cell tree before its last window (63,280 nodes; exterior wall
//! time on one host, the mean over 50 runs in integer µs): a clone takes 211 µs; the window's two
//! faces read in cell order take 122 µs and read with nothing known 73 µs. [agent-inferred] An
//! overlay admits arrivals past the declared population by the window's own earlier cells while
//! the widths' operands at that count fit `u128`; its faces are exact executed faces, normalized
//! for any stop weight, and its certificates are not read.
//!
//! [definition] **Faces.** [`Landmarks::probability`] is one class's executed face, exact;
//! [`Landmarks::face`] all classes with their grain exponents, `Σ_c q̂(c) = 1` exactly: the face the
//! receiving read and the card consume. It reads each splitting dyadic cell's paths once (a
//! dyadic cell's tree is reached only by arrivals its ancestors' trees were reached by, so its walk
//! ends no deeper than theirs), multiplies the splits down the dyadic heap, and
//! decides each grain exponent `⌊L_R log₂ q̂⌋` by a certified binary logarithm (exact integer
//! squaring, [`binary_log`]) with the exact comparison (`grain_exponent`) as its fallback.
//! [`Landmarks::splits`] returns the splits alone (the digit-0 numerator at every splitting dyadic
//! cell), the quantity the card's read returns and the host completes ([`LandmarkFace::of_splits`]).
//!
//! [definition; agent-inferred] **The ideal tree weighting is a reference oracle**
//! ([`IdealLandmarks`]): the same arena with `β` in ℚ and every face exact, the join included,
//! consumed by the tests and by the notebook's report of the executed face's cost. It is never on
//! the hot path; at scale it carries `β` at the reference width
//! `W_o = O + ⌈log₂(3 B n*² P²)⌉` ([`IdealLandmarks::reference_width`], `O` the enclosure grid's
//! octaves), whose rebases keep its code length within `2^(−O)` of the ideal over the passage.
//!
//! [definition; agent-inferred] **The declared stop prior** ([`StopPrior`]; Lean
//! `Compression/Landmark/Context/Tree` item 12; agent-inferred: campaign 2's controls showed that `½` at every node
//! is not the code-length optimum, since constant slots, which carry nothing but raise the stop
//! weight, coded the development cells up to 133 bits below the cell-only tree). A node at context
//! depth `d` (in its branch's letters) stops with
//! `w_d = 1 − 2^(−j_d)`, a rung of the dyadic ladder, and splits with `2^(−j_d)`: the tree is the
//! mixture over pruned trees with the prior `∏_stops w_d ∏_splits (1 − w_d)`, whose weights sum to
//! one, and it codes within `−log₂` of its prior of every pruned tree
//! (`stop_mixture_over_trees`, `stop_kraft_and_dominance`). The law enters the executed tree only
//! at the founding: each node is founded at `β₀ = w_d/(1 − w_d) = 2^(j_d) − 1`, an odd integer
//! carried exactly, with its stop weight `λ̂ = ⟦1 − 2^(−j_d)⟧` exact on the lattice
//! (`stop_founding_step`), and every step after it is the landmark tree's, `β' = β k/q̂'`
//! (`stop_ratio_step`), so the lattice law, the widths and the certificates are unchanged. `[1]` is
//! the `½` stop prior. A rung at a mixing depth must fit the carrier `W` (the declaration is refused
//! otherwise). The joins of an enlarged tree keep their own `β = 1`. Campaign 2's constant-slot
//! controls are the per-depth law `(j_0, j_(≥1)) = (1, r + 1)` exactly in the ideal weighting (the
//! test `landmark_constant_slots_are_the_per_depth_prior`).
//!
//! [definition; agent-inferred] **Weighing is local** (Lean `Compression/Landmark/Context/LocalWeighing`). A
//! mixture of whole passages telescopes to `½W_T + ½W_X` and uses a face only where it beats the
//! tree over the whole passage; the tree's own law weighs every landmark by its own evidence. Of
//! local weighing's three local laws, the one adopted lives here (the switching mixture across epochs,
//! the fixed share, is the population's `receiver::population::Dormancy`):
//! - **in each digit tree** ([`StopMixture`], [`JoinTree`], [`FaceJoins`]): `K` trees under the
//!   declared stop priors, and in each dyadic cell a join tree of two-face joins mixing their digit
//!   faces by that digit tree's evidence, each join's chart and certificates the enlarged tree's
//!   join's. The joins run on any faces' digit-0 numerators ([`FaceJoins::receive`]), so the
//!   development harness measures every member on the trees' executed faces, which the mixture does
//!   not change.
//!
//! [historical; measured] **The node-local law is retired** (its realization, `LocalLaw` and
//! `Landmarks::local`, measured at commit `d2a2e0db`, is at commit `89460425`; its law stays in
//! Lean `Compression/Landmark/Context/LocalWeighing.{node_local_dominance, node_local_founding}` over the own-weight tree
//! `Compression/Landmark/Context/Tree.{own_mixture_over_trees, own_weight_step}`): each landmark's own face mixed its KT face with an external face read
//! causally at the same digit, and held out it read above the tree (below).
//!
//! [established-bounded; measured] **On the standing cut** (notebook `hnn_landmark -- … local`,
//! development cells, prequential, each law charged `⌈log₂⌉` of its family): the node-local law
//! (`j = 2`, the Born `Dyadic` `χ = 1` digit split) codes `−52 + 11/16 + ε` bits below the `½` tree
//! and the stop-weight mixture (`½` with `(1, 3)` at `π_½ = ½`) `−121 + 7/16 + ε`. Held out, only the
//! stop-weight mixture stays below: `3 + 1/16 + ε` a cell, `−7 + 12/16 + ε` bits below the `½` tree
//! charged, and below online order-0, order-1 and PPM-2; the node-local law reads `+17 + 3/16 + ε`
//! above the tree.
//!
//! [established-bounded; measured] **On the wide cut** (notebook `hnn_landmark -- … wide`, the
//! wide cut; `2^20` cells, the final `2^17` held out; `D = 6`, the deepest the 20 GB cap admits, chosen on
//! the development cells): `½` stays first of the stop prior's 529 laws. Held out, the `½` tree reads
//! `1 + 15/16 + ε` a cell, `−133980 + 11/16 + ε` bits below PPM-2 charged (a cell
//! `−2 + 15/16 + ε`), and the stop-weight mixture charged 15 bits lies `−38 + 7/16 + ε` below it
//! (uncharged `−50 + 7/16 + ε`); on the standing cut's own cells, read at the wide standing, it lies
//! above the tree.
//!
//! [established-bounded; measured] **Stored where paths part, on the wide cut** (notebook
//! `hnn_landmark -- … compact`, the storage where paths part, at commit `2fb0c1c0`'s widths, `W` from `n*` alone;
//! development 917,504 cells, held out the final 131,072; `n* = 2^20`; bits at `L_R = 16`, each
//! `+ ε`, exact enclosures; bytes are the counted allocator's growth, allocated capacity and not
//! occupancy). At `D = 6` on the development cells the compacted tree codes `1822006 + 1/16` as the
//! full arena does, their difference
//! `[−505516772782985345855/2^96, −505516772782985345853/2^96]` bits against certificates summing to
//! `1005 + 4/16` (484 + 1/16 compacted, 521 + 3/16 full), with 2,784,875 nodes and 477,104,868
//! allocated bytes against 4,620,707 and 914,361,060 (14,291 ms against 16,436). The depth sweep, doubling
//! (`D = 6, 12, 24, 48, 73`, 73 the carriers' limit, charged 3 bits): `1802252 + 14/16`,
//! `1801962 + 7/16`, `1801940 + 12/16`, and at `D = 73` a code above `D = 48` by
//! `[51135399609700288000155/2^93, 204541598438801152000621/2^95]` (a grain `0 + 0/16`, far inside
//! both certificates): the development cells choose **`D = 48`**, 10,985,626 nodes, 35,373,218
//! label letters and 2,097,158,484 allocated bytes in 24,936 ms (each passage 14,291 to 25,133
//! ms). Charged
//! 3 bits it lies below the full tree at `D = 6` charged 3 by `−20066 + 10/16`. Held out, once:
//! `258201 + 3/16` (`1 + 15/16` a cell) against the full tree's `261616 + 4/16` (re-read exactly), PPM-2
//! `395598 + 8/16`, order-1 `496687 + 2/16` and order-0 `631713 + 1/16`; charged 3 bits it lies below
//! the full tree by `−3416 + 15/16`, PPM-2 by `−137395 + 11/16` (a cell `−2 + 15/16`), order-1 by
//! `−238483 + 1/16` and order-0 by `−373509 + 2/16`, each decided. The whole passage at `D = 48`
//! stores 12,542,969 nodes and 40,352,545 label letters in 2,097,158,516 allocated bytes (29,052
//! ms), against the full arena's 5,110,443 nodes at `D = 6` in 914,361,092 (19,126 ms).
//! [established-bounded; measured] **Re-measured once with the splits counted in `W`** (`W = 37,
//! 39, 41, 43, 44` at `D = 6, 12, 24, 48, 73`; the full arena retired): every reading above at the
//! grain is reproduced (the codes, the choice `D = 48`, the held-out passage and each ordering),
//! the rise at `D = 73` above `D = 48` is now
//! `[402375638051304080257559/2^96, 402375638051304080257561/2^96]`, and the bytes occupied (96 a
//! node, 16 a child-table entry, 4 a label letter) are 313,643,028 at `D = 6`, 969,583,660,
//! 1,249,468,440, 1,371,879,880 at `D = 48` and 1,472,140,904 on the development cells, and
//! 1,566,219,572 over the whole passage at `D = 48` (its 2,097,158,516 allocated); 168,704 ms in
//! all.
//!
//! [established-bounded; measured] **A landmark's storage has a capacity, on the wide cut**
//! (notebook `hnn_landmark -- … capacity`, the register's capacity; `D = 48`, the `½` prior, cells only;
//! development 917,504 cells, held out the final 131,072; bits at `L_R = 16`, each `+ ε`, exact
//! enclosures; the family `c ∈ {∞, 5, 7, 9, 11}` charged `⌈log₂ 5⌉ = 3` bits, `c = ∞` carrying no
//! capacity bit). `c = ∞` reproduces the compacted tree's development code `1801940 + 12/16`. The
//! development codes by `c = 5, 7, 9, 11`: `1950535 + 3/16`, `1827589 + 1/16`, `1804070 + 6/16`,
//! `1801600 + 13/16`, against `c = ∞` `+148594 + 7/16`, `+25648 + 5/16`, `+2129 + 9/16` and
//! `−340 + 1/16`, each decided; every passage stores 10,985,626 nodes in 1,371,879,880 occupied
//! bytes (the capacity moves no topology), 19,940 to 20,259 ms. The development cells choose
//! **`c = 11`** (`L = 2048`), charged 3 bits `−337 + 1/16` below `c = ∞`, and below every other
//! ceiling. Held out, once: `258018 + 5/16` (`1 + 15/16` a cell), against the compacted tree's recorded
//! `258201 + 3/16` charged 3 bits within `[−180 + 1/16, −180 + 3/16]` (uncharged
//! `[−183 + 1/16, −183 + 3/16]`), and against PPM-2's recorded `395598 + 8/16` charged 6 bits within
//! `[−137575 + 12/16, −137575 + 14/16]`, each decided below; 12,542,969 nodes, 23,762 ms. The code
//! falls with `c` through the declared family's edge.
//!
//! [definition; agent-inferred] **The depth, the family and the prior** are chosen on the development
//! cells only (the exposure's measurement, `hnn::reference::{choose_depth, choose_prior}`): `D` increases from `max(1, forced)` while the
//! development prequential code length decreases strictly (disjoint exact enclosures), every `D`
//! tried is reported, and `⌈log₂⌉` of the family tried is charged as description bits; each stop
//! prior of the declared family ([`prior_family`]: the global ladder `j = 1, …, J`, then the
//! per-depth pairs `(j_root, j_below)`, `J = ⌈log₂(n* B)⌉`, [`ladder_top`]) runs its own depth sweep,
//! and the choice is charged `⌈log₂⌉` of the laws tried. The held-out cells never choose anything.
//! [agent-inferred] A declared deepest depth bounds the depth sweep (`choose_depth_within`;
//! the wide cut): the resident memory cap bounded the retired full arena's a-priori founded nodes
//! `n* B D + 2^B − 1`, and so its depth at a population; stored where paths part, `2 n* B` nodes
//! bound no depth (stored where paths part), and the carriers' widths are its only limit.
//!
//! [definition; agent-inferred, from the retention and deposition laws] **The measurement is
//! prequential** (`hnn::reference::prequential` on the exposure's cut): every cell is scored at the current standing
//! before its own deposit, then deposited, for the tree and the online baselines alike. The tree's
//! faces and the oracle's are read by [`code_length`], `log₂ d − log₂ n` of `q = n/d` by the
//! certified binary logarithm ([`binary_log`]) within the enclosure grid `2^(−O)`; the baselines
//! read their own faces ([`baseline`]). Both are certified enclosures of `−log₂ q`, and
//! every ordering is decided by disjoint enclosures. [agent-inferred] A population's code is its
//! faces' product, enclosed once ([`PassageCode`]: exact integer bounds of the product, kept at
//! 127 significant bits and rounded outward, then one certified logarithm), not the sum of the
//! cells' enclosures: on the wide cut's development cells (`917,504 = 2^17·7`) the `D = 1` tree's
//! run with the per-cell sum took 29,902 ms, of which its passage 3,137 ms (the wide cut).
//!
//! [definition; agent-inferred] **The host realization** (the hardware law) is the reader's: which
//! regions run together is recorded where they are run (`hnn::reference`'s header). Within the
//! prequential measurement the tree and the baselines run together, each reading the shared
//! immutable cut and writing only its own state and sums; a window's phases read their own
//! overlays together. Within one tree the cells stay serial: they share mutable counts along their
//! paths.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the typed suffix address; an unfounded node reads the prior, and founding at first arrival keeps the law | `Compression/Landmark/Context/Tree.{unfounded_reads_prior, founded_tree_same_law}` | [`Letter`], [`address`], [`Landmarks::deposit`] |
//! | the bundle: causal, restricted by whole bundles, its code injective, its partitions finite | `Compression/Landmark/Context/Address.{bundle_causal, bundle_restrict, feature_scale_square, bundle_code_injective, phase_partition_finite, lock_partition_finite}` | [`Bundle`], [`LetterFamily`] (the slots' readers are `hnn::receiving::Feature`; the contact slot's letter is `hnn::contact::ContactReading::letter`), [`letter_address`] |
//! | the enlarged tree keeps the cell-only branch | `Compression/Landmark/Context/Address.cell_only_dominance_with_feature_charge` | the join (`Law::digit`), [`Landmarks::face_rule`] |
//! | the path face is positive and normalized for any `λ ∈ [0, 1]`; on the lattice too | `Compression/Landmark/Context/Tree.{path_face_normalized, lattice_path_laws}` | [`Landmarks::face`], [`Landmarks::probability`] |
//! | the lattice path's floor, its deviation adding down the path, and the executed face's bound with the address residual | `Compression/Landmark/Context/Tree.{lattice_path_floor, lattice_path_deviation, executed_face_bound}` | [`face_bits`], [`CellReading::residual`] |
//! | the mixture moves by at most the factors of `β` and of the child's face | `Compression/Landmark/Context/Tree.mix_ratio_bound` | [`CellReading::residual`] |
//! | the likelihood-ratio step of β, the opened-path update, and its executed telescope with a rebase | `Compression/Landmark/Context/Tree.{weight_step, landmark_step, lattice_step_telescope, lattice_node_telescope, weight_log_lipschitz}` | [`Landmarks::deposit`], [`ChartReport`] |
//! | a mantissa rebase's residual; the carrier's rebase, its enclosure and its total | `Compression/Landmark/Context/Tree.rebase_log_residual`; `Compression/Landmark/Context/Carrier.{rebase_decode, rebase_ratio_enclosed, rebase_step_enclosed, rebase_log_residual_sum, width_or_rebase_total}` | [`Beta::carry`], [`Beta::step`], [`carrier_width`] |
//! | the telescope on an opened path | `Compression/Landmark/Context/Tree.path_telescope_exact` | [`OpenedPath::edge_ratios`] |
//! | the executed dyadic split and the cells' partition; the forced digits when `\|A\| < 2^B` | `Compression/Landmark/Context/Tree.{executed_split_laws, cell_faces_partition, forced_digits_normalized}` | [`Landmarks::probability`], [`Landmarks::face`] |
//! | a digit face's floor and the rounding's residual (the first-order bound fails downward) | `Compression/Landmark/Context/Tree.{digit_face_ge, digit_log_residual, host_digit_bound_fails_downward}` | [`Landmarks::face_rule`] |
//! | the ideal tree weighting (the oracle) | `Compression/Landmark/Context/Tree.{landmark_step, mixture_is_probability, kraft_and_dominance, sequential_mixture}` | [`IdealLandmarks`] |
//! | the declared stop prior: the mixture over pruned trees with its prior, the weights summing to one, the dominance, the founding at `β₀ = 2^(j_d) − 1` and the step unchanged; `½` the corollary | `Compression/Landmark/Context/Tree.{stop_mixture_over_trees, PrunedTree.prior_const, PrunedTree.prior_sum, stop_kraft_and_dominance, stop_weight_step, stop_ratio_step, stop_founding_step, ladder_founding, stopWeight_half}` | [`StopPrior`], [`LandmarkDeclaration::prior`], the founding charts (`Law::founding`, [`ArenaView::founding`]), [`IdealLandmarks`] |
//! | the prior chosen on the development cells, charged `⌈log₂⌉` of the laws and of each law's depths | (a measurement, not a theorem) | [`ladder_top`], [`prior_family`]; the sweeps are the exposure's (`hnn::reference::{choose_prior, choose_depth_within, PriorSweep}`) |
//! | a population's code is its faces' product, enclosed once | (a certified reading: integer bounds and the certified logarithm) | [`PassageCode`], [`ProductBound`] |
//! | the stop-weight mixture per digit tree: the mixture over (law, pruned tree), its prior complete, within `−log₂ π_k − log₂ prior_(w_k)(S)`; the joins telescope to the Bayesian mixture, the executed chart's drift once | `Compression/Landmark/Context/LocalWeighing.{stop_mixture_per_tree, static_mixture, forward_executed}` | [`StopMixture`], [`JoinTree`], [`FaceJoins`] |
//! | a window's phases in cell order: each reads the standing after the earlier phases' deposits | `Compression/Landmark/Context/Tree.{landmark_step, treeWeight_arrive_off}` | [`Landmarks::window`], [`Window`] |
//! | founding where paths converge (second-arrival founding, measured and retired): the stopped path normalized under any stopping rule decided before the digit (a complete code); the tree with absent children, its Kraft form and dominance; the stopped step (`β` still at the stop); the second arrival opening with the first count; the first-arrival tree its case | `Compression/Landmark/Context/ConvergenceFounding.{stopping_rule_normalized, prequential_code_complete, conv_mixture_over_trees, conv_kraft_and_dominance, conv_weight_step, conv_ratio_step, second_arrival_opens_with_the_first_count, convergence_step, convergence_is_probability, first_arrival_is_the_full_tree}` | retired (its realization is at commit `d137e8a6`; the development cells kept the first arrival) |
//! | a landmark's storage has a capacity: the tree weighting over any node law whose state is a function of the arrivals reaching the node (its Kraft form, dominance, step and prequential code), the compacted tree for that law, and the capped register as an instance (positive, normalized, the carry lowering the register and keeping each reached symbol, KT below its ceiling, `c = ∞` KT) | `Compression/Landmark/Context/Tree.{NodeLaw, own_mixture_over_trees, own_kraft_and_dominance, own_weight_step₀, law_standing_is_routed, ktLaw_standing}`; `Compression/Landmark/Context/Compaction.{MassRouted, own_weight_prequential, compacted_node_law}`; `Compression/Landmark/Context/Capacity.{capLaw, cap_face_pos, cap_face_sum, cap_carry_laws, cap_carry_half_units, cap_run_total_le, cap_unbounded_is_kt, cap_below_ceiling_is_kt, capped_tree_laws}` | [`Capacity`], [`Capacity::carry`], [`LandmarkDeclaration::capacity`], `Law::apply_branch`, [`IdealLandmarks`] |
//! | stored where paths part: a chain with its bottom is one node at the summed rung (`1 − ρ_top = 2^(−S)(1 − ρ_bottom)`, founded at `2^S − 1`), a chain to `D` one KT node, the split's two ratios, the landmark tree's face exactly, at most `2n − 1` nodes a tree | `Compression/Landmark/Context/Compaction.{chain_ratio, chain_ratio_dyadic, leaf_chain_is_one_node, chain_split, compacted_is_the_full_tree, compacted_node_bound}` | [`Landmarks`], [`LandmarkDeclaration::rung_sums`], the split ([`Beta::split`], `Law::part`, `Law::chain`), [`Landmarks::face_rule`], [`Landmarks::tree_sizes`], [`IdealLandmarks`] |
//!
//! [open] Owed in #62 (Lean `Compression/Landmark/Context/Tree`'s `[open]`): the passage-level composition of the
//! drift bound (the subtree sum over the tree and the passage, from `lattice_node_telescope`,
//! `weight_log_lipschitz` and `mix_ratio_bound`) into the per-cell rule, and the certified binary
//! logarithm's squaring invariant; both are checked by the tests, the first cell by cell against
//! the oracle.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use thiserror::Error;

use crate::compression::cost::ceil_log2;
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ExactValueError, LOG_OCTAVES, interval_sum};
use crate::receiver::face::{GrainRefusal, grain_exponent};

pub mod baseline;
pub mod sections;
pub mod spans;

pub use sections::{Section, SectionChart, SectionSlots, Sections};
pub use spans::{Located, SpanReading};
mod checkpoint;
pub use checkpoint::StandingCodecError;
mod passage_checkpoint;
pub use passage_checkpoint::PassageCodecError;

// -------------------------------------------------------------------------------------------
// the refusals

/// [definition] **Every refusal of the context tree**: an extent that does not match its
/// declaration, a cell outside the exterior chart, a declaration that is not positive, a passage
/// past the declared population, an enclosure's, and the grain read's. Bad input is a typed
/// return, never a panic; a reader (the HNN, `hnn::HnnError::Context`) converts at its boundary.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ContextError {
    #[error("{what}: expected {expected}, found {found}")]
    Extent {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("cell code {code} lies outside the exterior chart of {alphabet}")]
    CellOutside { code: usize, alphabet: usize },
    #[error("the tree's declared population and grain must be positive")]
    NonpositiveDeclaration,
    #[error(
        "the landmark tree's declared population n* = {population} is passed; its chart's certificates hold only within it"
    )]
    PopulationReached { population: u64 },
    #[error(transparent)]
    Exact(#[from] ExactValueError),
    #[error(transparent)]
    Grain(#[from] GrainRefusal),
}

// -------------------------------------------------------------------------------------------
// letters, bundles and the declared family

/// [definition] **A typed bundle**: an earlier tick's cell with its declared features' letters,
/// their mixed-radix code over the family's slots ([`LetterFamily::encode`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bundle {
    pub cell: usize,
    pub features: u32,
}

/// [definition] **A typed address letter**: the boundary before the cut's first cell, a cell of
/// the cell-only family, or a bundle of a declared family.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Letter {
    Boundary,
    Cell(usize),
    Bundle(Bundle),
}

impl Letter {
    /// The cell letter's code: `0` for the boundary, `1 + code` for a cell (a bundle's cell).
    pub fn code(self) -> u64 {
        match self {
            Letter::Boundary => 0,
            Letter::Cell(code) | Letter::Bundle(Bundle { cell: code, .. }) => 1 + code as u64,
        }
    }

    /// The tick's cell, or none at the boundary.
    pub fn cell(self) -> Option<usize> {
        match self {
            Letter::Boundary => None,
            Letter::Cell(code) | Letter::Bundle(Bundle { cell: code, .. }) => Some(code),
        }
    }
}

/// [definition] **The declared letter family**: each bundle slot's finite alphabet `s_i`, in order,
/// the slots each bundle carries after its cell. The empty family is the cell-only tree
/// (campaign 1). The tree reads only the alphabets; what a slot's letter reads is its reader's (in
/// the HNN, a ring's phase class or a contact's reading, `hnn::receiving::Feature`, whose
/// `FeatureFamily` builds this family from its features' alphabets).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LetterFamily {
    sizes: Vec<u64>,
}

impl LetterFamily {
    /// The cell-only family.
    pub fn cells() -> Self {
        Self::default()
    }

    /// **Declare a family of slot alphabets**, refused at a slot of fewer than two letters (one
    /// letter carries nothing, module header) or when the slots' product passes 32 bits.
    pub fn new(sizes: Vec<u64>) -> Result<Self, ContextError> {
        let mut product = 1u64;
        for &size in &sizes {
            if size < 2 {
                return Err(shape(
                    "a feature slot of at least two letters (one letter carries nothing)",
                    2,
                    usize::try_from(size).unwrap_or(usize::MAX),
                ));
            }
            product = product.saturating_mul(size);
            if product > u64::from(u32::MAX) {
                return Err(shape(
                    "a family whose features' code fits 32 bits",
                    u32::MAX as usize,
                    usize::try_from(product).unwrap_or(usize::MAX),
                ));
            }
        }
        Ok(Self { sizes })
    }

    /// [definition; agent-inferred] **The constant-slot control of `slots` slots** (module header):
    /// each slot holds one letter, so the family carries no information and its code length against
    /// the cell-only tree is the enlarged tree's own reweighting. A development harness's control,
    /// never a declared family ([`Self::new`] refuses a slot of one letter), and never charged.
    pub fn constant_control(slots: usize) -> Self {
        Self {
            sizes: vec![1; slots],
        }
    }

    /// Each slot's alphabet `s_i`.
    pub fn sizes(&self) -> &[u64] {
        &self.sizes
    }

    /// `r`, the feature slots.
    pub fn slots(&self) -> usize {
        self.sizes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sizes.is_empty()
    }

    /// `Π_i s_i`, the features' codes.
    pub fn codes(&self) -> u64 {
        self.sizes.iter().product()
    }

    /// **The features' mixed-radix code** `Σ_i v_i Π_(k<i) s_k`, refused at a value outside its slot.
    pub fn encode(&self, values: &[u64]) -> Result<u32, ContextError> {
        if values.len() != self.sizes.len() {
            return Err(shape(
                "one value per feature slot",
                self.sizes.len(),
                values.len(),
            ));
        }
        let mut code = 0u64;
        let mut radix = 1u64;
        for (value, &size) in values.iter().zip(&self.sizes) {
            if *value >= size {
                return Err(shape(
                    "a feature value within its slot",
                    usize::try_from(size).unwrap_or(usize::MAX),
                    usize::try_from(*value).unwrap_or(usize::MAX),
                ));
            }
            code += value * radix;
            radix *= size;
        }
        Ok(u32::try_from(code).expect("the family's codes fit 32 bits"))
    }

    /// The slot values of a features' code.
    pub fn decode(&self, code: u32) -> Vec<u64> {
        let mut rest = u64::from(code);
        self.sizes
            .iter()
            .map(|&size| {
                let value = rest % size;
                rest /= size;
                value
            })
            .collect()
    }

    /// **The bundle's code** (Lean `Compression/Landmark/Context/Address.bundle_code_injective`): `0` for the
    /// boundary and `1 + x + |A| · f` for a cell `x` with the features' code `f`.
    pub fn bundle_code(&self, letter: Letter, alphabet: usize) -> u64 {
        match letter {
            Letter::Boundary => 0,
            Letter::Cell(cell) => 1 + cell as u64,
            Letter::Bundle(Bundle { cell, features }) => {
                1 + cell as u64 + alphabet as u64 * u64::from(features)
            }
        }
    }

    /// `1 + |A| · Π_i s_i`, the bundles' codes with the boundary.
    pub fn bundle_codes(&self, alphabet: usize) -> u64 {
        1 + alphabet as u64 * self.codes()
    }

    /// **The letters a bundle writes into the bundle tree**: its cell, then its slots, each `0` at
    /// the boundary and `1 + value` otherwise.
    fn flatten_into(&self, letter: Letter, flat: &mut Vec<u32>) {
        match letter {
            Letter::Boundary => flat.extend(std::iter::repeat_n(0, 1 + self.slots())),
            Letter::Cell(cell) => flat.push(1 + cell as u32),
            Letter::Bundle(Bundle { cell, features }) => {
                flat.push(1 + cell as u32);
                flat.extend(self.decode(features).into_iter().map(|v| 1 + v as u32));
            }
        }
    }
}

/// [definition] **The address of cell `position`**: `[x_(j−1), …, x_(j−D)]`, newest first, with
/// `Boundary` for every position before the cut's first cell (the cell-only family).
pub fn address(cells: &[usize], position: usize, depth: usize) -> Vec<Letter> {
    (1..=depth)
        .map(|back| {
            position
                .checked_sub(back)
                .map_or(Letter::Boundary, |at| Letter::Cell(cells[at]))
        })
        .collect()
}

/// [definition] **The address of cell `position` in a stream of ticks' letters**:
/// `[b_(j−1), …, b_(j−D)]`, newest first, `Boundary` before the stream's first tick.
pub fn letter_address(letters: &[Letter], position: usize, depth: usize) -> Vec<Letter> {
    (1..=depth)
        .map(|back| {
            position
                .checked_sub(back)
                .map_or(Letter::Boundary, |at| letters[at])
        })
        .collect()
}

/// **The cell-only family's letters** of a stream: each tick's cell.
pub fn cell_letters(cells: &[usize]) -> Vec<Letter> {
    cells.iter().map(|&cell| Letter::Cell(cell)).collect()
}

// -------------------------------------------------------------------------------------------
// the declared stop-weight law

/// The ladder's greatest rung: `β₀ = 2^j − 1` fits a machine word.
const MAX_RUNG: u32 = u64::BITS - 1;

/// [definition; agent-inferred] **The tree's declared stop-weight law** (the declared stop prior; Lean
/// `Compression/Landmark/Context/Tree` item 12): a node at context depth `d` stops with `w_d = 1 − 2^(−j_d)`, the rung
/// `j_d ≥ 1` of the dyadic ladder, and is founded at `β₀ = w_d/(1 − w_d) = 2^(j_d) − 1`, an odd
/// integer carried exactly (Lean `stop_founding_step`, `ladder_founding`); every later step is
/// the landmark tree's, `β' = β k/q̂'` (`stop_ratio_step`). The rungs are listed from the root, and a depth
/// past the list reads its last rung: one rung is the global law, and `[1]` is the `½` stop prior
/// ([`StopPrior::half`]). A repeated last rung is dropped, so two declarations of one law compare
/// equal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StopPrior {
    rungs: Vec<u32>,
}

impl StopPrior {
    /// The landmark tree's law: `w = ½` at every depth (rung 1, `β₀ = 1`).
    pub fn half() -> Self {
        Self { rungs: vec![1] }
    }

    /// **The global law at rung `j`**, refused outside `1..=63`.
    pub fn global(rung: u32) -> Result<Self, ContextError> {
        Self::per_depth(vec![rung])
    }

    /// **A per-depth law**: rung `j_d` at depth `d`, the last rung at every depth past the list;
    /// refused when empty or at a rung outside `1..=63` (`β₀ = 2^j − 1` fits a word).
    pub fn per_depth(mut rungs: Vec<u32>) -> Result<Self, ContextError> {
        if rungs.is_empty() {
            return Err(shape("a stop prior of at least one rung", 1, 0));
        }
        if let Some(&rung) = rungs.iter().find(|&&j| j == 0 || j > MAX_RUNG) {
            return Err(shape(
                "a rung of the dyadic ladder within 1..=63",
                MAX_RUNG as usize,
                rung as usize,
            ));
        }
        while rungs.len() >= 2 && rungs[rungs.len() - 1] == rungs[rungs.len() - 2] {
            rungs.pop();
        }
        Ok(Self { rungs })
    }

    /// The rungs from the root (the last read at every deeper depth).
    pub fn rungs(&self) -> &[u32] {
        &self.rungs
    }

    /// The rung `j_d` at context depth `d`.
    pub fn rung(&self, depth: usize) -> u32 {
        self.rungs[depth.min(self.rungs.len() - 1)]
    }

    /// Whether one rung holds at every depth.
    pub fn is_global(&self) -> bool {
        self.rungs.len() == 1
    }

    /// The stop weight `w_d = 1 − 2^(−j_d)`, exact.
    pub fn weight(&self, depth: usize) -> Rat {
        Rat::one() - two_power(-i64::from(self.rung(depth)))
    }

    /// The founding ratio `β₀ = w_d/(1 − w_d) = 2^(j_d) − 1`.
    pub fn founding(&self, depth: usize) -> u64 {
        (1u64 << self.rung(depth)) - 1
    }

    /// The greatest rung: the bits of the widest founding ratio.
    pub fn widest(&self) -> u32 {
        self.rungs.iter().copied().max().expect("at least one rung")
    }
}

impl std::fmt::Display for StopPrior {
    /// `j = 3` for a global law; `j_0 = 1, j_(≥1) = 4` per depth.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let last = self.rungs.len() - 1;
        if last == 0 {
            return write!(f, "j = {}", self.rungs[0]);
        }
        for (depth, rung) in self.rungs.iter().enumerate() {
            if depth > 0 {
                write!(f, ", ")?;
            }
            if depth == last {
                write!(f, "j_(≥{depth}) = {rung}")?;
            } else {
                write!(f, "j_{depth} = {rung}")?;
            }
        }
        Ok(())
    }
}

/// [definition; agent-inferred] **The ladder's top rung** `J = ⌈log₂(n* B)⌉` (the declared stop prior), derived
/// from the passage: for a fixed pruned tree the best stop weight at a depth is
/// `stops_d/(stops_d + splits_d)` (Lean `PrunedTree.prior_const`'s maximum), the rung
/// `log₂((stops_d + splits_d)/splits_d)`, and a depth holds at most `n* B` founded nodes (each cell
/// founds at most one node a depth in each of its `B` opened digit trees), so every such optimum lies
/// at or below `J`. It lies below every carrier width (`W = ⌈log₂(12 B L_R n* P²)⌉ > J`), so each
/// rung's founding ratio is carried exactly.
pub fn ladder_top(declaration: &LandmarkDeclaration) -> u32 {
    let nodes = BigUint::from(declaration.population)
        * BigUint::from(odometer_digits(declaration.alphabet));
    u32::try_from(ceil_log2(&nodes).max(1))
        .unwrap_or(MAX_RUNG)
        .min(MAX_RUNG)
}

/// [definition; agent-inferred] **The declared family of the stop prior's development choice**: the
/// global ladder `j = 1, …, J` (rung 1 first, the `½` stop prior), then the per-depth laws
/// `(j_root, j_below)`, the root at one rung and every deeper depth at another, `j_root ≠ j_below`,
/// in lexicographic order: `J²` laws. The per-depth shape is the one campaign 2's constant-slot
/// controls took (the root at `½`, every cell depth past it at `1 − 2^(−(r+1))`), without their
/// join.
pub fn prior_family(top: u32) -> Vec<StopPrior> {
    let top = top.clamp(1, MAX_RUNG);
    let global = (1..=top).map(|rung| StopPrior { rungs: vec![rung] });
    let pairs = (1..=top).flat_map(move |root| {
        (1..=top)
            .filter(move |&below| below != root)
            .map(move |below| StopPrior {
                rungs: vec![root, below],
            })
    });
    global.chain(pairs).collect()
}

// -------------------------------------------------------------------------------------------
// the declared node law: the register's capacity

/// [definition; agent-inferred] **A landmark's storage capacity** (Lean
/// `Compression/Landmark/Context/Capacity`): the node's two counts `n_0, n_1` are a register of ceiling `L = 2^c`.
/// The deposit counts its arrival, and when that brings `n_0 + n_1` to `L` both counts carry,
/// `n_b ← ⌈n_b/2⌉`, before the next arrival is read ([`Capacity::carry`]): the node's register is a
/// function of the arrivals that reached it, and its face is KT's on the carried counts, positive
/// and normalized (Lean `capLaw`, `cap_face_pos`, `cap_face_sum`). A reached symbol keeps a count.
/// `Unbounded` (`c = ∞`) is the KT node, and so is any ceiling a node never reaches: a node
/// reached fewer than `L` times reads KT's face exactly (`cap_below_ceiling_is_kt`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Capacity {
    /// `c = ∞`: the counts never carry (the uncapped tree).
    #[default]
    Unbounded,
    /// The ceiling exponent `c`: the register carries when a deposit brings `n_0 + n_1` to `2^c`.
    Ceiling(u32),
}

impl Capacity {
    /// **The ceiling in half-units**: a node's half-unit masses `2n_b + 1` total `2(n_0 + n_1) + 2`,
    /// so the register carries at the total `2L + 2 = 2^(c+1) + 2`; `None` when unbounded or when
    /// the ceiling passes every total a `u32` mass can hold (it is never reached). The card's
    /// mirror uploads it with its law (`holonics-cuda`, `hnn::tree`).
    pub fn ceiling_halves(self) -> Option<u64> {
        match self {
            Capacity::Unbounded => None,
            Capacity::Ceiling(exponent) if exponent < u32::BITS => Some((2u64 << exponent) + 2),
            Capacity::Ceiling(_) => None,
        }
    }

    /// **The register's carry after a deposit** on its half-unit masses `h_b = 2n_b + 1`: when
    /// `n_0 + n_1 ≥ L`, each `n_b ← ⌈n_b/2⌉`, that is `h_b ← 2⌊(h_b + 1)/4⌋ + 1`. Returns whether it
    /// carried. The total carried is at most `L/2 + 1`, so a node's total never passes the arrivals
    /// that reached it, and KT's floor `1/(2n* + 2)` and the widths' rule hold unchanged.
    pub fn carry(self, halves: &mut [u32; 2]) -> bool {
        carry_at(self.ceiling_halves(), halves)
    }
}

/// The register's carry at a ceiling in half-units ([`Capacity::carry`]).
fn carry_at(ceiling: Option<u64>, halves: &mut [u32; 2]) -> bool {
    match ceiling {
        Some(top) if u64::from(halves[0]) + u64::from(halves[1]) >= top => {
            for half in halves.iter_mut() {
                *half = 2 * ((*half + 1) / 4) + 1;
            }
            true
        }
        _ => false,
    }
}

impl std::fmt::Display for Capacity {
    /// `c = ∞`, or `c = 5`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Capacity::Unbounded => write!(f, "c = ∞"),
            Capacity::Ceiling(exponent) => write!(f, "c = {exponent}"),
        }
    }
}

// -------------------------------------------------------------------------------------------
// the declaration and its derived widths

/// [definition] **A landmark tree's declaration**: the exterior chart's `|A|`, the address depth
/// `D` in bundles, the forced splits of the cell tree (context depths `d < forced` mix nothing,
/// `λ_d = 0`), the declared population `n*` bounding the passage, the receiver's grain `L_R`, the
/// declared letter family, the declared stop-weight law ([`StopPrior`], read at each node's
/// depth in its branch's letters; the joins of an enlarged tree keep their own `β = 1`), and the
/// declared node law's capacity ([`Capacity`], the register's capacity; `Unbounded` is the KT node).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkDeclaration {
    pub alphabet: usize,
    pub depth: usize,
    pub forced: usize,
    pub population: u64,
    pub grain: u64,
    pub family: LetterFamily,
    pub prior: StopPrior,
    pub capacity: Capacity,
}

impl LandmarkDeclaration {
    /// **The branches' depths in letters**: the cell tree's `D`, then, with features declared, the
    /// bundle tree's `D(1 + r)`.
    pub fn branch_depths(&self) -> Vec<usize> {
        if self.family.is_empty() {
            vec![self.depth]
        } else {
            vec![self.depth, self.depth * (1 + self.family.slots())]
        }
    }

    /// **Each branch's letters of an address** (the tree's keys under their parents): the cells'
    /// codes, then, with features declared, the flattened bundles (module header, "branches").
    pub fn letters(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.branch_depths()
            .iter()
            .enumerate()
            .map(|(branch, &depth)| {
                let mut flat = Vec::with_capacity(depth);
                for &letter in address {
                    if branch == 0 {
                        flat.push(letter.code() as u32);
                    } else {
                        self.family.flatten_into(letter, &mut flat);
                    }
                }
                flat
            })
            .collect()
    }

    fn odometer(&self) -> Odometer {
        Odometer {
            alphabet: self.alphabet,
            digits: odometer_digits(self.alphabet),
        }
    }

    /// **The digits a class opens**: `(h, b)`, the splitting dyadic cells of its descent with its
    /// digit in each (a forced digit opens nothing).
    pub fn emitted(&self, class: usize) -> Vec<(usize, usize)> {
        self.odometer().emitted(class)
    }

    /// **The splitting dyadic cells**, heap-ordered: the order of [`Splits::numerators`].
    pub fn splitting(&self) -> Vec<usize> {
        self.odometer().splitting()
    }

    /// **The path depth `P` the widths' rule reads** (module header, "The widths"): `D`, or
    /// `D + D(1 + r) + 2` for the enlarged tree.
    pub fn path_depth(&self) -> u64 {
        let depths = self.branch_depths();
        if depths.len() == 1 {
            depths[0] as u64
        } else {
            depths.iter().map(|&d| d as u64).sum::<u64>() + 2
        }
    }

    /// **Each branch's summed rungs from the root** (stored where paths part): `sums[b][d] = Σ_(i<d, i ≥ f_b) j_i`
    /// for `d = 0, …, D_b`, `f_b` the branch's forced depths (the cell branch's `forced`, none in
    /// the bundle branch; a forced depth's rung is `0`). A stored chain from `top` to `bottom`
    /// below `D_b` is one node at the summed rung `sums[b][bottom + 1] − sums[b][top]`
    /// (`Compression/Landmark/Context/Compaction.chain_ratio_dyadic`).
    pub fn rung_sums(&self) -> Vec<Vec<u64>> {
        self.branch_depths()
            .into_iter()
            .enumerate()
            .map(|(branch, depth)| {
                let forced = if branch == 0 { self.forced } else { 0 };
                let mut sums = vec![0u64; depth + 1];
                for at in 0..depth {
                    let rung = if at >= forced {
                        u64::from(self.prior.rung(at))
                    } else {
                        0
                    };
                    sums[at + 1] = sums[at] + rung;
                }
                sums
            })
            .collect()
    }
}

/// `B = ⌈log₂|A|⌉`, the odometer digits of a cell.
pub fn odometer_digits(alphabet: usize) -> u64 {
    ceil_log2(&BigUint::from(alphabet))
}

/// `K = 2n* + 2`: a binary KT face after at most `n*` arrivals is at least `1/K`.
fn floor_reciprocal(population: u64) -> BigUint {
    BigUint::from(population) * 2u32 + 2u32
}

/// [definition; agent-inferred] **The path lattice's width** `M_p`: the least `M` with
/// `2^M ≥ 3 B L_R (2n* + 2)(n* P² + 2P + 1)`, which holds the lattice's rounding within a quarter
/// grain a cell (module header, "The widths").
pub fn face_bits(population: u64, digits: u64, grain: u64, depth: u64) -> u64 {
    let (n, d) = (BigUint::from(population), BigUint::from(depth));
    let terms = &n * &d * &d + &d * 2u32 + 1u32;
    ceil_log2(
        &(BigUint::from(3u32)
            * BigUint::from(digits)
            * BigUint::from(grain)
            * floor_reciprocal(population)
            * terms),
    )
}

/// [definition; agent-inferred] **The β carrier width** `W`: the least width (at least 2) with
/// `2^W ≥ 12 B L_R (2n* + 1) P²`, which holds the rebases' drift, the splits' included (stored where
/// paths part: `(2n* + 1) P²` units of `2^(1−W)`), within a quarter grain a cell (module header, "The
/// widths").
pub fn carrier_width(population: u64, digits: u64, grain: u64, depth: u64) -> u64 {
    let d = BigUint::from(depth);
    ceil_log2(
        &(BigUint::from(12u32)
            * BigUint::from(digits)
            * BigUint::from(grain)
            * (BigUint::from(population) * 2u32 + 1u32)
            * &d
            * &d),
    )
    .max(2)
}

/// [definition; agent-inferred] **The widths a declaration derives** (module header, "The
/// widths"): the digits `B`, the path lattice `M_p`, the β carrier `W`, the certificates' grid
/// `C = M_p + W`, and the carrier rebase's denominator width `R = 126 − W` when the β step's
/// product can pass `u128` (else `0`: no carrier rebase is ever taken).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Widths {
    pub digits: u64,
    pub face: u64,
    pub carrier: u64,
    pub certificate: u64,
    pub rebase: u64,
}

impl Widths {
    /// The widths the rule derives from a declaration.
    pub fn derived(declaration: &LandmarkDeclaration) -> Self {
        Self::at_depth(declaration, declaration.path_depth(), None)
    }

    /// The derived widths with a declared carrier `W` in place of the rule's.
    fn with_carrier(declaration: &LandmarkDeclaration, carrier: u64) -> Self {
        Self::at_depth(declaration, declaration.path_depth(), Some(carrier))
    }

    /// The widths at a path depth `P`, with the rule's carrier or a declared one.
    fn at_depth(declaration: &LandmarkDeclaration, depth: u64, carrier: Option<u64>) -> Self {
        let digits = odometer_digits(declaration.alphabet);
        let carrier = carrier.unwrap_or_else(|| {
            carrier_width(declaration.population, digits, declaration.grain, depth)
        });
        let face = face_bits(declaration.population, digits, declaration.grain, depth);
        let kappa = floor_reciprocal(declaration.population).bits();
        let rebase = if 2 * carrier + kappa + face + 1 > u64::from(u128::BITS) {
            126u64.saturating_sub(carrier)
        } else {
            0
        };
        Self {
            digits,
            face,
            carrier,
            certificate: face + carrier,
            rebase,
        }
    }

    /// The largest `u128` operand the widths ask for, in bits: the lattice mixture
    /// `max(2M + 2, M + κ + 3)` (its parts divided apart, [`lattice_mix`]; the two faces' blend
    /// `2M + 2`), the stop weight `M + W + 3` (decided before its division past `2^(M+1)`,
    /// [`Beta::stop_weight`]), the β step's carrier `W + κ + M` and, unless the carrier rebases,
    /// its mantissa division `2W + κ + M + 1`, with `κ` the bits of `2n* + 2`.
    pub fn operand_bits(&self, population: u64) -> u64 {
        let kappa = floor_reciprocal(population).bits();
        let (m, w) = (self.face, self.carrier);
        let division = if self.rebase > 0 {
            self.rebase + w + 1
        } else {
            2 * w + kappa + m + 1
        };
        self.lattice_operands(kappa).max(division)
    }

    /// The lattice mixture's, the stop weight's and the β carrier's operands, in bits.
    fn lattice_operands(&self, kappa: u64) -> u64 {
        let (m, w) = (self.face, self.carrier);
        (2 * m + 2)
            .max(m + kappa + 3)
            .max(m + w + 3)
            .max(w + kappa + m)
    }

    /// [agent-inferred] **Whether the single divisions fit `u128`** at a population: the lattice
    /// mixture read as one division `(2^M λ̂ u + (2^M − λ̂) x v)/(2^M v)` (`2M + κ + 3` bits) and the
    /// stop weight decided only past `|exponent| > M + W` (`2W + M + 3` bits). The card's kernel
    /// (`holonics-cuda`, `kernels/tree.cu`) executes that realization, so its mirror refuses wider
    /// widths; the host's split operands ([`lattice_mix`], [`Beta::stop_weight`]) return the same
    /// integers wherever both admit.
    pub fn single_division_admitted(&self, population: u64) -> bool {
        let kappa = floor_reciprocal(population).bits();
        (2 * self.face + kappa + 3).max(2 * self.carrier + self.face + 3) <= u64::from(u128::BITS)
    }

    /// Whether the widths at a population admit every product in `u128`, the carrier rebase
    /// keeping at least `W` bits.
    fn admitted(&self, population: u64) -> bool {
        let kappa = floor_reciprocal(population).bits();
        let rebase_needed = 2 * self.carrier + kappa + self.face + 1 > u64::from(u128::BITS);
        let rebase_kept = !rebase_needed || 126u64.saturating_sub(self.carrier) >= self.carrier;
        rebase_kept && self.lattice_operands(kappa) <= u64::from(u128::BITS)
    }
}

/// `log₂ e < 3/2`, the constant of the certified residual (`ln 2 > 2/3`).
pub(crate) fn log2_e_bound() -> Rat {
    Rat::new(BigInt::from(3), BigInt::from(2))
}

fn two_power(exponent: i64) -> Rat {
    let shift = exponent.unsigned_abs() as usize;
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << shift)
    } else {
        Rat::new_raw(BigInt::one(), BigInt::one() << shift)
    }
}

/// `⌈a/b⌉` in `u128`.
fn ceil_div(a: u128, b: u128) -> u128 {
    a.div_ceil(b)
}

/// `⟦2^M u/v⟧`: the lattice numerator nearest `u/v` (ties up), inside `[1, 2^M − 1]`.
fn lattice_round(widths: &Widths, numerator: u128, denominator: u128) -> u64 {
    let rounded = (2 * numerator + denominator) / (2 * denominator);
    (rounded as u64).clamp(1, (1u64 << widths.face) - 1)
}

/// **`⟦λ̂ u/v + (1 − λ̂) x⟧` on `2^(−M)`** (module header, "The lattice mixture and the stop weight
/// read split operands"): the nearest lattice numerator (ties up) of `λ̂u/v + (2^M − λ̂)x/2^M`, inside
/// `[1, 2^M − 1]`, each part divided with its remainder so that no operand passes
/// `max(2M, M + κ + 3)` bits (`u ≤ v < 2^κ`, `λ̂ ≤ 2^M`, `x < 2^M`).
pub(crate) fn lattice_mix(widths: &Widths, stop: u64, u: u64, v: u64, below: u64) -> u64 {
    let face = widths.face;
    let full = 1u128 << face;
    let (stop, u, v) = (u128::from(stop), u128::from(u), u128::from(v));
    let (a, b) = (stop * u, (full - stop) * u128::from(below));
    let whole = a / v + (b >> face);
    let (left, right) = (a % v, b & (full - 1));
    let half = ((left << (face + 1)) + 2 * right * v + (v << face)) / (v << (face + 1));
    ((whole + half) as u64).clamp(1, (1u64 << face) - 1)
}

/// `⟦λ̂ a + (1 − λ̂) b⟧` of two lattice faces with the stop weight `λ̂` (numerators of `2^(−M)`).
fn lattice_blend(widths: &Widths, stop: u64, a: u64, b: u64) -> u64 {
    let full = 1u128 << widths.face;
    let stop = u128::from(stop);
    lattice_round(
        widths,
        stop * u128::from(a) + (full - stop) * u128::from(b),
        full,
    )
}

/// **One carried β step** on `2^(−C)`: `β' = β u/(v x) 2^s`, with its rebase units `⌈2^C/m'⌉` and
/// `⌈2^C/D̂⌉` (a mantissa kept, a carrier released).
fn carried_step(
    widths: &Widths,
    beta: Beta,
    u: u128,
    v: u128,
    x: u128,
    shift: i64,
) -> (Carried, u128) {
    let (n, d, e) = beta.parts();
    let carried = Beta::step(
        u128::from(n) * u,
        u128::from(d) * v * x,
        e + shift,
        widths.carrier,
        widths.rebase,
    );
    let units = carried
        .mantissa
        .map_or(0, |m| ceil_div(1u128 << widths.certificate, m))
        .saturating_add(
            carried
                .released
                .map_or(0, |kept| ceil_div(1u128 << widths.certificate, kept)),
        );
    (carried, units)
}

/// A certificate on `2^(−C)` in `ln`, read in bits: times `3/2 > log₂ e`.
fn certified(widths: &Widths, units: u128) -> Rat {
    Rat::new(
        BigInt::from(units) * 3,
        BigInt::from(2u32) << widths.certificate as usize,
    )
}

/// The greatest common divisor of two odd integers (binary: subtract, then shed twos).
fn odd_gcd(mut a: u128, mut b: u128) -> u128 {
    while a != b {
        if a > b {
            a -= b;
            a >>= a.trailing_zeros();
        } else {
            b -= a;
            b >>= b.trailing_zeros();
        }
    }
    a
}

fn shape(what: &'static str, expected: usize, found: usize) -> ContextError {
    ContextError::Extent {
        what,
        expected,
        found,
    }
}

fn bits128(x: u128) -> u64 {
    u64::from(u128::BITS - x.leading_zeros())
}

// -------------------------------------------------------------------------------------------
// the β chart

/// [definition; agent-inferred] **A carried mixture ratio** `β = (numerator/denominator) · 2^exponent`,
/// numerator and denominator odd and coprime, each below `2^W` (module header, "The widths").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Beta {
    numerator: u64,
    denominator: u64,
    exponent: i64,
}

/// [definition] **One carried step of β**: the carried ratio, the kept mantissa when the odd parts
/// were rebased to `W` bits, and the carrier's rebased denominator `D̂` when its remainder was
/// released (module header, "The carrier rebases past `u128`").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Carried {
    pub beta: Beta,
    pub mantissa: Option<u128>,
    pub released: Option<u128>,
}

impl Beta {
    /// `β = 1`: a join's ratio at first arrival, and a node's under the `½` stop prior.
    pub const ONE: Beta = Beta {
        numerator: 1,
        denominator: 1,
        exponent: 0,
    };

    /// The carried value, exact.
    pub fn value(&self) -> Rat {
        let (mut numerator, mut denominator) =
            (BigInt::from(self.numerator), BigInt::from(self.denominator));
        let shift = self.exponent.unsigned_abs() as usize;
        if self.exponent >= 0 {
            numerator <<= shift;
        } else {
            denominator <<= shift;
        }
        // Odd coprime parts times a power of two on one side stay coprime.
        Rat::new_raw(numerator, denominator)
    }

    /// The odd numerator, the odd denominator and the binary exponent (the carry).
    pub fn parts(&self) -> (u64, u64, i64) {
        (self.numerator, self.denominator, self.exponent)
    }

    /// The binary exponent (the carry).
    pub fn exponent(&self) -> i64 {
        self.exponent
    }

    /// **Carry the positive ratio `(numerator/denominator) · 2^exponent` at width `W`**: its twos
    /// moved into the exponent and its odd parts reduced; exact when both fit `W` bits, otherwise
    /// rebased to its mantissa `m' = ⌊v 2^s⌋ ∈ [2^(W−1), 2^W)`, which is returned: the relative
    /// residual `r = 1 − m'/(v 2^s)` has `|ln(1 − r)| < 1/m' ≤ 2^(1−W)` (Lean
    /// `Compression/Landmark/Context/Tree.rebase_log_residual`). The operands must be positive, with
    /// `W + bits(denominator) ≤ 128`.
    pub fn carry(
        numerator: u128,
        denominator: u128,
        exponent: i64,
        width: u64,
    ) -> (Self, Option<u128>) {
        let carried = Self::step(numerator, denominator, exponent, width, 0);
        debug_assert!(carried.released.is_none());
        (carried.beta, carried.mantissa)
    }

    /// **One step of the carried ratio with the carrier's rebase** (module header, "The carrier
    /// rebases past `u128`"; Lean `Compression/Landmark/Context/Carrier`): the ratio `(N/D) · 2^exponent` carried
    /// at width `W` as [`Beta::carry`] carries it, except that when the mantissa's division
    /// `N 2^s / D` would pass `u128` (`W + bits(D) > 128`), `D`'s odd part first rebases to its
    /// top `R` bits (`rebase`, `R ≥ W`): `D = 2^e D̂ + r_D`, the exponent takes `−e`, and a
    /// nonzero remainder is released, the carried ratio then lying in `[1, 1 + 1/D̂)` times the
    /// exact one (`released = Some(D̂)`). The operands must be positive.
    pub fn step(
        numerator: u128,
        denominator: u128,
        exponent: i64,
        width: u64,
        rebase: u64,
    ) -> Carried {
        debug_assert!(numerator > 0 && denominator > 0);
        let (twos_n, twos_d) = (numerator.trailing_zeros(), denominator.trailing_zeros());
        let (mut a, mut b) = (numerator >> twos_n, denominator >> twos_d);
        let mut exponent = exponent + i64::from(twos_n) - i64::from(twos_d);
        let mut released = None;
        if width + bits128(b) > u64::from(u128::BITS) {
            debug_assert!(rebase >= width);
            // The carrier's rebase: keep `D`'s top `R` bits; `N 2^s` is exact at any `s ≥ e`.
            let e = bits128(b) - rebase;
            let kept = b >> e;
            if kept << e != b {
                released = Some(kept);
            }
            b = kept;
            exponent -= e as i64;
            let twos = b.trailing_zeros();
            b >>= twos;
            exponent -= i64::from(twos);
        }
        let common = odd_gcd(a, b);
        (a, b) = (a / common, b / common);
        if bits128(a) <= width && bits128(b) <= width && released.is_none() {
            return Carried {
                beta: Self {
                    numerator: a as u64,
                    denominator: b as u64,
                    exponent,
                },
                mantissa: None,
                released,
            };
        }
        // `a/b ∈ (2^(t−1), 2^(t+1))`, `t = bits(a) − bits(b)`, so `a 2^s/b ∈ (2^(W−1), 2^(W+1))`
        // at `s = W − t`.
        let floor = |shift: i64| -> u128 {
            if shift >= 0 {
                (a << shift) / b
            } else {
                a / (b << shift.unsigned_abs())
            }
        };
        let mut shift = width as i64 - (bits128(a) as i64 - bits128(b) as i64);
        let mut mantissa = floor(shift);
        if bits128(mantissa) > width {
            shift -= 1;
            mantissa = floor(shift);
        }
        debug_assert_eq!(bits128(mantissa), width);
        let twos = mantissa.trailing_zeros();
        Carried {
            beta: Self {
                numerator: (mantissa >> twos) as u64,
                denominator: 1,
                exponent: exponent - shift + i64::from(twos),
            },
            mantissa: Some(mantissa),
            released,
        }
    }

    /// [definition; agent-inferred] **A chain's split ratios** (stored where paths part; Lean
    /// `Compression/Landmark/Context/Compaction.chain_split`): a stored chain carrying `β` at the summed rung
    /// `S = S_up + S_low` (`S_up, S_low ≥ 1`) parts between its two rungs; its lower part keeps its
    /// counts at `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)` and its upper part holds the same counts at
    /// `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low) − 1) + 2^S − 1)`, each formed exactly and
    /// carried once at width `W` (exact when both odd parts fit, otherwise the `W`-bit floor
    /// mantissa, returned). Returns `[upper, lower]`: the executed split's two charts (`Law::part`)
    /// and the card's split (`holonics-cuda`, `kernels/tree.cu`), checked against it.
    pub fn split(self, upper: u64, lower: u64, width: u64) -> [(Self, Option<u128>); 2] {
        let (e, n, d) = (
            self.exponent,
            BigUint::from(self.numerator),
            BigUint::from(self.denominator),
        );
        let (up, low, whole) = (ladder(upper), ladder(lower), ladder(upper + lower));
        let below = carry_ratio(&n * &low, &d * &whole, e, width);
        let shift = e.unsigned_abs() as usize;
        let (numerator, denominator) = if e >= 0 {
            (
                (&up * &n) << (lower as usize + shift),
                ((&n * &low) << shift) + &d * &whole,
            )
        } else {
            (
                (&up * &n) << lower as usize,
                &n * &low + ((&d * &whole) << shift),
            )
        };
        [carry_ratio(numerator, denominator, 0, width), below]
    }

    /// **The stop weight** `λ̂ = ⟦β/(1 + β)⟧` on the lattice `2^(−M)`, as its numerator in
    /// `[0, 2^M]` (round to nearest, ties up). When one side of `1 + β` passes the other by at least
    /// `2^(M+1)` the rounding is decided (`λ̂ = 1` or `0`: the other side's share is below half a
    /// lattice step); it is read from the sides' bits before any division, so every operand stays
    /// within `M + b + 3` bits for odd parts of `b` bits (`b ≤ W` on the carrier; a leaf's founding
    /// chart, never stepped, may hold a rung up to 63). The width is the carrier's, unused.
    pub fn stop_weight(&self, face_bits: u64, _width: u64) -> u64 {
        let full = 1u64 << face_bits;
        let (a, b) = (u128::from(self.numerator), u128::from(self.denominator));
        let (bits_a, bits_b) = (bits128(a) as i64, bits128(b) as i64);
        let decided = face_bits as i64 + 2;
        let twice = 1u128 << (face_bits + 1);
        if self.exponent >= 0 {
            // 2^M λ = 2^M − z, z = 2^M b/g, g = a 2^e + b; ⌊2^M − z + ½⌋ = 2^M − ⌈z − ½⌉. When
            // bits a − 1 + e ≥ M + 1 + bits b, a 2^e > 2^(M+1) b, so z < ½.
            if self.exponent + bits_a >= decided + bits_b {
                return full;
            }
            let g = (a << self.exponent) + b;
            let t = twice * b;
            let up = if t <= g { 0 } else { (t - g).div_ceil(2 * g) };
            full - up as u64
        } else {
            // 2^M λ = 2^M a/h, h = a + b 2^|e|: below ½ when b 2^|e| > 2^(M+1) a.
            let shift = self.exponent.unsigned_abs();
            if shift as i64 + bits_b >= decided + bits_a {
                return 0;
            }
            let h = a + (b << shift);
            ((twice * a + h) / (2 * h)) as u64
        }
    }
}

/// [definition] **The β chart's report**: the carrier `W`, the rebases in all and at the
/// most-rebased node or join, the carrier's releases, and the largest drift certificate over the
/// nodes and joins, `|log₂ β̂ − log₂ β|` in bits (the `drift` times `3/2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReport {
    pub carrier: u64,
    pub rebases: u64,
    pub node_rebases: u64,
    pub released: u64,
    pub drift: Rat,
}

// -------------------------------------------------------------------------------------------
// the odometer and the arena

/// The dyadic chart of the alphabet: which cells split and which digits a class opens.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Odometer {
    alphabet: usize,
    digits: u64,
}

impl Odometer {
    /// Whether the dyadic cell at `level` with `prefix` holds a class.
    fn holds(&self, level: u64, prefix: usize) -> bool {
        (prefix << (self.digits - level)) < self.alphabet
    }

    /// Whether the dyadic cell at `level` with `prefix` splits: its upper half holds a class.
    fn splits(&self, level: u64, prefix: usize) -> bool {
        (((prefix << 1) | 1) << (self.digits - level - 1)) < self.alphabet
    }

    /// **The trees a class's digits open**, with its digit in each: the splitting dyadic cells of
    /// its descent (a forced digit opens nothing).
    fn emitted(&self, class: usize) -> Vec<(usize, usize)> {
        (0..self.digits)
            .filter_map(|level| {
                let prefix = class >> (self.digits - level);
                let digit = (class >> (self.digits - level - 1)) & 1;
                self.splits(level, prefix)
                    .then_some(((1usize << level) | prefix, digit))
            })
            .collect()
    }

    /// Every splitting dyadic cell, heap-ordered (a parent before its children).
    fn splitting(&self) -> Vec<usize> {
        (0..self.digits)
            .flat_map(|level| (0..1usize << level).map(move |prefix| (level, prefix)))
            .filter(|&(level, prefix)| self.splits(level, prefix))
            .map(|(level, prefix)| (1usize << level) | prefix)
            .collect()
    }
}

/// The top bit of a node's depth word: its branch (the bundle tree).
const BRANCH_BIT: u32 = 1 << 31;

/// The arena's topology and masses, stored where paths part, shared by the executed
/// tree and the oracle: the roots per tree, the child table, each node's depth word (its bottom
/// depth, its branch in the top bit), its two half-unit masses and its label end, and the label
/// pool, whose runs are the tree's own paths.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Arena {
    roots: Vec<Option<u32>>,
    children: HashMap<u64, u32>,
    depths: Vec<u32>,
    halves: Vec<[u32; 2]>,
    ends: Vec<u32>,
    letters: Vec<u32>,
}

fn key(parent: u32, letter: u32) -> u64 {
    (u64::from(parent) << 32) | u64::from(letter)
}

/// [definition] **Where a branch's read stops**, decided from the standing before the digit is
/// read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stop {
    /// The path's last node is a leaf at the branch's depth and reads its own KT face alone.
    Node,
    /// The depth below the path's last matched depth is unfounded and reads the prior `½`.
    Prior,
}

/// [definition; agent-inferred] **A branch's walk down its tree** along an address: the stored
/// nodes it opens from the root, where the last one's chain parts from the address (stored where paths part:
/// its upper part, down to that depth, is read), and where it stops.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Walk {
    nodes: Vec<u32>,
    parting: Option<usize>,
    stop: Stop,
}

/// **The stored nodes as a read opens them**: the root of each tree, the child behind a letter,
/// each node's two half-unit masses, its depth word and its label end, the label pool's letters and
/// the count of stored nodes. The arena answers them (for the oracle and the
/// executed tree), and so does a window's working overlay ([`Working`]).
trait Topology {
    fn root(&self, tree: usize) -> Option<u32>;
    fn child(&self, parent: u32, letter: u32) -> Option<u32>;
    fn halves(&self, node: u32) -> [u32; 2];
    /// The node's depth word: its bottom depth, its branch in the top bit.
    fn word(&self, node: u32) -> u32;
    /// A node's label end: one past its bottom's letter in the label pool.
    fn end(&self, node: u32) -> u32;
    /// The label pool's letter at an index.
    fn letter(&self, index: u32) -> u32;
    fn len(&self) -> usize;
    /// The label pool's letters.
    fn held(&self) -> usize;

    /// The node's bottom depth: the depth of the chain's last node.
    fn bottom(&self, node: u32) -> usize {
        (self.word(node) & !BRANCH_BIT) as usize
    }

    /// A node's label letter at depth `d`, below its top and at most its bottom.
    fn label(&self, node: u32, depth: usize) -> u32 {
        let bottom = self.bottom(node);
        let end = self.end(node) as usize;
        self.letter(u32::try_from(end + depth - 1 - bottom).expect("a pool index"))
    }

    /// **The walk along an address in tree `t`** (letters `a_1, …, a_D`, `letters[d − 1] = a_d`):
    /// from the root, each stored node's label is compared letter by letter below its top to its
    /// bottom (a one-depth chain compares nothing); the first letter that differs parts the path
    /// at the depth above it; a leaf at `D` stops the walk at its own face; a missing child stops
    /// it at the prior.
    fn walk(&self, tree: usize, letters: &[u32]) -> Walk {
        let mut nodes = Vec::new();
        let Some(mut node) = self.root(tree) else {
            return Walk {
                nodes,
                parting: None,
                stop: Stop::Prior,
            };
        };
        let mut top = 0;
        loop {
            let bottom = self.bottom(node);
            nodes.push(node);
            if bottom > top {
                let end = self.end(node) as usize;
                for depth in top + 1..=bottom {
                    let index = u32::try_from(end + depth - 1 - bottom).expect("a pool index");
                    if self.letter(index) != letters[depth - 1] {
                        return Walk {
                            nodes,
                            parting: Some(depth - 1),
                            stop: Stop::Prior,
                        };
                    }
                }
            }
            if bottom == letters.len() {
                return Walk {
                    nodes,
                    parting: None,
                    stop: Stop::Node,
                };
            }
            match self.child(node, letters[bottom]) {
                Some(next) => {
                    top = bottom + 1;
                    node = next;
                }
                None => {
                    return Walk {
                        nodes,
                        parting: None,
                        stop: Stop::Prior,
                    };
                }
            }
        }
    }

    /// `(2C_b, 2N)`, the node's KT mass of `b` and its total, in half-units.
    fn kt(&self, node: u32, symbol: usize) -> (u64, u64) {
        let [zero, one] = self.halves(node);
        (
            u64::from([zero, one][symbol]),
            u64::from(zero) + u64::from(one),
        )
    }

    /// Refused when founding `nodes` more would pass 31-bit node numbers, or holding `letters` more
    /// would pass a 32-bit label pool.
    fn founded_within(&self, nodes: usize, letters: usize) -> Result<(), ContextError> {
        if self.len() + nodes >= BRANCH_BIT as usize {
            return Err(shape(
                "a landmark arena within 31-bit node numbers",
                BRANCH_BIT as usize,
                self.len(),
            ));
        }
        if self.held() + letters >= u32::MAX as usize {
            return Err(shape(
                "a label pool within 32-bit indices",
                u32::MAX as usize,
                self.held(),
            ));
        }
        Ok(())
    }
}

impl Topology for Arena {
    fn root(&self, tree: usize) -> Option<u32> {
        self.roots[tree]
    }

    fn child(&self, parent: u32, letter: u32) -> Option<u32> {
        self.children.get(&key(parent, letter)).copied()
    }

    fn halves(&self, node: u32) -> [u32; 2] {
        self.halves[node as usize]
    }

    fn word(&self, node: u32) -> u32 {
        self.depths[node as usize]
    }

    fn end(&self, node: u32) -> u32 {
        self.ends[node as usize]
    }

    fn letter(&self, index: u32) -> u32 {
        self.letters[index as usize]
    }

    fn len(&self) -> usize {
        self.halves.len()
    }

    fn held(&self) -> usize {
        self.letters.len()
    }
}

impl Arena {
    fn new(trees: usize) -> Self {
        Self {
            roots: vec![None; trees],
            children: HashMap::new(),
            depths: Vec::new(),
            halves: Vec::new(),
            ends: Vec::new(),
            letters: Vec::new(),
        }
    }

    /// **Found a node** of `branch` at bottom depth `bottom` with its masses and its label end; it
    /// is linked apart ([`Arena::link`]).
    fn push(&mut self, branch: usize, bottom: usize, halves: [u32; 2], end: u32) -> u32 {
        let node = u32::try_from(self.len()).expect("the arena is checked within 31 bits");
        let depth = u32::try_from(bottom).expect("a depth within 31 bits");
        self.depths
            .push(depth | if branch == 1 { BRANCH_BIT } else { 0 });
        self.halves.push(halves);
        self.ends.push(end);
        node
    }

    /// **Link a node** as tree `t`'s root (`parent` absent) or as the child behind
    /// `(parent, letter)`, replacing what was there.
    fn link(&mut self, tree: usize, parent: Option<(u32, u32)>, child: u32) {
        match parent {
            None => self.roots[tree] = Some(child),
            Some((parent, letter)) => {
                self.children.insert(key(parent, letter), child);
            }
        }
    }

    /// **Hold a label run** in the pool, returning its end.
    fn hold(&mut self, letters: &[u32]) -> u32 {
        self.letters.extend_from_slice(letters);
        u32::try_from(self.letters.len()).expect("the pool is checked within 32 bits")
    }

    /// One arrival of `symbol` counted at the path's nodes whose bottom is at least `forced`, each
    /// register carried at the ceiling (the register's capacity).
    fn count(&mut self, nodes: &[u32], forced: usize, symbol: usize, ceiling: Option<u64>) {
        for &node in nodes {
            if self.bottom(node) >= forced {
                let halves = &mut self.halves[node as usize];
                halves[symbol] += 2;
                carry_at(ceiling, halves);
            }
        }
    }
}

/// A node to found on a standing: its branch and bottom depth, its masses, its label end and its
/// chart.
#[derive(Clone, Copy, Debug)]
struct Founded {
    branch: usize,
    bottom: usize,
    halves: [u32; 2],
    end: u32,
    chart: Chart,
}

/// **The executed tree's standing as a deposit moves it** (module header, "The arena"): the
/// stored nodes with their charts, the joins, the label pool, the rebases and the cells passed. The
/// tree's own [`Nodes`] carry it, and so does a window's working overlay ([`Working`]).
trait Standing: Topology {
    fn chart(&self, node: u32) -> &Chart;
    fn chart_mut(&mut self, node: u32) -> &mut Chart;
    fn join(&self, dyadic: usize) -> &Chart;
    fn join_mut(&mut self, dyadic: usize) -> &mut Chart;
    fn halves_mut(&mut self, node: u32) -> &mut [u32; 2];
    /// Found a node, unlinked.
    fn found(&mut self, node: Founded) -> u32;
    /// Link a node as tree `t`'s root (`parent` absent) or the child behind `(parent, letter)`.
    fn link(&mut self, tree: usize, parent: Option<(u32, u32)>, child: u32);
    /// Hold a label run in the pool, returning its end.
    fn hold(&mut self, letters: &[u32]) -> u32;
    fn passed(&self) -> u64;
    fn pass(&mut self);
    fn rebased(&mut self);
    fn released(&mut self);
}

/// The executed tree's own standing: the arena, each node's chart, each dyadic cell's join chart
/// (enlarged trees), the
/// rebases, the carrier's releases and the cells passed.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Nodes {
    arena: Arena,
    charts: Vec<Chart>,
    joins: Vec<Chart>,
    rebases: u64,
    releases: u64,
    passed: u64,
}

impl Topology for Nodes {
    fn root(&self, tree: usize) -> Option<u32> {
        self.arena.root(tree)
    }

    fn child(&self, parent: u32, letter: u32) -> Option<u32> {
        self.arena.child(parent, letter)
    }

    fn halves(&self, node: u32) -> [u32; 2] {
        self.arena.halves[node as usize]
    }

    fn word(&self, node: u32) -> u32 {
        self.arena.depths[node as usize]
    }

    fn end(&self, node: u32) -> u32 {
        self.arena.ends[node as usize]
    }

    fn letter(&self, index: u32) -> u32 {
        self.arena.letters[index as usize]
    }

    fn len(&self) -> usize {
        self.arena.len()
    }

    fn held(&self) -> usize {
        self.arena.letters.len()
    }
}

impl Standing for Nodes {
    fn chart(&self, node: u32) -> &Chart {
        &self.charts[node as usize]
    }

    fn chart_mut(&mut self, node: u32) -> &mut Chart {
        &mut self.charts[node as usize]
    }

    fn join(&self, dyadic: usize) -> &Chart {
        &self.joins[dyadic]
    }

    fn join_mut(&mut self, dyadic: usize) -> &mut Chart {
        &mut self.joins[dyadic]
    }

    fn halves_mut(&mut self, node: u32) -> &mut [u32; 2] {
        &mut self.arena.halves[node as usize]
    }

    fn found(&mut self, node: Founded) -> u32 {
        let founded = self
            .arena
            .push(node.branch, node.bottom, node.halves, node.end);
        self.charts.push(node.chart);
        founded
    }

    fn link(&mut self, tree: usize, parent: Option<(u32, u32)>, child: u32) {
        self.arena.link(tree, parent, child);
    }

    fn hold(&mut self, letters: &[u32]) -> u32 {
        self.arena.hold(letters)
    }

    fn passed(&self) -> u64 {
        self.passed
    }

    fn pass(&mut self) {
        self.passed += 1;
    }

    fn rebased(&mut self) {
        self.rebases += 1;
    }

    fn released(&mut self) {
        self.releases += 1;
    }
}

/// A node a working overlay founded: its depth word, masses, label end and chart.
#[derive(Clone, Debug)]
struct Fresh {
    word: u32,
    halves: [u32; 2],
    end: u32,
    chart: Chart,
}

/// [definition; agent-inferred] **A working overlay on the tree** (module header, "A window in
/// cell order"): the nodes and joins a window's earlier phases' deposits wrote, each copied from
/// the tree at its first write, the nodes they founded, numbered after the tree's, the links they
/// changed (a compacted split relinks a parent to its new upper part) and the label runs they held,
/// numbered after the tree's pool; every other node reads through to the tree, which is never
/// written.
#[derive(Clone, Debug)]
struct Working<'a> {
    base: &'a Nodes,
    charts: HashMap<u32, Chart>,
    joins: HashMap<usize, Chart>,
    halves: HashMap<u32, [u32; 2]>,
    founded: Vec<Fresh>,
    roots: HashMap<usize, u32>,
    children: HashMap<u64, u32>,
    letters: Vec<u32>,
    passed: u64,
}

impl<'a> Working<'a> {
    fn on(base: &'a Nodes) -> Self {
        Self {
            base,
            charts: HashMap::new(),
            joins: HashMap::new(),
            halves: HashMap::new(),
            founded: Vec::new(),
            roots: HashMap::new(),
            children: HashMap::new(),
            letters: Vec::new(),
            passed: 0,
        }
    }

    /// The index of a node the overlay founded, or `None` for a node of the tree.
    fn fresh(&self, node: u32) -> Option<usize> {
        (node as usize).checked_sub(self.base.len())
    }
}

impl Topology for Working<'_> {
    fn root(&self, tree: usize) -> Option<u32> {
        self.roots
            .get(&tree)
            .copied()
            .or_else(|| self.base.root(tree))
    }

    fn child(&self, parent: u32, letter: u32) -> Option<u32> {
        self.children
            .get(&key(parent, letter))
            .copied()
            .or_else(|| self.base.child(parent, letter))
    }

    fn halves(&self, node: u32) -> [u32; 2] {
        match self.fresh(node) {
            Some(index) => self.founded[index].halves,
            None => self
                .halves
                .get(&node)
                .copied()
                .unwrap_or_else(|| self.base.halves(node)),
        }
    }

    fn word(&self, node: u32) -> u32 {
        match self.fresh(node) {
            Some(index) => self.founded[index].word,
            None => self.base.word(node),
        }
    }

    fn end(&self, node: u32) -> u32 {
        match self.fresh(node) {
            Some(index) => self.founded[index].end,
            None => self.base.end(node),
        }
    }

    fn letter(&self, index: u32) -> u32 {
        match (index as usize).checked_sub(self.base.held()) {
            Some(own) => self.letters[own],
            None => self.base.letter(index),
        }
    }

    fn len(&self) -> usize {
        self.base.len() + self.founded.len()
    }

    fn held(&self) -> usize {
        self.base.held() + self.letters.len()
    }
}

impl Standing for Working<'_> {
    fn chart(&self, node: u32) -> &Chart {
        match self.fresh(node) {
            Some(index) => &self.founded[index].chart,
            None => self
                .charts
                .get(&node)
                .unwrap_or_else(|| self.base.chart(node)),
        }
    }

    fn chart_mut(&mut self, node: u32) -> &mut Chart {
        match self.fresh(node) {
            Some(index) => &mut self.founded[index].chart,
            None => {
                let base = self.base;
                self.charts.entry(node).or_insert_with(|| *base.chart(node))
            }
        }
    }

    fn join(&self, dyadic: usize) -> &Chart {
        self.joins
            .get(&dyadic)
            .unwrap_or_else(|| self.base.join(dyadic))
    }

    fn join_mut(&mut self, dyadic: usize) -> &mut Chart {
        let base = self.base;
        self.joins
            .entry(dyadic)
            .or_insert_with(|| *base.join(dyadic))
    }

    fn halves_mut(&mut self, node: u32) -> &mut [u32; 2] {
        match self.fresh(node) {
            Some(index) => &mut self.founded[index].halves,
            None => {
                let base = self.base;
                self.halves.entry(node).or_insert_with(|| base.halves(node))
            }
        }
    }

    fn found(&mut self, node: Founded) -> u32 {
        let founded = u32::try_from(self.len()).expect("the arena is checked within 31 bits");
        let depth = u32::try_from(node.bottom).expect("a depth within 31 bits");
        self.founded.push(Fresh {
            word: depth | if node.branch == 1 { BRANCH_BIT } else { 0 },
            halves: node.halves,
            end: node.end,
            chart: node.chart,
        });
        founded
    }

    fn link(&mut self, tree: usize, parent: Option<(u32, u32)>, child: u32) {
        match parent {
            None => {
                self.roots.insert(tree, child);
            }
            Some((parent, letter)) => {
                self.children.insert(key(parent, letter), child);
            }
        }
    }

    fn hold(&mut self, letters: &[u32]) -> u32 {
        self.letters.extend_from_slice(letters);
        u32::try_from(self.held()).expect("the pool is checked within 32 bits")
    }

    fn passed(&self) -> u64 {
        self.base.passed + self.passed
    }

    fn pass(&mut self) {
        self.passed += 1;
    }

    fn rebased(&mut self) {}

    fn released(&mut self) {}
}

fn check(
    declaration: &LandmarkDeclaration,
    address: &[Letter],
    class: usize,
) -> Result<(), ContextError> {
    if address.len() != declaration.depth {
        return Err(shape(
            "an address of the declared depth",
            declaration.depth,
            address.len(),
        ));
    }
    let alphabet = declaration.alphabet;
    if class >= alphabet {
        return Err(ContextError::CellOutside {
            code: class,
            alphabet,
        });
    }
    let family = &declaration.family;
    for letter in address {
        match *letter {
            Letter::Boundary => {}
            Letter::Cell(code) | Letter::Bundle(Bundle { cell: code, .. }) if code >= alphabet => {
                return Err(ContextError::CellOutside { code, alphabet });
            }
            Letter::Cell(_) if !family.is_empty() => {
                return Err(shape(
                    "a bundle letter of the declared family",
                    family.slots(),
                    0,
                ));
            }
            Letter::Bundle(Bundle { features, .. })
                if family.is_empty() || u64::from(features) >= family.codes() =>
            {
                return Err(shape(
                    "a bundle's features within the declared family",
                    usize::try_from(family.codes()).unwrap_or(usize::MAX),
                    features as usize,
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

fn check_declaration(declaration: &LandmarkDeclaration) -> Result<(), ContextError> {
    if declaration.alphabet < 2 || declaration.alphabet >= u32::MAX as usize / 2 {
        return Err(shape(
            "a landmark tree over at least two classes, within 31 bits",
            2,
            declaration.alphabet,
        ));
    }
    if declaration.population == 0 || declaration.grain == 0 {
        return Err(ContextError::NonpositiveDeclaration);
    }
    if declaration.population >= u64::from(u32::MAX / 2) || declaration.grain > u64::from(u32::MAX)
    {
        return Err(shape(
            "a population whose half-unit counts and a grain that fit 32 bits",
            (u32::MAX / 2) as usize,
            usize::try_from(declaration.population).unwrap_or(usize::MAX),
        ));
    }
    if declaration.forced > declaration.depth {
        return Err(shape(
            "forced splits within the address depth",
            declaration.depth,
            declaration.forced,
        ));
    }
    let largest = declaration
        .family
        .sizes()
        .iter()
        .copied()
        .max()
        .unwrap_or(0);
    if largest >= u64::from(u32::MAX) {
        return Err(shape(
            "a feature slot's letters within 32 bits",
            u32::MAX as usize,
            usize::try_from(largest).unwrap_or(usize::MAX),
        ));
    }
    Ok(())
}

// -------------------------------------------------------------------------------------------
// the executed tree

/// [definition] **One cell's reading** at the standing before its deposit: the executed face of the
/// cell, exact (a dyadic), and the certified bound on `|log₂ q̂ − log₂ q|` against the ideal tree
/// weighting, in bits (module header, "The certificate").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellReading {
    pub executed: Rat,
    pub residual: Rat,
}

/// [definition] **One opened digit's reading** ([`Landmarks::receive_digits`]): its dyadic cell
/// `h`, its digit `b`, the executed digit-0 numerator `q̂_h(0)` on `2^(−M_p)` (the observed side is
/// `q̂_h(b)`), its read certificate and its deposit's top excess increment, each on `2^(−C)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DigitReading {
    pub dyadic: usize,
    pub symbol: usize,
    pub split: u64,
    pub certificate: u128,
    pub increment: u128,
}

/// [definition] **A cell received digit by digit**: its reading and each opened digit's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DigitsReading {
    pub reading: CellReading,
    pub digits: Vec<DigitReading>,
}

/// [definition] **One opened path**: the dyadic cell `h` whose tree it descends and the branch (`0`
/// the cells, `1` the bundles), the digit it emits there, how many stored nodes it opens (its
/// levels: one a stored chain, the storage where paths part) with each level's bottom depth (a parting chain's the
/// depth where it parts), its faces `q_0, …, q_top` of that digit (the executed lattice faces from
/// [`Landmarks::opened`], the ideal ones from [`IdealLandmarks::opened`]; `top` the last level at a
/// leaf, otherwise one past it, where the prior `1/2` is read), and at each level the node's KT
/// face `k_ℓ` of the digit and its carried `β_ℓ` (a parting chain's upper part's split `β`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedPath {
    pub dyadic: usize,
    pub branch: usize,
    pub symbol: usize,
    pub founded: usize,
    pub bottoms: Vec<usize>,
    pub faces: Vec<Rat>,
    pub masses: Vec<Rat>,
    pub betas: Vec<Rat>,
}

impl OpenedPath {
    /// **The edge ratios** `R_(d→d+1) = q_(d+1)/q_d` along the path, whose logarithms are the
    /// path's additive cochain: `q_0 · Π_d R_(d→d+1) = q_f`.
    pub fn edge_ratios(&self) -> Vec<Rat> {
        self.faces
            .windows(2)
            .map(|pair| &pair[1] / &pair[0])
            .collect()
    }
}

/// [definition] **All classes' executed faces at one address**, each with its grain exponent
/// `2^(k_c) ≤ q̂(c)^(L_R) < 2^(k_c+1)`; `Σ_c q̂(c) = 1` exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkFace {
    pub grain: u64,
    pub probabilities: Vec<Rat>,
    pub exponents: Vec<BigInt>,
}

/// [definition; agent-inferred] **The splits of one address** ([`Landmarks::splits`]): at each
/// splitting dyadic cell `h` (heap-ordered, [`Landmarks::splitting`]), the executed digit-0 face's
/// numerator on `2^(−M_p)`. The class faces are their products down the dyadic heap
/// ([`LandmarkFace::of_splits`]); this is what a card's read returns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Splits {
    pub face_bits: u64,
    pub numerators: Vec<u64>,
}

impl LandmarkFace {
    /// **The all-class face from its splits** (module header, "Faces"): each class's face the
    /// product of its opened digits' splits, each grain exponent decided by the certified binary
    /// logarithm with the exact comparison as its fallback. Refused unless there is one split per
    /// splitting dyadic cell.
    pub fn of_splits(
        declaration: &LandmarkDeclaration,
        splits: &Splits,
        grain: u64,
    ) -> Result<Self, ContextError> {
        let odometer = Odometer {
            alphabet: declaration.alphabet,
            digits: odometer_digits(declaration.alphabet),
        };
        let splitting = odometer.splitting();
        if splits.numerators.len() != splitting.len() {
            return Err(shape(
                "one split per splitting dyadic cell",
                splitting.len(),
                splits.numerators.len(),
            ));
        }
        let cells = 1usize << odometer.digits;
        let mut split = vec![None; cells];
        for (&h, &zero) in splitting.iter().zip(&splits.numerators) {
            split[h] = Some(zero);
        }
        let full = 1u64 << splits.face_bits;
        // The heap over dyadic cells: each class's descent, multiplied down the splits.
        let mut numerators: Vec<Option<BigUint>> = vec![None; 2 * cells];
        let mut opened = vec![0u64; 2 * cells];
        numerators[1] = Some(BigUint::one());
        for level in 0..odometer.digits {
            for prefix in 0..(1usize << level) {
                if !odometer.holds(level, prefix) {
                    continue;
                }
                let h = (1usize << level) | prefix;
                let numerator = numerators[h].take().expect("a held cell's descent");
                match split[h] {
                    Some(zero) => {
                        for (child, side) in [(2 * h, zero), (2 * h + 1, full - zero)] {
                            numerators[child] = Some(&numerator * side);
                            opened[child] = opened[h] + 1;
                        }
                    }
                    None => {
                        opened[2 * h] = opened[h];
                        numerators[2 * h] = Some(numerator);
                    }
                }
            }
        }
        let mut probabilities = Vec::with_capacity(declaration.alphabet);
        let mut exponents = Vec::with_capacity(declaration.alphabet);
        for class in 0..declaration.alphabet {
            let leaf = cells | class;
            let numerator = numerators[leaf].take().expect("a class's descent");
            let exponent = opened[leaf] * splits.face_bits;
            exponents.push(dyadic_grain_exponent(&numerator, exponent, grain)?);
            probabilities.push(dyadic(numerator, exponent));
        }
        Ok(Self {
            grain,
            probabilities,
            exponents,
        })
    }
}

/// The executed chart of one node or join: its carried β, the cached stop weight `λ̂` (a numerator
/// of `2^(−M_p)`), its rebases, and its certificates on `2^(−C)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Chart {
    beta: Beta,
    stop: u64,
    rebases: u32,
    drift: u128,
    excess: u128,
}

/// [definition; agent-inferred] **A parting chain's two parts** (stored where paths part; Lean `Compression/Landmark/Context/Compaction.chain_split`): the read's last stored chain parts from the address at
/// `depth`; its upper part, down to `depth`, is read (and founded at the deposit) with `upper`, and
/// its lower part keeps its counts with `lower` (none when it keeps its chart: a leaf, or an upper
/// part above the forced depths). `units` is the split's rounding on `2^(−C)` (each ratio carried at
/// `W` bits, one mantissa rebase at most), added once to the increment the deposit carries up, and
/// `rebases` counts its mantissa rebases.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Parting {
    depth: usize,
    upper: Chart,
    lower: Option<Chart>,
    units: u128,
    rebases: u32,
}

/// One branch's executed read at an address: the tree it descends, where it stops, the stored
/// nodes its walk opened from the root with each level's bottom depth (the parting chain's the
/// depth where it parts), the parting chain's parts, and the lattice faces of the digit `0`,
/// `q̂_ℓ(0)` as numerators of `2^(−M_p)`, at the levels `ℓ = 0, …, top` (`top` the last node at a
/// leaf, or one past it where the prior `2^(M_p − 1)` is read). A level is a stored chain.
#[derive(Clone, Debug)]
struct LatticeRead {
    tree: usize,
    branch: usize,
    symbol: usize,
    stop: Stop,
    nodes: Vec<u32>,
    bottoms: Vec<usize>,
    parting: Option<Parting>,
    faces: Vec<u64>,
}

impl LatticeRead {
    /// Whether level `ℓ` is the parting chain's upper part.
    fn parts(&self, level: usize) -> bool {
        self.parting.is_some() && level + 1 == self.nodes.len()
    }

    /// The top depth of the leaf the arrival founds when the read stops at the prior: `0` with no
    /// root, otherwise one past the last level's bottom.
    fn leaf_top(&self) -> usize {
        self.bottoms.last().map_or(0, |bottom| bottom + 1)
    }
}

/// One digit's executed read: its dyadic cell, its digit, each branch's read and the digit-0 face
/// at the top (the join's in an enlarged tree, the cell branch's otherwise).
#[derive(Clone, Debug)]
struct DigitRead {
    dyadic: usize,
    symbol: usize,
    reads: Vec<LatticeRead>,
    face: u64,
}

/// One branch of the law: its depth in letters and its forced depths.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Branch {
    depth: usize,
    forced: usize,
}

/// The tree's law, apart from its standing: the declaration, its derived widths, the odometer, the
/// branches, the founding chart at each depth (the declared stop prior's `β₀ = 2^(j_d) − 1` with
/// its stop weight `λ̂ = ⟦1 − 2^(−j_d)⟧`), each branch's summed rungs from the root
/// (`Σ_(i<d, i ≥ forced) j_i`, a forced depth's rung `0`; the stored chains read their rungs
/// from them), and the node register's ceiling in half-units (the register's capacity, [`Capacity`]). Its reads
/// and its deposit act on any [`Standing`], the tree's own or a working overlay.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Law {
    declaration: LandmarkDeclaration,
    widths: Widths,
    odometer: Odometer,
    branches: Vec<Branch>,
    founding: Vec<Chart>,
    sums: Vec<Vec<u64>>,
    ceiling: Option<u64>,
}

/// [definition] **The landmark tree, executed** (module header): the declaration, its derived
/// widths, the arena stored at the faces where paths part with each node's chart and
/// each join, and the chart's counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Landmarks {
    law: Law,
    nodes: Nodes,
}

/// `2^k − 1`, exact.
fn ladder(rung: u64) -> BigUint {
    (BigUint::one() << rung as usize) - 1u32
}

/// **A positive ratio `(N/D) 2^e` carried at width `W`** (a split's ratio, the storage where paths part): its twos
/// moved into the exponent and its odd parts reduced; exact when both fit `W` bits, otherwise its
/// mantissa `m' = ⌊v 2^s⌋ ∈ [2^(W−1), 2^W)`, returned (the relative residual lies in `[0, 1/m')`, as
/// [`Beta::carry`]'s rebase).
fn carry_ratio(
    numerator: BigUint,
    denominator: BigUint,
    exponent: i64,
    width: u64,
) -> (Beta, Option<u128>) {
    let twos_n = numerator.trailing_zeros().expect("a positive numerator");
    let twos_d = denominator
        .trailing_zeros()
        .expect("a positive denominator");
    let reduced = Rat::new(
        BigInt::from(numerator >> twos_n as usize),
        BigInt::from(denominator >> twos_d as usize),
    );
    let (a, b) = (reduced.numer().magnitude(), reduced.denom().magnitude());
    let exponent = exponent + twos_n as i64 - twos_d as i64;
    if a.bits() <= width && b.bits() <= width {
        return (
            Beta {
                numerator: a.to_u64().expect("within W bits"),
                denominator: b.to_u64().expect("within W bits"),
                exponent,
            },
            None,
        );
    }
    let (m, shift) = mantissa(a, b, width);
    let m = m.to_u128().expect("W bits");
    let twos = m.trailing_zeros();
    (
        Beta {
            numerator: (m >> twos) as u64,
            denominator: 1,
            exponent: exponent - shift + i64::from(twos),
        },
        Some(m),
    )
}

impl Law {
    fn new(declaration: LandmarkDeclaration, widths: Widths) -> Self {
        let odometer = Odometer {
            alphabet: declaration.alphabet,
            digits: widths.digits,
        };
        let branches = declaration
            .branch_depths()
            .into_iter()
            .enumerate()
            .map(|(branch, depth)| Branch {
                depth,
                forced: if branch == 0 { declaration.forced } else { 0 },
            })
            .collect::<Vec<Branch>>();
        let deepest = branches.iter().map(|b| b.depth).max().unwrap_or(0);
        let chart_of = |ratio: u64| {
            let beta = Beta {
                numerator: ratio,
                denominator: 1,
                exponent: 0,
            };
            Chart {
                beta,
                stop: beta.stop_weight(widths.face, widths.carrier),
                rebases: 0,
                drift: 0,
                excess: 0,
            }
        };
        // `β₀ = 2^(j_d) − 1`, odd, carried exactly: within `W` bits at every mixing depth (the
        // declaration is refused otherwise), and never stepped at a leaf.
        let founding = (0..=deepest)
            .map(|depth| chart_of(declaration.prior.founding(depth)))
            .collect();
        let sums = declaration.rung_sums();
        let ceiling = declaration.capacity.ceiling_halves();
        Self {
            declaration,
            widths,
            odometer,
            branches,
            founding,
            sums,
            ceiling,
        }
    }

    fn full(&self) -> u64 {
        1u64 << self.widths.face
    }

    fn cells(&self) -> usize {
        1usize << self.widths.digits
    }

    fn joined(&self) -> bool {
        self.branches.len() > 1
    }

    /// The path depth the widths' rule reads: the declaration's `P`.
    fn path_depth(&self) -> u64 {
        self.declaration.path_depth()
    }

    /// Tree `t = branch · 2^B + h`.
    fn tree(&self, branch: usize, dyadic: usize) -> usize {
        branch * self.cells() + dyadic
    }

    /// **Each branch's letters** of an address: the cells, then the flattened bundles.
    fn flatten(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.declaration.letters(address)
    }

    /// `⟦2^M u/v⟧`: the lattice numerator nearest `u/v` (ties up), inside `[1, 2^M − 1]`.
    fn round(&self, numerator: u128, denominator: u128) -> u64 {
        lattice_round(&self.widths, numerator, denominator)
    }

    /// A certificate on `2^(−C)` in `ln`, read in bits: times `3/2 > log₂ e`.
    fn certified_bits(&self, units: u128) -> Rat {
        certified(&self.widths, units)
    }

    /// A join's fresh chart: `β = 1`, `λ̂ = 1/2`, no certificate (the join's own two-face mixture).
    fn unit(&self) -> Chart {
        Chart {
            beta: Beta::ONE,
            stop: self.full() / 2,
            rebases: 0,
            drift: 0,
            excess: 0,
        }
    }

    /// **The summed rung of a chain** from `top` to `bottom` (below the branch's depth) in `branch`:
    /// `Σ_(d = max(top, forced))^bottom j_d` (stored where paths part).
    fn rung_sum(&self, branch: usize, top: usize, bottom: usize) -> u64 {
        self.sums[branch][bottom + 1] - self.sums[branch][top]
    }

    /// **The chart a chain of summed rung `S ≥ 1` is founded with** (stored where paths part; Lean
    /// `Compression/Landmark/Context/Compaction.leaf_chain_is_one_node`): `β₀ = 2^S − 1`, carried exactly within `W`
    /// bits, otherwise as its mantissa `2^W − 1` (`⌊(2^S − 1) 2^(W−S)⌋`) times `2^(S − W)` with the
    /// rebase's unit `⌈2^C/(2^W − 1)⌉` in its drift.
    fn chain(&self, rung: u64) -> Chart {
        let Widths {
            face,
            carrier,
            certificate,
            ..
        } = self.widths;
        let (beta, units) = if rung <= carrier {
            (
                Beta {
                    numerator: (1u64 << rung) - 1,
                    denominator: 1,
                    exponent: 0,
                },
                0,
            )
        } else {
            let kept = (1u64 << carrier) - 1;
            (
                Beta {
                    numerator: kept,
                    denominator: 1,
                    exponent: (rung - carrier) as i64,
                },
                ceil_div(1u128 << certificate, u128::from(kept)),
            )
        };
        Chart {
            beta,
            stop: beta.stop_weight(face, carrier),
            rebases: u32::from(units > 0),
            drift: units,
            excess: 0,
        }
    }

    /// **A chain's split at `depth`** (stored where paths part; Lean `Compression/Landmark/Context/Compaction.chain_split`): the
    /// stored chain `node` from `top` to its bottom parts at `depth`, `S = S_up + S_low`. Above a
    /// leaf the upper part is founded at `2^(S_up) − 1` ([`Law::chain`]) and the leaf keeps its
    /// chart. Above an internal bottom, `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)` and
    /// `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low) − 1) + 2^S − 1)`, each formed exactly and
    /// carried once at `W` bits: `|ln β̂_ℓ − ln β_ℓ| ≤ Δ + 1/m'_ℓ` and, the map
    /// `β ↦ β_u` being 1-Lipschitz in `ln β`, `|ln β̂_u − ln β_u| ≤ Δ + 1/m'_u`, each `1/m' < 2^(1−W)`
    /// with `Δ` the chain's drift ([`Beta::split`]). An upper part above the forced depths
    /// (`S_up = 0`) passes its face through, and the lower part then keeps `β`.
    fn part(
        &self,
        nodes: &impl Standing,
        branch: usize,
        top: usize,
        node: u32,
        depth: usize,
    ) -> Parting {
        let Widths {
            face,
            carrier,
            certificate,
            ..
        } = self.widths;
        let bottom = nodes.bottom(node);
        let upper_rung = self.rung_sum(branch, top, depth);
        if upper_rung == 0 {
            return Parting {
                depth,
                upper: self.founding[depth],
                lower: None,
                units: 0,
                rebases: 0,
            };
        }
        if bottom == self.branches[branch].depth {
            let upper = self.chain(upper_rung);
            return Parting {
                depth,
                upper,
                lower: None,
                units: upper.drift,
                rebases: upper.rebases,
            };
        }
        let lower_rung = self.rung_sum(branch, depth + 1, bottom);
        let chart = *nodes.chart(node);
        let [upper, lower] = chart.beta.split(upper_rung, lower_rung, carrier);
        let unit = |kept: Option<u128>| kept.map_or(0, |m| ceil_div(1u128 << certificate, m));
        let (lower_units, upper_units) = (unit(lower.1), unit(upper.1));
        let chart_of = |beta: Beta, units: u128, kept: Option<u128>| Chart {
            beta,
            stop: beta.stop_weight(face, carrier),
            rebases: chart.rebases + u32::from(kept.is_some()),
            drift: chart.drift.saturating_add(units),
            excess: chart.excess,
        };
        Parting {
            depth,
            upper: chart_of(upper.0, upper_units, upper.1),
            lower: Some(chart_of(lower.0, lower_units, lower.1)),
            units: upper_units.saturating_add(lower_units),
            rebases: u32::from(upper.1.is_some()) + u32::from(lower.1.is_some()),
        }
    }

    /// The chart a read's level mixes with: the parting chain's upper part, or the node's own.
    fn level<'a>(
        &self,
        nodes: &'a impl Standing,
        read: &'a LatticeRead,
        level: usize,
    ) -> &'a Chart {
        match &read.parting {
            Some(parting) if read.parts(level) => &parting.upper,
            _ => nodes.chart(read.nodes[level]),
        }
    }

    /// The leaf's lattice face `⟦k(0)⟧`.
    fn leaf(&self, nodes: &impl Standing, node: u32) -> u64 {
        let (u, v) = nodes.kt(node, 0);
        self.round(u128::from(u) << self.widths.face, u128::from(v))
    }

    /// `⟦λ̂ u/v + (1 − λ̂) x⟧` with the stop weight `λ̂` and a lattice face `x` ([`lattice_mix`]).
    fn mix_stop(&self, stop: u64, u: u64, v: u64, below: u64) -> u64 {
        lattice_mix(&self.widths, stop, u, v, below)
    }

    /// The join's lattice face `⟦λ̂_h q̂_cells + (1 − λ̂_h) q̂_bundles⟧`.
    fn join_face(&self, nodes: &impl Standing, dyadic: usize, cells: u64, bundles: u64) -> u64 {
        lattice_blend(&self.widths, nodes.join(dyadic).stop, cells, bundles)
    }

    /// **One branch's executed read** at its letters in tree `t`: its walk, and a parting chain's
    /// split (stored where paths part).
    fn read(
        &self,
        nodes: &impl Standing,
        branch: usize,
        dyadic: usize,
        symbol: usize,
        letters: &[u32],
    ) -> LatticeRead {
        let forced = self.branches[branch].forced;
        let tree = self.tree(branch, dyadic);
        let Walk {
            nodes: path,
            parting,
            stop,
        } = nodes.walk(tree, letters);
        let mut bottoms: Vec<usize> = path.iter().map(|&node| nodes.bottom(node)).collect();
        let parting = parting.map(|depth| {
            let last = path.len() - 1;
            let top = if last > 0 { bottoms[last - 1] + 1 } else { 0 };
            bottoms[last] = depth;
            self.part(nodes, branch, top, path[last], depth)
        });
        let top = match stop {
            Stop::Node => path.len() - 1,
            Stop::Prior => path.len(),
        };
        let mut faces = vec![0u64; top + 1];
        faces[top] = match stop {
            Stop::Node => self.leaf(nodes, path[top]),
            Stop::Prior => self.full() / 2,
        };
        for level in (0..top).rev() {
            let weight = match &parting {
                Some(parting) if level + 1 == path.len() => parting.upper.stop,
                _ => nodes.chart(path[level]).stop,
            };
            faces[level] = if bottoms[level] < forced {
                faces[level + 1]
            } else {
                let (u, v) = nodes.kt(path[level], 0);
                self.mix_stop(weight, u, v, faces[level + 1])
            };
        }
        LatticeRead {
            tree,
            branch,
            symbol,
            stop,
            nodes: path,
            bottoms,
            parting,
            faces,
        }
    }

    /// **One digit's executed read**: each branch's read, joined in an enlarged tree.
    fn digit(
        &self,
        nodes: &impl Standing,
        dyadic: usize,
        symbol: usize,
        letters: &[Vec<u32>],
    ) -> DigitRead {
        let reads: Vec<LatticeRead> = (0..self.branches.len())
            .map(|branch| self.read(nodes, branch, dyadic, symbol, &letters[branch]))
            .collect();
        let face = if self.joined() {
            self.join_face(nodes, dyadic, reads[0].faces[0], reads[1].faces[0])
        } else {
            reads[0].faces[0]
        };
        DigitRead {
            dyadic,
            symbol,
            reads,
            face,
        }
    }

    /// Every digit a class opens, read at the standing.
    fn reads(&self, nodes: &impl Standing, address: &[Letter], class: usize) -> Vec<DigitRead> {
        let letters = self.flatten(address);
        self.odometer
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| self.digit(nodes, dyadic, symbol, &letters))
            .collect()
    }

    /// A lattice face of `symbol` from the digit-`0` numerator.
    fn side(&self, zero: u64, symbol: usize) -> u64 {
        if symbol == 0 {
            zero
        } else {
            self.full() - zero
        }
    }

    /// **A level's rounding bound** `θ_ℓ` of `symbol` on `2^(−C)`: `2^(−M)/min(q̂_ℓ, k_ℓ, q̂_(ℓ+1))`
    /// at a mixing level, `2^(−M−1)/min(q̂_D, k_D)` at a stored leaf, zero at a forced or unfounded
    /// level (their faces pass exactly).
    fn rounding(&self, nodes: &impl Standing, read: &LatticeRead, level: usize) -> u128 {
        let Widths {
            face, certificate, ..
        } = self.widths;
        let forced = self.branches[read.branch].forced;
        let top = read.faces.len() - 1;
        if level > top || (level == top && read.stop == Stop::Prior) {
            return 0;
        }
        if read.bottoms[level] < forced {
            return 0;
        }
        let (u, v) = nodes.kt(read.nodes[level], read.symbol);
        let here = u128::from(self.side(read.faces[level], read.symbol));
        let kt =
            |shift: u64| ceil_div(u128::from(v) << (certificate - face - shift), u128::from(u));
        if level == top {
            let lattice = ceil_div(1u128 << (certificate - 1), here);
            lattice.max(kt(1))
        } else {
            let below = u128::from(self.side(read.faces[level + 1], read.symbol));
            let lattice = ceil_div(1u128 << certificate, here.min(below));
            lattice.max(kt(0))
        }
    }

    /// **The join's rounding bound** `θ_h = 2^(−M)/min(q̂_h, q̂_cells, q̂_bundles)` on `2^(−C)`.
    fn join_rounding(&self, digit: &DigitRead) -> u128 {
        let side = |zero: u64| u128::from(self.side(zero, digit.symbol));
        let least = side(digit.face)
            .min(side(digit.reads[0].faces[0]))
            .min(side(digit.reads[1].faces[0]));
        ceil_div(1u128 << self.widths.certificate, least)
    }

    /// `ρ ≤ Σ drift + Σ θ` of one branch's read on `2^(−C)` (a parting chain's upper part carries
    /// its split's drift).
    fn certificate(&self, nodes: &impl Standing, read: &LatticeRead) -> u128 {
        let forced = self.branches[read.branch].forced;
        let mixing = read.nodes.len().min(read.faces.len() - 1);
        let drift = (0..mixing)
            .filter(|&level| read.bottoms[level] >= forced)
            .map(|level| self.level(nodes, read, level).drift)
            .fold(0u128, u128::saturating_add);
        (0..read.faces.len())
            .map(|level| self.rounding(nodes, read, level))
            .fold(drift, u128::saturating_add)
    }

    /// One digit's certificate: its branches' and, in an enlarged tree, the join's drift and
    /// rounding.
    fn digit_certificate(&self, nodes: &impl Standing, digit: &DigitRead) -> u128 {
        let branches = digit
            .reads
            .iter()
            .map(|read| self.certificate(nodes, read))
            .fold(0u128, u128::saturating_add);
        if self.joined() {
            branches
                .saturating_add(nodes.join(digit.dyadic).drift)
                .saturating_add(self.join_rounding(digit))
        } else {
            branches
        }
    }

    /// The cell's reading from its digits' reads.
    fn reading(&self, nodes: &impl Standing, digits: &[DigitRead]) -> CellReading {
        let mut numerator = BigUint::one();
        let mut certificate = 0u128;
        for digit in digits {
            numerator *= self.side(digit.face, digit.symbol);
            certificate = certificate.saturating_add(self.digit_certificate(nodes, digit));
        }
        CellReading {
            executed: dyadic(numerator, digits.len() as u64 * self.widths.face),
            residual: self.certified_bits(certificate),
        }
    }

    /// **The splits at an address** (module header, "Faces"): each splitting dyadic cell's digit-0
    /// face, heap-ordered.
    fn splits(&self, nodes: &impl Standing, address: &[Letter]) -> Splits {
        let letters = self.flatten(address);
        let numerators = self
            .odometer
            .splitting()
            .into_iter()
            .map(|dyadic| self.digit(nodes, dyadic, 0, &letters).face)
            .collect();
        Splits {
            face_bits: self.widths.face,
            numerators,
        }
    }

    /// **All classes' executed faces at an address** (module header, "Faces").
    fn face(
        &self,
        nodes: &impl Standing,
        address: &[Letter],
        grain: u64,
    ) -> Result<LandmarkFace, ContextError> {
        LandmarkFace::of_splits(&self.declaration, &self.splits(nodes, address), grain)
    }

    /// **One carried β step** on `2^(−C)`: the step `β' = β u/(v x) 2^s`, its rebase units
    /// `⌈2^C/m'⌉` and `⌈2^C/D̂⌉` (a mantissa kept, a carrier released), and whether it rebased.
    fn beta_step(&self, beta: Beta, u: u128, v: u128, x: u128, shift: i64) -> (Carried, u128) {
        carried_step(&self.widths, beta, u, v, x, shift)
    }

    /// Record a carried step's rebases on the standing and its chart.
    fn record(nodes: &mut impl Standing, carried: &Carried) -> u32 {
        if carried.mantissa.is_some() {
            nodes.rebased();
        }
        if carried.released.is_some() {
            nodes.released();
        }
        u32::from(carried.mantissa.is_some())
    }

    /// **Deposit one branch's read** on a standing: each mixing level's β steps by
    /// `k(b)/q̂_(ℓ+1)(b)` bottom-up and its certificates grow (a parting chain's upper part is
    /// stepped on its split's chart, and its split's rounding added once to the increment). Then
    /// the storage acts (stored where paths part): a parting chain is split (its upper part founded with its
    /// stepped chart and the chain's counts, its lower part keeping its counts at `β_ℓ`, the parent
    /// relinked to the upper part), and an arrival stopped at the prior founds its leaf at `D`'s
    /// `β₀`, its label ending in the cell's run `run`. Then each node's mass of the digit grows,
    /// and its register carries at the declared ceiling (the register's capacity, [`Capacity::carry`]; a stored
    /// chain is one register, since its nodes route the same arrivals). Returns the root's excess
    /// increment.
    fn apply_branch(
        &self,
        nodes: &mut impl Standing,
        letters: &[u32],
        read: LatticeRead,
        run: Option<u32>,
    ) -> u128 {
        let face = self.widths.face;
        let forced = self.branches[read.branch].forced;
        let top = read.faces.len() - 1;
        let levels = read.nodes.len();
        // The parting chain's upper part, stepped here and founded below.
        let mut upper = read.parting.map(|parting| parting.upper);
        // Bottom-up over the stored levels: θ and the rebases add to the excess, the child's
        // excess increment and the rebases to the drift.
        let mut carried = 0u128;
        for level in (0..levels).rev() {
            if read.bottoms[level] < forced {
                break;
            }
            let theta = self.rounding(nodes, &read, level);
            let node = read.nodes[level];
            let parts = read.parts(level);
            let split = match read.parting {
                Some(parting) if parts => parting.units,
                _ => 0,
            };
            let mut rebase = 0u128;
            if level < top {
                let below = self.side(read.faces[level + 1], read.symbol);
                let beta = match &upper {
                    Some(chart) if parts => chart.beta,
                    _ => nodes.chart(node).beta,
                };
                let (u, v) = nodes.kt(node, read.symbol);
                let (step, units) = self.beta_step(
                    beta,
                    u128::from(u),
                    u128::from(v),
                    u128::from(below),
                    face as i64,
                );
                rebase = units;
                let rebased = Self::record(nodes, &step);
                let chart = match upper.as_mut() {
                    Some(chart) if parts => chart,
                    _ => nodes.chart_mut(node),
                };
                chart.beta = step.beta;
                chart.stop = step.beta.stop_weight(face, self.widths.carrier);
                chart.rebases += rebased;
                chart.drift = chart.drift.saturating_add(carried).saturating_add(rebase);
            }
            let increment = theta
                .saturating_add(rebase.saturating_mul(2))
                .saturating_add(carried)
                .saturating_add(split);
            let chart = match upper.as_mut() {
                Some(chart) if parts => chart,
                _ => nodes.chart_mut(node),
            };
            chart.excess = chart.excess.saturating_add(increment);
            carried = increment;
        }
        let LatticeRead {
            tree,
            branch,
            symbol,
            stop,
            nodes: mut path,
            parting,
            ..
        } = read;
        let depth = letters.len();
        if let Some(parting) = parting {
            // The parting chain splits: its upper part is founded above its lower part.
            let chain = path.pop().expect("a parting chain");
            let at = parting.depth;
            let chain_top = path.last().map_or(0, |&parent| nodes.bottom(parent) + 1);
            let bottom = nodes.bottom(chain);
            let end = nodes.end(chain) - u32::try_from(bottom - at).expect("a depth");
            let halves = if at >= forced {
                nodes.halves(chain)
            } else {
                [1, 1]
            };
            let key = nodes.label(chain, at + 1);
            for _ in 0..parting.rebases {
                nodes.rebased();
            }
            if let Some(lower) = parting.lower {
                *nodes.chart_mut(chain) = lower;
            }
            let upper = nodes.found(Founded {
                branch,
                bottom: at,
                halves,
                end,
                chart: upper.expect("the parting chain's upper part"),
            });
            let parent = path.last().map(|&parent| (parent, letters[chain_top - 1]));
            nodes.link(tree, parent, upper);
            nodes.link(tree, Some((upper, key)), chain);
            path.push(upper);
        }
        if stop == Stop::Prior {
            // The arrival founds its leaf, labelled to the declared depth.
            let leaf_top = path.last().map_or(0, |&parent| nodes.bottom(parent) + 1);
            let leaf = nodes.found(Founded {
                branch,
                bottom: depth,
                halves: [1, 1],
                end: run.expect("an arrival's label run"),
                chart: self.founding[depth],
            });
            let parent = path.last().map(|&parent| (parent, letters[leaf_top - 1]));
            nodes.link(tree, parent, leaf);
            path.push(leaf);
        }
        for &node in &path {
            if nodes.bottom(node) >= forced {
                let halves = nodes.halves_mut(node);
                halves[symbol] += 2;
                carry_at(self.ceiling, halves);
            }
        }
        carried
    }

    /// **Deposit one cell's reads** on a standing (module header): each branch's label run (the address's letters below the shallowest leaf this cell founds in that
    /// branch, held once and shared by its leaves), then each branch's opened path, then each join's
    /// β by `q̂_cells(b)/q̂_bundles(b)` with its certificates. Returns each opened digit's top excess
    /// increment on `2^(−C)` (the join's in an enlarged tree, the cell branch root's otherwise).
    /// Refused before anything moves once the standing has passed `admitted` cells, or past 31-bit
    /// node numbers or a 32-bit label pool.
    fn apply(
        &self,
        nodes: &mut impl Standing,
        address: &[Letter],
        digits: Vec<DigitRead>,
        admitted: u64,
    ) -> Result<Vec<u128>, ContextError> {
        if nodes.passed() >= admitted {
            return Err(ContextError::PopulationReached {
                population: self.declaration.population,
            });
        }
        let letters = self.flatten(address);
        let founding: usize = letters.iter().map(|l| l.len() + 1).sum();
        let held: usize = letters.iter().map(Vec::len).sum();
        nodes.founded_within(digits.len() * founding, held)?;
        let runs: Vec<Option<u32>> = (0..self.branches.len())
            .map(|branch| {
                let top = digits
                    .iter()
                    .map(|digit| &digit.reads[branch])
                    .filter(|read| read.stop == Stop::Prior)
                    .map(LatticeRead::leaf_top)
                    .min()?;
                Some(nodes.hold(&letters[branch][top..]))
            })
            .collect();
        let face = self.widths.face;
        let mut tops = Vec::with_capacity(digits.len());
        for digit in digits {
            let theta = if self.joined() {
                self.join_rounding(&digit)
            } else {
                0
            };
            let DigitRead {
                dyadic,
                symbol,
                reads,
                ..
            } = digit;
            let sides: Vec<u64> = reads
                .iter()
                .map(|read| self.side(read.faces[0], symbol))
                .collect();
            let mut increments = 0u128;
            for read in reads {
                let branch = read.branch;
                increments = increments.saturating_add(self.apply_branch(
                    nodes,
                    &letters[branch],
                    read,
                    runs[branch],
                ));
            }
            if self.joined() {
                let beta = nodes.join(dyadic).beta;
                let (step, units) =
                    self.beta_step(beta, u128::from(sides[0]), 1, u128::from(sides[1]), 0);
                let rebased = Self::record(nodes, &step);
                let chart = nodes.join_mut(dyadic);
                chart.beta = step.beta;
                chart.stop = step.beta.stop_weight(face, self.widths.carrier);
                chart.rebases += rebased;
                chart.drift = chart.drift.saturating_add(increments).saturating_add(units);
                let increment = theta
                    .saturating_add(units.saturating_mul(2))
                    .saturating_add(increments);
                chart.excess = chart.excess.saturating_add(increment);
                tops.push(increment);
            } else {
                tops.push(increments);
            }
        }
        nodes.pass();
        Ok(tops)
    }
}

impl Landmarks {
    /// **Declare a tree**, empty: every node unfounded, so every face is uniform. Refused at an
    /// alphabet below two classes or past 31 bits, a zero population or grain, a population or
    /// grain past 32 bits, a forced depth past the address depth, derived widths whose products
    /// exceed `u128` (module header, "The carrier rebases past `u128`"), or a stop prior's rung at a
    /// mixing depth past the carrier `W` (its founding ratio `2^j − 1` would not be carried exactly).
    pub fn new(declaration: LandmarkDeclaration) -> Result<Self, ContextError> {
        check_declaration(&declaration)?;
        let widths = Widths::derived(&declaration);
        Self::with_widths(declaration, widths)
    }

    /// **Declare a tree at a declared carrier width `W`** in place of the rule's. A width below the
    /// rule's gives up the rule's place below the grain ([`Landmarks::face_rule`] reports it); the
    /// executed face stays exactly normalized and every certificate stays valid.
    pub fn with_carrier(
        declaration: LandmarkDeclaration,
        carrier: u64,
    ) -> Result<Self, ContextError> {
        check_declaration(&declaration)?;
        let widths = Widths::with_carrier(&declaration, carrier);
        Self::with_widths(declaration, widths)
    }

    fn with_widths(declaration: LandmarkDeclaration, widths: Widths) -> Result<Self, ContextError> {
        let operands = widths.operand_bits(declaration.population);
        if !(2..=63).contains(&widths.carrier)
            || widths.face > 62
            || widths.certificate > 126
            || !widths.admitted(declaration.population)
        {
            return Err(shape(
                "derived widths whose operands fit u128",
                u128::BITS as usize,
                usize::try_from(operands).unwrap_or(usize::MAX),
            ));
        }
        // The mixing depths' founding ratios are stepped on the carrier: each within `W` bits.
        let deepest = declaration.branch_depths().into_iter().max().unwrap_or(0);
        let widest = (0..deepest)
            .map(|depth| declaration.prior.rung(depth))
            .max()
            .unwrap_or(0);
        if u64::from(widest) > widths.carrier {
            return Err(shape(
                "a stop prior whose founding ratio 2^j − 1 fits the carrier's W bits",
                widths.carrier as usize,
                widest as usize,
            ));
        }
        let law = Law::new(declaration, widths);
        let trees = law.branches.len() * law.cells();
        let joins = if law.joined() {
            vec![law.unit(); law.cells()]
        } else {
            Vec::new()
        };
        Ok(Self {
            nodes: Nodes {
                arena: Arena::new(trees),
                charts: Vec::new(),
                joins,
                rebases: 0,
                releases: 0,
                passed: 0,
            },
            law,
        })
    }

    /// The label pool's letters (stored where paths part).
    pub fn held(&self) -> usize {
        self.nodes.arena.letters.len()
    }

    /// [definition] **The stored nodes of each tree** `t = branch · 2^B + h`, counted from its root
    /// through the child table (the compacted tree's `2n − 1` a tree reached by `n` arrivals).
    pub fn tree_sizes(&self) -> Vec<usize> {
        let arena = &self.nodes.arena;
        let mut children: HashMap<u32, Vec<u32>> = HashMap::new();
        for (&key, &child) in &arena.children {
            children.entry((key >> 32) as u32).or_default().push(child);
        }
        arena
            .roots
            .iter()
            .map(|root| {
                let mut stack: Vec<u32> = root.iter().copied().collect();
                let mut size = 0;
                while let Some(node) = stack.pop() {
                    size += 1;
                    if let Some(below) = children.get(&node) {
                        stack.extend(below);
                    }
                }
                size
            })
            .collect()
    }

    /// The declaration.
    pub fn declaration(&self) -> &LandmarkDeclaration {
        &self.law.declaration
    }

    /// The derived widths.
    pub fn widths(&self) -> Widths {
        self.law.widths
    }

    /// `B = ⌈log₂|A|⌉`, the odometer digits of a cell.
    pub fn digits(&self) -> u64 {
        self.law.widths.digits
    }

    /// `M_p`, the path lattice's width.
    pub fn face_bits(&self) -> u64 {
        self.law.widths.face
    }

    /// The splitting dyadic cells, heap-ordered: the order of [`Splits::numerators`].
    pub fn splitting(&self) -> Vec<usize> {
        self.law.odometer.splitting()
    }

    /// The stored nodes (stored where paths part: each a chain).
    pub fn nodes(&self) -> usize {
        self.nodes.len()
    }

    /// The cells passed (deposited).
    pub fn passed(&self) -> u64 {
        self.nodes.passed
    }

    /// **The tree's exact stored bits**: every half-unit mass `2C` (odd) as the ratio `(2C)/2`,
    /// `bits(2C) + 2`, at the nodes whose bottom is at least their branch's `forced`; at each mixing
    /// node (bottom below its branch's depth) and each join, β's odd numerator and odd denominator,
    /// `max(1, bits) + 1` each, and its exponent, `max(1, bits|e|) + 2` with its sign; each stored
    /// child's letter, `max(1, bits(letter)) + 1`; each node's bottom depth and its label end (an
    /// index into the pool), `max(1, bits) + 1` each (its label's length is the difference of its
    /// bottom from its parent's; the storage where paths part), and each letter of the label pool,
    /// `max(1, bits) + 1`; and one bit a splitting dyadic cell and branch for its root's presence.
    /// A split keeps the lower part's key letter in the pool, where the chain held it, and stores
    /// it again as the lower part's child letter, so that letter is counted twice: one letter a
    /// split. The totals (the masses' sum), the cached stop weight (read from β) and the
    /// certificates are readings kept beside them and are not counted.
    pub fn bits(&self) -> u64 {
        let slot = |value: u64| u64::from((u64::BITS - value.leading_zeros()).max(1)) + 1;
        let beta_bits = |beta: &Beta| {
            slot(beta.numerator) + slot(beta.denominator) + slot(beta.exponent.unsigned_abs()) + 1
        };
        let arena = &self.nodes.arena;
        let nodes: u64 = (0..arena.len())
            .map(|node| {
                let word = arena.depths[node];
                let branch = &self.law.branches[usize::from(word & BRANCH_BIT != 0)];
                let at = (word & !BRANCH_BIT) as usize;
                let depth = slot(at as u64) + slot(u64::from(arena.ends[node]));
                if at < branch.forced {
                    return depth;
                }
                let masses: u64 = arena.halves[node]
                    .iter()
                    .map(|&units| u64::from(u32::BITS - units.leading_zeros()) + 2)
                    .sum();
                let beta = if at < branch.depth {
                    beta_bits(&self.nodes.charts[node].beta)
                } else {
                    0
                };
                masses + beta + depth
            })
            .sum();
        let letters: u64 = arena
            .children
            .keys()
            .map(|key| slot(key & u64::from(u32::MAX)))
            .chain(arena.letters.iter().map(|&letter| slot(u64::from(letter))))
            .sum();
        let splitting = self.law.odometer.splitting();
        let joins: u64 = if self.law.joined() {
            splitting
                .iter()
                .map(|&h| beta_bits(&self.nodes.joins[h].beta))
                .sum()
        } else {
            0
        };
        nodes + letters + joins + (splitting.len() * self.law.branches.len()) as u64
    }

    /// **The β chart's report** (module header).
    pub fn chart(&self) -> ChartReport {
        let charts = self.nodes.charts.iter().chain(&self.nodes.joins);
        let (mut drift, mut node_rebases) = (0u128, 0u64);
        for chart in charts {
            drift = drift.max(chart.drift);
            node_rebases = node_rebases.max(u64::from(chart.rebases));
        }
        ChartReport {
            carrier: self.law.widths.carrier,
            rebases: self.nodes.rebases,
            node_rebases,
            released: self.nodes.releases,
            drift: self.law.certified_bits(drift),
        }
    }

    /// **The rule's a-priori bound per cell**, in bits (module header, "The widths"):
    /// `(1 + 2^(−min(M_p, W))) (3/2) B [(n* P² + 2P + 1) ε/μ̂ + (2n* + 1) P² 2^(1−W) + n* P² ρ_c]`
    /// with `ε/μ̂ = 1/(2⌊2^(M_p)/K⌋)`, `K = 2n* + 2`, and `ρ_c = 2^(1−R)` when the carrier rebases
    /// (else `0`). [proved-derived; agent-inferred] Stored where paths part, each
    /// split rounds its two ratios once at `W` bits (`Law::part`: each `1/m' < 2^(1−W)`): an arrival
    /// splits at most one chain in each digit tree it opens, and adds the split's units once to its
    /// increment (a further rebase of that arrival at one level), and a stored node's lineage is
    /// split at most `D ≤ P` times, each time adding one unit to its drift; so the mantissa term
    /// reads `(2n* + 1) P² 2^(1−W)`, which the derived `W` holds within a quarter grain
    /// ([`carrier_width`]). At the derived widths the rule is at most `(1 + 2^(−min(M_p, W))) · 3/4`
    /// of a grain, and `· 1/2` without the carrier's rebase.
    pub fn face_rule(&self) -> Rat {
        let Widths {
            digits,
            face,
            carrier,
            rebase,
            ..
        } = self.law.widths;
        let declaration = &self.law.declaration;
        let (n, d) = (
            BigInt::from(declaration.population),
            BigInt::from(self.law.path_depth()),
        );
        let paths = &n * &d * &d;
        let floor = (BigInt::one() << face as usize)
            / BigInt::from(floor_reciprocal(declaration.population));
        let rounding = Rat::new(&paths + &d * 2 + 1, floor * 2);
        let splits = &paths + &d * &d;
        let mut rebases = Rat::from_integer(&paths + splits) * two_power(1 - carrier as i64);
        if rebase > 0 {
            rebases += Rat::from_integer(paths) * two_power(1 - rebase as i64);
        }
        let grid = Rat::one() + two_power(-(face.min(carrier) as i64));
        grid * log2_e_bound() * Rat::from_integer(BigInt::from(digits)) * (rounding + rebases)
    }

    /// **The executed face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, ContextError> {
        Ok(self.score(address, class)?.executed)
    }

    /// **Score one class** at an address at the current standing: its executed face and its
    /// certified residual, with nothing deposited.
    pub fn score(&self, address: &[Letter], class: usize) -> Result<CellReading, ContextError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        Ok(self.law.reading(&self.nodes, &reads))
    }

    /// **Score one class digit by digit** at an address at the current standing, with nothing
    /// deposited: [`Self::receive_digits`]'s reading and each opened digit's dyadic cell, digit,
    /// executed digit-0 numerator and certificate (its increment zero: nothing is deposited). The
    /// admitted receivers read a located class's face within the bytes from it
    /// (`receiver::population::admitted`).
    pub fn score_digits(
        &self,
        address: &[Letter],
        class: usize,
    ) -> Result<DigitsReading, ContextError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        let reading = self.law.reading(&self.nodes, &reads);
        let digits = reads
            .iter()
            .map(|digit| DigitReading {
                dyadic: digit.dyadic,
                symbol: digit.symbol,
                split: digit.face,
                certificate: self.law.digit_certificate(&self.nodes, digit),
                increment: 0,
            })
            .collect();
        Ok(DigitsReading { reading, digits })
    }

    /// **The opened paths of one class** at an address, with their executed lattice faces: per
    /// opened digit, each branch's path.
    pub fn opened(
        &self,
        address: &[Letter],
        class: usize,
    ) -> Result<Vec<OpenedPath>, ContextError> {
        check(&self.law.declaration, address, class)?;
        let law = &self.law;
        let scale = BigInt::one() << law.widths.face as usize;
        Ok(law
            .reads(&self.nodes, address, class)
            .into_iter()
            .flat_map(|digit| {
                let dyadic = digit.dyadic;
                digit.reads.into_iter().map(move |read| (dyadic, read))
            })
            .map(|(dyadic, read)| OpenedPath {
                dyadic,
                branch: read.branch,
                symbol: read.symbol,
                founded: read.nodes.len(),
                bottoms: read.bottoms.clone(),
                faces: read
                    .faces
                    .iter()
                    .map(|&zero| Rat::new(BigInt::from(law.side(zero, read.symbol)), scale.clone()))
                    .collect(),
                masses: read
                    .nodes
                    .iter()
                    .map(|&node| {
                        let (u, v) = self.nodes.kt(node, read.symbol);
                        Rat::new(BigInt::from(u), BigInt::from(v))
                    })
                    .collect(),
                betas: (0..read.nodes.len())
                    .map(|level| law.level(&self.nodes, &read, level).beta.value())
                    .collect(),
            })
            .collect())
    }

    /// **The splits at an address** (module header, "Faces"): each splitting dyadic cell's
    /// executed digit-0 numerator, heap-ordered.
    pub fn splits(&self, address: &[Letter]) -> Result<Splits, ContextError> {
        check(&self.law.declaration, address, 0)?;
        Ok(self.law.splits(&self.nodes, address))
    }

    /// **All classes' executed faces at an address**, with their grain exponents at `grain`
    /// (module header, "Faces").
    pub fn face(&self, address: &[Letter], grain: u64) -> Result<LandmarkFace, ContextError> {
        check(&self.law.declaration, address, 0)?;
        self.law.face(&self.nodes, address, grain)
    }

    /// [definition; agent-inferred] **A window's standings in cell order** (module header, "A
    /// window in cell order"; prequential scoring within a window): phase `j` reads the tree at
    /// `addresses[j]` at the standing after the deposits of the phases before it whose classes are
    /// known (`known[i]` at `addresses[i]`, `i < j`), each on a working overlay of the nodes those
    /// deposits wrote, built here in cell order; the tree itself is unchanged. With nothing known
    /// every phase reads the current standing. Each phase's read ([`Window::splits`],
    /// [`Window::face`]) reads its own overlay and writes nothing, so a reader may run the phases
    /// together (the HNN's host realization does, `hnn::receiving::window_faces`). Refused at an
    /// address or class outside the declaration.
    pub fn window<'a>(
        &'a self,
        addresses: &'a [Vec<Letter>],
        known: &[usize],
    ) -> Result<Window<'a>, ContextError> {
        let law = &self.law;
        for address in addresses {
            check(&law.declaration, address, 0)?;
        }
        let deposits = known.len().min(addresses.len().saturating_sub(1));
        for (address, &class) in addresses.iter().zip(known).take(deposits) {
            check(&law.declaration, address, class)?;
        }
        let admitted = self.working_admission(deposits as u64);
        let mut working = Working::on(&self.nodes);
        let mut standings = Vec::with_capacity(deposits);
        for (address, &class) in addresses.iter().zip(known).take(deposits) {
            let reads = law.reads(&working, address, class);
            law.apply(&mut working, address, reads, admitted)?;
            standings.push(working.clone());
        }
        Ok(Window {
            law,
            nodes: &self.nodes,
            addresses,
            standings,
        })
    }

    /// [agent-inferred] **The arrivals a working overlay admits**: the declared population, and
    /// past it the window's own earlier cells (a deposit's re-read at its successor reads the
    /// window's cells again) while the widths' operands at that count still fit `u128`. A working
    /// read's faces are exact executed faces, normalized for any stop weight; its certificates are
    /// not read.
    fn working_admission(&self, deposits: u64) -> u64 {
        let population = self.law.declaration.population;
        let reach = population + deposits;
        if reach < u64::from(u32::MAX / 2) && self.law.widths.admitted(reach) {
            reach
        } else {
            population
        }
    }

    /// **Deposit one cell** on the paths it opens, read at the current standing (module header):
    /// each mixing chain's β steps by `k(b)/q̂_(ℓ+1)(b)` bottom-up and its certificates grow, a
    /// chain the address parts from splits (stored where paths part) and the arrival founds its leaf, then each
    /// node's mass of the digit grows, and each join's β steps. Refused before anything moves at a
    /// bad address or class, or past the declared population.
    pub fn deposit(&mut self, address: &[Letter], class: usize) -> Result<(), ContextError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        let population = self.law.declaration.population;
        self.law
            .apply(&mut self.nodes, address, reads, population)
            .map(|_| ())
    }

    /// **Receive one cell**: score it at the current standing, then deposit it.
    pub fn receive(
        &mut self,
        address: &[Letter],
        class: usize,
    ) -> Result<CellReading, ContextError> {
        Ok(self.receive_digits(address, class)?.reading)
    }

    /// **Receive one cell, digit by digit** (the development harness's and a join's reading): the
    /// cell's reading, and per opened digit its dyadic cell, its digit, its executed digit-0
    /// numerator on `2^(−M_p)`, its certificate and the deposit's top excess increment on `2^(−C)`.
    pub fn receive_digits(
        &mut self,
        address: &[Letter],
        class: usize,
    ) -> Result<DigitsReading, ContextError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        let reading = self.law.reading(&self.nodes, &reads);
        let digits: Vec<DigitReading> = reads
            .iter()
            .map(|digit| DigitReading {
                dyadic: digit.dyadic,
                symbol: digit.symbol,
                split: digit.face,
                certificate: self.law.digit_certificate(&self.nodes, digit),
                increment: 0,
            })
            .collect();
        let population = self.law.declaration.population;
        let increments = self
            .law
            .apply(&mut self.nodes, address, reads, population)?;
        Ok(DigitsReading {
            reading,
            digits: digits
                .into_iter()
                .zip(increments)
                .map(|(digit, increment)| DigitReading { increment, ..digit })
                .collect(),
        })
    }

    /// **The stored nodes and joins a deposit writes** (the mirror's per-deposit lockstep), read at
    /// the current standing before it: every stored node of every branch's walk of every digit
    /// `class` opens at `address` (their masses and charts step, and a parting chain's lower part
    /// takes `β_ℓ`), and the opened dyadic cells (whose joins an enlarged tree steps). The nodes the
    /// deposit founds (the parting chains' upper parts and the leaves) are numbered after the stored
    /// ones. Each sorted, without repeats.
    pub fn touched(
        &self,
        address: &[Letter],
        class: usize,
    ) -> Result<(Vec<u32>, Vec<usize>), ContextError> {
        check(&self.law.declaration, address, class)?;
        let (mut nodes, mut dyadic) = (Vec::new(), Vec::new());
        for digit in self.law.reads(&self.nodes, address, class) {
            dyadic.push(digit.dyadic);
            for read in digit.reads {
                nodes.extend(read.nodes);
            }
        }
        nodes.sort_unstable();
        nodes.dedup();
        dyadic.sort_unstable();
        dyadic.dedup();
        Ok((nodes, dyadic))
    }

    /// **The arena as flat words** (module header, "The arena"; the layout the card ports): the
    /// roots per tree (`u32::MAX` unfounded), the children as `(key, child)` pairs, each node's
    /// depth word, label end and masses, the label pool, each node's chart `(β_n, β_d, β_e, λ̂)`,
    /// and each join's.
    pub fn arena(&self) -> ArenaView<'_> {
        ArenaView { tree: self }
    }
}

/// [definition; agent-inferred] **A window's standings in cell order** ([`Landmarks::window`]):
/// the window's addresses, and for each phase after the first whose predecessors' classes are
/// known, the working overlay of their deposits over the published tree, which is never written.
pub struct Window<'a> {
    law: &'a Law,
    nodes: &'a Nodes,
    addresses: &'a [Vec<Letter>],
    standings: Vec<Working<'a>>,
}

impl Window<'_> {
    /// The window's phases.
    pub fn phases(&self) -> usize {
        self.addresses.len()
    }

    /// **Phase `j`'s splits** (the quantity a card's read returns), at the standing after the
    /// window's earlier known phases' deposits.
    pub fn splits(&self, phase: usize) -> Splits {
        match phase.min(self.standings.len()).checked_sub(1) {
            Some(index) => self
                .law
                .splits(&self.standings[index], &self.addresses[phase]),
            None => self.law.splits(self.nodes, &self.addresses[phase]),
        }
    }

    /// **Phase `j`'s all-class face** at `grain`, from its splits ([`LandmarkFace::of_splits`]).
    pub fn face(&self, phase: usize, grain: u64) -> Result<LandmarkFace, ContextError> {
        LandmarkFace::of_splits(&self.law.declaration, &self.splits(phase), grain)
    }
}

/// [definition] **A read-only view of the executed arena** ([`Landmarks::arena`]), for a device
/// realization that mirrors the tree.
#[derive(Clone, Copy, Debug)]
pub struct ArenaView<'a> {
    tree: &'a Landmarks,
}

/// One node's or join's chart as words: `β`'s odd numerator, odd denominator and exponent, and the
/// stop weight's numerator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartWords {
    pub numerator: u64,
    pub denominator: u64,
    pub exponent: i64,
    pub stop: u64,
}

impl ArenaView<'_> {
    /// The trees, `branches · 2^B`.
    pub fn trees(&self) -> usize {
        self.tree.nodes.arena.roots.len()
    }

    /// The branches' depths in letters.
    pub fn branch_depths(&self) -> Vec<usize> {
        self.tree.law.branches.iter().map(|b| b.depth).collect()
    }

    /// The cell branch's forced depths.
    pub fn forced(&self) -> usize {
        self.tree.law.branches[0].forced
    }

    /// Each tree's root, `u32::MAX` unfounded.
    pub fn roots(&self) -> Vec<u32> {
        self.tree
            .nodes
            .arena
            .roots
            .iter()
            .map(|root| root.unwrap_or(u32::MAX))
            .collect()
    }

    /// The child table as `(parent << 32 | letter, child)` pairs of founded children, in no order.
    pub fn children(&self) -> Vec<(u64, u32)> {
        self.tree
            .nodes
            .arena
            .children
            .iter()
            .map(|(&key, &child)| (key, child))
            .collect()
    }

    /// Each node's two half-unit masses.
    pub fn halves(&self) -> &[[u32; 2]] {
        &self.tree.nodes.arena.halves
    }

    /// Each node's depth word: its bottom depth, its branch (the bundle tree) in the top bit.
    pub fn words(&self) -> &[u32] {
        &self.tree.nodes.arena.depths
    }

    /// Each node's label end: one past its bottom's letter in the label pool (stored where paths part).
    pub fn ends(&self) -> &[u32] {
        &self.tree.nodes.arena.ends
    }

    /// The label pool's letters: each node's label, the letters below its top to its bottom, ends
    /// at its label end.
    pub fn labels(&self) -> &[u32] {
        &self.tree.nodes.arena.letters
    }

    /// Each node's chart.
    pub fn charts(&self) -> Vec<ChartWords> {
        self.tree.nodes.charts.iter().map(chart_words).collect()
    }

    /// Each dyadic cell's join chart (empty unless enlarged).
    pub fn joins(&self) -> Vec<ChartWords> {
        self.tree.nodes.joins.iter().map(chart_words).collect()
    }

    /// One node's chart; `None` past the founded nodes.
    pub fn chart(&self, node: u32) -> Option<ChartWords> {
        self.tree.nodes.charts.get(node as usize).map(chart_words)
    }

    /// One dyadic cell's join chart; `None` unless enlarged.
    pub fn join(&self, dyadic: usize) -> Option<ChartWords> {
        self.tree.nodes.joins.get(dyadic).map(chart_words)
    }

    /// **The chart a node is founded with at its depth** (the declared stop prior): the declared stop prior's
    /// `β₀ = 2^(j_d) − 1` and its stop weight `λ̂ = ⟦1 − 2^(−j_d)⟧`; `None` past the deepest branch.
    pub fn founding(&self, depth: usize) -> Option<ChartWords> {
        self.tree.law.founding.get(depth).map(chart_words)
    }

    /// Each branch's letters of an address (the cells, then the flattened bundles).
    pub fn letters(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.tree.law.flatten(address)
    }
}

fn chart_words(chart: &Chart) -> ChartWords {
    let (numerator, denominator, exponent) = chart.beta.parts();
    ChartWords {
        numerator,
        denominator,
        exponent,
        stop: chart.stop,
    }
}

// -------------------------------------------------------------------------------------------
// dyadic faces: the certified binary logarithm

/// A dyadic `numerator/2^exponent`, reduced.
fn dyadic(numerator: BigUint, exponent: u64) -> Rat {
    let twos = numerator.trailing_zeros().unwrap_or(0).min(exponent);
    Rat::new_raw(
        BigInt::from(numerator >> twos),
        BigInt::one() << (exponent - twos) as usize,
    )
}

/// [definition; agent-inferred] **The fixed point of the binary logarithm's squaring**: `P`
/// fraction bits for `y ∈ [1, 2]`, the widest with `y² ≤ 4` held in `P + 3 ≤ 128` bits.
const FIXED: u32 = u128::BITS - 3;

/// `(hi, lo)` with `a b = hi 2^128 + lo`.
fn wide_mul(a: u128, b: u128) -> (u128, u128) {
    let mask = u128::from(u64::MAX);
    let (a1, a0, b1, b0) = (a >> 64, a & mask, b >> 64, b & mask);
    let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
    let middle = (p00 >> 64) + (p01 & mask) + (p10 & mask);
    (
        p11 + (p01 >> 64) + (p10 >> 64) + (middle >> 64),
        (p00 & mask) | (middle << 64),
    )
}

/// `⌊x²/2^P⌋` and `⌈x²/2^P⌉` for `x ≤ 2^(P+1) + 1`.
fn square(x: u128) -> (u128, u128) {
    let (hi, lo) = wide_mul(x, x);
    let floor = (hi << (u128::BITS - FIXED)) | (lo >> FIXED);
    let exact = lo & ((1u128 << FIXED) - 1) == 0;
    (floor, floor + u128::from(!exact))
}

/// [definition; agent-inferred] **A certified binary logarithm** of a positive integer `m`:
/// `log₂ m ∈ [whole + fraction/2^bits, whole + (fraction + 1)/2^bits]`, exactly `whole` when `m`
/// is a power of two (`exact`), and otherwise strictly inside (it is then irrational).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryLog {
    pub whole: u64,
    pub fraction: u128,
    pub bits: u32,
    pub exact: bool,
}

/// **The binary logarithm by exact squaring** (agent-inferred; the invariant's Lean statement is
/// owed in #62): `y = m/2^whole ∈ [1, 2)` is held between two fixed-point integers on `2^(−P)`,
/// rounded outward; each step squares both, and a bit is emitted only when both bounds agree on
/// `y² ≥ 2` (then both halve, outward). It stops at `bits` fraction bits, when `decided` accepts,
/// or when the bounds straddle `2` (a shorter, still certified enclosure). At most 128 bits.
pub fn binary_log(
    m: &BigUint,
    bits: u32,
    mut decided: impl FnMut(&BinaryLog) -> bool,
) -> BinaryLog {
    debug_assert!(!m.is_zero() && bits <= u128::BITS);
    let whole = m.bits() - 1;
    let mut log = BinaryLog {
        whole,
        fraction: 0,
        bits: 0,
        exact: m.count_ones() == 1,
    };
    if log.exact {
        return log;
    }
    let fixed = u64::from(FIXED);
    let (mut lower, mut upper) = if whole <= fixed {
        let y = (m << (fixed - whole) as usize)
            .to_u128()
            .expect("P + 1 bits");
        (y, y)
    } else {
        let shifted = m >> (whole - fixed) as usize;
        let y = shifted.to_u128().expect("P + 1 bits");
        (y, y + 1)
    };
    let two = 1u128 << (FIXED + 1);
    while log.bits < bits && !decided(&log) {
        let (low, _) = square(lower);
        let (_, high) = square(upper);
        let bit = if low >= two {
            true
        } else if high < two {
            false
        } else {
            break;
        };
        log.fraction = (log.fraction << 1) | u128::from(bit);
        log.bits += 1;
        (lower, upper) = if bit {
            (low >> 1, (high + 1) >> 1)
        } else {
            (low, high)
        };
    }
    log
}

/// `⌊L log₂ m⌋`, decided by the certified binary logarithm within 64 fraction bits (every operand
/// within `u128` for `L < 2^32` and `m` of fewer than `2^31` bits), or `None`.
fn grain_floor(m: &BigUint, grain: u64) -> Option<BigInt> {
    if grain == 0 {
        return Some(BigInt::zero());
    }
    let limit = u32::BITS - 1;
    if grain > u64::from(u32::MAX) || m.bits() > 1u64 << limit {
        return None;
    }
    let floors = |log: &BinaryLog| {
        let base = (u128::from(log.whole) << log.bits) | log.fraction;
        let grain = u128::from(grain);
        (
            (grain * base) >> log.bits,
            (grain * (base + 1) - 1) >> log.bits,
        )
    };
    let log = binary_log(m, u64::BITS, |log| {
        let (lower, upper) = floors(log);
        lower == upper
    });
    if log.exact {
        return Some(BigInt::from(log.whole) * grain);
    }
    let (lower, upper) = floors(&log);
    (lower == upper).then(|| BigInt::from(lower))
}

/// **The grain exponent of a dyadic face** `m/2^J` at `L`: `⌊L log₂ m⌋ − L J`, decided by the
/// certified binary logarithm, the exact comparison (`grain_exponent`) when it does not decide.
fn dyadic_grain_exponent(
    numerator: &BigUint,
    exponent: u64,
    grain: u64,
) -> Result<BigInt, ContextError> {
    match grain_floor(numerator, grain) {
        Some(floor) => Ok(floor - BigInt::from(grain) * BigInt::from(exponent)),
        None => Ok(grain_exponent(
            numerator,
            &(BigUint::one() << exponent as usize),
            grain,
        )?),
    }
}

// -------------------------------------------------------------------------------------------
// the reference oracle

/// [definition] **The ideal tree weighting, the reference oracle** (module header): the executed
/// tree's arena, stored at the faces where paths part, with `β` in ℚ and every path
/// face exact: along an opened path `q_top = k` at a leaf (`½` past the last stored level),
/// `q_ℓ = (β_ℓ k_ℓ + q_(ℓ+1))/(1 + β_ℓ)` at each stored chain, the deposit `β' = β k/q_(ℓ+1)` on the
/// exact faces, and in an enlarged tree each join `q_h = (β_h q_cells + q_bundles)/(1 + β_h)` from
/// `β_h = 1`, `β'_h = β_h q_cells/q_bundles`. Each stored chain is one node at its summed rung,
/// split exactly in ℚ (`β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`,
/// `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low) − 1) + 2^S − 1)`, `2^(S_up) − 1` above a leaf):
/// its faces are the full tree's (one node a depth, each founded at `β₀ = 2^(j_d) − 1`),
/// exactly (`compacted_is_the_full_tree`; the tests hold it against a full reference kept in
/// `hnn/tests`). Each node's register carries at the declared capacity as the executed tree's does
/// (the register's capacity; `compacted_node_law`). With no width `β` is exact (the tests); at a width it is
/// rebased past it with the residual `1/m'`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdealLandmarks {
    declaration: LandmarkDeclaration,
    odometer: Odometer,
    branches: Vec<Branch>,
    sums: Vec<Vec<u64>>,
    arena: Arena,
    beta: Vec<Rat>,
    joins: Vec<Rat>,
    width: Option<u64>,
    rebases: u64,
}

/// One branch's ideal read: where it stops, the stored nodes with each level's bottom (the parting
/// chain's the depth where it parts), the parting chain's upper and lower ratios (none kept below
/// when the lower part keeps its `β`), and the faces.
struct IdealRead {
    branch: usize,
    stop: Stop,
    nodes: Vec<u32>,
    bottoms: Vec<usize>,
    parting: Option<(usize, Rat, Option<Rat>)>,
    faces: Vec<Rat>,
}

impl IdealRead {
    fn parts(&self, level: usize) -> bool {
        self.parting.is_some() && level + 1 == self.nodes.len()
    }
}

struct IdealDigit {
    dyadic: usize,
    symbol: usize,
    reads: Vec<IdealRead>,
    face: Rat,
}

impl IdealLandmarks {
    /// **Declare the oracle**, empty, with `β` exact (`width = None`) or carried at a width.
    pub fn new(declaration: LandmarkDeclaration, width: Option<u64>) -> Result<Self, ContextError> {
        check_declaration(&declaration)?;
        let digits = odometer_digits(declaration.alphabet);
        let branches: Vec<Branch> = declaration
            .branch_depths()
            .into_iter()
            .enumerate()
            .map(|(branch, depth)| Branch {
                depth,
                forced: if branch == 0 { declaration.forced } else { 0 },
            })
            .collect();
        let cells = 1usize << digits;
        let joins = if branches.len() > 1 {
            vec![Rat::one(); cells]
        } else {
            Vec::new()
        };
        Ok(Self {
            odometer: Odometer {
                alphabet: declaration.alphabet,
                digits,
            },
            arena: Arena::new(branches.len() * cells),
            sums: declaration.rung_sums(),
            branches,
            declaration,
            beta: Vec::new(),
            joins,
            width,
            rebases: 0,
        })
    }

    /// The stored nodes.
    pub fn nodes(&self) -> usize {
        self.arena.len()
    }

    /// [definition; agent-inferred] **The reference width** `W_o = O + ⌈log₂(3 B n*² P²)⌉`: the
    /// oracle's rebases move a cell's code length by at most `(3/2) B n* P² 2^(1−W_o)` bits
    /// (the executed chart's drift rule with no rounding), so by at most `2^(−O)` over the passage.
    pub fn reference_width(declaration: &LandmarkDeclaration) -> u64 {
        let (n, d) = (
            BigUint::from(declaration.population),
            BigUint::from(declaration.path_depth()),
        );
        let digits = BigUint::from(odometer_digits(declaration.alphabet));
        u64::from(LOG_OCTAVES) + ceil_log2(&(BigUint::from(3u32) * digits * &n * &n * &d * &d))
    }

    /// The oracle's own rule per cell, in bits: `(3/2) B n* P² 2^(1−W_o)` (zero with `β` exact).
    pub fn drift_rule(&self) -> Rat {
        let Some(width) = self.width else {
            return Rat::zero();
        };
        let (n, d) = (
            BigInt::from(self.declaration.population),
            BigInt::from(self.declaration.path_depth()),
        );
        log2_e_bound()
            * Rat::from_integer(BigInt::from(self.odometer.digits) * n * &d * &d)
            * two_power(1 - width as i64)
    }

    /// The rebases so far.
    pub fn rebases(&self) -> u64 {
        self.rebases
    }

    fn kt(&self, node: u32, symbol: usize) -> Rat {
        let (u, v) = self.arena.kt(node, symbol);
        Rat::new(BigInt::from(u), BigInt::from(v))
    }

    fn flatten(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.declaration.letters(address)
    }

    /// The ratio `2^k − 1`.
    fn ladder_ratio(rung: u64) -> Rat {
        Rat::from_integer(BigInt::from(ladder(rung)))
    }

    /// **A chain's split in ℚ** (stored where paths part; the executed [`Law::part`], exact): the stored chain
    /// `node` from `top` parts at `depth`; returns the upper part's `β` and the lower part's (none
    /// when it keeps its `β`: a leaf, or an upper part above the forced depths, whose ratio is
    /// never read).
    fn split(&self, branch: usize, top: usize, node: u32, depth: usize) -> (Rat, Option<Rat>) {
        let bottom = self.arena.bottom(node);
        let upper_rung = self.sums[branch][depth + 1] - self.sums[branch][top];
        if upper_rung == 0 {
            let founding = self.declaration.prior.founding(depth);
            return (Rat::from_integer(BigInt::from(founding)), None);
        }
        if bottom == self.branches[branch].depth {
            return (Self::ladder_ratio(upper_rung), None);
        }
        let lower_rung = self.sums[branch][bottom + 1] - self.sums[branch][depth + 1];
        let beta = &self.beta[node as usize];
        let (up, low, whole) = (
            Self::ladder_ratio(upper_rung),
            Self::ladder_ratio(lower_rung),
            Self::ladder_ratio(upper_rung + lower_rung),
        );
        let lower = beta * &low / &whole;
        let upper = up * two_power(lower_rung as i64) * beta / (beta * &low + &whole);
        (upper, Some(lower))
    }

    fn read(&self, branch: usize, dyadic: usize, symbol: usize, letters: &[u32]) -> IdealRead {
        let Branch { forced, .. } = self.branches[branch];
        let tree = branch * (1usize << self.odometer.digits) + dyadic;
        let Walk {
            nodes,
            parting,
            stop,
        } = self.arena.walk(tree, letters);
        let mut bottoms: Vec<usize> = nodes.iter().map(|&n| self.arena.bottom(n)).collect();
        let parting = parting.map(|depth| {
            let last = nodes.len() - 1;
            let top = if last > 0 { bottoms[last - 1] + 1 } else { 0 };
            bottoms[last] = depth;
            let (upper, lower) = self.split(branch, top, nodes[last], depth);
            (depth, upper, lower)
        });
        let top = match stop {
            Stop::Node => nodes.len() - 1,
            Stop::Prior => nodes.len(),
        };
        let mut faces = vec![Rat::new(BigInt::one(), BigInt::from(2)); top + 1];
        if stop == Stop::Node {
            faces[top] = self.kt(nodes[top], symbol);
        }
        for level in (0..top).rev() {
            faces[level] = if bottoms[level] < forced {
                faces[level + 1].clone()
            } else {
                let beta = match &parting {
                    Some((_, upper, _)) if level + 1 == nodes.len() => upper,
                    _ => &self.beta[nodes[level] as usize],
                };
                (beta * self.kt(nodes[level], symbol) + &faces[level + 1]) / (Rat::one() + beta)
            };
        }
        IdealRead {
            branch,
            stop,
            nodes,
            bottoms,
            parting,
            faces,
        }
    }

    fn reads(&self, address: &[Letter], class: usize) -> Vec<IdealDigit> {
        let letters = self.flatten(address);
        self.odometer
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| {
                let reads: Vec<IdealRead> = (0..self.branches.len())
                    .map(|branch| self.read(branch, dyadic, symbol, &letters[branch]))
                    .collect();
                let face = if reads.len() > 1 {
                    let beta = &self.joins[dyadic];
                    (beta * &reads[0].faces[0] + &reads[1].faces[0]) / (Rat::one() + beta)
                } else {
                    reads[0].faces[0].clone()
                };
                IdealDigit {
                    dyadic,
                    symbol,
                    reads,
                    face,
                }
            })
            .collect()
    }

    /// **The ideal face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, ContextError> {
        check(&self.declaration, address, class)?;
        Ok(self
            .reads(address, class)
            .iter()
            .map(|digit| digit.face.clone())
            .product())
    }

    /// **The opened paths of one class** at an address, with their ideal faces (a level a stored
    /// node; a parting chain's upper part carries its split `β`).
    pub fn opened(
        &self,
        address: &[Letter],
        class: usize,
    ) -> Result<Vec<OpenedPath>, ContextError> {
        check(&self.declaration, address, class)?;
        let mut paths = Vec::new();
        for digit in self.reads(address, class) {
            for read in digit.reads {
                let betas = (0..read.nodes.len())
                    .map(|level| match &read.parting {
                        Some((_, upper, _)) if read.parts(level) => upper.clone(),
                        _ => self.beta[read.nodes[level] as usize].clone(),
                    })
                    .collect();
                paths.push(OpenedPath {
                    dyadic: digit.dyadic,
                    branch: read.branch,
                    symbol: digit.symbol,
                    founded: read.nodes.len(),
                    bottoms: read.bottoms.clone(),
                    masses: read
                        .nodes
                        .iter()
                        .map(|&node| self.kt(node, digit.symbol))
                        .collect(),
                    betas,
                    faces: read.faces,
                });
            }
        }
        Ok(paths)
    }

    /// A ratio carried at the oracle's width, its rebase counted.
    fn carry(&mut self, value: &Rat) -> Rat {
        let (carried, rebased) = carried_ratio(value, self.width);
        self.rebases += u64::from(rebased);
        carried
    }

    /// **Receive one cell**: its ideal face at the current standing, then its deposit.
    pub fn receive(&mut self, address: &[Letter], class: usize) -> Result<Rat, ContextError> {
        check(&self.declaration, address, class)?;
        let digits = self.reads(address, class);
        let letters = self.flatten(address);
        let founding: usize = letters.iter().map(|l| l.len() + 1).sum();
        let held: usize = letters.iter().map(Vec::len).sum();
        self.arena.founded_within(digits.len() * founding, held)?;
        let face = digits.iter().map(|digit| digit.face.clone()).product();
        let cells = 1usize << self.odometer.digits;
        // The storage where paths part: each branch's label run, held once and shared by the leaves it founds.
        let runs: Vec<Option<u32>> = (0..self.branches.len())
            .map(|branch| {
                let top = digits
                    .iter()
                    .map(|digit| &digit.reads[branch])
                    .filter(|read| read.stop == Stop::Prior)
                    .map(|read| read.bottoms.last().map_or(0, |bottom| bottom + 1))
                    .min()?;
                Some(self.arena.hold(&letters[branch][top..]))
            })
            .collect();
        for digit in digits {
            if digit.reads.len() > 1 {
                let stepped =
                    &self.joins[digit.dyadic] * &digit.reads[0].faces[0] / &digit.reads[1].faces[0];
                self.joins[digit.dyadic] = self.carry(&stepped);
            }
            for read in digit.reads {
                self.deposit_read(read, &letters, &runs, digit.dyadic, digit.symbol, cells);
            }
        }
        Ok(face)
    }

    /// **Deposit one branch's ideal read**: each mixing level's `β` steps (the parting chain's
    /// upper part on its split `β`), then the parting chain splits and an arrival stopped at the
    /// prior founds its leaf, then each node's mass of the digit grows.
    fn deposit_read(
        &mut self,
        read: IdealRead,
        letters: &[Vec<u32>],
        runs: &[Option<u32>],
        dyadic: usize,
        symbol: usize,
        cells: usize,
    ) {
        let forced = self.branches[read.branch].forced;
        let top = read.faces.len() - 1;
        let levels = read.nodes.len();
        let mut upper = read.parting.as_ref().map(|(_, upper, _)| upper.clone());
        for level in (0..levels.min(top)).rev() {
            if read.bottoms[level] < forced {
                break;
            }
            let node = read.nodes[level] as usize;
            let kt = self.kt(read.nodes[level], symbol);
            let beta = match &upper {
                Some(upper) if read.parts(level) => upper.clone(),
                _ => self.beta[node].clone(),
            };
            let stepped = self.carry(&(beta * kt / &read.faces[level + 1]));
            match upper.as_mut() {
                Some(upper) if read.parts(level) => *upper = stepped,
                _ => self.beta[node] = stepped,
            }
        }
        let IdealRead {
            branch,
            stop,
            mut nodes,
            parting,
            ..
        } = read;
        let letters = &letters[branch];
        let depth = letters.len();
        let tree = branch * cells + dyadic;
        if let Some((at, _, lower)) = parting {
            let chain = nodes.pop().expect("a parting chain");
            let chain_top = nodes.last().map_or(0, |&p| self.arena.bottom(p) + 1);
            let bottom = self.arena.bottom(chain);
            let end = self.arena.end(chain) - u32::try_from(bottom - at).expect("a depth");
            let halves = if at >= forced {
                self.arena.halves(chain)
            } else {
                [1, 1]
            };
            let key = self.arena.label(chain, at + 1);
            if let Some(lower) = lower {
                self.beta[chain as usize] = self.carry(&lower);
            }
            let node = self.arena.push(branch, at, halves, end);
            self.beta
                .push(upper.expect("the parting chain's upper part"));
            let parent = nodes.last().map(|&p| (p, letters[chain_top - 1]));
            self.arena.link(tree, parent, node);
            self.arena.link(tree, Some((node, key)), chain);
            nodes.push(node);
        }
        if stop == Stop::Prior {
            let leaf_top = nodes.last().map_or(0, |&p| self.arena.bottom(p) + 1);
            let run = runs[branch].expect("an arrival's label run");
            let leaf = self.arena.push(branch, depth, [1, 1], run);
            let founding = self.declaration.prior.founding(depth);
            self.beta.push(Rat::from_integer(BigInt::from(founding)));
            let parent = nodes.last().map(|&p| (p, letters[leaf_top - 1]));
            self.arena.link(tree, parent, leaf);
            nodes.push(leaf);
        }
        let ceiling = self.declaration.capacity.ceiling_halves();
        self.arena.count(&nodes, forced, symbol, ceiling);
    }
}

/// A positive ratio carried at an optional width: exact when both odd parts fit, otherwise its
/// mantissa `⌊v 2^s⌋ ∈ [2^(W−1), 2^W)` times `2^(−s)`.
fn carried_ratio(value: &Rat, width: Option<u64>) -> (Rat, bool) {
    let Some(width) = width else {
        return (value.clone(), false);
    };
    let (numerator, denominator) = (value.numer().magnitude(), value.denom().magnitude());
    let odd = |x: &BigUint| x >> x.trailing_zeros().unwrap_or(0);
    if odd(numerator).bits() <= width && odd(denominator).bits() <= width {
        return (value.clone(), false);
    }
    let (m, shift) = mantissa(numerator, denominator, width);
    (Rat::from_integer(BigInt::from(m)) * two_power(-shift), true)
}

/// **The `W`-bit mantissa of a positive ratio** `a/b`: `m = ⌊a 2^s / b⌋ ∈ [2^(W−1), 2^W)` and its
/// shift `s`, so `m 2^(−s) ≤ a/b < (m + 1) 2^(−s)`.
fn mantissa(a: &BigUint, b: &BigUint, width: u64) -> (BigUint, i64) {
    let floor = |shift: i64| -> BigUint {
        if shift >= 0 {
            (a << shift as usize) / b
        } else {
            a / (b << shift.unsigned_abs() as usize)
        }
    };
    let mut shift = width as i64 - (a.bits() as i64 - b.bits() as i64);
    let mut m = floor(shift);
    if m.bits() > width {
        shift -= 1;
        m = floor(shift);
    }
    debug_assert_eq!(m.bits(), width);
    (m, shift)
}

// -------------------------------------------------------------------------------------------
// The stop-weight mixture per digit tree

/// One side of a join: a face, or an earlier join (post-order).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Side {
    Face(usize),
    Join(usize),
}

/// One join: its two sides and its founding ratio `β₀ = π_left/π_right`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Joint {
    left: Side,
    right: Side,
    founding: u64,
}

/// [definition; agent-inferred] **A join tree over `K` faces** (local weighing; Lean
/// `Compression/Landmark/Context/LocalWeighing.{static_mixture, two_face_prior}`): every join is a two-face sequential
/// mixture of its sides' faces, founded at `β₀ = π_left/π_right` and stepped by
/// `β' = β q_left(b)/q_right(b)`, so the joins telescope to the Bayesian mixture of the `K` faces
/// with the tree's prior: each face's prior weight is the product of the join weights
/// `β₀/(1 + β₀)` (left) and `1/(1 + β₀)` (right) down to it ([`JoinTree::prior`]), and they sum to
/// one. The joins are held in post-order, the root last.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct JoinTree {
    faces: usize,
    joints: Vec<Joint>,
    root: Side,
}

impl JoinTree {
    fn build(joints: &mut Vec<Joint>, low: usize, high: usize) -> Side {
        if high - low == 1 {
            return Side::Face(low);
        }
        let middle = low + (high - low) / 2;
        let left = Self::build(joints, low, middle);
        let right = Self::build(joints, middle, high);
        joints.push(Joint {
            left,
            right,
            founding: 1,
        });
        Side::Join(joints.len() - 1)
    }

    /// **The balanced join tree** over `K ≥ 1` faces, every join founded at `β₀ = 1`: each face's
    /// prior is `2^(−depth)`, uniform when `K` is a power of two.
    pub fn balanced(faces: usize) -> Result<Self, ContextError> {
        if faces == 0 {
            return Err(shape("a join tree over at least one face", 1, 0));
        }
        let mut joints = Vec::with_capacity(faces - 1);
        let root = Self::build(&mut joints, 0, faces);
        Ok(Self {
            faces,
            joints,
            root,
        })
    }

    /// **The incumbent's join tree** over `K ≥ 2` faces: face 0 (the incumbent) against the
    /// balanced join of faces `1..K`, the root founded at `β₀ = 2^j − 1` (the incumbent's prior
    /// `1 − 2^(−j)`, the dyadic ladder), every inner join at `1`. Refused outside `1..=63`.
    pub fn incumbent(faces: usize, rung: u32) -> Result<Self, ContextError> {
        if faces < 2 {
            return Err(shape(
                "an incumbent's join tree over at least two faces",
                2,
                faces,
            ));
        }
        if rung == 0 || rung > MAX_RUNG {
            return Err(shape(
                "a join rung of the dyadic ladder within 1..=63",
                MAX_RUNG as usize,
                rung as usize,
            ));
        }
        let mut joints = Vec::with_capacity(faces - 1);
        let right = Self::build(&mut joints, 1, faces);
        joints.push(Joint {
            left: Side::Face(0),
            right,
            founding: (1u64 << rung) - 1,
        });
        Ok(Self {
            faces,
            root: Side::Join(joints.len() - 1),
            joints,
        })
    }

    /// `K`, the faces.
    pub fn faces(&self) -> usize {
        self.faces
    }

    /// The joins, `K − 1`.
    pub fn joins(&self) -> usize {
        self.joints.len()
    }

    /// **Each face's prior weight**, exact: the product of the join weights down to it; they sum to
    /// one.
    pub fn prior(&self) -> Vec<Rat> {
        let mut prior = vec![Rat::zero(); self.faces];
        let mut stack = vec![(self.root, Rat::one())];
        while let Some((side, weight)) = stack.pop() {
            match side {
                Side::Face(face) => prior[face] = weight,
                Side::Join(join) => {
                    let joint = self.joints[join];
                    let founding = Rat::from_integer(BigInt::from(joint.founding));
                    let total = Rat::one() + &founding;
                    stack.push((joint.left, &weight * &founding / &total));
                    stack.push((joint.right, &weight / &total));
                }
            }
        }
        prior
    }

    /// The widest founding ratio's bits.
    fn widest(&self) -> u64 {
        self.joints
            .iter()
            .map(|joint| u64::from(u64::BITS - joint.founding.leading_zeros()))
            .max()
            .unwrap_or(0)
    }
}

/// [definition] **One digit through a mixture's joins** ([`FaceJoins::receive`]): the mixed
/// digit-0 numerator on `2^(−M)`, its read certificate and the root's excess increment on
/// `2^(−C)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JoinReceipt {
    pub split: u64,
    pub certificate: u128,
    pub increment: u128,
}

/// [definition; agent-inferred] **A mixture's joins on the lattice** (local weighing): per dyadic
/// cell, each join of a [`JoinTree`] carries its chart as a node or an enlarged tree's join does
/// (the carried `β` of `W` bits, the stop weight `λ̂ = ⟦β/(1 + β)⟧`, its rebases, its drift and
/// excess certificates on `2^(−C)`). A join's face is `⟦λ̂ q̂_left + (1 − λ̂) q̂_right⟧` on the
/// faces' lattice, a positive normalized split for any `λ̂` (`path_face_normalized`); its step is
/// `β' = β q̂_left(b)/q̂_right(b)`, the drift growing by both sides' excess increments and the
/// rebases, the excess by its rounding `2^(−M)/min(q̂, q̂_left, q̂_right)`, twice the rebases and
/// both sides' increments (the enlarged tree's join accounting; Lean
/// `Compression/Landmark/Context/LocalWeighing.forward_executed`). A read's certificate is the faces' plus each join's drift
/// and rounding. Each dyadic cell is its own digit tree, weighed by its own evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceJoins {
    tree: JoinTree,
    widths: Widths,
    charts: Vec<Vec<Chart>>,
    rebases: u64,
    releases: u64,
}

impl FaceJoins {
    /// **The joins of a mixture on a tree's lattice**, every dyadic cell's at its founding. Refused
    /// at a founding ratio past the carrier `W`.
    pub fn new(tree: JoinTree, widths: Widths) -> Result<Self, ContextError> {
        if tree.widest() > widths.carrier {
            return Err(shape(
                "a join tree whose founding ratios fit the carrier's W bits",
                widths.carrier as usize,
                tree.widest() as usize,
            ));
        }
        let founding: Vec<Chart> = tree
            .joints
            .iter()
            .map(|joint| {
                let beta = Beta {
                    numerator: joint.founding,
                    denominator: 1,
                    exponent: 0,
                };
                Chart {
                    beta,
                    stop: beta.stop_weight(widths.face, widths.carrier),
                    rebases: 0,
                    drift: 0,
                    excess: 0,
                }
            })
            .collect();
        let cells = 1usize << widths.digits;
        Ok(Self {
            charts: vec![founding; cells],
            tree,
            widths,
            rebases: 0,
            releases: 0,
        })
    }

    /// The join tree.
    pub fn tree(&self) -> &JoinTree {
        &self.tree
    }

    /// The rebases so far, and the carrier's releases.
    pub fn rebases(&self) -> (u64, u64) {
        (self.rebases, self.releases)
    }

    /// The largest drift certificate over every dyadic cell's joins, in bits.
    pub fn drift(&self) -> Rat {
        let largest = self
            .charts
            .iter()
            .flatten()
            .map(|chart| chart.drift)
            .max()
            .unwrap_or(0);
        certified(&self.widths, largest)
    }

    fn check(&self, dyadic: usize, faces: &[u64]) -> Result<(), ContextError> {
        let full = 1u64 << self.widths.face;
        if faces.len() != self.tree.faces || dyadic >= self.charts.len() {
            return Err(shape(
                "one digit-0 face per face of the join tree, at a dyadic cell of the odometer",
                self.tree.faces,
                faces.len(),
            ));
        }
        if let Some(&x) = faces.iter().find(|&&x| x == 0 || x >= full) {
            return Err(shape(
                "a digit-0 face inside the lattice's open unit interval",
                full as usize,
                x as usize,
            ));
        }
        Ok(())
    }

    /// Each join's digit-0 face at a dyadic cell, post-order.
    fn values(&self, dyadic: usize, faces: &[u64]) -> Vec<u64> {
        let charts = &self.charts[dyadic];
        let mut values = Vec::with_capacity(self.tree.joints.len());
        for (join, joint) in self.tree.joints.iter().enumerate() {
            let left = side_value(&values, faces, joint.left);
            let right = side_value(&values, faces, joint.right);
            values.push(lattice_blend(&self.widths, charts[join].stop, left, right));
        }
        values
    }

    /// **The mixed digit-0 face** at a dyadic cell from the faces' digit-0 numerators.
    pub fn split(&self, dyadic: usize, faces: &[u64]) -> Result<u64, ContextError> {
        self.check(dyadic, faces)?;
        let values = self.values(dyadic, faces);
        Ok(side_value(&values, faces, self.tree.root))
    }

    /// **Receive one digit** at a dyadic cell: the mixed split read before the step, its
    /// certificate (the faces' `certificates` plus each join's drift and rounding), then every join
    /// steps by the observed digit `symbol`, its certificates growing by the faces' excess
    /// `increments` (zeros when the faces are exterior and exact).
    pub fn receive(
        &mut self,
        dyadic: usize,
        faces: &[u64],
        symbol: usize,
        certificates: &[u128],
        increments: &[u128],
    ) -> Result<JoinReceipt, ContextError> {
        self.check(dyadic, faces)?;
        if certificates.len() != faces.len() || increments.len() != faces.len() || symbol > 1 {
            return Err(shape(
                "one certificate and one increment per face, and a binary digit",
                faces.len(),
                certificates.len(),
            ));
        }
        let widths = self.widths;
        let full = 1u64 << widths.face;
        let side = |zero: u64| u128::from(if symbol == 0 { zero } else { full - zero });
        let values = self.values(dyadic, faces);
        let split = side_value(&values, faces, self.tree.root);
        let mut certificate = certificates.iter().fold(0u128, |a, &b| a.saturating_add(b));
        let mut increment = vec![0u128; self.tree.joints.len()];
        let side_increment = |increment: &[u128], at: Side| match at {
            Side::Face(face) => increments[face],
            Side::Join(join) => increment[join],
        };
        for (join, joint) in self.tree.joints.iter().enumerate() {
            let (left, right) = (
                side_value(&values, faces, joint.left),
                side_value(&values, faces, joint.right),
            );
            let theta = ceil_div(
                1u128 << widths.certificate,
                side(values[join]).min(side(left)).min(side(right)),
            );
            let chart = self.charts[dyadic][join];
            certificate = certificate
                .saturating_add(chart.drift)
                .saturating_add(theta);
            let (step, units) = carried_step(&widths, chart.beta, side(left), 1, side(right), 0);
            self.rebases += u64::from(step.mantissa.is_some());
            self.releases += u64::from(step.released.is_some());
            let children = side_increment(&increment, joint.left)
                .saturating_add(side_increment(&increment, joint.right));
            let grown = theta
                .saturating_add(units.saturating_mul(2))
                .saturating_add(children);
            let chart = &mut self.charts[dyadic][join];
            chart.beta = step.beta;
            chart.stop = step.beta.stop_weight(widths.face, widths.carrier);
            chart.rebases += u32::from(step.mantissa.is_some());
            chart.drift = chart.drift.saturating_add(children).saturating_add(units);
            chart.excess = chart.excess.saturating_add(grown);
            increment[join] = grown;
        }
        Ok(JoinReceipt {
            split,
            certificate,
            increment: side_increment(&increment, self.tree.root),
        })
    }
}

/// A side's digit-0 face: a face's own, or an earlier join's value.
fn side_value(values: &[u64], faces: &[u64], side: Side) -> u64 {
    match side {
        Side::Face(face) => faces[face],
        Side::Join(join) => values[join],
    }
}

/// [definition; agent-inferred] **The stop-weight mixture per digit tree** (local weighing, "in each
/// digit tree"; Lean `Compression/Landmark/Context/LocalWeighing.stop_mixture_per_tree`): `K` trees over one declaration,
/// one per declared stop prior (their widths agree: the prior enters only at the founding), and in
/// each dyadic cell a [`JoinTree`]'s joins ([`FaceJoins`]) mixing the trees' digit faces by that
/// digit tree's own evidence. Each digit tree's weight is `Σ_k π_k W_(h,k)`, the mixture over
/// (law, pruned tree) with prior `π_k prior_(w_k)(S)`, which sums to one; it codes within
/// `−log₂ π_k` of each law's tree in that dyadic cell. The mixed face is a positive normalized
/// split at every digit, so the cells' faces partition the unit cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StopMixture {
    trees: Vec<Landmarks>,
    joins: FaceJoins,
}

impl StopMixture {
    /// **Declare the mixture**, empty: one tree per prior (`declaration` with each prior), joined by
    /// `tree`. Refused unless there is one prior per face of the join tree, or as each tree and the
    /// joins are refused.
    pub fn new(
        declaration: LandmarkDeclaration,
        priors: Vec<StopPrior>,
        tree: JoinTree,
    ) -> Result<Self, ContextError> {
        if priors.len() != tree.faces() {
            return Err(shape(
                "one stop prior per face of the join tree",
                tree.faces(),
                priors.len(),
            ));
        }
        let trees = priors
            .into_iter()
            .map(|prior| {
                Landmarks::new(LandmarkDeclaration {
                    prior,
                    ..declaration.clone()
                })
            })
            .collect::<Result<Vec<Landmarks>, ContextError>>()?;
        let widths = trees[0].widths();
        let joins = FaceJoins::new(tree, widths)?;
        Ok(Self { trees, joins })
    }

    /// Each tree's declared stop prior, in the join tree's face order.
    pub fn priors(&self) -> Vec<StopPrior> {
        self.trees
            .iter()
            .map(|tree| tree.declaration().prior.clone())
            .collect()
    }

    /// The trees.
    pub fn trees(&self) -> &[Landmarks] {
        &self.trees
    }

    /// The joins.
    pub fn joins(&self) -> &FaceJoins {
        &self.joins
    }

    /// **Receive one cell**: every tree's digits read at the current standing and deposited, then
    /// in each opened dyadic cell the joins read the trees' pre-deposit splits and step by the
    /// digit. The cell's executed face is the product of the mixed digits' sides; its residual the
    /// digits' certificates in bits.
    pub fn receive(
        &mut self,
        address: &[Letter],
        class: usize,
    ) -> Result<CellReading, ContextError> {
        for tree in &self.trees {
            check(tree.declaration(), address, class)?;
        }
        let readings = self
            .trees
            .iter_mut()
            .map(|tree| tree.receive_digits(address, class))
            .collect::<Result<Vec<DigitsReading>, ContextError>>()?;
        let widths = self.trees[0].widths();
        let full = 1u64 << widths.face;
        let digits = readings[0].digits.len();
        let (mut numerator, mut certificate) = (BigUint::one(), 0u128);
        for i in 0..digits {
            let DigitReading { dyadic, symbol, .. } = readings[0].digits[i];
            let faces: Vec<u64> = readings.iter().map(|r| r.digits[i].split).collect();
            let certificates: Vec<u128> =
                readings.iter().map(|r| r.digits[i].certificate).collect();
            let increments: Vec<u128> = readings.iter().map(|r| r.digits[i].increment).collect();
            let receipt = self
                .joins
                .receive(dyadic, &faces, symbol, &certificates, &increments)?;
            numerator *= if symbol == 0 {
                receipt.split
            } else {
                full - receipt.split
            };
            certificate = certificate.saturating_add(receipt.certificate);
        }
        Ok(CellReading {
            executed: dyadic(numerator, digits as u64 * widths.face),
            residual: certified(&widths, certificate),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the code length of faces and passages (the tree's prequential measurement on a cut, and its
// development choices, are the exposure's: `hnn::reference`)

fn zero() -> ExactInterval {
    ExactInterval::point(Rat::zero())
}

/// [definition; agent-inferred] **A face's code length** `−log₂ q`, enclosed (module header, "The
/// measurement"): for `q = n/d`, `log₂ d − log₂ n`, each by the certified [`binary_log`] at
/// `O + 1` fraction bits (`O` the declared enclosure grid's octaves, `ratio::algebraic::LOG_OCTAVES`), so the
/// enclosure is at most `2^(−O)` wide on the grid `interval_sum` rounds every sum out to; exact when
/// both are powers of two (a dyadic face with a power-of-two numerator).
pub fn code_length(probability: &Rat) -> Result<ExactInterval, ContextError> {
    if !probability.is_positive() {
        return Err(shape("a positive face's code length", 1, 0));
    }
    ratio_code_length(
        probability.numer().magnitude(),
        probability.denom().magnitude(),
    )
}

/// **The code length of an unreduced ratio** `−log₂(n/d) = log₂ d − log₂ n`, enclosed as
/// [`code_length`] encloses a face (each logarithm by the certified [`binary_log`] at `O + 1`
/// fraction bits), without reducing the ratio: the harness's products of many faces are read this
/// way, with no greatest common divisor of their numerators. Refused at a zero part.
pub fn ratio_code_length(
    numerator: &BigUint,
    denominator: &BigUint,
) -> Result<ExactInterval, ContextError> {
    if numerator.is_zero() || denominator.is_zero() {
        return Err(shape("a positive ratio's code length", 1, 0));
    }
    let bits = LOG_OCTAVES + 1;
    let bounds = |value: &BigUint| -> (Rat, Rat) {
        let log = binary_log(value, bits, |_| false);
        let whole = BigInt::from(log.whole) << log.bits as usize;
        let scale = BigInt::one() << log.bits as usize;
        let lower = &whole + BigInt::from(log.fraction);
        let upper = if log.exact { lower.clone() } else { &lower + 1 };
        (Rat::new(lower, scale.clone()), Rat::new(upper, scale))
    };
    let (numerator, denominator) = (bounds(numerator), bounds(denominator));
    ExactInterval::new(&denominator.0 - &numerator.1, &denominator.1 - &numerator.0)
        .map_err(|_| shape("an ordered enclosure of a code length", 0, 1))
}

/// The significant bits a product bound keeps: `2^(K−1) ≤ m < 2^K` once a factor has rounded it.
const KEPT: u64 = 127;

/// [definition; agent-inferred] **One side of a product's enclosure**: the integer `m · 2^e`, its
/// mantissa `m < 2^127` and its binary exponent `e`, rounded down (a lower bound) or up (an upper
/// bound) after each factor ([`PassageCode`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProductBound {
    pub mantissa: u128,
    pub exponent: u64,
}

impl ProductBound {
    /// The empty product, `1`.
    pub const ONE: ProductBound = ProductBound {
        mantissa: 1,
        exponent: 0,
    };

    /// Keep `KEPT` significant bits of `top 2^64 + bottom` (`top < 2^127`, `bottom < 2^64`),
    /// rounding down, or up when `up`.
    fn kept(top: u128, bottom: u128, exponent: u64, up: bool) -> Self {
        let total = if top == 0 {
            bits128(bottom)
        } else {
            bits128(top) + 64
        };
        if total <= KEPT {
            return Self {
                mantissa: (top << 64) | bottom,
                exponent,
            };
        }
        let shift = total - KEPT;
        let (mantissa, dropped) = if shift <= 64 {
            (
                (top << (64 - shift)) | (bottom >> shift),
                bottom & ((1u128 << shift) - 1) != 0,
            )
        } else {
            let over = shift - 64;
            (top >> over, bottom != 0 || top & ((1u128 << over) - 1) != 0)
        };
        Self::rounded(mantissa, exponent + shift, up && dropped)
    }

    /// A kept mantissa, raised by one unit when `raise` (and renormalized at `2^127`).
    fn rounded(mantissa: u128, exponent: u64, raise: bool) -> Self {
        if !raise {
            return Self { mantissa, exponent };
        }
        let mantissa = mantissa + 1;
        if bits128(mantissa) > KEPT {
            Self {
                mantissa: mantissa >> 1,
                exponent: exponent + 1,
            }
        } else {
            Self { mantissa, exponent }
        }
    }

    /// **Times a word**, `m 2^e · x`, kept at `KEPT` bits (down, or up when `up`).
    pub fn times(self, factor: u64, up: bool) -> Self {
        let mask = u128::from(u64::MAX);
        let (low, high) = (
            (self.mantissa & mask) * u128::from(factor),
            (self.mantissa >> 64) * u128::from(factor),
        );
        Self::kept(high + (low >> 64), low & mask, self.exponent, up)
    }

    /// **Times an integer**, kept at `KEPT` bits (down, or up when `up`).
    pub fn times_integer(self, factor: &BigUint, up: bool) -> Self {
        if let Some(word) = factor.to_u64() {
            return self.times(word, up);
        }
        let product = BigUint::from(self.mantissa) * factor;
        let bits = product.bits();
        if bits <= KEPT {
            return Self {
                mantissa: product.to_u128().expect("within the kept bits"),
                exponent: self.exponent,
            };
        }
        let shift = bits - KEPT;
        let mantissa = (&product >> shift as usize)
            .to_u128()
            .expect("the kept bits");
        let dropped = product.trailing_zeros().is_some_and(|zeros| zeros < shift);
        Self::rounded(mantissa, self.exponent + shift, up && dropped)
    }

    /// **Times another bound**, kept at `KEPT` bits (down, or up when `up`).
    pub fn times_bound(self, other: ProductBound, up: bool) -> Self {
        let product = BigUint::from(self.mantissa) * BigUint::from(other.mantissa);
        let bound = Self {
            mantissa: 1,
            exponent: self.exponent + other.exponent,
        };
        bound.times_integer(&product, up)
    }

    /// `log₂` of the bound, enclosed by the certified [`binary_log`] at `bits` fraction bits:
    /// `(lower, upper)` on `2^(−bits)`.
    pub fn log2(self, bits: u32) -> (Rat, Rat) {
        let log = binary_log(&BigUint::from(self.mantissa), bits, |_| false);
        let scale = BigInt::one() << log.bits as usize;
        let whole = (BigInt::from(log.whole) + BigInt::from(self.exponent)) << log.bits as usize;
        let lower = &whole + BigInt::from(log.fraction);
        let upper = if log.exact { lower.clone() } else { &lower + 1 };
        (Rat::new(lower, scale.clone()), Rat::new(upper, scale))
    }
}

impl PartialOrd for ProductBound {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProductBound {
    /// The integers `m 2^e` compared exactly.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let size = |b: &ProductBound| {
            if b.mantissa == 0 {
                0
            } else {
                bits128(b.mantissa) + b.exponent
            }
        };
        match size(self).cmp(&size(other)) {
            std::cmp::Ordering::Equal if self.mantissa != 0 => {
                if self.exponent >= other.exponent {
                    (self.mantissa << (self.exponent - other.exponent)).cmp(&other.mantissa)
                } else {
                    self.mantissa
                        .cmp(&(other.mantissa << (other.exponent - self.exponent)))
                }
            }
            order => order,
        }
    }
}

/// [definition; agent-inferred] **A passage's code length, carried as its faces' product**
/// (the wide cut: the measurement at scale). The faces `q_t = n_t/(d_t 2^(k_t))` of a passage multiply
/// to `N/(D 2^E)`; `N` and `D` are held between exact integer bounds ([`ProductBound`], each kept at
/// 127 significant bits and rounded outward after every factor) and `E` exactly, so the passage's
/// code length `−log₂ ∏ q_t = log₂ D + E − log₂ N` is enclosed once, by the certified
/// [`binary_log`] at `O + 1` fraction bits, and rounded out on the enclosure grid `2^(−O)` as
/// `interval_sum` rounds (`O` the grid's octaves, `ratio::algebraic::LOG_OCTAVES`). A factor moves a
/// bound by a relative `2^(−126)` at most, so over `f` factors the enclosure stays within
/// `f 2^(−125) + 2^(1−O)` bits of the exact code length; a dyadic face (every tree's) moves only
/// `N`'s bounds and `E`. It is the per-cell sum of [`code_length`]s without their per-cell
/// enclosures: on the wide cut's development cells the `D = 1` tree's run with the per-cell sum took
/// 29,902 ms, of which its passage 3,137 ms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PassageCode {
    numerator: [ProductBound; 2],
    denominator: [ProductBound; 2],
    exponent: u64,
    factors: u64,
}

impl Default for PassageCode {
    fn default() -> Self {
        Self::new()
    }
}

impl PassageCode {
    /// The empty passage: code length zero.
    pub fn new() -> Self {
        Self {
            numerator: [ProductBound::ONE; 2],
            denominator: [ProductBound::ONE; 2],
            exponent: 0,
            factors: 0,
        }
    }

    /// **One lattice side** `x/2^bits` (a digit's executed side, `0 < x`).
    pub fn side(&mut self, numerator: u64, bits: u64) {
        debug_assert!(numerator > 0);
        self.numerator = [
            self.numerator[0].times(numerator, false),
            self.numerator[1].times(numerator, true),
        ];
        self.exponent += bits;
        self.factors += 1;
    }

    /// **One positive face**, exact: its numerator's bounds move, its denominator's twos go to
    /// `E` and its odd part moves the denominator's bounds. Refused at a face that is not positive.
    pub fn face(&mut self, face: &Rat) -> Result<(), ContextError> {
        if !face.is_positive() {
            return Err(shape("a positive face in a passage's code", 1, 0));
        }
        let numerator = face.numer().magnitude();
        let denominator = face.denom().magnitude();
        let twos = denominator.trailing_zeros().unwrap_or(0);
        let odd = denominator >> twos as usize;
        self.numerator = [
            self.numerator[0].times_integer(numerator, false),
            self.numerator[1].times_integer(numerator, true),
        ];
        if !odd.is_one() {
            self.denominator = [
                self.denominator[0].times_integer(&odd, false),
                self.denominator[1].times_integer(&odd, true),
            ];
        }
        self.exponent += twos;
        self.factors += 1;
        Ok(())
    }

    /// **One dyadic face from its numerator**, `n/2^k` (`n > 0`): a cell's product of lattice sides.
    pub fn dyadic(&mut self, numerator: &BigUint, exponent: u64) {
        debug_assert!(!numerator.is_zero());
        self.numerator = [
            self.numerator[0].times_integer(numerator, false),
            self.numerator[1].times_integer(numerator, true),
        ];
        self.exponent += exponent;
        self.factors += 1;
    }

    /// **Two passages joined**: the product of their faces.
    pub fn join(&mut self, other: &PassageCode) {
        for side in 0..2 {
            let up = side == 1;
            self.numerator[side] = self.numerator[side].times_bound(other.numerator[side], up);
            self.denominator[side] =
                self.denominator[side].times_bound(other.denominator[side], up);
        }
        self.exponent += other.exponent;
        self.factors += other.factors;
    }

    /// The faces multiplied in.
    pub fn factors(&self) -> u64 {
        self.factors
    }

    /// The bounds of the faces' product `N/(D 2^E)`: `(N_lower, N_upper, D_lower, D_upper, E)`.
    pub fn bounds(&self) -> ([ProductBound; 2], [ProductBound; 2], u64) {
        (self.numerator, self.denominator, self.exponent)
    }

    /// **The code length** `−log₂ ∏ q`, enclosed and rounded out on `2^(−O)`.
    pub fn bits(&self) -> Result<ExactInterval, ContextError> {
        let octaves = LOG_OCTAVES + 1;
        let (numerator_low, _) = self.numerator[0].log2(octaves);
        let (_, numerator_high) = self.numerator[1].log2(octaves);
        let (denominator_low, _) = self.denominator[0].log2(octaves);
        let (_, denominator_high) = self.denominator[1].log2(octaves);
        let exponent = Rat::from_integer(BigInt::from(self.exponent));
        let enclosure = ExactInterval::new(
            &denominator_low + &exponent - numerator_high,
            denominator_high + exponent - numerator_low,
        )
        .map_err(|_| shape("an ordered enclosure of a passage's code", 0, 1))?;
        Ok(interval_sum(&zero(), &enclosure)?)
    }
}

#[cfg(test)]
mod tests;
