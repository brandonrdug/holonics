# Petrov's types place the eigenvalues of the tide joined to the frame dragging, a forest retains nothing, a parallel bundle forgets only its uniform total, and the moment stays lossy across re-keys, in Lean

November 19, 10:18 UTC. The eighteenth formalization pass over #410, its nineteenth set, after [the
eighteenth](2026-11-19_THE_CANTOR_STRINGS_TUBE_BEATS_WITH_ITS_COMPLEX_DIMENSIONS_A_CONTINUUM_CLOCK_SPLITS_AS_A_COMPLEXS_DOES_AND_A_PASSIVE_WORD_MOVES_BY_THE_SUM_OF_ITS_STEPS_CHANGES_IN_LEAN.md)
(#1030). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Spacetime/PetrovTypes` | The observer's electric and magnetic parts join as `Q = E + iH`, complex symmetric and traceless (`weylQ_symm`, `weylQ_trace`); a traceless `3 × 3` over a field of characteristic zero has `Q³ = (I/2)Q + (J/3)·1`, `det Q = J/3` and characteristic polynomial `X³ − (I/2)X − J/3` with `I = tr Q²`, `J = tr Q³` (`cayley_hamilton`, `det_eq`, `charpoly_eq`), whose discriminant is `(I³ − 6J²)/2`, so a root repeats iff `I³ = 6J²` (`discriminant_eq`, `repeated_root_iff`); Petrov's six types (O `Q = 0`; N `Q² = 0`; III `Q³ = 0`; D `(Q − λ)(Q + 2λ) = 0` at `λ ≠ 0`; II `(Q − λ)²(Q + 2λ) = 0` with the shifted product open; I `I³ ≠ 6J²`) hold one at a time and exactly one for every traceless `Q`, read by a classifier from `I`, `J` and `λ = −J/I`, and the type does not depend on the field it is read in (`existsUnique_hasType`, `hasType_unique`, `classify`, `special_iff`, `pow_three_eq_zero_iff_classify`, `classify_map`); `(E + iH)² = (E² − H²) + i(EH + HE)`, so `Q² = 0` iff strain and rotation have one square and anticommute (`complexQ_sq_eq_zero_iff`, `hasType_N_iff`), and a real symmetric `E` with `E² = 0` is zero, so a Weyl tensor with no frame dragging is of type I, D or O (`eq_zero_of_symm_sq`, `classify_of_symm`, `weylQ_not_null_of_magnetic_eq_zero`); one witness of each type, the Schwarzschild tide `μ·diag(−2, 1, 1)` of type D and a plane wave of type N among them (`classify_schwarzschild`, `classify_planeWave`, `classify_typeIIIQ`, `classify_typeIIQ`, `classify_typeIQ`) | #410's box "Curvature's strain and rotation" (part); `Physics/Spacetime/Raychaudhuri`'s "What is not claimed"; the Swing record's §5.6 | `coupling.petrov-types` (new); `coupling.weyl-electric-magnetic` (scope) |
| `Objects/RetentionClasses` | On an incidence whose transpose is injective (a forest) every solve carries the one flux with `dᵀj = σ` and the observation never reads the constitution, so under every deposition law any two presents share every future and the minimal retention is a point, `(1, 1)` and `(1, 5)` on two edges in series (`IsForest.flux_eq`, `IsForest.all_futureAgreement`, `IsForest.pointStanding_exists`, `series_witness`); on the `m`-edge parallel bundle a solve reads the shares `r_e = Θ_e/T` alone (`bundle_flux`, `bundle_observeConstitution`), and under the square law two presents share every future iff their constitutions are equal or both uniform, one unit stroke moving equal shares on two totals apart by `r_e(R₂ − r_e)(T − T′)/((T + R₂)(T′ + R₂))` (`stroke_share_difference`, `stroke_separates_equal_shares`, `bundle_futureAgreement_iff`), with its minimal retention, lawful standing and leastness (`minimalRetain_eq_iff_futureAgreement`, `minimalStanding_exists`, `minimalRetain_factors_through_every_standing`); under the Joule law every step scales the constitution by `1 + g²`, so the classes are the projective classes, which the square law does not keep (`joule_stepConstitution_scale`, `joule_bundle_futureAgreement_iff`, `square_bundle_projective_class_is_not_a_retention`); a pendant edge carries its leaf's charge whatever its conductance, so the composite's minimal retention is the bundle's factor times the pendant's point (`pendant_flux`, `pendant_futureAgreement_iff`, `pendantMinimalRetain_eq_iff_futureAgreement`) | #410's box "The explicit classes of the square law's minimal retention" (part); `Objects/Retention`'s `[open]` paragraph; `Foundation/MinimalRetention` (#552) | `deposition.forest-retains-nothing`, `deposition.bundle-minimal-retention`, `deposition.joule-bundle-projective-retention`, `deposition.pendant-edge-forgotten` (new); `deposition.minimal-retention-general`, `deposition.projective-class-not-retention`, `deposition.joule-law-keeps-split` (owners and scope) |
| `HNN/RekeyedCapacity` | An event is a source cell or a re-key `(g, key < d_g)`, and a run of any interleaving ingests the cells as `Moment` does and applies `Keys.rekey` at the re-keys (`Event`, `run`); for any advance of at most one period each ring's winding rises by at most one a cell and a re-key keeps it, so after `n` cells the lift lies in `ReframedMoment`'s window at `M = n`, of `d_g(n + 1)` values, whatever the number of re-keys or aeons (`rekey_winding`, `winding_run`, `run_lift_mem_window`); a re-key adds and rewrites no count, so each source ring holds `n` counts whose letters are the cells and each offset `δ` holds `n − δ` pairs (`run_append_rekey`, `run_card_bins`, `run_bins_letters`, `run_card_pairBins`); the persisting state lies in a box of at most `N_rekey(n)` values, `Moment`'s count with each lift factor `2n + d_g` widened to `d_g(n + 1)`, and where `N_rekey(n) < |A|^n` the cells-to-state map is not injective for every placement of re-keys among the cells, a fixed schedule among them, with the crossover persisting (`card_rekeyedBox_le`, `rekeyed_moment_capacity`, `located_rekeyed_moment_capacity`, `rekeyed_capacity_of_schedule`, `rekeyed_capacity_persists`); the window discharges `reframed_mem_box`'s current premise (`rekeyed_mem_reframedBox`); on period-2 rings a re-key moves the later carries to a different lift of one winding, and on period-4 rings three cells reach winding `W + 3` (`rekey_changes_later_carries`, `rekeys_raise_the_winding_once_a_cell`) | #410's box "`HNN/Moment.moment_capacity` beyond one aeon, including re-keys"; `HNN/Keys.rekey_keeps_winding`; `HNN/ReframedMoment`; the record of October 6 on the source capacity | `hnn.rekeyed-moment-capacity` (new); `hnn.moment-capacity` (scope), `hnn.reframed-moment-capacity` (owners and scope), `hnn.rekey-keeps-winding` (owners) |

The boxes these answer, by their opening words: "Curvature's strain and rotation" (part); "The explicit classes of the
square law's minimal retention" (part); and "`HNN/Moment.moment_capacity` beyond one aeon, including re-keys".

## 2. What the pass corrected

1. Type D as briefed, `Q ≠ 0` and `(Q − λ)(Q + 2λ) = 0` for some `λ`, admits `λ = 0`, where the relation is `Q² = 0`, so
   every type N matrix would also be of type D and the types would not exclude each other; D is defined at `λ ≠ 0`, and
   `Q ≠ 0` follows. The brief's Swing reading, "`E` the boost part, `H` the turn part", contradicts the owner: `H` is
   symmetric (`magnetic_symm`) and the atlas row `coupling.weyl-electric-magnetic` reads both parts as boost-type, so
   the docstring carries `H`'s turn by the quarter-turn `i` at which it enters `Q` and by the gyroscope turn it drives,
   not by a skew part. The classification uses only that `Q` is traceless, so it is stated for every traceless `3 × 3`
   over a field of characteristic zero. No spectral theorem is used, and the sum-of-squares reading also rules out type
   II for a real symmetric `E`, which gives "I, D or O" whole. The plane wave's `H` is its tide turned by an eighth of a
   turn, not a quarter.
2. The owner's `squareLaw` and `jouleLaw` are laws on two edges only, so the bundle's laws are defined on `q` edges
   (`squareLawOn`, `jouleLawOn`) and agree with the owner's at `q = 2` by definition. The bundle's results need only `m
   ≥ 1`, not `m ≥ 2` (at one edge every constitution is uniform and the bundle is a forest); only the ramp that the
   square law separates needs two edges. The box's wording, "the orbit structure of deposition on projective classes",
   does not describe the square law's classes: on the bundle every non-uniform constitution is its own class and the
   uniform ones form one class across every total, while the projective classes are the Joule law's. The brief's series
   composition was written as the bundle with a pendant edge rather than two bundles in series; its reduction holds for
   every pair of laws that agree on the bundle's edges. The owner's docstring called its relation "the exact
   future-agreement relation"; the word is dropped there.
3. The brief's window `[W_g, W_g + ⌈2n/d_g⌉]`, and its lift counts `d_g(⌊2n/d_g⌋ + 2)` and `2n + 2d_g`, hold only
   without re-keys: a re-key can set a phase to `d_g − 1` before each cell, so the winding can rise by one a cell, and
   the window proved is `[W_g, W_g + n]`, which the period-4 witness shows is needed (it refutes all three forms). The
   brief's "the source counts are those of the cells alone" holds of the totals, the letters and the held cells, not of
   the phase bins: a cell binned after a re-key is labelled with the re-keyed phase. The pigeonhole holds for every
   placement of re-keys that is a function of the cells, wider than a fixed schedule, and since `N_rekey` is
   `RangedMoment.capacityBoundWith` at the rate `d_g` the located route and the crossover's persistence came from the
   owner; on period-2 rings `N_rekey = N`. Since a re-key keeps the winding, two runs with equal final windings carry
   the same total into the next ring: a re-key changes which cell carries, not how many carries there are.

## 3. What each statement stands on, and what is left

- `Physics/Spacetime/PetrovTypes` classifies `Q` for one observer at one point. The type's Lorentz invariance (a boost
  acting on `(E, H)` as `Q ↦ OQOᵀ`, `O ∈ SO(3, ℂ)`), the principal null directions and their multiplicities, the
  Bel–Debever criteria and the Newman–Penrose scalars are not stated; that every complex symmetric traceless `Q` comes
  from a tensor with the Weyl symmetries is not stated, no witness is built as `weylQ C`, since the owner exhibits no
  nonzero instance of `WeylSymmetries`, and the Schwarzschild tide is read, not derived from a metric. The box's other
  part, the deviation equation and the tide from a Lorentzian metric's connection, stays open, and the box stays part
  done.
- `Objects/RetentionClasses` computes the classes on forests, on the bundle and on the bundle with a pendant edge, for
  every solver. The classes on a graph whose cycles do not all share their two ends (a cycle of three edges, a wheel, a
  grid), where one cycle's split couples to the others' conductances, are not computed, and neither is a series of two
  bundles (whose classes the docstring names as the product of the two bundles'); deposition laws beyond the square and
  Joule laws enter only through the forest's every-law statement and the pendant's reduction; convergence of repeated
  deposition is not stated, and a solve's existence is proved only on these families. `MinimalRetention.IsMinimal` is
  not restated, since that would import a research module; it follows from the kernel, standing and leastness as in
  `parallel_minimalRetain_isMinimal`. The box stays part done.
- `HNN/RekeyedCapacity` counts the stream state across any number of aeons and re-keys, on the identity and the located
  routes. A key law that reads the stream is covered only as a choice of events from the cells, and its own retained
  state is not counted; learned constitutions, the leaky coordinates of `LeakyCapacity` and a sibling source's cells
  that advance the shared current (`M > n`) are not joined; the offset pairs' letters are counted only in total; which
  states of the box a declaration reaches is not stated beyond the witnesses. The owners' sentences were repointed:
  `Moment`'s capacity item, `RangedMoment`'s header (its "formal checking … is pending", stale since its module
  elaborates in the library) and `ReframedMoment`'s `reframed_mem_box`, whose docstrings also lose three uses of
  "exact".

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owners that named these statements as unstated or owed (`Physics/Spacetime/Raychaudhuri`'s "What is not claimed" on Petrov's classification; `Objects/Retention`'s and `Foundation/MinimalRetention`'s open paragraphs, the first also losing an "exact"; `HNN/Moment`'s capacity item, `HNN/RangedMoment`'s header, whose "formal checking … is pending" was stale, and `HNN/ReframedMoment`'s `reframed_mem_box` and three "exact"s; the `Holonics` modules and their importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3549 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10623 jobs)`, exit 0; `Holonics`, with `Objects/Retention`, `HNN/Moment`, `HNN/RangedMoment` and `HNN/ReframedMoment` and their importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
