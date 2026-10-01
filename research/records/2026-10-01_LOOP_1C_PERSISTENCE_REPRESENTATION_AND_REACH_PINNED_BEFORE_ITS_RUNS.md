# Loop 1c: persistence and coupling, representation, and reach, pinned before its runs

**Date.** October 1 (written September 30). **Issues.** #73, #148, #63 (THE_REBUILD U6, step 1,
loop 1c); #62. **Grade.** [definition; agent-inferred] for the experiments, their factors, the
search, the alignment, the budgets and the schedule; [measured] for the development cost reads
(§6.1) only; [proved-derived; formal-checked] for the Lean statements named in §7; owed (#62) as
§7 states. **No run of loop 1c's experiments has been made.** GPT-6 Astra reviews this pin before
anything runs.

**Occasion.** Gate A of step 1b stopped
([record](2026-09-30_STEP_1B_GATE_A_NO_FEASIBILITY_WITNESS_WITHIN_ITS_BUDGET_THE_CANDIDATES_OWN_MOVE_SOLVES_AT_MOST_SEVEN_OF_SIXTY_FOUR_DECISIONS.md)):
the candidate's own certified move, 16 moves on one epoch's 8 order-2 requests, solved at most 7 of
64 decision terms, released no whole section, read 45 to 56 of the 64 decisions at refinements that
did not lock them, and from move 3 on no decision solved at its refinement stayed solved after its
section's later locks. THE_REBUILD U6 names loop 1c's subject, measurement only, and Astra ordered
it: **persistence and coupling first, representation second, reach third, only if a witness
exists.** Gate A's no-whole-section and persistence failures are kept as they are: nothing here
repairs them, and no next law is selected.

The computational object is the helical pair interaction, read through the complex parametron's
executed comparison. Of the [winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects
this loop touches three: **faces and placement** (each station's lock face read whole at a declared
section; which stations the release places, in which order), **the tube** (the span's transport
`ρ^|τ_j − τ_k|` and its transported mass, whose normalization and entry are the landing's two parts)
and **the cell holonomy** (the executed growth over one turn, every sheet's weight). The helix, the
pair and the tower thread stay attached and unchanged.

## 0. The recorded failures each choice could repeat, and what holds each off

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and
the [prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):

| Choice | The failure it could repeat | What holds it off |
|---|---|---|
| Diagnostic placements (`storage_over`), diagnostic lock orders (`LockOrder::{Ascending, Descending}`), the later stations entered at their targets | 1 and lesson 5, an authored routine standing in for learning; lesson 3, a located cause carried into a new consumer | each is a diagnostic re-read, labelled so in its owner and its receipt; none enters the release (`generate_by_bank` and `compare` read `LockOrder::Gap` and `storage`), the move or the retained state; the targets enter only the instrumentation, as gate A's comparison already reads them; no diagnostic becomes a candidate law in this loop |
| The exterior fit (§3) | 1, an authored routine; 2, a fit counted as generation; lesson 5, an uncertified step | it is a search for a representation, never a learning result: its successors are never the machine's continuation, no clock or commit moves, and each is certified exactly through the actual release; it reads only the machine's own readings and the declared targets, never the terrain's rule, lag or key family |
| The retention reads keep earlier constitutions' fixed contexts (§2.2) | D3, retention by archive; lesson 4, an index | the list of contexts lives only in the measuring process; the machine never reads it; the constitution's retained state is its continuing state alone (§1) |
| Solved counts under interventions, the excess `X` as the search's merit | 7, a local pass or a scalar read as progress; D4 | every cell is reported whole, by its exact predicate; no count is progress and no intervention's count is a result about learning; the search's merit orders its trials only, and its answer is the strict test at all 64 terms |
| Seed `2_026_093_061` for every experiment | 6 and 8, seen material graded as unseen | it is gate A's development set, seen, and every reading on it is labelled so; a witness's scope is read once on a fresh development seed (§5); the final confirmation stays unread |
| Fixed deadlines from §6's reads | 9, a refusal answered with a larger limit | each run's deadline is its projection's upper end under an outer `timeout`, never raised; a run past it is reported incomplete, and the next loop changes the law, the partition or the read |
| The landing's parts stated as the span's mass and a datum's image | 3, text as the exception; 11, a design thought in arrays | the parts are the tube's: the transported mass, a systolic reduction over carried powers `ρ^r` read from the station, and a datum's image at its residue; nothing reads a byte, a pixel or a class's meaning, so an image's scan ticks, an acoustic stream's sample ticks and a motor word's steps read the same factorial |
| Telescoping attributions | the process failure "failure reports that name no mechanism", and its converse, a mechanism named from one order | both orders are always printed with the interaction (Lean `telescoping_orders_differ_by_interaction`, `sequential_attribution_depends_on_order`); no order is labelled causal |

## 1. Experiment 1a: the exact replay [definition; agent-inferred]

**Saved.** Gate A saved one complete continuing state, its best constitution 1
(`witness_best.state`). The other sixteen constitutions of its native continuation were read and
printed but not saved.

**The replay.** Gate A's pinned procedure, unchanged (`executed witness order2 2026093061 8 16 …`,
the candidate's own move on the same 8 requests from the founded opening), run with a states
directory: every constitution read writes its complete continuing state `c<k>.state`,
`k = 0 … 16`. The only change to the harness is that write (§8). It passes when all of these hold:

1. every constitution line and every move line equals gate A's receipt (`witness.txt` lines 2–34),
   the wall times masked; each move line carries the owner's persistence reads, so they are
   replayed too;
2. `c1.state` is byte-identical to `witness_best.state`;
3. each `c<k>.state` restored whole onto the declared opening writes back to its own text, and its
   reading reproduces the replay's: the coupling run (§2) restores every state, prints the
   write-back, and its native decision-term count and persistence tuple must equal the replayed
   lines (falsifier 2, §9); at `k = 1` the 72 lines of gate A's printed best (8 release lines, 64
   decision terms) were already reproduced exactly from the saved state by the development read
   (§6.1), and `c1.state` is that state byte for byte (item 2).

The replay is the baseline of every reading of the native continuation below. A mismatch stops
every run that consumes it (persistence and coupling, reach), and the mismatch is the next loop's
subject; the representation search, which reads only the founded opening and the set, is
reported apart.

**Its law** (Lean `HNN/ExecutedComparison.{restoreStanding, restored_continuation_agrees,
equal_states_agree}`, §7): with `S` the complete continuing state and `R` its continuation onto the
declared opening, `R(S Θ) = Θ` on the admitted constitutions makes `S` a standing law, so every
admitted future observation after any word of receptions reads the same from the restored
constitution as from the native one. `R(S Θ) = Θ` itself is the Rust owner's, held by its test
(`a_restored_checkpoint_continues_exactly_over_successive_receptions`) and measured here by items
2 and 3.

## 2. Experiment 1b: persistence and coupling [definition; agent-inferred]

### 2.1 The population, the contexts and the criterion

At each constitution `Θ_k` (`k = 0 … 16`, the replay's), each request `q` (8) and each station `j`
(8), the release is read under an order `O` (§2.4; the native order is the release's own):

- `λ_O(j)`: the refinement that locked `j`, if any; `C_j` the stations locked with it at `λ_O(j)`;
  `L_j` the stations locked at later refinements;
- **the decision section** `S_λ(j)`: the cells placed when `λ_O(j)` was read (station `j` open); for
  a station never locked, the last refinement's;
- **the release section** `S_rel(j)`: every lock of the release placed, `j` open
  (`S_rel = S_λ ∪ C_j ∪ L_j`);
- **the decision term** `d(j)`: gate A's reading (`λ_O(j)` when it lies before `r*`, else `r*`,
  `executed::sites_of`).

**The criterion** at a section is the strict rational test on the five candidates' exact joint
enclosures there, `1 + Σ_(x≠t) U_x < L_t` (holds, fails at `1 + Σ_(x≠t) L_x ≥ U_t`, else
undecided), the same function `executed::lock_face` gate A read. Every reading below names its
station, its section and its constitution; two readings are compared only when all three are
declared.

### 2.2 The three solved notions, apart

With the same station, the same context and the strict criterion:

- **solved at a refinement**: for a locked station, the criterion holds at `(Θ_k, S_λ(j))`, the
  section the release decided `j` in. The decision term at `d(j)` is read beside it (gate A's
  count); the two are one reading where `d(j) = λ(j)` and differ where gate A read the station at
  `r*` instead (a lock at or after `r*`, or none: gate A's "held"). A station never locked is read
  at its last refinement and counted apart.
- **solved at the actual release**: for a station solved at its refinement with a later lock
  (`L_j ≠ ∅`), the criterion holds at `(Θ_k, S_rel(j))`. This is the owner's persistence read
  (`executed::Persistence`): on the native order the harness prints
  `Persistence { locks, solved, reread, stay, fall }` in the owner's form, and it must equal the
  replayed move line's tuple at every `k ≤ 15` (a falsifier of the harness, §9). A station whose
  release placed no later lock is counted apart.
- **retained after later releases**: for a station solved at `(Θ_k, C)` with `C ∈ {S_λ(j),
  S_rel(j)}` of the native release, the criterion holds at `(Θ_k′, C)` for each later constitution
  `k′ > k`: the same station in the same fixed section, after the continuation's later moves and
  releases. Beside it, labelled as a different context, the own-context counterpart: solved at
  `Θ_k′`'s own `S_λ` and `S_rel`.

### 2.3 Which part of the joint field undoes a solved decision: the paired counterfactual

**The event** (native order): `j` solved at `S_λ(j)`, not solved at `S_rel(j)`, with `L_j ≠ ∅`.
Its landings are `C_j ∪ L_j`.

**The landing's two parts are exact** (Lean `HNN/IndexedOpen.transported_weight_insert`,
`transported_weight_insert_scale`). Read from `j`, a datum `k` landing on a span `S` gives
`z_j(S ∪ k) − z_pairs = μ (z_j(S) − z_pairs) + w_k I_k`, with `μ = M_j(S)/M_j(S ∪ k) ∈ (0, 1)` the
span's transported mass before over after (**the normalization**: `k`'s share of the mass taken
from every earlier datum alike, the request's included) and `w_k I_k` its image at its weight
(**the entry**). The realization charts each weight (`PopulationChart::chart`), so every cell below
is read by its own definition (`BankPlacement::storage_over`), and the split holds per cell exactly
(the owner's test `a_landing_splits_into_its_normalization_and_its_entry`), not across cells.

**The factors**, each a diagnostic, never a law:

- **N, the placement's normalization over the span's mass**: native (the mass of the section read),
  or frozen at the decision's mass `M_j(S_λ)`;
- **D, the later data's entry into the span**: native (the landings' images enter), or absent;
- **O, the release's order** (§2.4): the native order, ascending, descending;
- **B, which landings land** (native events only): every subset of `C_j ∪ L_j`, at the native law.

**The cells, paired by (constitution, request, station)**:

| Cell | Data entering | Mass | Reading |
|---|---|---|---|
| `N0D0` | `S_λ` | `S_λ` | the decision's own (solved at a refinement) |
| `N1D0` | `S_λ` | `S_rel` | the normalization alone |
| `N0D1` | `S_rel` | `S_λ` | the entry alone |
| `N1D1` | `S_rel` | `S_rel` | the release's own (solved at the release) |

read for every locked station with a landing under every order; and for every native event,
additionally, every subset `B` of its landings at the native law (the lattice; `B = ∅` is `N0D0`,
the full set `N1D1`), each landing alone with its normalization alone and its entry alone, and the
later stations entered at their targets (the terrain's, read here only as instrumentation, as gate
A's comparison reads them).

**What is reported** (nothing is read as a cause):

- the binary outcome: each station's four-cell pattern under each order, and the counts of the
  sixteen patterns by order and constitution. The patterns are named by their cells, never by a
  cause: *the normalization alone undoes* (`N1D0` not solved), *the entry alone undoes* (`N0D1` not
  solved), *jointly only* (both alone solved, `N1D1` not: an interaction), *either alone undoes*;
- the continuous outcome: `ℓ` enclosed in every cell, and the contrasts in both orders, the
  normalization first (`ℓ₁₀ − ℓ₀₀`, then `ℓ₁₁ − ℓ₁₀`) and the entry first (`ℓ₀₁ − ℓ₀₀`, then
  `ℓ₁₁ − ℓ₀₁`), with the interaction `ℓ₁₁ − ℓ₁₀ − ℓ₀₁ + ℓ₀₀` enclosed. The two orders' attributions
  differ by exactly the interaction (Lean `telescoping_orders_differ_by_interaction`) and on the
  binary criterion either part can be named by the order alone (Lean
  `sequential_attribution_depends_on_order`): both are printed, neither is called the cause;
- the lattice: every subset's predicate and `ℓ`; the minimal undoing sets (not solved there, solved
  at every proper subset); whether undoing is upward closed; and the Möbius interactions
  `μ(B) = Σ_(B′⊆B) (−1)^(|B|−|B′|) ℓ(B′)` of order two and more whose enclosure excludes zero, with
  the count that straddles zero. The native chain is one path through the lattice; the lattice keeps
  every order of the same landings;
- the order: §2.4's readings, paired.

### 2.4 The release's order [definition; agent-inferred]

`prediction::LockOrder`: the release's law is `Gap`, the stations of the largest positive gap
locking together. The diagnostics change only which of the same eligible stations (each top's flip
and lock certified, its gap positive) a refinement locks: `Ascending` the eligible station of least
index (the receiving ring's clock direction from the request's last tick), `Descending` the
greatest, one lock a refinement; the readings, eligibility, certificates and stopping rules are the
release's own (the owner's test `the_release_under_a_declared_order_keeps_the_releases_rules`). Under
each order every station is read in its own decision and release sections (§2.1), with its own
four-cell landing factorial (§2.3). Reported per order: the locks and classes, whole sections,
stations right, the three solved notions' counts, the persistence tuple, and each station's
pattern, paired with the native order's by (constitution, request, station). A release a
diagnostic order meets with an inadmissible crossing is reported refused, by request.

**Why these two orders** [agent-inferred]: they are the two orders of the clock itself, read
without the gap; at gate A's best constitution the native order locked from station 7 down to
station 0, one a refinement, so `Descending` brackets the native order where it is clock-like and
`Ascending` is its reverse. Neither is a candidate law.

## 3. Experiment 2: representation [definition; agent-inferred]

### 3.1 The question and its criterion

**Does any admissible shared constitution solve every station of the declared development set?**
The set: gate A's, order-2, seed `2_026_093_061`, 8 requests, 64 decision terms. The criterion is
gate A's witness: the strict test holds at every one of the 64 decision terms `d(j)` of each
request's own release, read through the actual continuing mechanism (`executed::compare` with
`Comparison::LOCK_DECISIONS`, the release's actual executed contexts). Never independently fitted
station charts, never a teacher-forced substitute.

**Admissible**: one constitution for all 8 requests; the declared opening (the field, the bank and
its members and pumps, every other locus) with the source port `E` and the transport modulus `ρ`
replaced; `E` on the source port's lattice `2^(−21)` with every entry in `[−2³, 2³]` (the entry
bound); `ρ` on the same lattice in `(0, 1]` (passive); the constitution's exact bits within its
budget `2³³`; every crossing of every request's release admissible (the reading refuses an
inadmissible one), every lock's Floquet certificate certified, every reading supported. The release
reads `E` and `ρ` alone, so a witness is stated by them; it is a representation diagnostic, not a
constitution the machine reached, and its file says so.

### 3.2 The search: the exterior fit, other than the candidate's own move

From the founded opening (gate A's constitution 0), at most **16 iterates** (the candidate's 16
moves of gate A, so the two procedures' budgets match in count), each:

1. **Read** every decision term's lock face `ℓ_j` and its gradient (`executed::site_gradients`): the
   lock face's covector `θ − q` at the shares' dyadic faces, through every candidate's leading
   member's storage covector at its dyadic face, pulled back to `E` at the placement's fixed weights
   (the storage is linear in `E` there) and to `ρ` through `∂z/∂ρ`. The identity is the owner's test
   (`each_decision_terms_gradient_is_its_pullback_to_e`: `⟨∂ℓ/∂E, ΔE⟩` equals the contributions'
   `Σ c ⟨ĝ, δz⟩` exactly).
2. **The active terms** `A`: those with `ℓ_j⁺ > ℓ* = (15/16) · (ln 2)⁻`, the solved level less one
   sixteenth of it (the receiver's grain `L_R = 16`); a term whose candidates' leading members are
   not all resolved is omitted and counted. Each row `J_j = (∂ℓ_j/∂E, ∂ℓ_j/∂ρ)` at 64 significant
   bits, its residual `r_j = ℓ_j⁺ − ℓ*`.
3. **The step**: the least-norm Gauss–Newton step placing every active term at the level at once,
   `Δ = −Jᵀ (JJᵀ)⁻¹ r`, solved exactly (the Gram's fraction-free inverse); a singular Gram is shifted
   by `μ = tr(JJᵀ)/(|A| · 2¹⁶)` and the shift printed.
4. **The ladder**: from `η₀ = min(1, 2^⌊log₂(2³/max|Δ_E|)⌋)` (no entry moved past the entry bound in
   one trial), halving, at most 8 trials (`LADDER_DEPTH`). A trial projects `E + ηΔ_E` onto the
   lattice (nearest, ties up) and the entry box, and `ρ + ηΔ_ρ` onto the lattice in
   `[2^(−21), 1]`, and **certifies it exactly**: its own release's 64 decision terms (solved count
   `S′`, excess `X′`), the iterate's frozen decision sites re-read there (`executed::frozen_reread`,
   solved count `F′`), its admissibility. Every certified admissible trial is read for the witness
   (`S′ = 64` is a witness wherever it occurs) and for the best (the most solved, the earliest among
   equals). A trial is **adopted** when it is admissible and its own release's excess is strictly
   lower by disjoint enclosures, `X′⁺ < X⁻`; else the next `η`. [agent-inferred, after the
   development read §6.1] The excess `X = Σ_j (ℓ_j − ln 2)_+` is the feasibility search's merit: it
   is zero exactly where every term is in the solved level (a boundary term at `ℓ = ln 2` aside, which
   the strict test never counts), and it moves continuously where the solved count moves by whole
   stations. A lexicographic merit, the solved count first, was written first and refused on the
   timing seed's development iterate a trial that lowered `X` from `[297681/4096, 297686/4096)` to
   `[225160/4096, 225165/4096)` nats while its own release solved one station fewer: it would stall
   a search whose question is reaching the solved level at all 64.
5. **Stop** at a witness (`S′ = 64` at a certified admissible trial, or `S = 64` at an iterate's
   reading), when no trial is adopted (the set is fixed: the next iterate would repeat it), when the
   iterates are spent, or at the deadline (checked before each iterate).

**How it differs from the candidate's own move**: no normal-law prepared step (the step is set in
`E`'s own coordinates, not through the source port's carried Gram), no fixed-mask descent guard,
no first-order certificate as a commit guard (each successor is certified by its exact readings
instead), every active term driven to the level at once by the least-norm step, a trust region
bounded by the entry box rather than the founding's half, and its own release's excess as the merit
(the candidate's move descends its incumbent's fixed mask). Nothing is deposited: no clock, commit
or carried Gram moves, and no successor joins the machine's continuation.

### 3.3 The scope labels

- **"witness found"**: some certified trial or iterate solves all 64 at its own release's decision
  terms; written as `E` and `ρ` (a representation diagnostic) and printed whole, every decision term
  with its whole sections; its three solved notions and landing factorial (§2.2–§2.4) are read by
  `executed coupling` on its file (`check-witness`, §6.2);
- **"frozen-context witness only"**: some trial solves all 64 frozen sites (the previous iterate's
  decision sections) while its own release does not: narrower scope, a representation in frozen
  contexts, not a witness;
- **"no witness found within this procedure and budget"**: otherwise, with the best solved count and
  how it was reached; never "infeasible".
- **Scope of a witness**: if one is found, it is read once on a fresh development set (seed
  `2_026_100_101`, 8 requests): whether it carries the key or fits the set. Labelled as scope, never
  an acceptance.
- Never a learning result, whatever it finds.

## 4. Experiment 3: reach, only if a witness exists [definition; agent-inferred]

Not built until a witness exists; its law is fixed here.

- **The compared**: the native continuation's constitutions `Θ_0 … Θ_16` (the replay's) and the
  certified witness `Θ_w`.
- **Source alignment**: both read on the same 8 development requests through one ingestion (one
  current and moment a request), on the same declared opening's other loci and the same bank. `E` is
  compared in the source port's own coordinates: rows the receiving ring's storage, columns the
  chart's classes, no class permutation (the targets name classes). The ring's rotation `P^s` of
  `E`'s rows is admitted as a gauge only where it leaves every one of the witness's 320 decision
  readings (64 sites, 5 candidates) exactly equal, checked exactly; the identity is always admitted.
  The candidates are the 15 rotations by a multiple of 4 below the period 60 [agent-inferred: 4 is
  every bank member's pump period, so such a rotation leaves each member's schedule; whether it
  leaves the readings, the pair ports' read included, is what the exact check decides].
- **Context alignment**: every decision site read at both constitutions in the same section: the
  witness's decision sections at each `Θ_k`, and each `Θ_k`'s own decision sections at `Θ_w`. Never
  one's own trajectory against the other's.
- **The readings, per `k`**: geometric, the exact squared distance `min_s ‖E_k − P^s E_w‖²` over the
  admitted gauge and `|ρ_k − ρ_w|`, and each native move's exact pairing with the direction to the
  witness, `⟨E_(k+1) − E_k, P^s E_w − E_k⟩`, with its squared cosine as an exact ratio; decisional,
  the witness's sites solved at `Θ_k` in the witness's sections, `Θ_k`'s sites solved at `Θ_w` in
  `Θ_k`'s sections, and every site's `ℓ_k − ℓ_w` enclosed.
- **Geometric distance alone need not track decision progress**: both are printed for every `k`;
  a falling distance is never read as progress, nor a rising one as regress.

## 5. The seeds [definition; agent-inferred]

| Seed | Role | Read by |
|---|---|---|
| `2_026_093_061` (8 requests) | gate A's development set: every experiment's subject | the replay, persistence and coupling, representation, reach |
| `2_026_093_062` (8 requests) | gate A's timing seed | §6.1's cost reads only, never an experiment |
| `2_026_100_101` (8 requests), fresh | a witness's scope, read once | only if a witness is found (§3.3) |
| `2_026_093_033/036/039` | the final confirmation | **unread** |

`2_026_100_101` is fresh: `git grep -E "2_?026_?100_?1[0-9]{2}"` over every branch (`main`,
`archive/leftovers-2026-09-24`, `protein-crate`, `origin/main`, `origin/codex/apple-silicon`) and a
grep of the main checkout's, this worktree's and the protein worktree's `research`, `crates`, `docs`
and `tools` return nothing in the whole family `2_026_100_1xx`. No training or validation seed of
1a or 1b is read.

## 6. Costs, deadlines, threads and the early stop

### 6.1 The measured development reads [measured]

Development reads only, on this host (24 hardware threads; the desktop's own processes beside
them, no other worker's run), each launched in the background by `loop_1c_runs.sh`, its artifacts
in the worktree's `.local/1c/`. None reads an experiment's question: the replay reads reproduce
gate A's printed output, and the coupling and fit reads run on gate A's timing seed
`2_026_093_062`; their readings are printed in the artifacts and are not interpreted here.

| Read | Threads | What it measured | Wall (ms) | CPU | Peak resident (bytes) |
|---|---|---|---|---|---|
| `cost-replay`: `witness_best.state` restored and read | 19, alone | the restore and one release read of 8 requests: 38,939; **it reproduces gate A's summary line and its 72 printed lines exactly, and the state writes back to its own file** | 38,982 | 1016 percent | 76,623,872 |
| `cost-move`: gate A's procedure, 1 move, states written | 19, alone | move 0: 115,542 (gate A: 109,917 at 24 threads); constitution 1's read 39,316; **gate A's three lines reproduced and `c1.state` byte-identical to `witness_best.state`** | 154,921 | 1154 percent | 189,038,592 |
| `cost-coupling`, the timing seed's founded opening | 19, alone | the three orders' releases and every station's reads, 6,840 readings: 64,808; 5 events' lattices, singletons and target entries, 2,865 readings: 11,321; in all 9,705 readings: 76,525; **the native `Persistence { locks: 64, solved: 6, reread: 6, stay: 1, fall: 5 }` and the 4 of 64 decision terms are gate A's own reading of this opening** | 76,567 | 1239 percent | 76,582,912 |
| the same, the orders read one after another (the harness's first form) | 19, alone | the same listing exactly, 113,417 | 113,462 | 792 percent | 75,034,624 |
| `cost-split`: gate A's move 0 | 12, beside the fit at 7 | move 0: 154,771; constitution 1's read 44,458; `c1.state` byte-identical again | 199,296 | 919 percent | 181,030,912 |
| `cost-split`: one iterate of the exterior fit, the timing seed | 7, beside the move, then beside the coupling read at 12 | the gradients (64 terms, 320 candidates' covectors and their pullbacks): 83,271; the Gram and the step (60 active terms, invertible): 18,894; three trials 93,424, 78,393, 89,911; the iterate 363,939; the last read 81,014 | 445,006 | 481 percent | 151,232,512 |
| `cost-coupling-12`, the timing seed's founded opening | 12, beside the fit at 7 | releases and stations, 6,840 readings: 95,349; the events, 2,865 readings: 17,667; in all 113,445; the same persistence tuple | 113,489 | 844 percent | 70,574,080 |

The coupling read's first form read the three orders one after another; reading them as co-present
regions (one placement, one output each) took the constitution from 113,417 to 76,525 ms with the
listing unchanged, and that form is the one projected.

### 6.2 The projections and the fixed deadlines

Each projection is the declared count of units times the measured upper time a unit, at the
thread count the run will hold (§6.3); the deadline is the projection's upper end, enforced by an
outer `timeout` in `loop_1c_runs.sh`, with the run's own deadline checked before each unit set so
that a unit started before it ends inside the guard. None is ever raised.

| Run | Unit and its measured upper | Count | Projection (ms) | Own deadline (ms) | Outer guard |
|---|---|---|---|---|---|
| `exp-replay` (12 threads) | a move: gate A's slowest, `211,948 · 154,771/109,917`, so **298,438** (the measured move 0 at 12 threads over gate A's move 0); the last read 44,458 | 16 moves and 1 read | expected `(154,771/109,917) · 2,726,567 + 44,458 = 3,883,660` (gate A's moves scaled); upper **4,819,466** | 4,476,570 | `timeout 4820` |
| `exp-coupling` (12 threads) | constitution `k`: `⌈95,349 · 7,200/6,840 + (17,667/2,865) · (4,290 + 640k)⌉`, from **126,822** at `k = 0` to **189,967** at `k = 16`: the releases at their largest reading count (one lock a refinement, 7,200 readings with the station reads), at most 6 events of at most 7 landings (4,290 readings; gate A's persistence tuples have at most 6 falls at any constitution 0–15, and constitution 16 is held to the same bound) and at most 128 retained contexts from each earlier constitution (5 readings each), at the measured rates | 17 constitutions | upper **2,692,707** | 2,502,740 | `timeout 2693` |
| `exp-represent` (7 threads) | an iterate: the gradients 83,271, the Gram 18,894 and eight trials at the slowest measured 93,424, so **849,557**; the last read and the scope read 81,014 each | 16 iterates and 2 reads | upper **13,754,940** (an iterate whose first trial is adopted, as the timing seed's was by the excess, reads near 195,589) | 12,743,355 | `timeout 13755` |
| `check-witness` (12 threads), only if a witness | the witness's read in a fresh process, 44,458 (the release's largest reading count; the process's setup measured under 50 ms); then its coupling reads, one constitution at `k = 0`, 126,822 | 1 and 1 | 44,458 and 126,822 | 126,822 for the coupling | `timeout 45`, `timeout 127` |
| reach (12 threads), only if a witness | a constitution's 640 context-aligned readings at the release phase's measured rate `95,349/6,840` ms, **8,922**; the gauge's certification, 15 rotations of 320 readings, 66,912 | 17 constitutions and the gauge | upper **218,586** | 209,664 | `timeout 219` |

Reach is not built; its first constitution is its own development read, and §6.4's early stop
holds it to the bound above. Peak resident sets measured stay under 200,000,000 bytes a process;
the four processes of the whole schedule hold under 1,000,000,000 bytes together.

### 6.3 The thread reservation and the schedule

**Reservation: 19 threads.** The host has 24; Codex has reserved at most 5. Every run of this loop
fixes its rayon pool by `RAYON_NUM_THREADS`, and the runs alive at any moment sum to at most 19
(the Lean and test gates are held to 19 processors by `taskset -c 0-18`). Memory: under
1,000,000,000 bytes for the whole schedule.

| Phase | Runs together | Threads | Starts | Upper end from the launch |
|---|---|---|---|---|
| 1 | `exp-replay` beside `exp-represent` | 12 + 7 | at once (independent: the fit reads the founded opening and the set, never the replay's states) | the replay by 4,820 s |
| 2 | `check-replay`, then `exp-coupling`, beside the continuing `exp-represent` | 12 + 7 | when the replay ends and its check passes (the coupling reads its states) | the coupling by 7,513 s |
| 3 | `check-witness`, then reach, only if a witness | 12 | when the fit ends (reach needs the witness and the replay's states) | the fit by 13,755 s, the checks by 13,927 s, reach by 14,146 s |

The split is the measured one (§6.1: the move read at 12 threads beside the fit at 7, and the
coupling read at 12 beside it). A failed check stops what consumes it: a replay that does not
reproduce gate A stops the coupling and reach (falsifier 1), and the fit, which does not read the
replay, runs on and is reported apart.

### 6.4 The early stop

Each run prints one line a unit (a move, a constitution, an iterate) with its elapsed
milliseconds, and one Monitor per run watches that line with a filter that also matches every
failure (`error`, `panic`, `Killed`, `exit`). When a unit's measured time passes its per-unit upper
bound (§6.2), the run is
stopped there and reported incomplete with its measured rate, and the projection's error is
reported as such; it is never waited out, and never relaunched with a larger deadline, timeout or
budget. A run that reaches its deadline is stopped by its own check before the next unit, or by the
outer `timeout`, and reported incomplete. The next loop changes the law, the partition or the
declared read, and says why.

## 7. The formal statements [proved-derived; formal-checked, or owed as stated]

| Statement | Where | Status |
|---|---|---|
| a landing splits into its normalization and its entry, `z(S ∪ k) = μ z(S) + w_k I_k` with `μ = M(S)/M(S ∪ k)` | Lean `HNN/IndexedOpen.transported_weight_insert` | proved |
| the normalization's scale lies in `(0, 1)` | `HNN/IndexedOpen.transported_weight_insert_scale` | proved |
| on the chart, each cell's split per cell: `storage(S ∪ k) − storage_over(S, S ∪ k)` and `storage_over(S ∪ k, S) − storage(S)` are each `k`'s entry at its weight | Rust `hnn::tests::coupling::a_landing_splits_into_its_normalization_and_its_entry` | tested |
| the two telescoping orders differ by the interaction, each sums to the whole | `HNN/ExecutedComparison.telescoping_orders_differ_by_interaction` | proved |
| on a binary criterion a sequential attribution can name either part by its order | `HNN/ExecutedComparison.sequential_attribution_depends_on_order` | proved (counterexample) |
| the restore law as a standing law; the restored continuation agrees on every admitted future; equal states agree | `HNN/ExecutedComparison.{restoreStanding, restored_continuation_agrees, equal_states_agree}` | proved, from the hypothesis `R(S Θ) = Θ` |
| `R(S Θ) = Θ` for the executed move's constitutions (`Constitution::continued` of `continuing_state`) | Rust `a_restored_checkpoint_continues_exactly_over_successive_receptions`; the replay §1 | tested and measured; its Lean statement on the constitution, with the move's determinism, owed (#62, gate A's item 3) |
| the decision term's gradient is the lock face's pullback at fixed weights | Rust `each_decision_terms_gradient_is_its_pullback_to_e`; the pullback's law at one weight is `HNN/Moment.encoder_covector_tape_free` (the response to `δE` is the transpose contraction of the counts), the covector `HNN/ExecutedComparison.lockFace_covector` | tested; the joined statement at the station-framed weights owed (#62) |
| the frozen sites at their own constitution are its terms | Rust `the_frozen_sites_at_their_own_constitution_are_its_terms` | tested |
| a diagnostic order keeps the release's eligibility, certificates and stops | Rust `the_release_under_a_declared_order_keeps_the_releases_rules` | tested; `decisions_release_the_section` abstracts the release's lock rule, so no order-specific Lean is owed |
| the Möbius interactions over the landings' lattice sum to the whole change, `ℓ(L) − ℓ(∅) = Σ_(∅≠B⊆L) μ(B)` | Möbius inversion on the Boolean lattice (Rota) | proved-standard; its Lean statement owed (#62); the harness computes each `μ(B)` from its definition, and nothing depends on the sum |

## 8. What was built for the cost reads (no experiment run)

Only what the cost reads needed; every addition is a diagnostic or a reading, labelled so in its
owner, and nothing the release, the move or the retained state reads changed.

**The library** (`crates/holonics`):

- `hnn::prediction::BankPlacement::storage_over` (the storage read over another span's mass; the
  release's `storage` is it at `mass = data`, and `weights` delegates to the private
  `weights_over`): the landing's cells (§2.3).
- `hnn::prediction::{LockOrder, bank_release_ordered}`: the release's order as a diagnostic factor;
  `bank_release` is `bank_release_ordered(…, LockOrder::Gap)`, so the release, `generate_by_bank` and
  `executed::compare` read exactly as before (§2.4).
- `hnn::executed::{SiteGradient, site_gradients, frozen_reread}`, and `sites_of` made public: the
  representation search's readings, no move made (§3).
- Four tests, `hnn::tests::coupling`: `a_landing_splits_into_its_normalization_and_its_entry`,
  `the_release_under_a_declared_order_keeps_the_releases_rules`,
  `each_decision_terms_gradient_is_its_pullback_to_e`,
  `the_frozen_sites_at_their_own_constitution_are_its_terms`.
- The module tables of `hnn::prediction` and `hnn::executed` name the new owners; the atlas gains
  `hnn.landing-split`, `hnn.landing-telescoping`, `hnn.release-order-diagnostic`,
  `hnn.restore-standing` and `hnn.site-gradient`.

**The harness** (`research/notebook/hnn_design`):

- `executed witness … [<states dir>]`: gate A's procedure unchanged, writing every constitution's
  complete continuing state when given a directory.
- `hnn_loop_1c.rs`: `executed replay` (a complete state restored whole and written back, or a file of
  `E` and `ρ` alone read as a labelled partial remount), `executed coupling` and `executed represent`,
  each stated in the module's header.
- `loop_1c_runs.sh`: the cost reads and their checks, and the experiments' runs with §6.2's fixed
  guards and §6.3's thread counts. None of the experiments' runs has been launched.

**Not built**: the reach mode (§4), which is built only if a witness exists, against the law fixed
here; its first constitution is its own development read under §6.4's early stop.

**Lean**: `HNN/IndexedOpen` gains `transported_weight_insert` and `transported_weight_insert_scale`;
`HNN/ExecutedComparison` gains its §8 (`telescoping_orders_differ_by_interaction`,
`sequential_attribution_depends_on_order`, `restoreStanding`, `restored_continuation_agrees`,
`equal_states_agree`) and imports `Foundation/Standing`.

**The gates** [measured], each held to 19 processors:

| Gate | Result |
|---|---|
| `cargo check --workspace --all-targets` | clean, no warning |
| `cargo test -p holonics --lib` | **886 passed**, 0 failed (882 at `44338508`; the four of `hnn::tests::coupling` added), 163,490 ms |
| `bash research/notebook/hnn_design/replay_baseline.sh` | the listing matches the baseline reference (41 lines); the read 95,747 ms, peak resident 80,285,696 bytes: the release, the comparison and the move read exactly as before |
| `bash tools/lean_check.sh Holonics HolonicsResearch` | built, no error, no `sorry` (79,482 ms, on the main checkout's build reused); the new declarations' axioms printed by the modules' audits |
| the GPU suite | not run: no card-mirrored code changed |

## 9. The outputs, receipts and falsifiers

**Outputs**, each run's stdout whole, kept in the worktree's `.local/1c/` while it runs and copied
into `2026-10-01_LOOP_1C_receipts/` beside the measured record (output paths replaced by `<out>`):

- `replay.txt` (gate A's procedure re-run: every constitution and move line) and its check; the 17
  states `c0.state … c16.state`, each state's write-back printed by the coupling run;
- `coupling.txt`: per constitution, gate A's decision-term count, per order the persistence tuple,
  the counts of the three solved notions, every request's release and every station's line (its
  lock, its readings at the lock, at the release and at its decision term, its four cells and the
  contrasts in both orders); every native event's lattice, minimal undoing sets, closure, Möbius
  interactions, each landing alone and the targets' entry; the retention table; per-unit readings
  and milliseconds;
- `represent.txt`: every iterate's reading line, its active terms, the Gram's shift if any, the
  step's size, every trial (own solved, frozen solved, `X`, sections, admissibility, adoption), the
  verdict with its scope label, the best's 64 terms whole, and the scope reading if a witness; the
  best's `E` and `ρ` (`represent_best.txt`, labelled a representation diagnostic);
- only if a witness exists: `witness_check.txt` and `witness_coupling.txt` (its fresh read and its
  three solved notions and landing factorial), and `reach.txt`;
- each run's `.time` (wall, user and system CPU, exit) and the harness's resident line.

**The measured record** states, for each run, its projection, deadline, measured wall time, peak
resident set and the ratio of measured to projected, and every count above exactly; it shows no
float and no decimal.

**Falsifiers** (each stops the run or the claim it names):

1. *The replay*: any line of `replay.txt` differs from gate A's receipt with the wall times masked,
   `c1.state` differs from `witness_best.state` by a byte, or a state does not write back to its own
   text: the replay fails, and every run that consumes it stops (§1).
2. *The harness reads the owner's release*: at some `k ≤ 15` the coupling's native
   `Persistence { … }` differs from the replayed move line's, or its decision-term count from
   gate A's constitution line: the harness does not read the release the move reads, and its
   coupling readings are void (the development read reproduced both on the timing seed, §6.1).
3. *The cells are the landing's*: the `N0D0` cell of a station differs from its lock face at its
   refinement, or the `N1D1` cell from its re-read at the release (both are read by construction
   from the same function; a difference is a harness defect).
4. *A diagnostic order is the release's*: `LockOrder::Gap` differs from the release
   (`the_release_under_a_declared_order_keeps_the_releases_rules` holds it on the joint field;
   falsifier 2 holds it on the experiment's states).
5. *A witness is a witness*: the written `E` and `ρ`, read in a fresh process by `executed replay`
   as a remount of `E` and `ρ` alone (labelled partial; the release reads nothing else), must
   reproduce all 64 decision terms solved, every crossing admissible and every lock certified; else
   the claim is withdrawn.
6. *Reach's gauge*: a rotation is admitted only if every one of the witness's 320 readings is
   exactly equal under it; an admitted rotation that changes one reading voids the aligned distance.
7. *The thread reservation and the deadlines* (§6): a run found above 19 threads in all, or one
   that passed its outer `timeout`, is reported incomplete, never rerun with a larger limit.

## 10. What each outcome would motivate (motivation only; no next law is selected)

Every outcome is kept as it is; none selects a law, and the next loop's pin decides from the
mathematics with its own review.

**Persistence and coupling.**

| Outcome | What it would motivate |
|---|---|
| the native events mostly read *the normalization alone undoes*, the entry alone not | the span's transported mass, taken by each landing from every earlier datum alike, quenches a decided station: a placement whose decided data keep their weight across later landings, or a decision read only after the span's mass is complete |
| *the entry alone undoes*, and the later stations entered at their targets undo too | the pumped reading couples placed data so that even right landings undo a decision: the coupling is intrinsic to the bank's reading of the joint field; the representation's answer (§3) then says whether any constitution escapes it |
| the entry undoes with the release's landings but not with the targets | the undoing is a wrong lock propagating through the release: the release's eligibility and order (lock only what stays solved), not the placement |
| *jointly only* dominates (an interaction), or the lattice's minimal undoing sets are large | no part alone: the landing is one transport, mass and image together; a repair of one part alone would be refused |
| a diagnostic order keeps what the native order loses, paired station by station | the release's order carries the undoing; if every order loses alike, the order is not the part |
| solved decisions fall at the next constitution in their own fixed sections | the move itself undoes solved decisions (the certified descent on the incumbent's mask moves the constitution against stations its mask does not hold), distinct from the in-release coupling: the move's comparison scope |
| the minimal undoing sets are the landings nearest the station | the tube's locality: a frontier effect of the two-sided transport (`ρ^|i − j|`), not mass accumulation |

**Representation.**

| Outcome | What it would motivate |
|---|---|
| a witness found | the declared representation (the bank, `E`, `ρ`) expresses the 64 decisions through the actual mechanism; the obstruction is the move: reach (§4) then reads whether and how the native movement approaches it |
| a frozen-context witness only | the representation exists in fixed contexts, but each release's own contexts move away from it: the obstruction is the coupling of contexts, joined to experiment 1's readings |
| no witness found within the procedure and budget | within this search the declared operands did not express it; the adaptable operands left out (the bank's members, the pumps) and the reading near resonance stay the candidates THE_REBUILD names; never "infeasible" |
| a witness that solves the fresh set (§3.3) | it carries order-2's key; one that does not fits the set |

**Reach** (only if a witness exists): native moves whose pairing with the direction to the witness
is negative, or whose decisions at the witness's sections do not rise, motivate the move's
direction; a falling distance with no decisional rise is the case "geometric distance alone need not
track decision progress", motivating a decisional reading of reach, not a metric one.

## Amended after Astra's focused source review (October 1), before any run

Astra checked the 128-significant-bit enclosure of the joint certificate. It is interval arithmetic
with exact floor and ceiling, correct reversal of negative endpoints, four-corner products and
enclosures retained into later pairings; no rounding error is dropped. Deriving the precision from
the grain stays owed (#62) as an efficiency and contract obligation, not a soundness one. Two
amendments govern over any conflicting statement above.

1. **Checkpoint availability.** Gate A's harness wrote only its best constitution (`c1`). The other
   16 states are not saved. They are regenerated deterministically by gate A's own procedure
   (`exp-replay`), under its own measured budget (unit upper 298,438 ms a move, deadline 4,476,570
   ms, guard 4,820 s) and with full-state identity checks: gate A's 33 constitution and move lines,
   with wall times masked, and `c1.state` byte-identical to the saved one. No state is claimed as
   saved that was regenerated.
2. **Persistence has three statuses, never pooled.** The owner's receipt (`hnn::executed::
   Persistence`) now separates the decisions that do not stay solved into `reversed` (the strict
   test proved to fail: a proved loss) and `uncertified` (undecided on the enclosures: lost
   certification, not a proved reversal). `fall` is their sum, kept because gate A printed it, and
   the replay's comparison masks only the two new fields. Every reading and every counterfactual
   attribution in §1–§2 reports the three statuses apart: solved, reversed, uncertified. A decision
   that is no longer certified is never counted as reversed.
3. **Intermediate contexts against terminal assignments.** Placement depends on the placed cells, so
   each release-order comparison (native, ascending, descending) reports, for each decision, its
   reading at its own lock, in the intermediate context the order produced, and at the release, the
   terminal assignment, separately. The coupling mode's line already reads "solved at the lock"
   apart from "at the release solved, not solved, undecided".

The controls, the exact certification, the thread reservation (at most 19 threads, beside Codex's
5) and the fixed deadlines of §6 are unchanged. Gates B and C stay closed, and the final
confirmation `2_026_093_033/036/039` stays unread.
