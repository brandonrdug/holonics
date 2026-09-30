# The two counts: the terrain's unicity against the machine's, and the step's descent against the comparison's operating point (pinned before its runs)

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6, step 1, loop 1a). **Grade.**
[definition; agent-inferred] for the declarations, the stopping object, D1, D2, the seeds, the
projections and the prediction; [proved-derived] for the family's structure on each terrain (§2,
derived from the terrains' laws, not read from any run); [formal-checked] where a Lean owner is
named. No run of this loop has been made at this commit: every number below comes from a cited
record or from the terrains' laws.

**Occasion.** The [modulus record](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_MEASURED_THE_MODULUS_STAYS_BELOW_ONE_AND_ORDER_TWO_TRAINING_LEARNS_THE_LAG_ONE_COPY.md)
left order-2 at 0 whole sections of 128 after 1,024 rule steps, against a key family the
[unicity record](2026-09-30_UNICITY_THE_READINGS_LEAVE_ONE_KEY_AND_THE_HELIXS_CELLS_ARE_THE_FAREY_SEQUENCE.md)
§5 shows can be pinned in 7 readings. THE_REBUILD U6's step 1, loop 1a (revised under Astra's
review) fixes this loop: measurement only, no change to any learning law. This record pins it,
with Astra's three clarifications on the loop folded in before any run (the validation set's reuse,
§4; both units, §4; the line's global family as a tested result and `H`'s prior and reset, §1–§2).

The computational object is the helical pair interaction; the receiving bank's rings are complex
parametrons, read through the executed comparison. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches three: **faces
and placement** (the stations read, each datum's weight from its station), **the cell holonomy**
(the bank's executed growth over the turn, which the comparison reads) and **the tube** (the span's
transport, its modulus). The helix, the pair and the tower thread stay attached and unchanged:
nothing here changes a phase, a contact or a restriction.

## 0. The recorded failures this loop could repeat, and the rule for each

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and the
[prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):
- **1, an authored routine standing in for learning.** The key family is read-only
  instrumentation, computed by the harness from the terrain's pairs. Nothing of it (keys,
  survivors, the true lag, the continuations it admits) reaches the native receiver, its opening,
  its update or its release. The machine is trained by the unchanged law of the modulus record
  (`executed train executed-open`). The training comparison's use of the terrain's targets is a
  separate, declared input: the executed comparison `F` reads each training request's target
  section (`hnn::executed::Request::targets`), as it did in every prior loop; the validation reads
  read no target until the released section is scored.
- **6, seen material graded as unseen.** Fresh seeds (§3), searched across every ref tip, every
  commit's patch in history (`git log --all -G`) and every local run artifact: `2_026_093_030`
  through `2_026_093_099` appear nowhere. `2_026_093_021`–`026` are spent. The final confirmation
  is declared and read by no run of this loop. The alternation's and the line's request spaces have
  16 members each (§2), so their validation requests cannot be unseen as content: those two terrains
  are regressions, and the record says so beside every count.
- **7, bits read as progress.** Information is `log₂` of survivor ratios, reported in bits as its
  own reading, never equated with a descent of `F` and never read as the machine's progress.
- **9, a refusal answered with a larger limit.** Every run is projected and its deadline pinned
  (§6). A run past its deadline is reported incomplete and never rerun larger.
- **11, a design thought in the programming language.** The family is stated in residues and maps
  (§1): a lag is a displacement along the passage's clock, a map is a map of the residue ring
  `ℤ/4`, and the survivors factor as a coset product over the map's arguments.
- **4, a located cause carried unrepaired.** No new consumer is built on the executed comparison:
  this loop only reads it. Its located causes (the modulus record §5) are named as the expected
  blockers in §7.

## 1. The declared reference family

[definition; agent-inferred] It is a declared reference, not the machine's hypothesis class and
not a learning optimum. On each terrain the passage is the terrain's requests of `n = 40` cells of
`ℤ/4`, each continued by `m = 8` stations (THE_REBUILD step 1; `hnn_prediction … executed`'s
`order_declared`: alphabet 5 with the termination, ring period `60`).

- **Keys.** `κ = (ℓ, f)`, a lag `ℓ ∈ [1, 40]` and a map `f : ℤ/4 → ℤ/4`:
  `40 · 4⁴ = 10240 = 2¹¹·5` keys under the uniform prior (Lean `Unicity.order2_family_count`).
- **Emitter.** At each station `t ∈ [n, n + m)` of a request, `e_κ(t) = f(x_(t−ℓ))`, where
  `x_(t−ℓ)` is read from the request (`t − ℓ < n`) or from the same request's earlier stations. The
  initial history is the request's 40 cells: they are arguments, never observations. Each station is
  one observation, read in the machine's own training passage's order (request by request, station
  by station). The termination is not a rule step: no observation is a termination, and the
  machine's terminations are reported apart. No pair crosses a request boundary.
- **The survivors** after `k` observations are `S_k = {κ : e_κ(o) = x(o) for every o < k}`
  (Lean `Population.survivors`). For a fixed lag the map's values at distinct arguments are
  independent coordinates, so `S_k` is a disjoint union over lags of coset products (Lean
  `Population.survivors_product`): each argument `a ∈ ℤ/4` is observed with one value, unobserved
  (its fibre all of `ℤ/4`), or contradicted (the lag dies). Hence
  `#S_k = Σ_(ℓ alive) 4^(u_ℓ(k))`, `u_ℓ(k)` the lag's unobserved arguments.
- **The ideal listener** is the uniform mixture over the family. Its surprise at observation `k` is
  `log₂(#S_k/#S_(k+1))` (Lean `Population.survivor_code`), pathwise and exact, reported as the exact
  ratio `#S_k/#S_(k+1)` with its `log₂` enclosed on the declared grid (`log2_enclosure`) and read at
  `2^(−8)` bits.
- **Scopes.** Order-2 and the alternation keep one rule across requests: one key, scoped globally.
  The line's slope changes between requests, so it is read in the **hierarchical family** `H`: a
  global lag `ℓ ∈ [1, 40]` and a per-request translation `f_r(a) = a + c_r`, `c_r ∈ ℤ/4`. The line
  is read in the global family too.
- **`H`'s prior and its reset convention** (Astra's review). The prior is uniform on the lag,
  `1/40`, and, independently of the lag and of every other request, uniform on each request's
  translation, `1/4`. At each request boundary the translation's fibre **resets** to all of `ℤ/4`;
  the lag and its death carry across requests, a translation never does. The survivors are counted
  over the fixed passage of `R = 128` training requests, `[1, 40] × (ℤ/4)^R`, `40 · 4^128 = 2²⁵⁹·5`
  keys: `#S_k = Σ_(ℓ alive) Π_r #C_(ℓ,r)(k)`, `C_(ℓ,r)(k)` the translations consistent with request
  `r`'s observations before `k` (all four for a request not yet begun). Each observation's ratio is
  the same under any passage length (the unbegun requests' factor `4^(R − r)` cancels in it), so
  the curve is scoped to this convention and not to the choice of `R`. A lag dies in `H` when some
  request's translation fibre empties.
- **Counted explicitly**: at every observation the alive lags and their unobserved arguments; the
  **lag aliases** (alive lags other than the terrain's generating lag); the **constant requests**
  (the request's 40 cells one class; the alternation with `a = b`, the line with `s = 0`), whose
  observations are counted apart: every lag reads their one symbol as its argument, so they
  separate no lag.

## 2. What the terrains' laws imply for the family [proved-derived, before any run]

- **Order-2** (`x_t = x_(t−2) + 1`): the generating key `(2, a ↦ a + 1)` is in the family. Every
  other lag reads at stations 0–3 a request cell unrelated to the target (lag 4 is consistent with
  `+2` only from station 4 on, lag 6 with `+3` from station 6 on), so it is separated when those
  readings contradict a map value; the syntactic class can be one key.
- **The alternation** (`x_t = x_(t−2)`): every request has period 2, so every even lag `2k`,
  `k ∈ [1, 20]`, with `f = id` emits the same on every alternation request: 20 keys, one
  observational class, never one key. An odd lag must swap each request's pair; it survives only
  while the observed pairs form a matching, and a constant request forces `f(a) = a` against it.
- **The line** (`x_t = x_0 + st`): the generating law `x_t = x_(t−1) + s` is not a global key (the
  translation changes with `s`). Every lag `ℓ ≡ 0 (mod 4)` with `f = id` emits every line request
  exactly, since `x_t − x_(t−ℓ) = sℓ ≡ 0 (mod 4)`: the 10 keys `(4k, id)` are consistent with any
  line passage, so the global family cannot empty on any finite passage. Whether it empties on the
  actual passage is a tested result (Astra's review; THE_REBUILD's "where it must empty" is being
  corrected to say so): the counts read it, and this derivation is the prediction they test. Lags
  `≡ 2 (mod 4)` need `f = +2s`, which differs between odd and even slopes; odd lags need `f = +sℓ`,
  which differs with `s`; each dies only when the passage observes the conflict at a shared
  argument.
- **The line in `H`**: `x_t − x_(t−ℓ) = sℓ` is constant on each request for every lag, so **every
  lag survives in `H`** and the lag never collapses. A fresh validation request's translation is
  unobserved at its release, so `H` admits no unique continuation of a fresh request (four
  translations at least). Read beside it: `H`'s continuation of stations 1–7 given the request's own
  station 0.
- **Request spaces.** An alternation request is fixed by `(a, b)` and a line request by `(x_0, s)`:
  16 each. Any 64 validation requests and 128 training requests share content: those terrains read
  seen material by construction. Order-2's space has `4⁴⁰` members; training against validation is
  checked exactly, and the final confirmation's disjointness is left to its one read at 1b (the
  collision bound `64 · 128 · 4^(−40)` is stated, not a check).
- The alphabet's lower bound `clog₄ 10240 = 7` (Lean `Unicity.order2_unicity_lower`) holds on every
  terrain for the global family.

## 3. The seeds

| Role | Order-2 | The alternation | The line | Count |
|---|---|---|---|---|
| Training (the machine's passage; the counts' passage) | `2_026_093_031` | `2_026_093_034` | `2_026_093_037` | 16 moves of 8 = 128 requests |
| Validation (every checkpoint, both openings, the stopping object) | `2_026_093_032` | `2_026_093_035` | `2_026_093_038` | 64 requests |
| Final confirmation (never read in this loop; 1b's acceptance) | `2_026_093_033` | `2_026_093_036` | `2_026_093_039` | 128 requests |
| Development (timing, the modes' checks; readable) | `2_026_093_041`, `2_026_093_042`, `2_026_093_043` | the same | the same | as needed |

The draws are `terrain_pairs` (the harness's one terrain owner) at each seed; the three roles of a
terrain are distinct seeds.

## 4. The stopping object, `n*_terrain`, `n*_machine`

- **The stopping object** [definition; agent-inferred]: the survivors' observational class on the
  validation set `V`: `Cont_k(v)`, the set of continuations of `v`'s 8 stations that the survivors
  `S_k` emit freely (each key's own emissions are its later arguments; an unobserved argument emits
  every value), is one continuation for every nonconstant `v ∈ V`. **`n*_terrain`** is the least
  observation count `k` of the training passage at which it holds; the survivor list at `k` is its
  certificate. Reported beside it: the same with the constant requests of `V` included; the
  **syntactic class**, the least `k` from which `S_k` no longer changes, and whether it is one key;
  the alive lags, their unobserved arguments and the lag aliases at `n*_terrain` and at the passage's
  end; the ideal listener's curve (every observation's ratio, in the receipts; the head in the
  record); and the bits carried by the constant requests' observations apart.
- **`n*_machine`** [definition]: the machine trained by the unchanged law (`executed train
  executed-open`, the founded opening `E₀` at `ρ₀ = 102837/131072`, 16 moves of 8 fresh requests),
  its constitution written after moves 1, 2, 4, 8 and 16. **The exposure unit** is the training
  request, with 8 station observations each; a move reads 8 requests. Each checkpoint and both
  openings (the lossless `E₀` at `ρ = 1`, the founded `E₀` at `ρ₀`) generate every validation
  request from the open section (`generate_by_bank`). **The success rule**: every nonconstant
  validation request's section released whole (equal to its target at all 8 stations). `n*_machine`
  is the least checkpoint's exposure at which it holds, bracketed by the checkpoint before it; if it
  never holds, `n*_machine > 128` training requests (1,024 observations), a lower bound. Reported per
  constitution: released and held, whole sections (nonconstant and constant apart), stations right
  by station, the first lock's station and whether it is right, terminations, refused certificates,
  and every released section.
- **One validation set, reused** (Astra's review). The same 64 validation requests per terrain
  are read by both openings, every checkpoint and the stopping object. That makes the checkpoints a
  comparable diagnostic trajectory, not independent confirmations: a checkpoint's reading is never
  a confirmation of the one before it, and no checkpoint reading stands in for the final
  confirmation, which stays untouched (§3).
- **Both units, with the rounding stated** (Astra's review). Every count of the terrain and of the
  machine is reported in observations (stations) and in requests. An observation count `k` is
  `⌊k/8⌋` requests plus `k mod 8` stations (a stopping object reached mid-request is written
  "`q` requests plus `j` stations", never rounded to a whole request); the machine's checkpoints lie
  on whole requests (`8m` observations after `m` requests), and a bracket between checkpoints is
  reported in both units.
- The station-framed refit's 96 of 128 (a float fit read natively) is a scoped representation
  control, not evidence of native learning.

## 5. D1 and D2 [definition; agent-inferred]

Per move, with the batch, the objective `C` (the executed comparison `F = Σ (f)_+`, the owner's
convention: every refinement of the machine's own open-section trajectory, re-run at the successor),
the other operands (the bank, the pumps, every other family) and the evaluation convention frozen,
and `δ = (ΔE, Δρ)` the actually applied step (the adopted trial's carried successor less the
constitution):

**D1, the step's descent.**
- The **predicted descent**, two readings: the commit guard's certificate
  `−Σ_terms sup_(α active) Df_α[δ]`, and the leading branches' `−Σ_lead sign ⟨ĝ, Δz⟩` (the
  proposal's own gradient on the carried move). Each is an exact enclosure of a first-order quantity
  (the covectors' enclosures paired with the exact storage moves, the modulus's included); as a
  prediction of the finite change it is **approximate** (no second-order remainder is bounded, and a
  changed trajectory is not linear in `δ`).
- The **measured descent** `C(θ) − C(θ + δ)`, an **exact** enclosure from the two exact enclosures
  of `F`; and whether the successor's trajectory changed (a request whose lock order differs).
- **The projection and clipping**: the ladder's start `η₀ = 2^⌊log₂ min(F⁻/(−s⁺), ½/u)⌋` (the
  first-order zero against the founding's entry scale, `u` the unit move's largest entry change) and
  which of the two binds; **the ladder's halvings** (trials before adoption) and each trial's
  refusal; **the step's norm** (`‖ΔE‖_∞`, `Σ ΔE²` exactly, the entries whose lattice coordinate
  moved, the carry's released residuals, `Δρ`); **the active bounds**: passive (`ρ + ηΔρ` held at 1
  or at `ρ/2`), lattice (the carried modulus off its target; `E`'s lattice unit), entry (a trial
  refused past `2³`; the successor's largest entry).
- **Zero or below the grain, apart**: a move whose predicted descent is not positive (its first
  order not certified negative, or the move refused `NoDescent`), and a move whose predicted descent
  is below **the grain**, the width `F(θ)⁺ − F(θ)⁻` of `F`'s enclosure at `θ` (the least decrease
  the disjoint-enclosure guard can ever certify there).
- **Decisions moved**: at the open section (the one context both constitutions read alike) of every
  request of the batch, the stations whose top class went wrong→right, right→wrong and wrong→wrong
  at the successor.
- **The ideal listener's information in the same batch**: `log₂(#S_(64m)/#S_(64(m+1)))` bits over
  the move's 64 observations, in the global family (and `H` on the line), in its own unit and never
  equated with the descents: no normalization between nats of `F` and bits of survivors is proved.

**D2, the comparison's operating point.** Per move, at `θ`, over every station comparison of every
refinement of the batch:
- the **class gap** `γ = ln a_t − ln a_r` (`r` the rival of largest upper end), enclosed as
  `[ln L_t − ln U_r, ln U_t − ln L_r]`, and the **threshold margin** `μ = ln a_t`, enclosed as
  `[ln L_t, ln U_t]`, reported separately and signed (certainly positive, certainly negative,
  straddling zero), with their sums and extremes;
- stratified by the station's decision (its top class right; wrong and eligible, a **confident
  wrong** decision the release would lock; wrong and not eligible) and by constant against
  nonconstant request. A confident wrong decision is never pooled with a solved one;
- the **derivative of the executed objective along the actual feasible direction**: each term of
  `F`'s support, its `sup_α Df_α[δ]` on the carried move (a straddling term's hinge at zero), in the
  same strata, with its sign; a term whose derivative is exactly zero and a term whose derivative's
  magnitude is below its own term's enclosure width (its grain) are kept and counted apart.
  A large margin alone is not saturation.

D1 and D2 are candidate causes, not an exhaustive split. The other named causes: **conservative
certificates** (the sup over active branches and the disjoint-enclosure guard refusing descents
that exist), **the grain** (descents below `F`'s enclosure width), **feasibility** (the entry bound,
the passive bound, the lattice), **a wrong derivative** (predicted and measured of opposite sign),
**adaptable operands left out** (the move adapts `E` and `ρ` only; the bank's members, the pumps
and the other families are declared and fixed), and **an unsuitable objective** (a descent of `F`
that does not move the release's decisions). Both, neither or another outcome is kept as it is.

## 6. The runs, their projections and deadlines

The build is this branch's tip after the modes are added (the commit named in the result record);
the learning law is `6dc1e5ae`'s, unchanged. Host: 24 hardware threads (12 cores), 32,746,147,840
bytes of memory, 17,987,383,296 available at this commit. The trainings run as three processes at
once, each on a declared pool of 8 threads (`RAYON_NUM_THREADS=8`): independent processes on shared
immutable input with disjoint output. Projections are made from the modulus record's measured wall
times (one process on 24 threads: order-2 16 moves 3,533,424 ms, a move between 146,135 and 247,059
ms; the alternation 8 moves 1,318,739 ms; the line 8 moves 1,496,629 ms; a confirmation read about
1,951 ms a request with 24 threads; peak resident 268,255,232 bytes) with a pool factor between
`3/2` and `3` for 8 threads against 24 under contention.

| Run (per terrain) | Command | Projection | Deadline (the harness's), outer guard |
|---|---|---|---|
| The counts | `executed counts <terrain> <training seed> 128 <validation seed> 64 <out>` | 1,000–120,000 ms, 1 GB | 600,000 ms, 660,000 ms |
| Training, 16 moves of 8 | `executed train executed-open <terrain> <training seed> 8 16 9000000 <out>` | order-2 5,300,000–9,000,000 ms; the others 4,000,000–9,000,000 ms; 4 GB | 9,000,000 ms before a move, 9,900,000 ms |
| Validation reads, 7 × 64 | `executed evaluate <terrain> <validation seed> 64 <out> lossless opening m1=… m2=… m4=… m8=… m16=…` | 900,000–2,700,000 ms; 4 GB | 2,700,000 ms, 2,760,000 ms |

**The partition's rule, fixed now**: one development move of 8 requests on each terrain, the three
at once on 8 threads each (development seed `2_026_093_041`). If the slowest move's time times 16,
times `5/4`, exceeds 9,000,000 ms, the trainings run one at a time on 24 threads instead, each with
projection 2,400,000–6,000,000 ms and deadline 6,000,000 ms (outer guard 6,600,000), and the
validation reads one at a time with projection 600,000–1,800,000 ms and deadline 1,800,000 ms.
Whichever partition runs, its projection and deadline are the ones above; a run past its deadline
is reported incomplete and not rerun.

## 7. The prediction [agent-inferred, falsifiable]

From the modulus record's order-2 training (`F` on each fresh batch fell from `875694/4096` to
between `156231/4096` and `195097/4096` while the batches' stations right stayed between 10 and 19
of 64 and no section was whole): **the dominant cause is an unsuitable objective read through D2,
not a step too small (D1)**. `F = Σ (f)_+` with `f = max(max_x ln(a_x/a_t), −ln a_t)` is zero on
the tie manifold (every candidate equal and above one: `f = 0`, `(f)_+ = 0`), with no margin, so the
certified descent lowers `F` by shrinking the wrong decisions' class gaps toward zero rather than by
flipping them. Expected blockers (the located causes the loop reads, unrepaired): the lag-1 copy
the trained order-2 constitution releases, and the comparison read past threshold.

Stated for order-2 (the alternation and the line are regressions):
- **D1**: every adopted move's measured descent is positive and at least `1/8` of the certificate's
  predicted descent; the leading branches' prediction and the measurement agree in sign on every
  adopted move; no move's prediction is zero or below the grain; the entry bound refuses no trial.
- **The ideal listener** carries at least 13 bits (`log₂ 10240` is between 13 and 14) on move 0's
  batch and 0 bits on every later batch, while `F` keeps falling: the descents after move 0 carry no
  key information the listener still lacked.
- **D2**: the mean class-gap magnitude of wrong decisions at the open section of the fresh batch
  falls from move 0 to move 15 by at least half, while the wrong decisions' count there at moves
  12–15 is at least `3/4` of its count at moves 0–3; summed over the moves, the wrong→right flips at
  the open section do not exceed twice the right→wrong flips.
- **The counts**: `n*_terrain` on order-2 at most 24 observations (3 requests plus 0 stations);
  the line's global family keeps exactly the 10 keys `(4k, id)` at the passage's end; the success
  rule never holds for the machine on any terrain, so `n*_machine > 128` training requests (1,024
  observations) on each.

**The falsifiers** (each read as written and kept as it fires):
1. The measured descent is below `1/8` of the certificate's prediction, or opposite in sign to the
   leading branches', on a majority of adopted order-2 moves (a wrong derivative, or the
   trajectory's change dominates: D1's derivative, not the objective).
2. A majority of order-2 moves are refused, or predicted zero or below the grain, or bound by the
   entry bound (feasibility or the grain, not the objective).
3. The wrong decisions' mean class-gap magnitude does not fall by half (`F` does not descend toward
   ties).
4. The wrong decisions at the open section fall below `3/4` of their early count, or the
   wrong→right flips exceed twice the right→wrong flips (the step does move decisions).
5. The success rule holds for order-2 at some checkpoint (`n*_machine` found).
6. `n*_terrain` on order-2 exceeds 24 observations, or the order-2 family never reaches its
   stopping object in the passage.
7. A resource bound is reached (reported incomplete).

## 8. What this loop does not do

It changes no learning law, adds no owner, and designs no loop 1b. Receipt-only fields may be added
to `hnn::executed` where D1 or D2 need values the owner already computes (per-term first-order
bounds, the leading branches' pairing, each term's site, the unit move's largest entry); they add no
law, change no move, and pass the existing tests.
