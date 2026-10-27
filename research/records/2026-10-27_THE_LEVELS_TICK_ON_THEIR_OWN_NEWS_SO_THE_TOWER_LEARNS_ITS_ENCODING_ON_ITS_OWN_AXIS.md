# The levels tick on their own news, so the tower learns its encoding on its own axis

Refs #404 #406. Status: [design fixed before the build; agent-inferred, October 27]. Host law
built and tested (§6.1, §7); the card's port written, its parity on the card owed (§6.2); the
measurement (§6.3) and Lean (§6.4) owed. Owners: `holonics::hnn::tower` (`NewsClock`,
`Tower::join_news`, `Tower::step`, `Tower::reverse_joined`, `TowerState`),
`holonics::hnn::tower::realization`, `holonics_cuda::hnn::tower` and `kernels/tower.cu` (the level
loop of the forward and the reverse), the command `train-two-ladder-news-tower-classes`. Existing owners it joins: `holonics::aeon::EpochTower`,
Lean `Aeon/Clock/Epoch` (`odometer_tower`, `monotone_count_is_flux`, `coarse_epoch_is_union_of_fine`),
`hnn::tower::face_code`, the helical code's moments (the elementary objects, "The helical code").

## 1. What the tower reads now, and what Brandon asked

Every level of the tower steps once an octet. The octet is the codec's grain, fixed before the
tower reads it, so the four levels of the [race track](2026-10-27_THE_RACE_TRACK_RUNS_THE_PLAIN_TOWER_FOR_HOURS_ON_THE_CARD_AND_WRITES_AFTER_EVERY_LAP.md)
differ in what they hold, never in when they move. That is the recorded failure "text run on its
codec's grain as the exception" in its plain form, declared there as the plain tower's
measurement.

On October 27 Brandon asked why the tower does not read text through its own learned encoding, an
encoding whose learning is recursive and runs along its own axis, and asked that the two lines not
be mixed. The founded units (`hnn::units`, atlas `hnn.founded-units`) are not that encoding: they
are founded once, outside the constitution, priced by an order-one receiver of their own and never
re-founded by the tower's reading ([the review's §5](2026-10-27_THE_REVIEW_FINDS_THE_READ_CUTS_INSIDE_THE_MACHINES_OWN_UNITS_THE_CREDIT_STOPS_AT_THE_SECTION_AND_THE_EQUALS_HAS_ONE_STEP.md#5-strategy-beyond-the-equals)),
which is the form the September 29 lessons (§2) name as a founding outside the constitution. The
encoding asked for is the tower's own: its grain must come from its own reading and move as it
learns.

## 2. The law: each level is a receiver whose clock counts its own news

[definition; agent-inferred, October 27] A receiver ticks when the motion crosses its section, and
its epoch ticks count the flux through that section; coarsening merges epochs at the odometer's
carry (the elementary objects, §12). The flux the tower already reads at every arrival is its own
news: the code of the arriving class under the face that predicted it,
`c_t = −log₂ p̂_{t−1}(u_t)` on `2^(−20)` bits (`face_code`), the surprise that crosses the
receiver's section (CLAUDE.md, "the classical loss is the perceived difference"). It is never
negative, so its running sum `S_t = Σ_{k ≤ t} c_k` is a monotone clock.

- Level 0 ticks at every arrival: the input's own clock, as now.
- Level `l ≥ 1` ticks at the sections `S = j · B · rˡ⁻¹`, `j` whole. At arrival `t` it advances by
  `Δτ_l(t) = ⌊S_t / (B rˡ⁻¹)⌋ − ⌊S_{t−1} / (B rˡ⁻¹)⌋`, a whole number of ticks, zero inside a span
  the level already predicts and more than one where one arrival carries more news than a section.
- A crossing of a multiple of `B rˡ` is a crossing of a multiple of `B rˡ⁻¹`, so each coarser
  level's ticks lie among the finer's: an epoch tower whose coarsening is the odometer's carry
  (`EpochTower`, Lean `odometer_tower`, `coarse_epoch_is_union_of_fine`).
- `B = 8` bits: `log₂ 256`, the news of one octet read with no prediction, so level 1 ticks about
  once an octet at rest. `r = 2`: the least radix whose carry merges epochs. At the race's opening
  read (2.2 to 2.7 bits a class) levels 1 to 3 then tick about every 3, 7 and 14 octets. Both are
  agent-inferred; the run measures them.

**The level's move under its clock.** With `λ_t` the level's gated move at arrival `t` (as now,
`|λ|^(c r_t) u`) and `γ_t = √(1 − |λ_t|²)` its push scale,

```text
h_t = λ_t^(Δτ_l(t)) h_{t−1} + γ_t P x_t
```

Every arrival's input enters the level (no octet is dropped), and the level turns and decays only
as its own clock advances. Between ticks it holds its phase and gathers the span: the level's state
is the helical code's moment `m = Σ_k Ĝ(τ_l(k))⁻¹ E(u_k)` with `τ_l` the level's own clock, so the
arrivals of one span share one phase. Each tick carries the same news, `B rˡ⁻¹` bits: the induced
clock of the elementary objects' A4 (Abramov), under which the level reads its source at an even
rate of information. The read, the contacts and the return are unchanged, and the level reaches the
readout only through the residual stream, as now.

**Why this is the learned encoding, on its own axis.** The boundaries are where the tower's own
prediction has accumulated a section of news. As the tower learns a span, the span's news falls,
and the span merges into fewer ticks of every coarser level: the segmentation moves with the
learning, read from the constitution itself, and it is recursive, each level's ticks being the
carries of the level below. Its axis is information time, not octet time. Nothing names a class, a
boundary letter or a modality: a stroke or a half-cycle ticks the same levels by the same law.

## 3. Causality, release and the state

`c_t` is known once `u_t` arrives against the face before it, so the clock is decided before the
step reads `u_t`, in training and in release alike (a drawn class ticks the levels exactly as a read
one). The stream's state carries what continuation needs: the open face (the prediction the next
arrival is read against) and the clock's open phase, `S` modulo the coarsest section `B r^(L−2)`.
At rest there is no open face, so the first arrival carries no news and moves no level above 0, as
the code already counts classes after the first.

## 4. The reverse and the certificate

The clock is a reading of the forward, held in the reverse as the gate's `held` flag is: a section
crossing is an event, and no covector runs through it. The move's covector is the existing one
over `Δτ` sub-moves, `∂(λⁿ h)/∂λ = n λⁿ⁻¹ h`, run as `n` applications of the per-move derivative on
the states between them; `Δτ = 0` passes the covector through unchanged and sends none to the move.
The certificate is unchanged: the reread under a candidate deposit derives the candidate's own
clock, so the bits it certifies are the candidate's whole read, its segmentation included.

## 5. The recorded failures this design could repeat

- *An authored routine standing in for learning*: no boundary is authored; the clock is the
  learner's own news, and the founded units are left on their own axis.
- *Recitation or an index of contexts counted as generation*, and the October 26 copiers (the reset
  clock that ticked on a named class and raised a logit): the clock names no class, the held state
  is mode phase, nothing raises a logit at the readout, and there is no table keyed by class.
- *Text run on its codec's grain as the exception*: this is the repair, and it is modality-free.
- *An uncertified deposition step*: the certificate rereads under the candidate's own clock.
- *A design thought in the programming language*: the change is stated as a receiver's section,
  its flux and its epochs, and the arrays follow from them.
- *Bits read as progress*: the measurement below shows the writings beside the bits.

## 6. Acceptance, fixed before the build

1. **Host law.** A tower declared on the octet clock (every level `Δτ = 1`) is today's tower bit for
   bit (its saved learners' SHA-256 unchanged). On the flux clock: the reverse's covector equals the
   code difference it predicts on a small tower (the pattern of
   `the_pumped_strands_covector_matches_the_code_difference`); a learner's section carried across a
   save and a release matches the class-by-class advance; the ticks of a read form an epoch tower.
2. **Card.** `TowerCard` carries the flux clock: the forward kernel reads `c_t` from the face it
   formed (`face_code` on the card, the same integers) and each level's `Δτ` before the next cell,
   and the reverse reads them per cell and level. Parity at the race's declaration, 32 sections at
   24 streams and 4 at 320, every face, entry, learner and state equal. The kernel's level loop is
   shared with the review thread's face ports; the two are joined, never forked.
3. **The measurement.** The race's passage and declaration with the flux clock, lap for lap beside
   the plain race: training and held-out bits a class by region, each level's ticks a lap (the
   learned segmentation's grain), and the six writings whole. No claim is made before it runs.
4. **Lean** (into #410): the flux clock's ticks form an epoch tower under a monotone flux, and the
   clocked move over a span is the product of its sub-moves (the scale square
   `r ∘ T_fine = T_coarse ∘ r` for diagonal modes).

## 7. What was built (October 27)

- **Host.** `NewsClock { bits, radix }` joins a tower (`Tower::join_news`, saved as
  `news-clock B r`); the stream carries the open face and the phase (`TowerState::open`,
  `TowerState::news`). Acceptance 1 holds in the tests of `hnn::tower`: on one level the clock is
  the tower without it, face for face and mode for mode; a read's ticks form an epoch tower and
  count from rest the sections their news has crossed; a passage read in carried sections is the
  passage read whole; a learner's section carried across a save advances through the host's
  realization as class by class. The covector matches the code difference on the passage and
  steps the unclocked covector is read at, two levels gated and ungated and three gated, with level
  1's section at one bit so its ticks run 0, 1, 2 and 3 over the passage. On a longer passage with
  more crossings the reading is the limit, not the law: a step that moves a section crossing
  anywhere is not read, and on sixty-one classes at a two-bit section most families' steps moved
  one; the same three-level tower without the clock drifts with the step as much on that passage
  (its first gate bias −105.8, −113.6 and −139.3 against −113.8, ×10⁶, at `2^(−8)` to `2^(−10)`).
- **Card.** The forward's thread 0 reads each arrival's code from the face the block formed
  (`face_code` on the card, the host's integers: the width, then twenty squarings of the mantissa)
  and every level's ticks before the cell's levels move; the move acts once a tick, the face becomes
  the open face, and each stream's open face and phase cross in and out beside its modes. The modes'
  scan carries the covector back through the later cell's ticks and sums the move's covector over
  its sub-moves, the states between them read again from the state before the move (`Δτ²` moves a
  cell, `Δτ` a few at the race's sections). The card refuses the clock beside the ring face, as the
  host does. Its parity tests (32 sections clocked, the clock beside turned modes and the pair face,
  the clocked advance class by class) are in `tests/tower_pass.rs`, and `tower_pass parity` takes
  the clock; their run on the card is owed.

