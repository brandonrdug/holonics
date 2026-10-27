# The levels tick on their own news, so the tower learns its encoding on its own axis

Refs #404 #406. Status: [design fixed before the build; agent-inferred, October 27]. Host law
built and tested (§6.1, §7); the card carries it, its parity at the race's declaration equal (§6.2,
§7); the measurement (§6.3) beside the plain race read through lap 12 (§8); the Lean (§6.4) in
`HNN/NewsClock`. §8 replaces §2's move with the held step after the race measured the first law's
two clocks: host and card built, the host tests passing and the card equal to the host. Owners: `holonics::hnn::tower` (`NewsClock`,
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

(The first law, built, raced and replaced in §8 by the step held through the ticks.) Every
arrival's input enters the level (no octet is dropped), and the level turns and decays only
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
   `r ∘ T_fine = T_coarse ∘ r` for diagonal modes). Proved in `HolonicsResearch/HNN/NewsClock`
   (atlas `hnn.tower-news-clock-carry`): the coarse count is the carry of the fine count through
   the flux (levels `l ≥ 1`), so the ticks form an epoch tower and `Δτ_(l+1) ≤ Δτ_l`; a span's move
   is the product of its sub-moves, for one mode `z^(Δ⌊S/σ⌋)`; the scale square is exact where the
   fine count's residue modulo `r` is the same at both ends of the arrival, and holds up to that
   residue otherwise; §4's covector over the `Δτ` sub-moves sums to `conj(∂(λⁿ h)/∂λ) G`
   (`move_covector_is_derivative`).

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
  the clock. On the RTX 4080 SUPER at `07b7e4a8f` (merged as `9ea537430`) the suite passed 13 of 13,
  these three among them, and the parity at the race's declaration (width 64, 128 modes, 256
  contacts, four levels, sections of 128 classes, the clock `B = 8`, `r = 2`) on the race passage
  was equal in every face, covector entry and learner: 32 sections at 24 streams (98,304 faces,
  10,588,192 entries; host 14.3 s, card 3.0 s; peak resident 1,025,648 KiB) and 4 at 320 (163,840
  faces, 1,323,524 entries; host 16.8 s, card 1.1 s; 1,319,676 KiB). A clocked learner's release ran
  on the card.
- **The race beside the plain race** (§6.3, `race.sh` with the command
  `train-two-ladder-news-tower-classes`; launched 07:45 UTC October 27 on the plain race's passage,
  keys and declaration, the two races taking the card lock lap by lap). Its opening read, one lap on
  the card: training 2.799 bits a class, held out 2.463 (GSM8K 2.529, prose 2.412), against the
  plain tower's 2.748 and 2.356 (2.407, 2.317) at its own opening; 726 of 726 deposits certified;
  118.7 s, its forwards 64.7 s and reverses 34.7 s; peak resident 547,368 KiB. Its widest 32-section
  window was 6,136 ms (every other full window 5,048 to 5,265 ms), so its lap deadline is `⌈1.12 ·
  (23 · 6.136 + 0.800)⌉ + 120 = 279` s and its window stop 6,872 ms, fixed for the race. Its laps
  are reported beside the plain race's and none is claimed here before they run.

## 8. The drive's clock (October 27, measured on the race)

**What the race measured.** Through lap 12 on the RTX 4080 SUPER the news race read 1.986 bits a
class on training and 2.156 held out (GSM8K 2.176, prose 2.141), from 2.799 and 2.463 at lap 0.
From lap 3 it trailed the plain race lap for lap by about 0.22 bit (the plain race's lap 12: 1.763
and 1.914), and its held-out reading stayed between 2.15 and 2.17 from lap 8. Its upper levels
swelled: at lap 12 level 2's largest mode reached 3,817,935,029 state numerators and level 3's
largest read 10,511,165,077, some ten times the plain race's levels 2 and 3, which stay between
about `10^7` and `5·10^8`. Its
forward on the card slowed lap by lap (43.8 ms a launch at lap 0, 48.1 at lap 9, the plain race's
39.1 and 39.6 at its laps 0 and 40), its pass from 117.8 s (lap 5) to 127.0 s (lap 12) and its
widest 32-section window from 5,203 ms to 6,054 ms against the race's fixed stop of 6,872 ms; its
reverse held level.

**How the races ended.** The news race ran to lap 21 and stopped on its own window rule at
09:06:19 UTC, with no other load on the host (load average 1.8): its upper levels kept growing,
level 2's largest mode reaching 9,364,325,803 and its largest read 20,602,068,538 at lap 21, about
twice lap 12's, so its ordinary 32-section windows had crept to about 5.8 s (from about 5.1 s at
lap 5), and one burst of 25 certificate halvings took a window to 7,279 ms against the 6,872 ms
stop. Its last reading, its best held out: 1.958 bits a class on training and 2.121 held out
(GSM8K 2.128, prose 2.115). The plain race stopped at 08:51:51 UTC after lap 45, when a Lean build
on the same host took its cores and pushed its widest window to 6,322 ms against its 5,953 ms stop
(the card did not slow); its last reading, its best on both, 1.691 and 1.850 (GSM8K 1.800, prose
1.888), its levels' modes between about `10^7` and `10^8` and its reads about `3–5·10^8` at lap 40.
At the races' end the news race trailed by about 0.27 bit held out. Both ran on the RTX 4080 SUPER
under the card lock; laps 0 to 45 and 0 to 21 are complete, and the writings stay outside the
repository.

**The cause: two clocks.** The first law moved a level only on its own ticks but pushed it at every
arrival: a drive on the arrivals' clock beside a move on the news clock, the second clock §2 meant
to refuse. Between ticks a level integrated its span's pushes undecayed, so a tick's drive was the
span's length times `γ |P x|` and passivity no longer bounded the mode by its drive (`|h| ≤ √((1 +
ρ)/(1 − ρ)) max|P x|` at level 0): the spans of levels 2 and 3 are about 8 and 16 octets at 2 bits a
class, and their modes grew toward that factor as their pushes learned to agree within a span.
[agent-inferred] The slowdown follows the magnitude: the card sums a dot product in 64 bits only
while `max|w| · max|face| · (count + 1) < 2^62` (`narrow_terms`) and in 128 bits otherwise, so the
swelling faces moved the upper levels' reads to the wide carrier, a lawful widening at a declared
crossing whose cost rises with the faces.

**The law now: the plain step once a tick, the arrival held.** At each of the level's `Δτ_l(t)`
ticks its modes take the level's own step with the arrival's input held,

```text
h ← λ_t h + γ_t P x_t      Δτ_l(t) times,
h_t = λ_t^Δτ h_{t−1} + (1 + λ_t + … + λ_t^(Δτ−1)) γ_t P x_t,
```

each step released to the state's grain as the plain step is. An arrival that ticks no time moves
nothing. The drive and the move run on the one clock, so a level is the plain tower run on its own
clock, every tick the plain passive step (Lean `HNN/PassiveMode`, `passive_step` and
`passive_recursion` over the ticks' sequence; an arrival without a tick is the identity), and its
modes are bounded exactly as level 0's are, whatever the span between ticks. The level's input is
the output of the level below, which ticks at least as often and carries the span between, so the
level hears one input a section of news, read at the arrival whose news completes the section: the
level's own tokens, their boundaries placed where the tower's prediction has gathered news, and
moving as it learns. The zero-order hold is the exact clocked form of a step whose input is held
over an interval of `Δτ` ticks. One level on the clock is still the tower without it (every
`Δτ = 1`), face for face.

**The reverse.** Over the `Δτ` sub-steps the covector of `λ_t` is `Σ_j conj(h⁽ʲ⁻¹⁾) G⁽ʲ⁾` as
before, that of `γ_t` is `Σ_j Re(conj(G⁽ʲ⁾) P x_t)` and the push's is `γ_t Σ_j G⁽ʲ⁾`, the states
between the sub-steps read again by the step's own law (pushes included) and the covector carried
back through each, `G⁽ʲ⁻¹⁾ = conj(λ_t) G⁽ʲ⁾`; no tick sends none, to the move, the push or the
input. The covector the cell hands its predecessor is unchanged, `conj(λ_t)^Δτ G_h(t)`, since the
push carries no state. The Lean of the held step's covectors is owed in #410 (the sum over the
sub-steps as the derivative of `λⁿ h + (Σ_(j<n) λʲ) γ P x` in `λ`, `γ` and `P x`, beside
`move_covector_is_derivative`).

**Built.** Host: `Tower::step` takes the held step and `Tower::reverse_joined` its covectors;
`a_clocked_level_takes_the_plain_step_once_a_tick_with_the_arrival_held` checks every clocked cell
of the passage against the step taken `Δτ` times and a no-tick cell against the state before it,
gated and ungated, beside the clock's earlier tests. The covector matches the code difference on
the first 31 classes of the clock's passage, two levels gated and ungated and three ungated: a
level now steps only on its ticks, so on the thirteen classes the unclocked covector is read on the
upper levels tick a few times and too few of their covectors stand above the reading's grain
(18 of 27 gated families read, every one within a tenth); on the 31 classes 26 of 27 read gated,
20 of 23 ungated and 30 of 33 on three levels ungated, none off by a tenth. On all 61 classes the
unclocked tower's own fit misses some families by more than a tenth (up to 45%), the faces' release
over the longer passage, so the reading stops at 31. Card: the forward's level loop and the modes'
scan in `kernels/tower.cu` carry the same law (the push and its covector summed over the
sub-steps). On the RTX 4080 SUPER at `e61399f2d` the card suite passed 13 of 13 and the parity at
the race's declaration on the race passage was equal in every face, covector entry, learner and
state: clocked (`B = 8`, `r = 2`), 32 sections at 24 streams (98,304 faces, 10,588,192 entries;
host 14.7 s, card 3.4 s; peak resident 1,027,932 KiB) and 4 at 320 (163,840 faces, 1,323,524
entries; host 15.7 s, card 1.2 s; 1,345,312 KiB); and without the clock, 32 sections at 24
streams, whose halvings section by section (`0 0 1 1 2 3 1 2 0 1 …`, 110 forwards) are the plain
race's own parity at its head, so the plain tower is unchanged. The clocked course departs from
the first law's from section 7 (its halvings `… 2 3 2 2 1 3 3 2 2 0 2 11 …` against `… 1 3 2 2 1 3
1 1 2 3 0 1 …`), as a changed law's should. The race on the first law ran to its end (above); a
race on the held step needs its own authorization.

