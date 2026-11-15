# Heat explores and a store tempers: a compressed source opens into its members as its reader cools, sleep consolidates a fast store into a slow one, and power follows news

November 15, 2026, near 19:15 UTC. A derivation on a lens, with host rulers on public arithmetic. Nothing is
built and nothing ran on a learner. Written by the theory thread that holds the theory beside the engine's
build. Each paragraph carries its grade: `tree` (read in this repository), `from training` (a result of the
literature, named) or `agent-inferred` (this record's join).

Owners touched: `deposition.rate-temperature-standing-spread`, `tower.field-lap-mean`, `tower.field-temperature-log`,
`parametron.pump-inverse-temperature`, `heat.adjacent-configuration-activation`, `store.finite-quality`,
`contact.crowd-slip-bound`, `floor.wideband-bit-energy`, `deposition.cost-follows-surprise`. Four atlas rows enter (§9).

Receipts: [`temper_ruler.py`](2026-11-15_HEAT_EXPLORES_AND_A_STORE_TEMPERS_A_COMPRESSED_SOURCE_OPENS_INTO_ITS_MEMBERS_AS_ITS_READER_COOLS_SLEEP_CONSOLIDATES_A_FAST_STORE_INTO_A_SLOW_ONE_AND_POWER_FOLLOWS_NEWS_receipts/temper_ruler.py),
every check an assert, all pass, about seven seconds on the cloud container's host (stand-in Python in floats,
read as readings). Output in
[`temper_ruler_output.txt`](2026-11-15_HEAT_EXPLORES_AND_A_STORE_TEMPERS_A_COMPRESSED_SOURCE_OPENS_INTO_ITS_MEMBERS_AS_ITS_READER_COOLS_SLEEP_CONSOLIDATES_A_FAST_STORE_INTO_A_SLOW_ONE_AND_POWER_FOLLOWS_NEWS_receipts/temper_ruler_output.txt).

## 1. The lens

Brandon, November 15, 18:49 UTC, in the theory thread (a paraphrase; his words stay out of the repository), on the
line of the previous record that the transformer traded work for span: that trade is no bad idea. It trades
precision for faster exploration, like heating a metal, and the industry does not fully understand how to temper
and compress what the heat explored. Heat it, then let it crystallize: that is how biology consolidates. And do not
take power as constant, if the record held it so.

Both points stand. The record of the four savings (PR #841) held a rate or a power fixed to compare breadth, and
read the transformer's trade only as a cost. This record reads the trade as a temperature and gives the laws of
cooling it.

## 2. What the tree held

`tree`:
- `deposition.rate-temperature-standing-spread`: a deposit's rate is a temperature, `k_BT_i = 2^(−k_i) s_i/2`, and a
  rate holds a standing spread at rest that costs a quarter of the step times the noise.
- `tower.field-lap-mean`: the lap's mean of the material is the line's rest position, a lap's end state one draw of
  the spread about it. This is Polyak–Ruppert averaging (Polyak and Juditsky 1992, `from training`), and the line
  already reads its level there.
- `tower.field-temperature-log` and §15.10 of the record of November 1: a lock's temperature is deposited in its
  logarithm, two a head (one for class receivers, one for open listeners), so the contact's sharpness is a store.
- `parametron.pump-inverse-temperature`: the pump is an inverse temperature; past the bifurcation a mode locks.
- `heat.adjacent-configuration-activation`: escape over a barrier is exponentially late in the barrier over the
  temperature (Arrhenius; Kramers).
- The rule of November 13 in this guide: a temperature is a store's state, never a dial a reading sets.

Not held, under each discipline's names: the annealing theorems (Hajek; Kibble–Zurek), deterministic annealing's
critical temperature, water-filling, and the consolidation of a fast store into a slow one.

## 3. The trade is a heating

`agent-inferred`, on `from training` results. Attention over every pair at once, a large step and a broad softmax
explore many configurations together at a low precision a configuration: they run hot. Heat is how a search leaves
a basin, since a barrier `ΔF` is crossed at a rate `e^(−ΔF/k_BT)`. So the trade buys exploration, and the record of
PR #841 read only its cost. What the trade owes is a cooling that keeps what the heat found.

The industry cools by hand: a step size warmed up and decayed on a schedule (and reheated at restarts, Loshchilov and
Hutter 2017), an average of late iterates (Izmailov et al. 2018), and afterwards a separate compression: a student
trained on the teacher's faces raised to a temperature (Hinton, Vinyals and Dean 2015), pruning to a sparse
subnetwork that the dense one contained (Frankle and Carbin 2019), quantization. A network that has fit its data can
still crystallize long after, into a compressed circuit that generalizes, under a slow pressure toward small weights
(grokking: Power et al. 2022). Each is a cooling. None is the system's own: the schedule, the compression step and
the temperature are set from outside.

## 4. How to temper

`from training`, with the joins `agent-inferred`.
- **Cooling must be slower than the deepest trap.** Under the schedule `T(t) = c/log(1 + t)`, annealing reaches the
  ground with probability one iff `c` is at least the depth of the deepest local minimum that is not global (Hajek
  1988; Geman and Geman 1984). Faster cooling leaves states in traps.
- **A finite cooling freezes defects by its rate.** Crossing a transition in a time `τ_Q` freezes in defects at a
  density that falls as a power of `τ_Q` (Kibble 1976; Zurek 1985): a slower quench leaves fewer domain walls.
- **Quench, then temper.** A metallurgist quenches to fix a hard phase fast and then tempers it: reheats below the
  transformation so that trapped stress relaxes locally while the phase stays. Exploration and consolidation are two
  temperatures, the second lower and longer.

The ruler (§1 of the output), on a spin glass of 14 spins whose ground is read by enumerating all its states: the mean
energy left above the ground over 60 runs is 1.048 after a quench, 0.886 after 3 sweeps of linear cooling, 0.472 after
30 and 0.071 after 300.

## 5. A compressed source opens into its members as its reader cools

`from training` for the theorem; the join to the contact `agent-inferred`.

**Deterministic annealing** (Rose, Gurewitz and Fox 1990; Rose 1998) compresses by minimizing a free energy
`F = D − T H` over soft associations `p(y|x) ∝ e^(−d(x, y)/T)`. At a high temperature every codeword sits at the data's
centroid: one representative, the most compressed code. As `T` falls, the code splits in phase transitions, and for
`d = |x − y|²` a cluster's codeword splits when `T` falls below `2 λ_max`, twice the largest eigenvalue of that
cluster's covariance. The ruler (§2): two clusters of 300 points, `2 λ_max = 5.005`; cooling by one percent a step, the
codeword first split at `T = 4.921`, 0.983 of it. Heat merges and cooling crystallizes, and the crystal is the
compressed code at the reader's resolution. This is the lens's "heat it, then let it crystallize", and it holds for
compression itself.

**The contact's crowds are its phase.** A row's shares are `2^(β s)` with `s = −½|a − c|² + ½|a|²` the half-lock
against an arriving face `c` (contact.rs), so a share is a Gibbs association at `T = 2/(β ln 2)`, and the splitting
point reads `β_c = 1/(λ_max ln 2)` for a crowd's arriving faces. The band test sent to the build thread for T7
(`contact.crowd-slip-bound`; admit a crowd while `β B_C ≤ ε`) is the same statement at a finite grain: a crowd stands as
one source while its reader is hot against its spread, and opens into its members as the reader cools. The listener's
temperature is deposited (§15.10 of November 1), so the support anneals itself: where the deposit sharpens a head's
open listeners, crowds open; where it softens them, they merge. No schedule is set, and the rule of November 13 holds.

## 6. Biology consolidates by two stores and a heat that is itself a store

`from training`, with the joins `agent-inferred`.
- **Two stores at two rates.** The hippocampus learns fast and the cortex slowly; the slow store learns from the fast
  one by interleaved replay, which spares it the interference that sequential learning in one store suffers
  (McClelland, McNaughton and O'Reilly 1995; McCloskey and Cohen 1989). Waking sequences are replayed in sleep
  (Wilson and McNaughton 1994), several times faster than they were lived (Nádasdy et al. 1999).
- **Sleep tempers.** Waking potentiates synapses broadly, and slow-wave sleep scales them down together, keeping their
  ratios and restoring the budget (Tononi and Cirelli 2003, 2014): a reheat below the transformation, in the
  metallurgist's word.
- **The heat is a store.** Sleep pressure accumulates with waking activity and discharges in sleep (Borbély's process
  S, 1982; adenosine, Porkka-Heiskanen et al. 1997): a store charged by use that leaks in rest, never a clock set from
  outside. Plasticity is raised where the world surprises: acetylcholine signals expected uncertainty and
  norepinephrine unexpected uncertainty (Yu and Dayan 2005). The heat is charged by news.

On the objects: the lap mean is already the slow store, and the line already reads there (§2). A deposit is the fast
store, and its rate is its temperature. What biology adds is twofold. Its slow store learns from the fast one by a
replay with no fresh input, which is the release's path read back through the deposit (the record of 04:45 UTC today,
self-induction in Brandon's sense). And its heat is charged by surprise and leaks by its own dynamics.

## 7. Power is not constant: it follows news

`from training`, correcting the premise of PR #841 §6, where a rate or a power was held fixed to compare breadth.
- **Water-filling.** With a power budget over channels or ticks of unequal gain `g_k` against their noise, the most
  information is carried by `P_k = (ν − 1/g_k)^+`: power is poured where a channel is quiet against its gain, and none
  goes under the water level `ν` (Shannon 1949; Cover and Thomas). Equal power is optimal only when every channel is
  alike. The ruler (§3): over 300 draws water-filling never falls under equal power and passes it in 299, and ties it
  within `4 × 10^(−15)` where the channels are alike.
- **Reverse water-filling.** Describing a source of components with variances `σ_k²` at a total distortion, the bits
  go to `½ log₂(σ_k²/θ)` for the components above the level `θ`, and none to those under it (Kolmogorov 1956; Cover and
  Thomas). On a passage of 128 ticks with two bursts of news the ruler gives the 120 quiet ticks no bits and the 8
  burst ticks 17.75. This is `deposition.cost-follows-surprise` stated as an optimum: predicted input goes dark, and
  power follows news.
- So the breadth law of PR #841 is the alike-channel case. In general, power is a store charged where news arrives,
  in time and in place. A brain's blood flow follows its local activity, and a neuron's power is a burst against a
  quiet mean.

## 8. What follows for the machine, and what does not transfer

`agent-inferred`. Readings on saved lap means, offered to the build thread and not ordered, each by region and slice
beside its total, with loudness beside nats where a lap is reported:
- **T9. The support anneals with the listeners' temperature.** Read the band test's admitted crowds (T7's instrument)
  at a fixed `ε` on the lap means of several laps of the line, with each head's open-listener temperature beside them.
  The prediction of §5: where a head's listener temperature rises across laps, its admitted crowds fall, octave by
  octave, and they open first at the near octaves and the tightest crowds.
- **T10. Does the deposit's heat follow news.** Read the standing spread (the lap end against the lap mean,
  `deposition.rate-temperature-standing-spread`) by part and by surprise fifth of the places that reach each part. The
  prediction of §7: an optimal heat stands highest where the news lands. A spread even across fifths reads a rate that
  does not follow news, and the candidate law is a part's rate as a heat store charged by the surprise that reaches it
  and leaking by its own dynamics (§6). That law changes the deposit's bits, so it would be carried in the learner's
  state with its parity, and it waits for T10.
- **The join of consolidation.** The slow store learning from the fast by replay is the release path read back
  through the deposit (§6). No build is proposed here; the 04:45 UTC record holds that design and its guess.

What does not transfer: the biology's anatomy, the metallurgy's phases, the logarithmic schedule (a proof device, far
too slow to run), and any temperature set by hand. The machine takes the laws: cooling slower than its deepest trap,
a compressed source that opens as its reader cools, a heat charged by news, and power that pours where news lands.

## 9. Atlas and receipts

Four rows enter:
- `heat.anneal-cooling-depth` (`physics.tsv`): Hajek's schedule, Kibble–Zurek's frozen defects, quench and temper.
- `compression.anneal-split-temperature` (`objects.tsv`): deterministic annealing's split at `2 λ_max`, and the
  contact's crowds as its phase.
- `deposition.two-rate-consolidation` (`objects.tsv`): two stores at two rates, replay, downscaling and a heat
  charged by news, as an interpretation.
- `floor.water-filling-power` (`information.tsv`): water-filling and its reverse, power following news.

The receipts directory holds the ruler and its output.
