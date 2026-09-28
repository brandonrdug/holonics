# The learner must move: a chase terrain, data as particles with flux, and release as a threshold commit

**Date:** 2026-09-27. Refs #63, #27, #148.

**Occasion.** A conversation after the README and workflow review, which began with Brandon's
question: "Predictions aside, architecture beyond LLMs, what can you see?" Claude answered from the
measured receipts. Brandon then corrected the picture three times, from how motion, pursuit, aim
and communication feel to him. This record keeps the derivation and what it asks of the machine.

**Truth discipline.**
- Classical results are `[proved-standard]`, with their authors.
- Our own measurements are `[established-bounded; measured]`, with their records.
- Joins into the objects are `[interpretation]`, with a falsifier where one exists.
- Choices for the machine are `[definition; agent-inferred]`.
- The images are Brandon's derivation. They are stated here as general phenomena of motion, aim and
  communication; nothing personal is recorded.

## 1. Navigators beat contexts, and birth is the open problem

- **The receipts.** On the arithmetic terrain the composed egg codes at exactly its truth, and the
  landmark tree does not.
  - Base-10 digit products (`2^12` records): the egg `108857 + 3/16 + ε` bits, the tree `273520 + 7/16`.
  - Prime streams over `[0, 10^4)`: the egg `15 + 9/16 + ε`, which is the key's description, the tree
    `161780 + 3/16`.
  - The tree pays between `3 + 3/16` and `4 + 7/16` bits for each determined cell; the egg pays zero
    once the clock is located.

  `[established-bounded; measured]` ([population record](2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md)).
- **An LLM is a context model at scale.** It predicts the next symbol from past symbols and holds
  the process that made them only implicitly, spread over its weights. A receiver that holds the
  navigator and its key explicitly, and selects among candidates by Bayes, is a Solomonoff mixture
  with a population: the egg population. `[interpretation]`
- **Birth is the open problem.** On terrain with known truth we declared the families. On text, no
  family we declared beat the tree: campaign 2's 41 ring and contact families all lost to their
  controls ([campaign 2 record](2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md)). `[established-bounded; measured]`
- **The dilemma.** Gradient descent over a smooth parameterization finds approximate navigators
  without enumerating programs, because it spreads the search across training. Levin search is
  exact, but its cost grows with the program space. A machine beyond the context model needs both:
  a continuous search that falls into structure, and a discrete, exact result. `[interpretation]`

## 2. The rings as the search

**The parametron settles into discrete sheets.**
- Goto's parametron (1954) is a pumped resonator that, past its bifurcation, settles on one of two
  phase sheets; parametron computers were built from it. `[established-bounded]` (the historical
  machines)
- Coherent Ising machines use networks of optical parametric oscillators, raising the pump through
  the bifurcation to reach low-energy Ising states. `[established-bounded]` (their published
  measurements)

**Mode locking weights simple keys more heavily.**
- For the sine circle map `θ ↦ θ + Ω − (K/2π) sin 2πθ` at small coupling `K`, the width of the
  `p/q` Arnold tongue shrinks like `K^q`. `[proved-standard]` (Arnold; the perturbation expansion
  of the circle map)
- The tongues are ordered by Farey mediants, and every rational has a unique finite path in the
  Stern–Brocot tree, which is a self-delimiting code for it. `[proved-standard]`
- At critical coupling the locked intervals fill the full measure of `Ω`: the complete devil's
  staircase, found numerically by Jensen, Bak and Bohr and proved for critical circle maps by
  Świątek. `[proved-standard]`
- Plateaus need a nonlinearly driven family. A rigid rotation has none: the atlas row
  `lock.rigid-rotation-no-staircase` refutes a universal staircase for driven pairs.
  `[counterexample]`

**The join** `[interpretation]`. Our Farey lock addresses, the population's Kraft prior `2^(−ℓ)`,
and the basins of coupled rings are one structure seen three ways. A basin for period `q` weighted
like `K^q = 2^(−q log₂(1/K))` is a description-length prior, linear in the period.

**The reading** `[interpretation]`.
- The population predicts, by its mixture.
- Coupled rings search: their locked states are candidate keys, found by dynamics running in
  parallel. A lock is a birth (FOUND); driving an existing lock is RIDE; deposition changes the
  couplings.
- Campaign 2 used the rings as feature carriers inside a predictor, which may be the wrong role.

**The experiment and its falsifier.** Put a bank of coupled rings on terrain with known keys: the
moiré sheets and the rotor cribs (`holarchy::terrain`). Measure:
1. whether the rings lock onto the true period in less work than enumerating keys;
2. whether the fraction of initial conditions landing on each lock tracks `2^(−ℓ)` for the key's
   description length `ℓ`.

If neither holds, the reading is refuted. Brandon's later correction (§5) adds a second role for
the rings: the emissions of a moving source. The two readings are not exclusive.

## 3. Retention is the causal state

`[proved-standard]` Crutchfield and Young (1989): the causal states of a process are the classes of
pasts with the same conditional future. They are the minimal sufficient statistic for prediction,
and their entropy is the statistical complexity.

`[interpretation]`
- The retention law, "the quotient of the past that every admitted future reads alike", is this
  construction. The [July 28 record](2026-07-28_THE_FUTURE_SPLITS_THE_HISTORY_THE_ORGANIZATIONAL_FIBER_TRANSPORTS_OVER_CAUSAL_STATE.md)
  built an exact causal-state learner in the laboratory era.
- A transformer's context cache is a tape: it keeps every past token and attends over all of them.
- The causal state's size is the source's statistical complexity, not the passage's length. This is
  the 20 W principle stated exactly: cost follows the causal structure actually present.

## 4. The root: a distinction re-entering itself

`[proved-standard]` for the constructions; `[interpretation]` for the joins.
- **Spencer-Brown**, *Laws of Form* (1969): the calculus begins from one act, drawing a
  distinction. A distinction fed back into itself, `f = ¬f`, has no static solution; its solution
  is an oscillation.
- **Kauffman**: that oscillation, taken as the iterant `[+1, −1]` with a half-period shift, is `i`,
  with `i² = −1`. The Holonic half-turn `−1 = e^{iπ}` and quarter-turn `i` are the same pair.
- **The join.** A ring is what a difference looks like when it refers to itself. A cycle is born of
  self-reference, not measured on a background clock: "a cycle is completeness, not duration" and
  "no privileged clock".
- **Bateson** (1972): information is "a difference which makes a difference". That is the classical
  loss read as the perceived difference, the surprise that crosses a receiver's section.
- **Maturana and Varela** (autopoiesis): a system that keeps producing the processes that produce
  it. On this reading, a self is a receiver whose terrain includes itself: the quotient of its own
  past that it must keep in order to go on reconstructing itself. No theory of consciousness is
  claimed.

## 5. The moving source (Brandon's derivation)

**The rings are the wavefronts of a moving source.** "The rings are probably comparable to the
shockwaves that follow the breaking of sound-barriers, it's just the geometry of the egg surface
again."
- A source moving at speed `v` through a medium with signal speed `c` leaves its fronts nested off
  centre, crowded ahead and spread behind, when `v < c`. At `v = c` every front passes through the
  source. For `v > c` their envelope is a cone with `sin μ = c/v`. `[proved-standard]`
- The pattern records the source's motion relative to the medium's response speed.
- The identification with the [egg record](2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md)
  (egg below the barrier, neck at it, cone above it) is `[interpretation]`. It is held as an image
  under the September 26 scope correction until a receiver and transport map carry it.

**Talking and striking** `[interpretation]`.
- **Communication is subsonic.** The fronts arrive before the source, so the receiver can
  anticipate and move with it.
- **A strike is supersonic.** Nothing precedes the front, and the receiver meets a shock, which is
  pure surprise. Venom acts faster than the target's homeostasis can answer.
- The [light record](2026-09-24_THE_LIGHT_IS_THE_CHANGE_AND_EXPRESSION_COLLAPSES_ONTO_FINITELY_MANY_CRITICAL_CLASSES.md)
  already holds venom and language as keys that fit a lock. Convergent toxin evolution onto a few
  ion-channel targets shows that the finiteness belongs to the receiver's locks
  (`[established-bounded]`, there).

**Speech entrains.** Auditory cortex phase-locks to the rhythm of speech (Giraud and Poeppel, 2012).
`[established-bounded]` The speaker's releases entrain the listener's rings, and two long
acquainted receivers learn each other's tongues. `[interpretation]`

**The moving self is a packet.** When coupling passes its critical value, many oscillators fall
into one collective phase and move as one degree of freedom (Kuramoto). `[proved-standard]`

**Gain.** The locus coeruleus's noradrenaline switches between broad exploration and narrow
exploitation (Aston-Jones and Cohen, adaptive gain theory, 2005). `[established-bounded]` In the
parametron, gain is the pump. `[interpretation]`

## 6. Pursuit, corrected twice

**First reading: tau** `[proved-standard]` for the constructions.
- Lee's `τ = x/ẋ` is the time for a gap to close at its current rate (Lee, 1976). Animals steer
  approach and landing by `τ` directly, and coordinated movements couple two gaps' taus in a fixed
  ratio (Lee, 1998, general tau theory).
- For a gap `x`, the ratio's log derivative is `d log x/dt = ẋ/x = 1/τ`. The learning covector
  `R⁻¹dR` is the gap's closing rate over the gap. `[interpretation]`
- Chasing a target's current position lags forever (pure pursuit). Holding the line-of-sight
  direction constant intercepts a target that keeps its course (constant bearing, the basis of
  proportional navigation). Against a turning target, you have to know its navigator.
  `[proved-standard]` for the geometry; `[interpretation]` for "interception is prediction".

**First correction** (Brandon: "I lock onto the free-fall between me and the target … it's about
guaranteeing that I'd strike it like an arrow").
- **Reachability, not tracking.** Isaacs' *Differential Games* (1965): the "homicidal chauffeur"
  pits a fast pursuer of bounded turning radius against a slow evader who can turn instantly. The
  game is played in relative coordinates. The barrier, a one-way surface that neither player can
  push the state back across, bounds the region from which capture is certain. Viability theory
  (Aubin, 1991) calls that region the capture basin. `[proved-standard]`
- **Traction sets the turning radius.** On level ground, keeping traction requires `v²/r ≤ μg`, so
  the tightest turn at speed `v` has radius `v²/(μg)`. `[proved-standard]` A faster, less agile
  animal loses by being forced to curve, above all over ground of low friction. The chaser models
  the other by its law (speed, turning, traction) and the terrain, not by its path. That is the
  Holon as the law and its ports, not its state. `[interpretation]`
- **Traffic is the same act at the scale of the medium.** Lighthill–Whitham–Richards (1955–1956):
  a road's density field carries kinematic waves and shocks. `[proved-standard]` A driver reading
  density classes and lane flow, rather than individual cars, reads the medium's classes. A
  reliably slow vehicle is a landmark, whose future is cheap to predict, so attention goes only
  where the future is open. `[interpretation]`
- **Communication is constraint shaping.** A speaker does not predict the listener's words; they
  shape the constraints on the listener's response so that it is forced. `[interpretation]`

**Second correction** (Brandon: there is "no moment where a catch is certain"; the felt certainty
is "pseudo-certainty", and "I need to output the action in order to see where to go next").
- **Navigable, not planned.** The viability kernel is the set of states from which some next move
  always remains viable (Aubin). `[proved-standard]` One can be nearly certain of being inside it
  while the trajectory stays unknowable, as with the difference between "can you navigate the next
  ten years?" and "what will you be doing?". The capture basin was the wrong object: the agent lives
  in the viability kernel and makes committed strikes whose outcome is not promised.
  `[interpretation]`
- **Threshold commits.** Wald's sequential probability ratio test (1945) accumulates log-odds until
  they cross a threshold, and it minimizes the expected sample size for given error rates (Wald and
  Wolfowitz, 1948). The drift-diffusion model of choice has the same form (Ratcliff, 1978). The
  optimal threshold is set by the cost of waiting, not by a level of certainty, and under lethal
  time pressure it drops. `[proved-standard]`
- **The join** `[interpretation]`. Accumulating log-odds is Bayes as a translation, the two-Swing
  step of the [probability record](2026-09-27_PROBABILITY_IS_A_RECEIVER_GEOMETRY_BAYES_IS_THE_RATIOS_TRANSLATION_AND_THE_EGGS_PERIOD_IS_HYPERGEOMETRIC.md).
  Pseudo-certainty is the threshold being crossed. The errors of a fast mover are the error rate
  that its threshold buys; they are the price, not a defect.

## 7. The flick: firing on a prediction

- **Forward models.** The brain predicts the sensory result of its own motor command from a copy
  of that command (von Holst and Mittelstaedt, 1950; Wolpert, Ghahramani and Jordan, 1995).
  `[established-bounded]`
- **Open loop.** Visual feedback takes about a tenth to a fifth of a second, longer than a fast
  interceptive event, so a flick is launched open-loop and the click is timed to a predicted
  alignment. Batsmen's eyes jump ahead to where the ball will bounce (Land and McLeod, 2000).
  `[established-bounded]`
- **The prefired shot is a population release** `[interpretation]`, as in a sniper's shot across a
  well-known doorway (Dust 2's mid-to-B cross).
  - Opponents' motion is constrained (four directions, crouch, jump), so it falls into a few
    families.
  - Players at a given level move along habitual curves: an evolved prior learned over many
    matches.
  - The shot is released at the predicted alignment, where the shooter's code for that terrain is
    short.
  - The motions a shooter usually misses are families not carried: the cokernel, where a birth is
    owed.

## 8. Expected surprise, contradiction and collapse

- **Expected surprise is calibration.** Brandon: "it would not be that surprising if this turned
  out to be surprising". This is the entropy of one's own forecast: the surprise one expects. A
  calibrated forecaster's expected and realized surprise agree over its passages. `[proved-standard]`
  for the definitions; `[interpretation]` for the join. The readings `3 + 1/16 + ε` take the same
  stance: an exact statement, and the exact size of what is unresolved.
- **Certainty that something is wrong is a failed loop closure** `[interpretation]`.
  - The inner ear senses rotation with three semicircular canals, rings of fluid at right angles,
    whose inertia lags the head. `[established-bounded]`
  - When they report a rotation that vision and proprioception do not confirm, the felt state is
    not uncertainty but certainty that receivers which ought to agree do not: a loop that fails to
    close.
  - The Bombe never confirmed a key; it rejected keys by contradiction. One can know *that*
    something is wrong without knowing *what* is right.
  - Water changes the medium's constitution (buoyancy, drag), so a forward model tuned in air
    mispredicts.
- **Collapse onto few classes.** Under lethal pressure, behaviour falls onto a few coarse classes
  (fight, flight, freeze) grown from indiscriminate microscopic dynamics. This is the light record's
  collapse onto finitely many critical classes, in a body. `[interpretation]`
- **Mutual cost.** A defence that makes the attack costly (a plant's pungency, a bee's sting) is an
  emission aimed at the attacker's lock: the attack's cost reflected back. `[interpretation]`

## 9. Knowing which way it missed

Brandon's derivation, as a general phenomenon of skilled aim:
- After a miss, the mover knows exactly what went wrong before any outcome feedback, from where the
  predicted intersection and the actual one parted, "as it happens".
- A missing confirmation is itself felt.
- Whether a miss came from the channel (network lag) or from the mover is usually clear.
- The motion can be replayed in the mind.
- For whole-body movements that a mover can only feel, not see, second-guessing a correct movement
  produces overcorrection.

`[interpretation]` throughout, with the classical constructions `[proved-standard]` where named.
- **The directed error exists at the moment of action.** The forward model's predicted consequence,
  compared with the unfolding one, gives a signed error before any outcome arrives. The learning
  covector's sign is available at the action, not only after the result.
- **An omitted expected signal is news.** When the confirmation that should have arrived does not,
  its absence is the surprise.
- **Self versus channel is decided by loop closure.**
  - A miss caused by the channel (lag) and a miss caused by the mover differ in which loop fails to
    close. The mover's prediction closes against its own motor record in the first case, but not in
    the second.
  - This is the deposition law in motion: deposit only at the locus a covector actually reached.
    An error attributed to the channel must not change the mover's constitution.
- **Overcorrection is tampering.** Deming's funnel (*Out of the Crisis*, 1986): adjusting a stable
  process in response to each deviation increases its variance. `[proved-standard]`
  - The Kalman gain (Kalman, 1960) weights a correction by the ratio of the prior's uncertainty to
    the total uncertainty. `[proved-standard]`
  - A sense that cannot see the body (proprioception alone) is a noisy sensor. Its corrections
    deserve a small gain, and treating it as precise is tampering.
- **Replay is regeneration from the quotient, not a tape.** A mental replay regenerates the motion
  from the retained keys and constitution, which is what the retention law permits. Nothing is
  archived.

## 10. Data as particles with real flux

**What carries flux** `[definition; agent-inferred]`. Flux is the change an emission makes in a
receiver. A source carries real flux when it records:
1. identities that persist across epochs;
2. their changes, with the real intervals between them;
3. the causes of each change;
4. where the source is live, its response to the learner's own emissions.

Bytes read at uniform ticks carry none of these. They are the recording of the boom, not the
motion that made it. `[interpretation]`

**Sources that carry it** `[interpretation]`.
- **Games.** Entities with identity, exact changes every tick, causes (inputs and collisions), a
  closed loop, and a known navigator in the rules. A human's own play traces add a mover in flow,
  recorded exactly.
- **Git history.** Diffs are changes, not states. Parent commits are incidence, and tests are
  receivers.
- **Conversation logs.** Their flux is what each message changed in the other side, visible in the
  next turn (the admitted response→later-human relation). Across months a concept moves (for
  example, "difference" became the Ratio), so a concept is a particle, its path across
  conversations is its motion, and the derivations are its forces. The logs are private; only
  counts, bits and hashes leave them.

**The encoder is what the intelligence does.** The laboratory's `src/eros/um/HOLON_ENCODER.md`
(June 13–15) already said so: "We do not write the Holon Encoder. Eros *performs* it." The draft
explodes a source's latent axes (layout, parse, graph, time, nesting, enclosure) into co-present
ports, measured never authored, and treats hand-built transducers as catalysts removable in
principle.

**Pin the record, never the encoding** `[definition; agent-inferred]`.
- The physical record (identities, changes, intervals, causes, ports) is pinned once, by hash, for
  honest evaluation.
- No encoding is pinned. Every re-encoding (learned classes, words, concepts across ports and
  aeons) is a lens in the population: a face map that pays its own description and stays only while
  it shortens held-out code.
- Lenses of lenses are the recursion, and the population arbitrates between them. That is the
  auto-training Brandon means.

**The first lens, honestly** `[established-bounded; measured]`
([notebook receipt](../notebook/hnn_design/README.md)): learned byte classes took the curated
stream against the flat stream as follows.

| Tail | Before the learned classes | After |
|---|---|---|
| Development | `−1699 + 15/16` | `−1820 + 9/16` |
| Held out | `−583 + 10/16` | `−535 + 8/16` |

The development cells chose the lens; the held-out tail has not yet shown that it pays.

## 11. Games as exact closed-loop media

- **Why games** `[interpretation]`. Intelligence needs a medium with its own dynamics and a closed
  loop, and games are the cheapest exact such media. Much of modern machine learning went through
  Atari, Go and StarCraft for this reason. `[established-bounded]` (the published results)
- **Laws, not a scalar.** Reinforcement learning typically learns a policy from one reward scalar
  through a function approximator. The Holonic reading is different: read the game's laws (its
  constitution, equation extraction), act by reachability and threshold commits, and read every
  entity's state as a receipt field, never a single scalar. The game is a Holarchy, and so is the
  learner.
- **Exactness.** Most engines run floating point, which the exact-arithmetic law forbids inside the
  machine. Fixed-point engines exist: Doom's arithmetic carried sixteen integer bits and sixteen
  fractional bits, and lockstep strategy games keep exact determinism. The terrain is therefore our
  own exact arena (§13). `[definition; agent-inferred]`

## 12. What the machine lacks: twelve necessities

`[definition; agent-inferred]` Each is a law already stated somewhere without a consumer, or a
consequence of the derivation above, with the owner it would extend and its test. The common cause:
the rebuild made compressing recorded text its first measurable step, and every law since was
fitted to that terrain. A recorded byte stream offers no motion, no receiver to address, no timing
and no loop.

1. **Motion.** Extends `holarchy::terrain` with a new `chase` terrain, together with
   `geometry::screw` and Lean `Transport/SerialScrewChain`. Test: the chase terrain (§13).
2. **Release addressed to a receiver.** Extends `receiver::release` and
   `receiver::population::admitted`.
   - A release's value is read at its receiver, as what it changes in the requester's next turn.
     This follows the Rational Speech Acts model (Frank and Goodman, 2012; `[established-bounded]`),
     in which the speaker chooses an utterance by how a listener would read it.
   - The response→later-human relation stays an observation and a receipt, never a reward.
   - Test: on development, releases chosen with the receiver term against releases without it,
     read by the later-human receipt. This enters F4 after its first receipt, not under it.
3. **Gain driven by surprise.** Extends `receiver::population::dormancy` (the fixed share
   `α = 2^(−j)`) and the parametron's pump in `hnn::ring`. Test: on the aeon-switching terrain, a
   switch rate driven by recent surprise against the fixed rate's `169 + 9/16 + ε` bits (the static
   population's `688 + 6/16`).
4. **Timing.** Extends source-contract item 9 in `HNN_FORMULA`, `curated_source.py` and
   `aeon::epoch`. Releases carry their intervals, since the phase between rings is where rhythm
   lives. Test: the curated stream with intervals as cells against without them, charged.
5. **Release as a threshold commit.** Extends `receiver::release::DecisionRule` and release-contract
   item 1.
   - The release is a sequential test on accumulated log-odds, its threshold priced by the declared
     cost of delay.
   - Its receipt states the threshold crossed and the expected surprise.
   - Test: on the chase terrain, capture ticks and error rate across declared delay costs trace the
     expected speed–accuracy frontier.
6. **Calibration.** Extends `receiver::face` (`GrainCell`) and the population's receipts. Expected
   surprise (an entropy enclosure) is read beside realized code. Test: the calibration gap on
   terrain with known truth is within its enclosure.
7. **A live loop-closure reading.** Extends `holarchy::gluing`.
   - Today `GluingDefect` is a structural check at gluing: uncancelled power, unit mismatch,
     non-commuting or degenerate cells, and a parted contact's uncancelled interface power.
   - Nothing reads disagreement between the machine's receivers during a passage.
   - Test: the chase terrain's faulty-sensor switch, located on the aeons it is active and nowhere
     else.
8. **Probing.** Extends `receiver::release` and the population's mixture. Where the fibre is wide,
   the machine emits the probe with the greatest expected information gain over its families
   (Lindley, 1956; `[proved-standard]` for the criterion). Test: in the chase terrain's reception
   phase, the runner's constitution is selected in fewer ticks with probing than with passive
   observation.
9. **Every action carries its prediction.** Extends the ratio calculus `R⁻¹dR` (`hnn::ratio`) and
   `holon::deposition`. Each emission records its predicted consequence, so the directed covector
   (predicted against unfolding) exists at the action. Test: on the chase terrain, deposits from
   action-time covectors against outcome-only deposits, in capture ticks.
10. **Attribution before deposition.** Extends `holon::deposition` and `holarchy::gluing`. The loop
    closure decides whether an error reached the mover's locus or the channel's, and only the
    reached locus deposits. Test: with the chase terrain's lag switch on, the mover's constitution
    is unchanged by errors that the lag caused.
11. **Gain by precision.** Extends the deposition step in `hnn::constitution` and the population's
    weights. A correction is weighted by the ratio of the prior's uncertainty to the total, so a
    noisy sensor corrects little. Test: on the chase terrain with a noisy channel, fixed-gain and
    precision-gain deposition compared, in capture ticks and in variance of the motion
    (Deming's funnel).
12. **Replay from the quotient at an aeon's close.** Extends `hnn::retention`, `receiver::standing`
    and the aeon boundary in `hnn::reference`. At an aeon's close, the machine regenerates passages
    from its retained keys and constitution and deposits from the regenerated comparison, never
    from an archive. Test: held-out code with replay against without, charged for its work.

## 13. The chase terrain

`[definition; agent-inferred]` The first terrain on which the machine moves (F6 in THE_REBUILD).

- **The arena.** An exact 2D arena over a rational lattice, with a declared tick. Each cell has a
  friction class `μ`, a rational from a declared finite set. Positions and velocities are exact
  rationals.
- **The runner.**
  - It is fast (speed bound `v_R`), and its acceleration per tick is bounded by traction: a velocity
    change `Δv` is admitted only if `|Δv|² ≤ (μ g h)²` on the cell it occupies, an exact quadrance
    inequality. For a pure turn this gives a radius of at least `v_R²/(μg)`.
  - A demanded change beyond traction slips: the runner keeps its tangent velocity for a declared
    number of ticks.
  - Its navigator is drawn from a declared family of evasion policies. The key (the initial
    configuration and the policy's parameters) is the terrain's truth.
- **The chaser (the machine).** Slower (`v_C < v_R`), with a larger traction class, so it is more
  agile. Every motion it emits satisfies its own traction bound exactly.
- **Capture.** The quadrance between the two is at most a declared capture radius squared.
- **Switches.**
  - A lag channel: the chaser observes the runner `d` ticks late.
  - A faulty sensor: one of two observation channels reports a rotated heading on declared aeons.
- **Reception phase.** The population reads the runner's passage and must select its constitution:
  its speed bound, its traction per friction class, its slip law and its policy family.
  - Acceptance: on hash-seeded arenas, the selected family is the true one.
  - Its code is within a declared margin of the truth code and strictly below the landmark tree
    reading the same passage.
- **Action phase.** The machine chases.
  - Acceptance: over pinned seeds, capture takes strictly fewer ticks in sum, and in more than half
    of the seeds, than both controls under the same traction bound: pure pursuit (head at the
    runner's present position) and constant bearing (null the line-of-sight rotation).
  - The traces show turns forced across low-friction cells, with the count of runner slips
    reported.
- **With the switches on.** Capture still beats the controls. The loop-closure reading locates the
  fault on exactly the aeons it is active, and lag-caused errors deposit nothing in the chaser's
  constitution.
- **The human baseline.** Brandon's own play through a small exact interface, recorded with real
  intervals. It is reported beside the machine, not as acceptance, and it is itself data with real
  flux.
- **Budget.** A few thousand ticks per seed in exact arithmetic, on the host. It is projected before
  running, against ten minutes and the host's memory.

## Obligations

- No law changes in code with this record. When a necessity above becomes a law, its classical
  counterpart enters Lean with it or is named in #62:
  - the Arnold-tongue scaling and the Stern–Brocot code;
  - the sequential test's optimality;
  - the viability kernel;
  - the Kalman gain.
- F6's rewrite and source-contract items 9 and 10 carry the plan and contract consequences.
