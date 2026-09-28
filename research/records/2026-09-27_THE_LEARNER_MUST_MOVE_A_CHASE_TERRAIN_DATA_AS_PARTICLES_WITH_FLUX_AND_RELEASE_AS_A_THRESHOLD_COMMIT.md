# The learner must move: a chase terrain, data as particles with flux, and release as a threshold commit

**Date:** 2026-09-27. Refs #63, #27, #148.

**Occasion.** A conversation after the README and workflow review, which began with Brandon's
question: "Predictions aside, architecture beyond LLMs, what can you see?" Claude answered from the
measured receipts. Brandon then corrected the picture three times, from how motion, pursuit, aim
and communication feel to him. This record keeps the derivation and what it asks of the machine.

**Reviewed the same day by GPT-6 Astra** (§14). Its corrections are marked in place with "§14"; the
original wording is in this record's history.

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
  `p/q` Arnold tongue shrinks like `K^q`: its two boundaries have contact order `q` at `K = 0`.
  `[proved-standard]` for this standard family (Banerjee, 2014); the exponent is not universal
  (§14.1)
- The tongues are ordered by Farey mediants, and every rational has a unique finite path in the
  Stern–Brocot tree. `[proved-standard]` The raw path is **not** self-delimiting (`L` is a prefix of
  `LL`); it becomes a prefix code only with its length coded first (§14.1).
- At critical coupling the locked intervals fill the full measure of `Ω`: the complete devil's
  staircase, found numerically by Jensen, Bak and Bohr and proved for critical circle maps by
  Świątek. `[proved-standard]`
- Plateaus need a nonlinearly driven family. A rigid rotation has none: the atlas row
  `lock.rigid-rotation-no-staircase` refutes a universal staircase for driven pairs.
  `[counterexample]`

**The join, as first stated, does not hold** (§14.1, `[counterexample]`). Tongue width (a set of
drive parameters), basin measure (a set of initial configurations) and a description prior are
three different quantities, and a period `q` can have a short description that `K^q` prices
linearly in `q`. What survives is narrower: coupled rings as **proposal dynamics**, a lock proposing
a key that exact receiver constraints then certify.

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

The two measurements test different hypotheses (search, and prior) and are reported separately
(§14.1). If neither holds, the reading is refuted. Brandon's later correction (§5) adds a second role for
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
- For a receiver that acts, the passive causal state is not enough: it can merge constitutions that
  a probe separates. Retention must be action-sufficient (§14.10).

## 4. The root: a distinction re-entering itself

`[proved-standard]` for the constructions; `[interpretation]` for the joins.
- **Spencer-Brown**, *Laws of Form* (1969): the calculus begins from one act, drawing a
  distinction. A distinction fed back into itself, `f = ¬f`, has no solution. With an added update
  law, `f_(n+1) = ¬f_n`, it oscillates with period two (§14.9).
- **Kauffman**: that oscillation, taken as the iterant `[+1, −1]` with a half-period shift, is `i`,
  with `i² = −1`. The Holonic half-turn `−1 = e^{iπ}` and quarter-turn `i` are the same pair.
- **The join.** A ring is what a difference looks like when it refers to itself. This is stronger
  than the algebra shows: re-entry with an oriented exchange gives the complex phase chart, and the
  Swing is the square of its quarter-turn, but not the parametron's storage law (§14.9). A cycle is born of
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
  (egg below the barrier, neck at it, cone above it) **fails** (§14.8, `[counterexample]`): the
  retarded front map yields the Mach cone and no envelope below the barrier, and the nonsingular egg
  curve has genus one, so no birational map carries the quadratic fronts onto it. It stays an image.

**Talking and striking** `[interpretation]`; the exact form is precursor information and lead time,
not a physical classification (§14.8).
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
parametron, gain is the pump. `[interpretation]`, **withdrawn as an identity** (§14.6): precision,
switching share and pump are distinct operands.

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
  the tightest turn at speed `v` has radius `v²/(μg)`. `[proved-standard]` for constant-speed
  circular motion; a discrete path's radius depends on its position-update convention (§14.4).
  Capture is not lock, and agility alone does not force capture in an open arena (§14.4). A faster, less agile
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
- **The directed error of execution exists at the moment of action.** The forward model's predicted
  consequence, compared with immediate actuator feedback, gives a signed execution error. The sign
  of an external error is available only once its signal reaches a receiver (§14.5).
- **An omitted expected signal is news**, once its declared arrival interval has passed: the
  evidence is the likelihood of no arrival by that receiver's clock (§14.5).
- **Self versus channel is decided by loop closure.**
  - A miss caused by the channel (lag) and a miss caused by the mover differ in which loop fails to
    close. The mover's prediction closes against its own motor record in the first case, but not in
    the second.
  - This is the deposition law in motion: deposit only at the locus a covector actually reached.
    An error attributed to the channel must not change the mover's constitution.
  - Two disagreeing channels detect a fault but cannot say which is faulty; localization needs the
    separation condition of §14.5 (for example three independent readings).
- **Overcorrection is tampering.** Deming's funnel (*Out of the Crisis*, 1986): adjusting a stable
  process in response to each deviation increases its variance. `[proved-standard]`
  - The Kalman gain (Kalman, 1960) weights a correction by the ratio of the prior's uncertainty to
    the total uncertainty. `[proved-standard]`
  - A sense that cannot see the body (proprioception alone) is a noisy sensor. Its corrections
    deserve a small gain, and treating it as precise is tampering. A grain's width alone does not
    give a precision; the uncertainty law must be declared (§14.6).
- **Replay is regeneration from the quotient, not a tape.** A mental replay regenerates the motion
  from the retained keys and constitution, which is what the retention law permits. Nothing is
  archived. A regenerated passage carries **no new evidence** in expectation; it may improve an
  approximate representation, never confidence (§14.10).

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

## 12. What the machine lacks: thirteen necessities

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
   - The law is `Q_R` of §14.3. A later turn made cheap to code is not by itself value: a useless
     reply that reliably provokes a complaint also makes the next turn predictable.
3. **Switching driven by evidence of change.** Extends `receiver::population::dormancy` (the fixed
   share `α = 2^(−j)`). Surprise magnitude alone is not evidence of change; the likelihood ratio of
   change against no change is. The law is a mixture over a declared ladder of hazards, with the
   pathwise bound of §14.6. Test: on the aeon-switching terrain, against the fixed rate's
   `169 + 9/16 + ε` bits (the static population's `688 + 6/16`). The pump is a separate operand.
4. **Timing.** Extends source-contract item 9 in `HNN_FORMULA`, `curated_source.py` and
   `aeon::epoch`. Releases carry their intervals, since the phase between rings is where rhythm
   lives. Test: the curated stream with intervals as cells against without them, charged.
5. **Release as a threshold commit.** Extends `receiver::release::DecisionRule` and release-contract
   item 1.
   - At each receiver section the machine compares releasing under `Q_R`, waiting, a viable probe
     and a typed refusal, each with its declared cost (the Bellman comparison of §14.3). The binary
     stationary case is the sequential test on log-odds. Delay has no canonical price in bits; the
     participating receiver's decision law supplies it.
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
   - The reading composes observed transports around declared circuits against their expected
     holonomy. A defect on at most `k` edges is uniquely located exactly when the circuit matrix's
     kernel holds no nonzero vector of support at most `2k` (§14.5).
   - Test: the chase terrain's faulty-sensor switch, over a channel menu that meets that condition,
     located on the aeons it is active and nowhere else.
8. **Probing.** Extends `receiver::release` and the population's mixture. Where the fibre is wide,
   the machine emits the probe with the greatest expected information gain over its families
   (Lindley, 1956; `[proved-standard]` for the criterion). Test: in the chase terrain's reception
   phase, the runner's constitution is selected in fewer ticks with probing than with passive
   observation.
9. **Every action carries its prediction.** Extends the ratio calculus `R⁻¹dR` (`hnn::ratio`) and
   `holon::deposition`. Each emission records its predicted consequence, so the execution error
   (predicted against actuator feedback) exists at the action, and the external error when its
   signal arrives. Test: on the chase terrain, deposits from
   action-time covectors against outcome-only deposits, in capture ticks.
10. **Attribution before deposition.** Extends `holon::deposition` and `holarchy::gluing`. The loop
    closure decides whether an error reached the mover's locus or the channel's, and only the
    reached locus deposits. Test: with the chase terrain's lag switch on, the mover's constitution
    is unchanged by errors that the lag caused.
11. **Gain by precision.** Extends the deposition step in `hnn::constitution` and the population's
    weights. The normal law's `H ← H + w f fᵀ` already has the slot: with `w` the observation's
    precision under a declared uncertainty law, it is the information-form update, and a noisy
    sensor corrects little. A grain's width alone is not a precision (§14.6). Test: on the chase terrain with a noisy channel, fixed-gain and
    precision-gain deposition compared, in capture ticks and in variance of the motion
    (Deming's funnel).
12. **Replay from the quotient at an aeon's close.** Extends `hnn::retention`, `receiver::standing`
    and the aeon boundary in `hnn::reference`. At an aeon's close, the machine regenerates passages
    from its retained keys and constitution and deposits from the regenerated comparison, never
    from an archive. Regenerated passages carry no new evidence in expectation, so replay may only
    refine an approximate representation (§14.10). Test: held-out code with replay against without,
    charged for its work.
13. **Action-sufficient retention.** Extends `receiver::standing`, `Foundation/Standing` and
    `Context/Merge.encoding_square_or_separator`. The retained quotient must not merge
    constitutions that an admitted action would separate (§14.10). Test: on the chase terrain, a
    passive quotient that merges two runners distinguishable only by a probe is refused, and a
    separating probe is emitted where one is affordable.

## 13. The chase terrain

`[definition; agent-inferred]` The first terrain on which the machine moves (F6 in THE_REBUILD).

- **The arena.** An exact, **bounded** 2D arena over a rational lattice, with a declared tick. Each
  cell has a friction class `μ`, a rational from a declared finite set. Positions and velocities are
  exact rationals. The walls (or a declared policy constraint) are what make forced turning
  possible: in an open arena a faster runner moving straight away is never caught (§14.4).
- **The runner.**
  - It is fast (speed bound `v_R`), and its acceleration per tick is bounded by traction: a velocity
    change `Δv` is admitted only if `|Δv|² ≤ (μ g h)²` on the cell it occupies, an exact quadrance
    inequality. For a pure turn this gives a radius of at least `v_R²/(μg)`.
  - A demanded change beyond traction slips: the runner keeps its tangent velocity for a declared
    number of ticks. This is a declared hybrid slip law, not a consequence of Coulomb friction.
  - Its navigator is drawn from a declared family of evasion policies. The key (the initial
    configuration and the policy's parameters) is the terrain's truth.
- **The chaser (the machine).** Slower (`v_C < v_R`), with a larger traction class, so it is more
  agile. Every motion it emits satisfies its own traction bound exactly.
- **Capture.** The quadrance between the two is at most a declared capture radius squared.
- **Switches.**
  - A lag channel: the chaser observes the runner `d` ticks late.
  - A faulty sensor: one of **three** independent, time-aligned observation channels reports a
    rotated heading on declared aeons. Two channels can detect the fault but not locate it (§14.5).
- **Reception phase.** The population reads the runner's passage and must select its constitution:
  its speed bound, its traction per friction class, its slip law and its policy family.
  - Acceptance: on hash-seeded arenas, the selected fibre is future-equivalent to the truth under
    the admitted actions. The exact family is required only where a probe separates it: two speed
    bounds stay indistinguishable while every observed motion lies below both (§14.10).
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

## 14. GPT-6 Astra's review

The same day, GPT-6 Astra (read-only) was asked ten questions on this record. Claude checked every
owner it cites against the tree (`Context/{Merge,Standing,Composition}`, `Physics/PhaseCarrier`,
`Foundation/RelationLadder`, `hnn::constitution`); each exists as cited. The corrections are applied
in place above. Its main results follow.

### 14.1 Birth

- `[counterexample]` No finite observation determines an unrestricted navigator family: after `n`
  zeroes, "always zero" and "zero until the next tick, then one" both survive. A residual excludes
  families; it does not specify the replacement.
- `[proved-derived]` **A tractable founding law in a finite rational chart.** From a reached
  separating covector `λ_r`, close the receiving forms under the admitted transports:
  `V₀ = span(V_old, λ_r)`, `V_(n+1) = V_n + Σ_a T_a* V_n`. Each strict step raises the dimension, so
  there are at most `d` of them. With a basis `φ_i` and `T_a* φ_i = Σ_j U_(a,ij) φ_j`, the map
  `E(x) = (φ_i(x))` satisfies `E T_a = U_a E`. It constructs an observable transport representation;
  it does not infer an unknown `T_a`.
- `[proved-standard]` When the transport is unknown but finite-state, distinguishing probes and
  counterexamples construct it efficiently, given membership and equivalence queries (Angluin,
  1987). Passive data does not supply the latter.
- `[counterexample]` The `K^q` tongue scaling is not universal. For `x + Ω + K sin(2πqx)`, the
  `q`-step resonant sum at `Ω = p/q` is `qK sin(2πqx)`, a first-order resonance.
- **The decisive ring experiment** measures search (work to a future-equivalent key on blind moiré,
  parity moiré and rotor terrain, against enumeration and menu propagation, all work charged) and
  prior (basin fractions over a certified partition against a declared mass law) separately. The
  controls include a nonlocking carry word.

### 14.2 Landmark to navigator

- `[proved-derived]` The context tree is already an egg family: its navigator shifts the address,
  its constitution holds the counts, and `Context/Standing.address_standing` gives the retention.
  A leaf alone suffices only under `ShiftClosed`; `unclosed_leaf_is_not_a_standing` is the
  counterexample.
- `[proved-derived]` Promotion of a landmark's continuation law `C` to a composed navigator `G`
  pays exactly when `π_G P_G(x) > π_C P_C(x)` on untouched observations, an integer cross-product
  comparison for rational operands (`Context/Merge.merge_cost_mass_iff`). The new family gets no
  credit for the observations used to build it, and a composed family pays its chain-rule code
  (`Context/Composition.chain_rule`).
- `[interpretation]` F1 generalizes from spelling merges to reusable **continuation transports**.

### 14.3 Release

- `[proved-derived]` **The receiver-conditioned release law.** With the population's law `P₀(e | s)`
  for a complete emission (its stopping section included), the addressed receiver's face
  `L_R(z | e, s)` for the requested consequence `z`, a declared emission cost `c_R(e)` in bits, and
  the viable emissions `A_K(s)`:

  ```text
  Q_R(e | s) = 1_(A_K(s))(e) · P₀(e | s) · L_R(z | e, s) · 2^(−c_R(e)) / Z_R(s)
  ```

  It is the unique minimizer, among laws supported on `A_K(s)`, of
  `D(Q ‖ P₀) + E_Q[c_R(e) − log₂ L_R(z | e, s)]`, which equals `D(Q ‖ Q_R) − log₂ Z_R(s)`.
- `[proved-derived]` Once a receiver term enters, `P_release = P_scored^release = Q_R`, timing and
  stopping included. `P₀` becomes the reported predictive control. Sampling `Q_R` and taking its
  maximizer are different laws and are recorded as such.
- `[proved-derived]` **Value at the receiver**: `v_R = log₂ q_R(b | c, e) − log₂ q_R(b | c)`, the
  reduction in a named receiver's code for the same later reading `b`. Its expectation under one
  joint law is `I(B; E | C)`. Individual values can be negative.
- `[counterexample]` Predictability is not the objective: a useless reply that reliably provokes
  "that did not answer my question" makes the next turn cheap to code. A recorded continuation of
  `e₀` is not an observed consequence of an alternative `e₁`.
- `[proved-derived]` The stopping law is a Bellman comparison of release, waiting, a viable probe and
  a typed refusal. For two hypotheses under stationary independent observations it is
  `B(p) = min{C₁₀(1−p), C₀₁ p, d + Σ_y q_p(y) B(p_y)}`, and Wald and Wolfowitz's optimality holds only
  in that scope.

### 14.4 Pursuit and reachability

- `[proved-derived]` The relative configuration is the Ratio `R = g_C⁻¹ g_R`, and the contact reads
  `Q = ⟨r, r⟩`, `Q̇ = 2⟨r, ṙ⟩`. A varying friction field keeps absolute placement in the state.
- `[counterexample]` **Capture is not lock**: zero relative velocity outside the capture radius
  persists forever, and crossing the capture boundary happens with nonzero relative velocity.
- `[proved-derived]` On a finite exact terrain, with `Pre(S) = {z : ∃u ∀w, T(z, u, w) ∈ S}`, the
  capture basin within `n + 1` ticks is `C_(n+1) = C_n ∪ Pre(C_n)` from `C₀ = {Q ≤ ρ²}`, and the robust
  viability kernel is the limit of `K_(n+1) = K_n ∩ Pre(K_n)`. Under partial observation they act on
  the compatible state fibre. Continuous reachability is the Hamilton–Jacobi–Isaacs zero sublevel
  set (Mitchell, Bayen and Tomlin, 2005).
- `[proved-derived]` Phase-only: `φ̇ = δ − K sin φ` has equilibria iff `|δ| ≤ K`. The lines `|δ| = K`
  bound parameters (saddle-node); the unstable roots bound state-space basins. With bounded control
  and disturbance, an interval admits robust inward control iff `F(a) + U − d ≥ 0` and
  `F(b) − U + d ≤ 0`. This is a phase viability condition, not an identity between tongues and
  capture barriers.
- `[proved-derived]` Constant bearing is a lock of the bearing receiver,
  `d/dt arg r = det(r, ṙ)/|r|² = 0`, which permits radial slip. Approach also needs `⟨r, ṙ⟩ < 0`.
- `[counterexample]` In an open arena a faster runner moving straight away is never caught:
  `r(t) = (r₀ + (v_R − v_C) t) e`. Hence the bounded arena in §13.

### 14.5 Attribution by loop closure

- `[proved-derived]` The live reading is `R_C = Ĥ_C⁻¹ H_C`, observed against expected holonomy
  (lawful curvature can be nonzero), in one base frame. This is `Transport/CellHolonomy` applied to a
  live comparison.
- `[proved-derived]` With circuit matrix `C` and syndrome `s = Ce`, a defect on at most `k` edges is
  uniquely located iff `ker C` has no nonzero vector of support at most `2k`. Over all cycles of a
  connected graph `ker C = im d₀`, whose smallest support is the minimum edge cut, so `k`-edge faults
  are recoverable iff the minimum edge cut exceeds `2k`.
- `[counterexample]` A triangle detects one edge fault but cannot locate it, and two disagreeing
  channels cannot say which is faulty. Three independent, time-aligned readings correct one by
  agreement, unless their errors share a common mode.
- `[proved-derived]` For `H = B T_e A`, a reached covector pulls back to the edge as
  `G_e = B* G_H A*`, and deposition consumes it there. A plural attribution stays plural until
  observations separate it.
- `[counterexample]` An action's prediction does not give the sign of an unobserved external error;
  a missing confirmation is evidence only after a declared arrival interval.

### 14.6 Gain

- `[proved-derived]` Minimizing `(x − m)²/(2P) + (y − x)²/(2R)` gives `x⁺ = m + K(y − m)` with
  `K = P/(P + R)`, exact over the rationals where the inverses exist. The normal law's
  `H ← H + w f fᵀ` is the information-form slot, with `w` the precision. (`hnn::constitution` carries
  the Gram `H` and the prox iterate `W`, not `B`.)
- `[counterexample]` A grain does not determine a precision: `[−1, 1]` carries laws of variance `1`
  and of variance `1/2`.
- `[proved-derived]` Fixed share at `α = 2^(−j)` over `N` transitions with `k` switches costs at most
  `kj + (N − k)c_j` beyond the comparator path, `c_j = −log₂(1 − 2^(−j)) ≤ 3·2^(−j)`
  (`Context/{LocalWeighing,Dormancy}`; Herbster and Warmuth, 1998). A mixture over a declared hazard
  ladder pays at most `−log₂ π_j` over each rung; with `j = ⌈log₂(N/k)⌉` on the ladder, the switch
  and stay charge is at most `k log₂(N/k) + 4k`, pathwise, without knowing where the switches fall.
- `[counterexample]` Surprise magnitude is not evidence of change; the change/no-change likelihood
  ratio is. Precision, switching share and pump are distinct operands: identifying them would need
  an intertwining transport and a power/code relation.

### 14.7 Data as particles

- `[proved-derived]` A pinned record `R` suffices for an admitted encoding family exactly when every
  admitted `E` factors as `Ē ∘ R`. `[counterexample]` No lossy record preserves every unrestricted
  future lens, so item 10's promise is relative to the lenses the acquisition contract admits.
- `[interpretation]` Pin the fullest lawful record: identities and lineage (split, merge and
  disappearance), changes with boundary state, clocks, intervals, units, grains and acquisition
  uncertainty, causal incidence and emitted controls, responses, censorship and channel status, and
  source versions. Unknown causes stay an unresolved fibre.
- `[proved-derived]` A concept's identity cannot come from similarity. Sameness of transformation is
  `U_out T₁ = T₂ U_in` preserving the admitted readings; persistence across aeons also needs
  lineage (`Foundation/RelationLadder`).
- `[interpretation]` Exact games give the most information per unit of compute for **closed-loop
  law discovery**, because probes separate competing constitutions. Git supplies exact
  transformations with latent causes; conversation supplies the product receiver.

### 14.8 The moving source

- `[proved-derived]` For a source `z(τ) = vτe` in a medium of signal speed `c`, fronts satisfy
  `(v² − c²)a² + 2v r_∥ a + |r|² = 0`. For `v > c` the envelope is `c² r_∥² = (v² − c²)|r_⊥|²` with
  `r_∥ < 0`, so `sin μ = c/v`. At `v = c` the fronts are tangent at the source; below it there is no
  envelope.
- `[counterexample]` This does not derive the Hügelschäffer egg: the fronts are quadratic, and the
  nonsingular egg's projective curve has genus one.
- `[proved-derived]` Predictability at a receiver is the precursor information `I(Z; F_R⁻ | Θ_R)`
  together with enough lead time: `λ_R(contact) − λ_R(first useful precursor) ≥ δ_R`, its response
  delay. `[counterexample]` Supersonic does not imply unpredictable (an announced impact, a faster
  optical channel), and subsonic does not imply informative.

### 14.9 Re-entry

- `[counterexample]` `f = ¬f` has no solution. Oscillation needs an added update law,
  `f_(n+1) = ¬f_n`, of period two, which supplies no duration.
- `[proved-derived]` Kauffman's iterants give the complex structure: `J = DS`, `J² = −I`, and the
  Swing is the square of the oriented quarter-turn `Q_a x = a + J(x − a)` (now in the
  [objects](../../docs/ELEMENTARY_OBJECTS.md)). The parametron's half-turn sheets come from its pump,
  `V(φ) = −κ cos(2φ − ψ)` (`Physics/PhaseCarrier`).
- `[counterexample]` Re-entry does not derive the parametron's incidence, storage, dissipation or
  pump, so "the ring is the first composite of difference" is stronger than the algebra shows.

### 14.10 The question nobody asked

**Does the retained quotient preserve the consequences of actions not yet taken?**
- `[counterexample]` Two constitutions both emit zero under the passive action and differ under a
  probe. A passive causal-state quotient merges them; an action-sufficient quotient must not. The
  same obstruction makes "select the exact true family" impossible in the chase's reception while
  every observed motion stays below both speed bounds.
- `[proved-derived]` The required equivalence is agreement of future faces under every admitted
  action word `do(a₁…a_m)` and receiver. In a linear chart, `ker E ⊆ ker ρ` and
  `T_a ker E ⊆ ker E` for every admitted `a`. Predictive-state representations (Littman, Sutton and
  Singh, 2001) are the established construction. This is now stated in the
  [objects](../../docs/ELEMENTARY_OBJECTS.md#8-deposition) and the guides' retention law.
- `[proved-derived]` A probe's value is `I(Θ; Y | h, do(a))`, zero for a probe whose outcome law is
  the same under every surviving constitution.
- `[proved-derived]` Regenerated passages drawn from the current predictive law carry no new
  evidence in expectation: `Σ_y P(y | h) P(θ | h, y) = P(θ | h)`.

### 14.11 Astra's ranking of plan changes

1. **F6:** controlled sufficiency and identifiability, with a future-equivalent fibre and a
   separating probe where one is available.
2. **F4:** the normalized receiver-conditioned release and stopping consumer, `Q_R`, after the first
   receipt.
3. **F1:** residual-founded transport discovery before any broad ring search.
4. **F6:** fault observability before localization: a channel menu that meets the separation
   condition.
5. **Gain and intervals:** joined to those consumers, with declared uncertainty laws and the hazard
   ladder's bound.

THE_REBUILD carries all five.

## Obligations

- No law changes in code with this record. When a necessity above becomes a law, its classical
  counterpart enters Lean with it or is named in #62:
  - the Arnold-tongue scaling and the Stern–Brocot code;
  - the sequential test's optimality;
  - the viability kernel;
  - the Kalman gain.
- From §14, owed in #62: the transport closure `E T_a = U_a E`; `Q_R`'s variational identity; the
  localization condition `ker C ∩ {support ≤ 2k} = 0`; the capture and viability recursions; the
  hazard ladder's bound; `Q_a² = S_a`; the action-sufficient quotient's descent; and the
  no-new-evidence identity for regenerated passages.
- F6's rewrite and source-contract items 9 and 10 carry the plan and contract consequences.
