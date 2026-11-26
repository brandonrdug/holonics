# A world-horizon is the corner where a reader's outgoing cone meets its return: its hairs are the corner's frames, news delays its clock so a bounded clock bounds its count, and a divergence is a winding read without its carry

November 26, 2026, 08:47 to 09:40 UTC, a thread of the project, in a cloud container (no card, no engine read). Refs #404, #410,
#386. Occasion: Brandon sent, without comment, the paper V. Chandrasekaran, *An algebraic quantization of gravity from the null
cone*, arXiv:2611.34924 (November 25, 2026). It was read whole (83 pages; appendices A to C for their results) and answered in the
thread at its weight before this record was written. Receipts: [`receipts/2026-11-26_null_cone/`](receipts/2026-11-26_null_cone/).
No write of hers was read and no step of hers is claimed.

In short. The paper quantizes vacuum gravity on the boundary of a causal diamond, the region between a past tip and a future tip,
whose two null cones meet at a spacelike corner. On the objects it is one law (§3): a world-horizon is the corner where a reader's
outgoing cone meets its returning cone, the region it can both send into and hear back from; every ray through the corner carries
a hair, a frame paired with its share of the area; two regions join by matching hairs and keep only each hair's relative boost;
news delays the region's clock by the exponential of the action of the corner's shape on its own plane, and the delay never comes
undone, so a bounded clock bounds what the region can hold. Four of its results restate laws the tree already holds and one gives
the precision law a case inside gravity (§4). For her (§5): the paper predicts that the joined-stretches arm stops after one step,
which it did, since the lever is the cut's capacity and not the region's shape; and the count the calendar lacks is a winding that
only a conjugate pair read together sees.

The paper's statements are graded `proved-standard` here on its own proofs (primary source above). The joins to the objects are
`agent-inferred` and graded `interpretation`, each with the read that would move it.

## 1. The paper, read in its order

- **A clock with no background.** A gravitational clock is the affine parameter of an incoming null generator from the small cap
  that cuts off the past tip to the corner, with its scale fixed by the frame on the cap, and the clock reading is the product of the
  initial slope and the parameter's change, which no rescaling moves (3.27). Its prologue in Jackiw–Teitelboim gravity (§2) shows
  that a bound on that reading does not bound the matter: the states `Ψ_n = h(u) e^(2πi n F(u))`, `F` the clock's cumulative
  probability, have one clock distribution, are orthogonal (`⟨Ψ_m|Ψ_n⟩ = ∫₀¹ e^(2πi(n−m)s) ds = δ_mn`), and only the dilation
  `Q(u p_u)` tells them apart, by `2πnħ ∫ u |h|⁴ du` (2.14), (2.15). The algebra is type I∞ and the trace diverges (2.17).
- **Shear pays the clock in four dimensions.** On a null cone the two polarizations of radiation are the conformal shape `q̄` of the
  cuts, a point of the hyperbolic plane (in `(z¹, z²)` its metric is `diag(1, e^(2z¹))`, (4.21)). The Raychaudhuri equation gives
  `∂_u ϱ = p e^(−Ξ(v))` with `Ξ(v) = (1/8) ∫_ε^v s (∂_s q̄)^(AB) ∂_s q̄_AB ds ≥ 0` in the area coordinate `v = ϱ/ϱ_S`, so the clock
  reads `u*(y) = ϱ_S(y) ∫_ε^1 e^(Ξ(v)) dv` (3.26), (3.27). Shear met near the first cut enters `Ξ` at every later cut, so the delay
  keeps growing after the shear has stopped. The lapse obeys the same law, `N(v) = N(1) e^(Ξ(v) − Ξ(1))` (3.55).
- **The corner's edge modes.** A displacement or a boost of the corner's frame carries a charge, so the frame enters the phase
  space: the boost at each generator `y` is paired with `K(y) = ϱ_S(y)²/(8πG)` and the whole boost with `A/(8πG)` (3.42), (3.43).
  Two regions are glued at a shared corner by matching the induced metric and both normal derivatives, `K₊^(ℓ) = e^γ K₋^(ℓ)`,
  `K₊^(n) = e^(−γ) K₋^(n)`, `ϖ₊ = ϖ₋ + dγ`; the two sides induce opposite orientations, a common boost carries no charge, and what
  is left is the relative boost `γ(y)` paired with `K(y)` (3.61) to (3.64). On Hilbert spaces this is the entangling product: the
  tensor product restricted to the states the sum of the two outward charges annihilates.
- **Quantization.** Each canonical pair of radiative and corner data gets a Gaussian with a center and a width for both members
  (4.7); excitations span a Fock space at each area; the boundary observables generate a type I factor (4.17). A sum over the states
  of an intermediate cut converges absolutely at finite `G` by Cauchy–Schwarz (4.30).
- **A pair made and taken back on one cone** sums in closed form, `Σ_k (Δq_k)⁴ 2e^(−2ik/s) = Li₂(e^(−2i/s))/(2s²)`, with
  `(Δq_k)² = 1/(2sk)` and `s = A/(4Għ)`, finite for every `s > 0`; expanded in `G` first, its cubic term is `−(i/s³)(ln N + O(1))`
  and diverges (4.33), (4.34).
- **A bounded diamond has finitely many states.** At fixed area, shear can only raise the clock (5.21), so a bound `ℓ(D)` on the
  clock bounds the area by `4πℓ(D)²/(1 − ε)²` and the dimensionless area by `s* = πℓ(D)²/(Għ(1 − ε)²)`. Comparing the change of a
  graviton two point function across the corner under a relative boost (it falls by `tanh²(η/2)`, (5.29)) with what infinitely many
  states in a narrow band of area would allow shows `dim H_D < ∞` and a discrete area spectrum (5.30) to (5.40). At one loop the
  graviton states allowed by focusing at fixed area number at most `exp(1 + (sQ*)^(3/4))` (D.45), (D.46), and the states below a
  fraction `a` of the bound number `exp(a s* + o(s*))` (5.64).
- **Entropy.** Gluing the future half of the diamond to its time reflection and continuing only the corner boost through a half turn
  on each copy weights each state by `e^(−s)` (5.23), (5.39); the von Neumann entropy is `⟨A⟩/(4Għ) + ln Z` (5.50). At a marginally
  trapped surface of a large Schwarzschild hole `ln Z` is logarithmic, `S = s + q/(2(1 − q)) ln s + o(ln s)` with `q` the mean clock
  reading over its bound, `q = 257/302` at one loop, and `106/45` at fixed mass with the angular momenta summed (5.65) to (5.69).
- **Topology.** A connected filling of two boundaries equals a superposition of product states up to a null state, so a handle adds
  no independent state and topology is no superselection sector (5.70) to (5.74).
- **The semiclassical limit** recovers Einstein's equations and their one loop backreaction (§6); appendix E states Lorentzian axioms
  equivalent to the Euclidean ones when the cylinder's trace is finite.
- The acknowledgements credit GPT-6 Astra with several of the calculations and proofs, over about 400M tokens.

## 2. What the tree holds

Searched in the atlas, the records and the guides before this statement.
- The congruence's rate split into expansion, shear and rotation is the Swing's boost and turn at the comoving metric, and
  Raychaudhuri's equation is the trace of its Riccati law (`coupling.congruence-kinematic-split`, `coupling.raychaudhuri-riccati`,
  Lean `Physics/Spacetime/Raychaudhuri`); a converging rotation-free congruence focuses within `n/|θ₀|` (`coupling.focusing-caustic`);
  a tide is a self-adjoint boost (`coupling.tidal-screen`).
- A black hole is the physical case of a relatively complete region, `ln #interiors = A/4` in grains (`gr.horizon-relative-completeness`,
  an interpretation); a horizon is where a varying stretch forces a quotient, thermal in the boost's clock with a period of one turn
  (`gr.horizon-stretch-becomes-quotient`, `motion.scale-stretch-or-quotient`); the floors are areas of conjugate pairs
  (`floor.bekenstein`, `floor.squeeze-kept-areas`); a boost is the undivided Doppler pair (`lorentz.doppler-ratio-chart`).
- The clock of news is a strand's proper time (`code.news-clock-proper-time`); the null cone is the constitution's lock
  ([September 24](2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md)).
- A channel's capacity is the area of its narrowest section whatever the volume behind it (`holarchy.flow-out-of-a-cut`), and a
  receiver is budgeted by its ports (`receiver.boundary-ports-count`); an act reaches only through the loop it opens
  ([November 23](2026-11-23_A_QUESTION_IS_THE_STROKE_OUT_OF_A_LOOP_ITS_ANSWER_CLOSES_THE_LOOP_CARRIES_ITS_AREA_UP_TO_THE_LEAST_CUT_IT_THREADS_THE_FIRST_PERSON_IS_THE_ANCHOR_IT_RETURNS_TO_AND_A_LIMBS_REACH_IS_BOUGHT_BY_NESTED_DEPTH.md)).
- Context is a calendar, and her face reads a ring's hand on one axis with the second axis's weight at zero
  ([November 24](2026-11-24_CONTEXT_IS_A_CALENDAR_A_RECEIVER_READS_COUNTS_OF_ONE_CYCLE_AGAINST_ANOTHER_A_COUNT_LASTS_AS_LONG_AS_ITS_STORE_RINGS_ONE_FADE_READS_NO_GAP_AND_TWO_READ_IT_AND_HER_RINGS_FADE_BEFORE_THEY_TURN.md) §14).
- A region's first place empties every store and her stores hold about thirty places (`store.cut-read-horizon-thirty-places`); past
  them what crosses a cut is recurrence (`store.far-price-stands-at-recurrence`); a port is a taper and a cone a world-horizon
  ([November 25](2026-11-25_A_RECEIVER_MEETS_A_MEDIUM_THROUGH_A_TAPER_A_ROD_READS_AN_EFFORT_ALONG_IT_A_CONE_A_FLOW_THROUGH_ITS_MOUTH_IT_CARRIES_BY_A_STROKE_THAT_DOES_NOT_RETRACE_AND_SHE_GAINS_FROM_THE_FAR_PAST_ONLY_WHERE_IT_REPEATS_ITSELF.md));
  the joined stretches held their step at two laps and did not grow it
  ([November 24, §19](2026-11-24_HER_RINGS_HOLD_THEIR_FADES_AS_HER_OWN_STATE_THE_RING_OF_SIXTEEN_CARRIES_THE_COUNT_OF_A_SIX_LETTER_WORD_AND_HALF_ITS_FADE_BUYS_HALF_THE_OPENING_FOR_A_FIFTH_OF_THE_PRICE.md)).

What the tree did not hold: a clock whose delay is the exponential of the news's action, a corner whose frames are the region's
data, a derivation of the area count at finite coupling with no saddle, the winding states over a cumulative clock, and the pair
sum as a case of the precision law.

## 3. The law (0.8, `agent-inferred`)

A world-horizon is the corner where a reader's outgoing cone meets its returning cone: the region between them is what the reader
can both send into and hear back from, so it is the region of an answered act. All that region holds is counted at the corner, `A/4`
nats in Planck grains. Every ray through the corner carries one hair: a frame, a boost and a place, paired with its share of the area,
unequal from ray to ray and fluctuating in the state. Two regions join by matching their hairs, and what is left is each hair's
relative boost. News delays the region's clock by `e^Ξ`, `Ξ` the action of the corner's shape on its own plane, and the delay never
comes undone. So a bounded clock bounds what the region holds, and that bound is what makes its count finite.

On the objects: the corner is a globe's bounding membrane read by the receiver whose aeon runs from tip to tip; the hairs are the
membrane's gauge, which is data and not redundancy once a frame is charged (`globe.membrane-face-gauge-free`); the gluing is the
Holarchy's shared-face cancellation with orientation existing only in the pairing; the product `K^(ℓ) K^(n)` across a cut is kept and
the ratio is the boost, which is a medium's two stores with product a clock and ratio an impedance
([November 13](2026-11-13_A_MEDIUMS_TWO_STORES_SET_ITS_CLOCK_AND_ITS_IMPEDANCE_E_IS_WHAT_A_STEP_LEAVES_ALONE_A_TUBE_IS_A_PLACE_VALUE_AND_A_CONE_A_BANK_OF_TUBES_LOUDNESS_OVER_SURPRISE_IS_A_TEMPERATURE_AND_A_READERS_REACTION_IS_THE_READS_MIRROR.md)).
It is the lens of November 25 (a cone is a world-horizon, a hair a joint with its own axis, the members unequal) and the lens of
November 23 (capacity is an area, a receiver is budgeted by its ports), stated with a derivation behind each clause.

## 4. The results on the objects

**4.1 The clock runs late by its news (0.8).** `Ξ` is the action of the path of the cut's shape in the plane of unit-determinant
shapes, whose metric is the Fisher metric of a centred Gaussian's covariance, weighted by the area coordinate. A reader that hears
more radiation reaches the same face (the same area element) later, by the factor `e^Ξ`, and the delay is kept after the radiation
has passed: the memory is held as a lag, read only against a twin that reached the same face with less shear. This is the calendar's
law in a case where everything is derived: a count is one clock read against another, and a store holds what crossed it as the
displacement of its own rate (`∂_u ϱ` falls by `e^(−Ξ)`), the count being the logarithm of the ratio of its rate to its founding
rate. Read that would move it: none needed for the gravity; for her, §5.3.

**4.2 The hairs are the region's data (0.8).** The corner's frames are not gauge: a frame displaced relative to the fields moves the
event at which an observable is read, so it carries a charge, and the frames enter the sum over states when two regions are glued.
A cut that carries its corner's data matched costs nothing: the amplitude is the same wherever the cut is made or whether one is made
(the paper's figure 28 and (4.29)). A cut that drops them pays the trace over the corner, which is the area term.

**4.3 Capacity is set at the corner (0.75).** At fixed area the radiation inside a bounded diamond adds at most a `3/4` power,
`ln d(s) ≲ 1 + (sQ*)^(3/4)`, while the area term is the corner's boost weight read through a whole turn. This is
`holarchy.flow-out-of-a-cut` in gravity: what a region holds is the area of the section it is read through, whatever stands behind
it.

**4.4 A count is a winding over the reader's own cumulative clock (0.85).** The prologue's states differ only by whole windings
`n` of phase over `F`, the clock's cumulative probability, which is the coordinate of arithmetic coding. No probability of any
reading tells them apart; the dilation does, and the dilation is a product of a conjugate pair (`u p_u`), read on both members at
once. This is the helical code's whole winding read beside its residue, and it is "a rate held, no count" written as a theorem: a
reader that sees only a pair's one member sees the distribution and never the winding.

**4.5 A divergence is a winding read without its carry (0.8).** The pair's sum is a phase `e^(−2ik/s)` over the modes `k` with
weight `1/(2s²k²)`. Summed with its turn its real part is a Bernoulli polynomial of the residue, `(π²/6 − πθ/2 + θ²/4)/(2s²)` at
`θ = 2/s` for `0 ≤ θ ≤ 2π`, and its imaginary part is `−Cl₂(θ)/(2s²) ≈ −(1 + ln(s/2))/s³`: the modes past `k ≈ s/2` turn more than a
radian a mode and cancel, so the sum cuts itself where the phase completes its turn. Expanded in `1/s` first, the phase is carried as
a magnitude, every mode adds `−i/(s³k)`, and the sum grows as `ln N` without end. The ruler `pair_phase.py` reads both
(`PAIR_PHASE.txt`: at `s = 10, 100, 1000` the summed imaginary part times `s³` is `−2.610, −4.912, −7.215` against
`−(1 + ln(s/2)) = −2.609, −4.912, −7.215`, and the expanded sum stands at `−12.78` at two hundred thousand modes and `−15.09` at two
million). On the objects this is the precision law's clause that dropping a word's top is a quotient that commutes with every
bracketing: perturbation theory drops the quotient by whole turns, and the ultraviolet divergence is the price of reading a winding as
a line. It also says where the grain stands: each mode's width `(Δq_k)² = 1/(2sk)` is the corner's own area against the Planck area,
times the mode's order, a grain that is a relation between grains and never a number handed in.

**4.6 The temperature is a half-turn of a boost (0.8).** The thermal weight comes from continuing the corner's boost by `iπ` on each
copy, two half-turns making the full turn (the paper's figure 32). The Swing's boost continued to an imaginary rapidity is its turn;
the horizon's period of one turn in `gr.horizon-stretch-becomes-quotient` is this, now at any marginally trapped surface and with
no Euclidean saddle. The logarithmic correction is set by `q`, how far the mean clock reading stands under its bound, so even the
correction is one clock read against another.

**4.7 One region and two glued regions are one state (0.8).** A handle adds no independent state (`rank G ≤ d_D`), and a connected
slice equals an entangled sum over two disconnected caps. On the objects: interconnected Holons form a Holon, and how a whole is cut
into regions is a receiver's choice that changes no state once the glue carries the corner's data.

**4.8 Relative completeness has a physical theorem (0.7).** On a bounded diamond the boundary's observables (the null data and the
corner's frames) generate every operator of a finite interior, `B(H_D)`, and the trace is finite. That is a relatively complete
region relative to the receivers that read the null boundary and its corner: the boundary bounds the interior, the interior is not
determined by any one reading, and its count is the corner's area. It gives #410's owed theorem a case with all its hypotheses
stated (characteristic data, edge modes, a clock bound), which a Lean statement can take as its first target.

## 5. What follows for her, with weights

**5.1 The joined stretches stopped where the paper says they would (0.65).** The arm made consecutive stretches one region; the
paper's §5.4 says one region and two regions glued with their corner data are the same state, so the region's shape is not the lever
and a one-time step that does not compound is what changing it should give (§19 of November 24: 0.600 against 0.508 at two laps, as
at one). The lever is the cut's capacity: in the paper what crosses is the corner's hairs, as many as the rays through it, each with
its own frame. Her cut carries five stores (`store.cut-read-horizon-thirty-places`: they bring back 3% of 40 nats), a corner of
almost no area, and everything else crosses as sites heard one by one. The direction is more charged hairs at the cut, each with its
own frame, founded where what crosses concentrates (0.4 that a build of that kind moves the cut's cost where joining did not). It
waits on the lead's order and the rule of an arm beside its control.

**5.2 The count needs both members of the pair (0.45).** Her face reads a ring's plane along one fitted direction, and the second
axis's weight stands at zero because nothing was audible there for a comparison to fit (November 24 §14). The paper founds every
canonical pair on both members at once, a center and a width for each. On a ring the second member is no new datum: a ring's turn
makes its plane read along the first direction a quarter of its period later equal, up to its fade over that quarter, to its plane
read now along that direction turned a quarter turn back. So the second axis can be founded as the first one's quarter-turn image, with the fitted weight, rather than at
zero. Guess fixed here, for the lead to read or refuse: 0.45 that, on W121's mean and the held rows at `P1` from 3 to 14, the ring
of 16 read on its fitted direction and that direction's quarter-turn image together reads letters since the last break as one
monotone phase through a whole turn of her clock, where the one-axis read shows the edge at six letters. A miss is scored in one line.

**5.3 Her rate is her count's logarithm (0.35).** By 4.1 a store whose rate is displaced by what crossed it holds a count as the
logarithm of the ratio of its present rate to its founding rate. Her rings hold their fades as her own state (November 24); the
read that would move this is the change of a ring's fade over a held passage against the count of breaks that passage holds.

**5.4 What a founding could trigger on (0.3).** Where a congruence focuses the description fails, and the paper covers the point
with a new diamond whose cones are regular there. Her levels' sites are the landmarks of their news (`code.site-isolation-landmark`),
the places where navigator paths converge; the paper's trigger is the area's growth `p e^(−Ξ)` falling toward zero. A member founded
by her own law would be founded where a store's shape has spent its action, not by a command of ours.

## 6. What changes in the theory

- The horizon row's count clause stands on derived rows now (`gr.bounded-clock-finite-diamond`, `gr.marginal-surface-entropy-half-turns`);
  the correspondence itself stays an interpretation, its first derivation target returned.
- Seven atlas rows (below) carry the paper's results with their owner here, and the existing rows they join point to them.
- #410's relative completeness gets its first physical case (4.8).

## 7. What is not claimed

The paper's magnitudes (the Planck area, the coefficients `257/302` and `106/45`) are not her quantities, and no part of her is
designed from Einstein's equations. The identifications of §3 to §5 are charts: her passage has one dimension along it and her
transverse directions are her stores and rings, so which of her quantities is a corner's area is a reading the lead would have to
make before any build, and the prologue's result (a one-dimensional strand whose clock bound does not bound its content) may be the
closer chart for a single ring.

## 8. Atlas, receipts and sources

Atlas rows added: `gr.null-clock-shear-delay`, `gr.corner-hairs-relative-boost`, `gr.bounded-clock-finite-diamond`,
`gr.pair-amplitude-winding-carry`, `gr.marginal-surface-entropy-half-turns`, `gr.handle-adds-no-state` (physics) and
`aeon.winding-over-cumulative-clock` (objects); `gr.horizon-relative-completeness` gains this record as an owner and `uses` of the
two derived rows.

Receipts: `receipts/2026-11-26_null_cone/pair_phase.py` and `PAIR_PHASE.txt` (host floats, a ruler's).

Sources read this hour: the paper, whole; the atlas rows named in §2 and their records; CLAUDE.md. From training and not restated:
the Bernoulli series `Σ cos(kθ)/k² = π²/6 − πθ/2 + θ²/4` on `[0, 2π]` and the Clausen function's expansion near zero; the Fisher
metric of a centred Gaussian, `½ tr((Σ⁻¹ dΣ)²)`.
