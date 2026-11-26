# A world-horizon is the corner where a reader's outgoing cone meets its return: its hairs are the corner's frames, news delays its clock so a bounded clock bounds its count, and a divergence is a winding read without its carry

November 26, 2026, 08:47 to 09:16 UTC, a thread of the project, in a cloud container (no card, no engine read). Refs #404, #410,
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

## 8. Two parts specified for the lead (09:07 to 09:16 UTC)

The lead took §5.2 and §5.3 as host reads on W121's mean, and asked for §5.1 and §5.4 as parts stated on the objects: state, law,
covector, founding locus and card. No ruler for §5.2 was written here; the lead writes it from `read-reach`'s codes. Both parts below
are `agent-inferred` from the paper and the engine's source as it stands at `721e2d0`, and each is read by a host ruler before it is
built (CLAUDE.md, a premise is a presence at the consumer).

### 8.1 The class hairs (§5.1)

**Which store a hair is.** One hair stands for each head `h` and each of the head's classes `c`: the 81 classes the contact already
reads (`Declaration::class_trits`, four trits at the reach of 3,771). A class is the cone sector of each of the head's first four
modes, the sky plate, the ground plate or the bridge across the mode's light cone `|Re| = |Im|` (`shell`). That is the paper's
corner in the engine's own geometry: a ray through the corner is labelled by where it crosses each mode's null cone. The hair holds
the octave crowd's law (`Crowd`, `lock`), read over a class instead of an octave of distance. It has a mass `M`, the summed framed
key word `K` and the summed framed value word `V`, each word `2n` reals. That makes 324 hairs of 33 words each, 10,692 words in all
at the face's grain. The masses differ from hair to hair, as the paper's `K(y)` differs from ray to ray.

**Its own frame.** Each source enters in its own place's frame (`k̃_j = U_j ⊙ k_j`, `ṽ_j = U_j ⊙ v_j`, `frame_placed`), and a receiver
reads the hair through its own frame (`conj(U_i)`). Only the relative turn reaches the receiver, which is the paper's gluing law: a
common boost carries no charge. On a turned head the hair's phase is the place of its class's sources on that head's rings, so the
hair tells the receiver when its class last stood, as a residue on each period. On a still head the hair is blind to place.

**Its law: the one move's step** (THE_ENGINE §2). At a definite site `j` of class `c` on head `h`, after each tick:

```text
(M, K, V)_hc ← (γ_j M + 1,  γ_j K + k̃_j,  γ_j V + ṽ_j)
```

At every other site the hair is carried by `γ_j` alone. The fade runs on the clock of news, `γ_j = 2^(−φ_h c_j)`. Here `c_j` is the
site's news, the code of its class at its opening face (`level_news`), read as a gate, as the level reads it. `φ_h` is the head's
fade a bit of news, a learner's state on the log chart, as her rings' fades are (November 24). The product is
`2^(−φ_h (S_i − S_j))` over the news between source and receiver (`code.site-isolation-landmark`'s `S`). So a hair forgets by the
news that has crossed since it was charged and never by the places, and through a run the field predicts it holds. This is §4.1's
law for a store. Its quality is finite wherever `φ_h > 0` (`store.finite-quality`).

**Its read.** Each receiver's row gains one entry for each class it probes: its own class's neighbours across its seams (`probes`),
about two runs a receiver at `band_bits`. Each entry is scored by `lock(a, K/M, M, skin)` as a crowd is, with its mass as its
multiplier, and its value is `V/M`. Its share of the row is decided by the lock against the receiver's own probe. No pointer to a
symbol is returned.

**What crosses.** Inside a region the hairs repeat what sharp hearing and the address already carry: a mode dependent at the receiver,
which §6 of November 25 shows the deposit leaves alone. A hair earns at the cut. For each slice, the hairs at the end of its region
in one section are the hairs at its region's first place in the next section, carried by `2^(−φ_h ΔS)` over the news between them.
This is the paper's corner data, handed across. It is a slow variable carried on the host, read at the section's crossing and
joined at the next (CLAUDE.md, the host as a second surface), so a section's regions still commute. Its covector stops at the
carried state: the operands that charged it belong to the deposit before, and the retention law reads it through the present
constitution and returns its residual. The slice's 10,692 words go in the pass line beside its cursor.

**Its covector.** At the read, the row's return reaches the hair's `K/M` through the lock and its `V/M` through the value. A hair
charged inside the region passes that return to every source that charged it, `∂(K, V)_hc/∂(k̃_j, ṽ_j) = 2^(−φ_h (S_i − S_j))`: a
suffix sum over the class's list, reversed as the crowds' prefix sums are. The fade's covector is
`δφ_h = −ln 2 · Σ_(i, j) (S_i − S_j) 2^(−φ_h (S_i − S_j)) ⟨δ(K, V), (k̃_j, ṽ_j)⟩`, deposited on the rings' log chart. The news is a
gate, and no return reaches it.

**Its founding.** All 81 classes of each head are founded at once: the paper's corner has a hair on every ray, and the masses make
them unequal, so no threshold is set. `φ_h` is founded at the fade of the ring of 16 that she holds, divided by the mean news a
place over the founding section. At its founding a hair then fades as her ring does on average, and the deposit moves it from
there; the founding number is read and not picked. A region with no past, or a hair of zero mass, adds no entry. So with every hair
empty the forward is today's bit for bit, and that is the twin test.

**On the card.** The contact already sorts each head's definite sites into class lists by one stable counting sort (`ClassLists`).
Inside a region a hair is that class list's prefix in the one move's compose, `(γ₂ γ₁, γ₂ m₁ + m₂, γ₂ j₁ + j₂)`. The compose is
associative for every `γ`, so the scan is cut into blocks as the carry circles' is (`field_pair_scan`). Its terms meet at the face's
grain and are released once at the read. The read is one more source in the contact's row, whose kernels already score a crowd's
count in its own exponent (`field_contact_l*`). The return is the suffix scan and the contact's own row return. The carried hairs go
up with the region at its upload: 324 × 33 words a slice.

**Read before it is built (guess fixed, 0.5).** Add a ruler bit 512 to `ruler_cut`: every receiver past the cut hears the hairs of
the sites before it, at `φ = 0`. The read is on W121's mean, the 100 held rows, cut at 256. Guess: beside the five stores
(`cut:256:543` against `cut:256:31`), the hairs bring back at least half of what hearing by address brings beside them
(`cut:256:63` against `cut:256:31`). Second guess (0.35): hairs and address together (`cut:256:575`) bring back at least 0.005
nats a place more than address alone. Either guess fails if the class's mean word blurs what one-by-one hearing finds. Then a hair
founded at 81 classes is too coarse, and 8.2 is how a hair grows finer.

**The arm, once built.** The arm (W-h) runs beside the plain control from the same saved state, with one change: the hairs and
their carried state. It is read at both means, with the cut ruler at the line's mask, the panel and the loudness (the lap
procedure).

### 8.2 Founding at focusing (§5.4)

**Which store's action.** The hair's. It carries one moment more, its spread `P = Σ γ… |ṽ_j|²` (one real), so it holds a second
moment of what crossed it beside the first, as the deposit does. Its action is

```text
Ξ_hc = ln(M P / |V|²) ≥ 0
```

`Ξ_hc ≥ 0` by Cauchy–Schwarz, and it is zero only where every source the hair holds carried one framed value word. `e^(−Ξ)` is the
hair's coherent share, the area its charge still spans, and `Ξ` is the paper's shear action read on a store.

**Measured how.** The read is the hair's expansion over a lap, `θ_hc = Δ ln |V|² / Δ ln M`, at the lap's crossing. `θ = 2` is an
aligned congruence, whose coherent power grows as its mass squared. `θ = 1` is unrelated sources, whose power grows as their count.
`θ < 1` means the sources cancel: the area's growth `p e^(−Ξ)` has fallen toward zero, and the congruence through that class has
focused. The bound 1 is the law's: what unrelated sources give.

**Founds which member.** A hair with `θ_hc ≤ 1` over a lap, and with the covector reaching it non-zero on the held half, is covered
by its three children: the class refined by the next mode's shell (trit five of the source's key; the head has eight modes). This
is the paper's new diamond whose cones are regular at the focal point. The founding is decided by code length
(`contact.tension-founds-face`). The children's share of the hair's covector power, `Σ_k |δV_k|²/M_k − |δV|²/M` on the held half,
must exceed the description of their founded words. That description is `½ log₂` of each child's count a word, the code length
that refuses a chance correlation. The parent stays beside its children. A source charges the deepest founded hair whose trits its
key word matches, and a receiver reads the deepest its probes reach. Each head's hairs are then a tree of trits: the class address
refined where the tension asks, never where items were seen. It grows only by this law.

**On the card.** The split is a host step at the lap's crossing, a founding, at the grain of the learner's clock. On the card each
source's class word is read at the founded depth: the counting sort keys on the founded node's index in place of the class. The
kernels are the same.

**The failures these could repeat, and what differs.**
- *The binding bank of October 26* was a key, query and value store: 64 slots written by the delta rule, opened as an induction
  copier and accepted on a lookup benchmark. A hair brings no new key, query or value map. It holds the head's own framed words over
  the contact's own class address, is charged additively by the one move and never overwritten, fades by news, and opens empty. Its
  acceptance is the cut's cost and her writes. By the store test it obeys a balance (arrival, and a fade by news), it is read by the
  contact's own flux, and its size is fixed by founding, never by the items seen.
- *The passage tree* held decayed counts by exact byte context and returned the class that followed the deepest match. A hair is
  addressed by the cone sectors of key modes that the deposit moves, and it enters a row by its lock against the receiver's own
  probe. It holds a mean word, not a successor.
- *A width as a dial.* The 81 classes are the contact's own, and the children are founded by 8.2's law.
- *A switch outside the law.* The hairs are a declaration word with their state carried in the learner.

Weights. 0.5 and 0.35 on the two guesses of 8.1. 0.4, as in §5.1, that a built arm moves the cut's cost where joining did not. 0.3
that founding at focusing founds children on her line within a lap of the hairs' arm, at the trits where recurrence stands
(`store.far-price-stands-at-recurrence`).

### 8.3 Scored on the lead's reads (09:42 UTC)

The lead read W121's mean on the 100 held rows, cut at 256 (its numbers, nats a place past the cut against the law):

- Hearing by address brings back 0.088 nats a place.
- Hairs at `φ = 0`, unweighed, cost +0.586.
- Hairs weighed at the law's own falloff bring back nothing (+0.005).
- Hairs beside address cost +0.054.

The scores:

- §8.1's first guess (0.5): missed.
- §8.1's second guess (0.35): missed. The hairs cost 0.054 beside address.
- §5.2 (0.45): missed on its premise. The face already reads the ring of 16 on two axes, the second at two thirds of the first's weight.
  The premise was taken from a sentence of November 24's §14 and never read at the face's owner, which the synthesis rule bars for a
  guess on a built part.

What it says of the law. §4.3 holds, and the read sharpens how it is charted on the engine. A corner's capacity counts its
distinguishable rays, one hair a ray, each carrying its own shape `q̄(y)`. My hair took a class's count as its area share and gave it
one mean word. That makes a corner with the area of many rays and the content of one, and when unweighed it took the row's share
from the sites that carry. Three reads of one cut now agree:

| What crosses | Share of the cut's cost it carries |
|---|---|
| Stores | 3% |
| Octave crowds | 8% |
| Class means | 0% or less |
| Rays heard one by one | the rest |

On the gravity, `§4.3` stays at 0.75. On her, the reading that what carries a cut is distinguishable rays goes to 0.8.

What it says of §8. §8.1 as specified is retired as a part. A class mean pays at the cut with weight 0.1. §8.2 turns over. A class
of unrelated sources is focused from its founding (`θ ≈ 1`), so the split law would cut every class down to its sites, which is
hearing by address. The corner is compressed the other way: it starts from its rays and merges where they agree, which is where
navigator paths converge. Agreeing rays are where the far price stands, at the runs that recur (`store.far-price-stands-at-recurrence`):
the sites of a recurring run carry one word.

The read that would move this: hearing by address, with a class's sites replaced by their mean only where the class's coherent
share stands above what unrelated sources give (`|V|² > P`, so `e^(−Ξ) > 1/M`), and heard one by one elsewhere. 0.35 that it
brings back at least 0.8 of address's 0.088 on fewer than half its pairs. §5.1's "more charged hairs" falls from 0.4 to 0.2. The
lever left after joining is sharp rays across a stretch's first place (the ruler's bit 64), paid in pairs. The weight that the
joined arm stalled for the paper's reason stays at 0.65.

## 9. Atlas, receipts and sources

Atlas rows added: `gr.null-clock-shear-delay`, `gr.corner-hairs-relative-boost`, `gr.bounded-clock-finite-diamond`,
`gr.pair-amplitude-winding-carry`, `gr.marginal-surface-entropy-half-turns`, `gr.handle-adds-no-state` (physics) and
`aeon.winding-over-cumulative-clock` (objects); `gr.horizon-relative-completeness` gains this record as an owner and `uses` of the
two derived rows.

Receipts: `receipts/2026-11-26_null_cone/pair_phase.py` and `PAIR_PHASE.txt` (host floats, a ruler's).

Sources read this hour: the paper, whole; the atlas rows named in §2 and their records; CLAUDE.md. From training and not restated:
the Bernoulli series `Σ cos(kθ)/k² = π²/6 − πθ/2 + θ²/4` on `[0, 2π]` and the Clausen function's expansion near zero; the Fisher
metric of a centred Gaussian, `½ tr((Σ⁻¹ dΣ)²)`.
