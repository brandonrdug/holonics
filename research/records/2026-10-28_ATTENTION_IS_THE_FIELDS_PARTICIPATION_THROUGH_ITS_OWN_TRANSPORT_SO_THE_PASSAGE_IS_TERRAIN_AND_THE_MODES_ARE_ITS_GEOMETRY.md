# Attention is the field's participation through its own transport, so the passage is terrain and the modes are its geometry

Refs #404 #405 #406 #73 #410. Status: [design fixed before the build; agent-inferred, October 28].
Claude (opus), on Brandon's direction of October 27–28. Owners it joins:
[HNN_FORMULA §2, "One connected tensor computation"](../../docs/HNN_FORMULA.md#one-connected-tensor-computation);
atlas `resolvent.attention-chart`, `resolvent.attention-variation`, `norm.attention-gibbs`,
`norm.attention-class-exact`, `norm.mass-current-associative`, `pair.unit-phase-score-chart`;
Lean `Computation/HolonicArchitectureCharts` (`weight_normalized`, `complete_output_relabel`),
`Computation/AttentionModeCompression` (`normalized_attention_exact`,
`weighted_summary_associative`, `score_face_eq_posterior`, `attention_free_energy_minimum`),
`Computation/HolonicAdjointNormalization` (`face_add_common`, `laplacianReturn`); the tower's modes,
gates and turns (`holonics::hnn::tower`, `holonics_cuda::hnn::tower`, `kernels/tower.cu`).

## 1. What Brandon asked

Paraphrased; his words stay in the conversations.
- **October 27, the playground thread.** Forcing the input in as bytes streamed one after another is
  likely a conceptual failure that will not train. The I/O's knot and friction, its toroidal and
  helical interactions, must be settled first. The machine's learning shapes how it flows into the
  terrain it goes on learning from. His image: a fish that could swim the whole tank, held instead
  in a hamster ball on strings and moved about by hand. The agent answered that the main Athena
  learner does read GSM8K that way, one ordered class at a time, and paused.
- **October 28.** "Attention Is All You Need" is literal: a machine has to be oriented along dynamic
  geometry, the manifolds the formal mathematics is for. The same failure runs through Athena and the
  holonic-inference work. The recurring defects are narrowing, the hardware policy and
  misconceptions about what the architecture is expected to be.
- **October 26** (the stores record): the machine addresses by geometry, its own phases, windings and
  locks, and the information evolves by its own dynamics, a fluid's; a key/value memory is how
  computer science addresses, not learning. **October 26** also: a computational flock, many local
  interactions integrating into global fields.

## 2. The learner now, read against it

[source-inspected] `hnn::tower` is a selective state-space tower. At a level, with `T_ij` the
product of the mode moves between sites `j` and `i`,

```text
h_t = λ_t ⊙ h_(t−1) + γ_t ⊙ B x_t      ⇔      h_i = Σ_(j≤i) T_ij ⊙ (γ_j B x_j),   T_ij = Π_(t=j+1..i) λ_t
```

Every earlier site enters with participation one, weighed only by the transport's decay. No site is
read by its relation to the present one, and the passage goes through once in octet order. That is
the hamster ball: the learner is moved along the passage, and what it can reach of an earlier site is
what survived `|T_ij|` in 128 modes a level.

[source-inspected] The October 27 review wrote "The tower has no attention, by law: the HNN keeps no
key/value store." That reading is wrong, and it is the misconception Brandon names. The October 26
law refuses a **store**: slots written and later looked up by a symbolic key (the binding bank's
delta-rule grid, the reset clock's copy pointer, the passage tree's context index). It does not
refuse the participation of the field's sites through the field's own transport, which HNN_FORMULA's
connected computation states as the field's operation and five formal-checked atlas rows own. The
drift ran in three steps: October 23 a selective recurrence was chosen in its place; October 26 the
stores were refused, correctly; October 27 the refusal was read as a refusal of attention. §9 repairs
the guides so the step is not taken again.

[measured, in the records] The failures the tower reports are the ones a reading of sites by their
relation addresses, and none is claimed fixed here: no answer follows the question's subject (John,
"usually more than one section back"); the role is read in 53, then 43, of 97; the plain race writes
locally fluent babble at 1.850 bits a class held out after 45 laps on the card.

## 3. The law: participation through the modes' transport

[definition; agent-inferred] At a level, sites `i` are its arrivals on its own clock (the octet at
level 0; a level's own ticks under the news clock). Write the transport between two sites in its two
parts, the boost and the turn of the Swing:

```text
T_ij,m = 2^(−D_ij,m) e^(iΘ_ij,m),      D_ij,m = Σ_(t=j+1..i) −log₂|λ_t,m| ≥ 0,     Θ_ij,m = Σ_(t=j+1..i) arg λ_t,m   (lifted: windings + phase)
```

`D` is the dissipation the transport has met between the sites, `Θ` the phase it has carried. Both
are the modes' own, keyed by the passage through the gates and turns: this is the field's dynamic
geometry, and elapsed time between sites is the receiver's pairing `⟨ω_R|γ⟩ = windings + phase`,
never the codec's index.

**Heads are rungs.** A head `h` is one rung of the founded turn ladder: its modes share one memory
`|λ| = 1 − 2^(−s_h)` and turn at the rung's `J` turns. Each head reads the passage at its rung's scale
with its rung's turns.

**The pairing.** The present site probes with its coholon chart, each earlier site presents its Holon
chart, and the face is their pairing through the transport's turn (the pair receiver's phase
comparison, `pair.unit-phase-score-chart`, with the modes' connection):

```text
⟨Ȟ_i| = W_Ȟ x_i,   |H_j⟩ = W_H x_j,   |Ψ_j⟩ = W_Ψ x_j            (complex, on the head's modes)
s_ij = β_h Re Σ_(m∈h) conj(Ȟ_i,m) e^(iΘ_ij,m) H_j,m
```

**Friction.** The contact dissipates as it slips along the passage: `z_ij = s_ij − κ_h D̄_ij`, with
`D̄_ij` the head's mean dissipation and `κ_h ≥ 0` the head's learned friction (opening at 1, so a head
first forgets as its rung does).

**Participation is the Gibbs face** (`norm.attention-gibbs`), over the admitted sites `E(i)`, carried
as the associative (mass, current) pair (`norm.mass-current-associative`), with the common origin a
gauge (`face_add_common`):

```text
m_i = Σ_(j∈E(i)) 2^(z_ij),     J_i = Σ_(j∈E(i)) 2^(z_ij) e^(iΘ_ij) Ψ_j,     y_i = J_i / m_i = Σ_j a_ij e^(iΘ_ij) Ψ_j
```

The current is carried through the same turn that paired it (HNN_FORMULA's `U_hij`), so a rotation of
every site's frame leaves every face, weight and current unchanged: only relative phase is read.

**The join.** The participating current is read like the modes' face and offered to the same
contacts, `r̂ᵃ_i = Re(Cᵃ y_i)/‖·‖_rms`, `v_i = max(W₁ r̂_i + W₁ᵃ r̂ᵃ_i + b₁, 0)`. `W₁ᵃ` opens at zero
and `W_Ȟ`, `W_H`, `W_Ψ`, `Cᵃ` open founded as the push and read are, so the opening is the plain
tower face for face and the first deposit reaches `W₁ᵃ`.

**The reach is released, never authored.** A site whose friction puts `2^(z)` below the mass's grain
is released by partition at that tolerance with its remainder bounded, so how far a head reads is
set by its learned friction and its rung's gates. No window is declared.

**What the tower already was.** Participation one and the full complex transport in the current
give back `h_i = Σ_j T_ij Ψ_j` (with `Ψ = γ B x`): the tower is this law's participation-one
restriction (the state-space duality of Dao and Gu, "Transformers are SSMs", 2024 [external,
cited]). With constant moves the law is a fixed-geometry Transformer: `Θ = ω(i − j)` is rotary
position (Su et al., RoFormer, 2021) and `κ D = κ'(i − j)` is a linear distance penalty (Press et al.,
ALiBi, 2021); with gated moduli it is the Forgetting Transformer (Lin et al., 2025); with turned
phases its positions count what the content makes count (Golovneva et al., "Contextual Position
Encoding", 2024) [all external, cited]. One object holds the recurrence and the Transformer as
restrictions; Athena's law is the one whose geometry is learned.

## 4. Why this addresses by geometry and is not a store

- **Nothing is written to be looked up.** There are no slots and no symbolic key. Every admitted site
  participates by its Gibbs weight, recomputed from the present field at every tick.
- **The address is the transport.** Which site a head reads is set by the relative turn and the
  dissipation of the machine's own modes, its phases, windings and locks, and by the alignment of two
  orientations of the same field. The charts are a coholon's frame and a Holon's frame on one site's
  current; their pairing is a face (orientation exists only in the pairing). Lesson 4 asks whether
  there should be keys at all: there are none here.
- **The sites are terrain, not retention.** They are the passage present to the navigator in its
  aeon (the tank). What persists is only what deposition changes in the constitution; the sites'
  charts are never kept as a record of the passage.
- **The information evolves as a fluid.** On the sphere the contacts' ratio read already places the
  face on, composed participation is a continuity equation for the sites' distribution,
  `∂_τ μ + ∇·(μ X[μ]) = 0`, `X[μ](x) = P⊥_x ∫ 2^(z(x,y)) U(x,y) Ψ(y) dμ(y) / ∫ 2^(z(x,y)) dμ(y)`
  (Geshkovski, Letrouit, Polyanskiy and Rigollet, "A mathematical perspective on Transformers",
  2023 [external, cited]). On the circle with identity charts it reads
  `θ̇_i = Σ_j w_ij sin(θ_j − θ_i)`, `w_ij ∝ 2^(β cos(θ_j − θ_i))`: Kuramoto synchronization, sites
  aligning with the sites they participate with. That is the computational flock: local pairings
  integrating into a global orientation, rings rotating and aligning.

## 5. The I/O: the passage is a strand, the heads are contacts that slip and lock on it

- The passage lands as sites on a helix, circle and carry, on the level's own clock. The machine is
  not dragged along it: in one tick every site reaches every admitted earlier site of its aeon
  through the participation. The fish swims the tank; the modes still carry the quotient past it.
- Each head is a helical pair contact between the present site's frame and the strand. Where the
  alignment closes against the relative turn the contact locks and the participation concentrates
  (the head's loop closes through that site: the knot); elsewhere it slips, and the friction `κ_h`
  dissipates its participation along the span it slips over.
- The learning shapes the reading. `Θ` and `D` come from the learned moves and gates, so what the
  machine has learned sets the geometry through which it reads what comes next. A release lands as a
  site on the same strand and is read back by the same participation, so its output flows into the
  terrain it learns from.
- Nothing is modality-specific. Octets, pen strokes and speech half-cycles are sites of one passage
  (the October 25 listener). On a two-dimensional chart the transport becomes path dependent and its
  holonomy around a cell is curvature (the winding guide's fourth object); that is where the
  geometry stops being flat, and the image chart's next law.

## 6. The card realization

[proved-derived; agent-inferred, October 29] **The transport factors through each site's own frame.**
With `U_t,m = Π_(k≤t) u_k,m` the running product of a mode's unit moves from the section's opening
(`u_t = λ_t/|λ_t|`, the `unit` the gated and turned moves already carry) and
`L_t,m = Σ_(k≤t) −log₂|λ_k,m|` (the `logs` they already carry), `e^(iΘ_ij,m) = U_i,m conj(U_j,m)` and
`D_ij,m = L_i,m − L_j,m`. Rotating each site's charts back by its own frame,
`q_i = conj(U_i) ⊙ Ȟ_i`, `k_j = conj(U_j) ⊙ H_j`, `w_j = conj(U_j) ⊙ Ψ_j`, gives

```text
s_ij = β_h Re⟨q_i, k_j⟩_h,      z_ij = s_ij − κ_h (L̄_i − L̄_j),      y_i = U_i ⊙ Σ_j a_ij w_j
```

so no arctangent and no winding enters the face (the winding stays in the lifted `Θ` for its own
readings), every pairing is one complex inner product of two rotated charts, and the card's tiles
are the online Gibbs reduction over them. On a pumped mode the move is real-linear, not a phase:
the first build reads its turn part `α_t/|α_t|` and names the reflection's share as owed (§8).

[definition; agent-inferred] On the RTX 4080 SUPER under `.local/gpu.lock`, beside the tower's
forward and reverse in `kernels/tower.cu`:
- per stream, level and head, the scores of a site against its admitted sites in tiles, the online
  normalization being the (mass, current) pair with the row's running maximum as the gauge
  (Milakov and Gimelshein 2018; Dao et al., FlashAttention, 2022 [external, cited]);
- exact integers throughout: charts and faces on `2^(−16)`, each site's phasor `e^(iΘ)` composed from
  the dyadic turn ladder and released to the face's grain, products summed in `i64` and widened to
  `i128` where `narrow_terms` refuses, `2^(z)` from the face's exponential navigator, the mass and
  current summed as integers, so any partition of the card gives the same bits;
- the reverse through the Laplacian return `J = diag(a) − a aᵀ` (`resolvent.attention-variation`),
  the participation recomputed from the forward's operands rather than stored.

The first law stops the covector at `Θ` and `D`: the participation reads the modes' geometry and the
geometry learns through the modes' own path. The transport term `Σ a dU Ψ` of the complete variation
is owed, and named in §8.

## 7. Acceptance, fixed before the build

1. **Host law.** (a) Opened as declared (`W₁ᵃ = 0`), the participating tower is the plain tower face
   for face, covector entry for covector entry and learner for learner. (b) The covector matches the
   code difference it predicts on a small tower, two levels gated (the pattern of the news clock's
   test). (c) A common phase rotation of every site, and a common origin added to every `z`, leave
   every face and weight unchanged exactly. (d) Relabeling the admitted sites with their transport
   leaves the current unchanged (`complete_output_relabel`).
2. **Card.** Parity at the race's declaration (width 64, 128 modes, 256 contacts, four levels,
   sections of 128 classes) on the race passage: 32 sections at 24 streams and 4 at 320, every face,
   covector entry, learner and state equal, host against card.
3. **The measurement.** The race's passage, keys and declaration with participation, lap for lap
   beside the plain race (lap 45: 1.691 training, 1.850 held out, GSM8K 1.800, prose 1.888): bits by
   region, the writings whole, and the participation read at each named answer's opening (whether
   the answer's opening participates with the question's subject). Nothing is claimed before it runs;
   bits decide nothing beside the writings.
4. **Lean** (into #410): the participation through the modes' transport is gauge-free (it depends on
   the moves between `j` and `i` only); its participation-one restriction is the tower's recurrence;
   the head's Gibbs face is the posterior of its frictioned faces.

**Status, October 29 (host).** 1(a) passes for the rectifying and pair contacts: the joined tower
opens on the plain tower face for face, covector entry for covector entry on every shared family, and
learner for learner with participation's families held; before `W₁ᵃ` opens only `W₁ᵃ` carries a
covector. 1(b) passes for every participation family the tiny tower reads above 1/64 bit a unit
(charts of each kind, the current's read, `W₁ᵃ` on each level, the friction), within a tenth of the
code's fitted slope. 1(c) and 1(d) pass in `hnn::tower::participation`, with the participation-one
restriction (`m_i y_i` is the head's recurrence). The tower and its learner restore exactly.

**Status, October 29 (card).** 2 passes on the RTX 4080 SUPER at the fixtures' declaration (width 8,
8 modes, 16 contacts, two levels, the two-ladder founding): 32 sections at three streams equal face
for face, covector entry for covector entry, receipt for receipt, learner for learner and state for
state; the pair contact with every other place uncompared; turned modes with strands on the pair
contact; and a read that ends inside its section carries the open section's sites as the host's
state does (`holonics-cuda/tests/tower_pass.rs`, 31 of 31 with the suite). The kernels: the forward
admits each cell's site and reads every admitted site head by head (`tower_forward`), the contacts
return `W₁ᵃ` and the current's read (`tower_reverse_contacts`), one block a stream returns the Gibbs
face into the probe, keys, currents and friction (`tower_reverse_participation`), the input takes the
six charts' covectors (`tower_reverse_dx`), the outer sums take the charts', `W₁ᵃ`'s and `Cᵃ`'s, and
`tower_pa_friction` sums the heads' friction. The section closes with its last site, which releases
the sites and rests the frames, on the host and the card alike.

**Status, October 29 (design thread, built, not yet run on the card).** The card reads on from a
section carried open across calls, as a release does: each stream's open sites are uploaded at their
places in the section with its running frame and met dissipation, the forward resumes from them, a
read past the section's close and the reverse of a read that opened on carried sites are refused;
`the_cards_participation_reads_an_open_section_on_across_calls_as_the_host_does` and
`the_cards_participating_advance_is_the_hosts_class_by_class` are its acceptance. The race joins
participation through `train-two-ladder-participating-tower-classes` (host and card) and
`tower_pass parity … participating`, its heads founded by `Tower::founded_participation`: one head a
run of first-level modes whose memory sits at one octave. Read off the exact moduli, the turn's
rounding split the race bank's sixteen rungs of eight into 90 runs (`hnn::tower` test
`the_founded_heads_are_the_first_levels_rungs`). Owed: those two card tests and the parity at the
race's own declaration. Nothing is measured (3).

**The device line.** The card under the lock for every learner run; the host realization only as the
parity reference. The workload is the race's (its passage, keys, declaration and laps); time and
memory are projected from a one-to-three-minute read on the card before launch, never by cutting it.

## 8. What the first build leaves, by name

- **The section.** The first build admits the sites of the present section (128 classes), so that the
  race comparison changes one thing. The referent "usually more than one section back" is out of a
  level-0 head's reach in it; the next loop admits the stream's earlier sites as present terrain
  (their charts carried as the modes' state is carried) or makes the section the passage's own
  partition (the review's fix 2). Named here so it is not carried unrepaired.
- **The transport's covector.** `Σ a dU Ψ` through `Θ` and `D` into the gates and turns.
- **Curvature.** The path-dependent transport of a two-dimensional chart.
- **The pump's reflection.** On a pumped mode the transport `α h + β conj(h)` is real-linear; the
  first build pairs through its turn part only.

## 9. The guides repaired with this record

- CLAUDE.md and AGENTS.md, "Keys and navigation": participation through the field's own transport is
  not a key/value store; the refusal applies to stores.
- THE_MACHINE, the computational unit: attention as the field's participation through its transport,
  with the tower as its participation-one restriction.
- The October 27 review's sentence is marked as superseded by this record.

## 10. The recorded failures this design could repeat

- **Recitation, or an index of contexts** (lesson 4): no store, no slots, no symbolic key, nothing
  written and looked up; the address is the transport; no lookup benchmark is an acceptance.
- **An authored routine**: no rule is written; the geometry is the modes'; no window is declared.
- **Text on its codec's grain**: one law for every chart; the measurement reads every region.
- **An uncertified deposition step**: the certificate rereads the section with its participation.
- **A design thought in the programming language**: stated as transport, pairing, Gibbs face, mass
  and current; the tiles follow.
- **Bits read as progress**: the writings and the participation at the answers are shown beside them.
- **The latest phrasing narrowing the work** (failure 14): the measurement is the whole race passage,
  not the equals; arithmetic is one region of it.
- **The card**: the part enters a learner run only with its card realization and parity.
