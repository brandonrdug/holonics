# A provisional founding is a revisable first key, and its constituents merge by a square and split only where the finer face was kept

**Date.** October 9. **Issues.** #73, #386, #62, #148, #63. **Grade.** Lens record. Each claim
carries its own grade. Why a kickstart is needed is standard, and the repository's tests assert it
(read here, not run); what is founded and what moves was read from the source; the merge square, the
split fibre, the equivariant founding and the counts were derived here and checked by exact rational
computation; the joins are owed.

## 1. The lens

Brandon, October 8, asking without presuming the answer: when learning seems to barely move at
first, does that mean the machine needs a push at the outset if it is to learn quickly? Authored
tokenizers such as byte-pair encodings are that push in ordinary machine learning, and there are
past notes on them. The ontology is that correct language cannot be authored: a recording of one
voice is one voice, and others say the same words differently; a reader infers tone, though some
phrasings leave far less room than others. Only deterministic outcomes admit a correct answer to
reinforce, and that is the role he gives the complex Navier–Stokes and Turing ideas. Supplying
starting pieces, as a tokenizer does, is a reasonable way to begin. The mistake would be to treat
those pieces as fixed truths rather than as material that may stay or be dropped: pinning a meaning
so that the machine can never depart from it removes the machine's own say, and he means that as a
mechanical defect, not a moral ornament, since an intelligence that cannot revise its pieces cannot
think for itself. Then he floated, without deciding it, that the agents might carefully author
starting helical codes for language: not a list of common morphemes, but units packaged the way
notes and chords are, able to shift as the system runs, in the manner of the double-helix encoding.

[definition; agent-inferred] **The lens in the objects.** A provisional founding is a declared,
task-neutral first configuration of the machine's own kind (a nonzero port, a frame family of
helices, prior scales, an initial key), offered as the first hypothesis that the machine's own laws
revise: key location revises keys, deposition revises the constitution, and the population revises
families. A founded constituent that no admitted encounter can move is a frozen inventory, not a
kickstart. The plasticity that is owed has an exact shape: a merge of constituents transports the
retained face by a continuation square; a split needs the finer face, which only a kept seed or a
forward founding from later passages supplies.

## 2. Why a kickstart is needed: a chain needs every member but one nonzero

[proved-standard] For a reading `⟨g, R E x⟩` through a chain of two linear maps, the derivatives are
`∂/∂E = Rᵀ g xᵀ` and `∂/∂R = g (E x)ᵀ`. At `R = 0` and `E = 0` both vanish: the all-zero founding is
a stationary point, and no covector reaches either factor. With `R = 0` and `E x ≠ 0`, the covector
reaches `R`; once `R` moves, it reaches `E`. In a longer chain the covector reaching a factor is the
product of all the others, so two zero factors silence every factor, and a founding lets every
factor learn only when at most one factor is zero.

[conditional; source-inspected] The HNN's tests assert exactly this, and it holds of the HNN on
condition that they pass at this revision (they were read here, not run). With `E = 0`, the pair
port at zero and `R = 0`, every covector is zero, and after a compare and its deposit `R` and `E`
are unchanged (`hnn::tests::receiving::the_wave_is_inert_when_every_map_opens_at_zero`). At the
declared founding (`R_0 = 0`, `E_0` the declared sign sequence times ½), `R` moves at the first
deposit and the covector reaches `E` from the second
(`r_opens_at_zero_and_learns_from_the_first_deposit`). The constitution's opening documents the
reason for its own chain: with every map at zero, no covector is carried
(`hnn::constitution::Constitution::initial`).

[proved-derived; formal-checked] A founding with distinct columns also gives a positive receiving
margin before any observation: with decoder rows `(2e_s, −‖e_s‖²)`, the margin is `‖e_t − e_s‖²`
(`Computation/HolonicCultivationCharts.CodecBootstrap.{bootstrap_margin, strict_bootstrap_margin}`,
whose header calls the first source and receiver rows a material prior).

[agent-inferred] **The answer to the open question, in two parts.** A kickstart is necessary for a
chain to learn at all, and it lets receivers separate from the first read. It does not by itself
make a deposit land: an update below half its locus's fine grain is heard and counted, and released
whole, leaving that entry of the constitution unchanged
(`HNN/LatticeDeposit.below_grain_heard_counted_not_deposited`; §10 of the
[objects](../../docs/ELEMENTARY_OBJECTS.md#10-receipt), hearing and listening). Whether a measured
slow start is a founding problem or a landing problem is separated by the comparison of §7 (item 5),
not by assumption.

## 3. What is founded today, and what is allowed to move

[definition; source-inspected] Read from the source on this branch:

| Operand | Founded as | Moves by |
|---|---|---|
| Source port `E` | the declared sign sequence times ½, task-neutral, kept as the normal law's prior `B_0 = E_0` with `H_0 = I` (`hnn::constitution::declared_source_port`) | the learned part `E − E_0`, deposited (`hnn::executed::pair_deposit`); the prior's precision stays `I` while the readings' Gram `Σ w f fᵀ` grows, so evidence dominates it in every direction the readings reach |
| Receiving prior | the ridge `2^k I` at the declared `k` (`hnn::constitution::NormalLaw::prior_scale`) | the located prior moves `k` (`NormalLaw::moved_prior`) |
| A contact's grain | the field's lattice | `Constitution::rebased`, a commit onto a finer lattice |
| Keys | not founded: located | loop closure (`compression::keys::transport::TransportLocation`), up to a dihedral gauge |
| Labels | exterior | free: the located chart reads no labels (`HolonicsResearch/Compression/Relabelling.codeLength_relabel`) |
| Families of receivers | declared seeds | birth from a reached residual (`receiver::population::birth`, `Compression/Landmark/Context/Birth.founding_intertwines`), death, the evolved Dirichlet prior over families (`Compression/Landmark/Context/Evolution.dirichletFace_isPrior`), species collapse and exact split (`Population::{collapse, split}`, `species_split`), priced merges and exact splits of receiver cells (`receiver::population::merge`) |
| Frames: the class count, helix periods, the pairing `σ`, clocks, the founded quotient | declared (`FieldDeclaration`; `CarryHelix` joint periods under `HELIX_PERIOD_CEILING = 2¹²`; a navigator's code ranks at most `LABEL_CEILING = 12` classes; `compression::keys::duplex::Pairing`; `Encoding::found` once per chart) | nothing live: a continuing state restores only onto the same declared material (`Constitution::{material_identity, continued}`, `ContinuingState`); the duplex decoder refuses a changed transport, which needs its own continuation square (`compression::keys::duplex::Decoder::new`) |

[definition; source-inspected] Every founding is governed by laws already written. The record is
pinned and the encoding is not: each re-encoding is a lens in the population that pays its own
description and stays only while it shortens held-out code, and a hand-built transducer is a
catalyst the population may retire (the
[HNN formula](../../docs/HNN_FORMULA.md#the-source-and-release-contract), source contract item 10;
the
[learner record](2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md),
§10). Exterior data waits for its encoding; no chart is founded from a passage's counts or placed at
first arrival; the alphabet fixes nothing ([THE_MACHINE](../../docs/THE_MACHINE.md), guard 9). The
September 29 lessons retired the count-priced founding, first-arrival placement, the founded `E_0`
and pseudo-random signs presented as a keyed latent (§4 of
[that record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)). The
declared `E_0` now in force replaced the founded one: a task-neutral prior declared by the field
alone, never called a key. Tokenizing is the field's own, and a declared family may be a navigator of the machine's own kind
whose keys are located (CLAUDE.md, "No catered machinery").

[definition; agent-inferred] **The lawful kickstart**, read off those laws. A provisional founding
may declare frames (navigator families with their periods and coprimality), a task-neutral nonzero
port or prior, prior scales, and an initial key offered as the first hypothesis on the menu. It may
not declare a class map or meanings for exterior codes, a chart built from counts, or a fixed
vocabulary of the field. Each founded operand needs a lawful path to change (the table), and its
weight must be one the evidence can dominate. The declared `E_0` meets this. The frames do not yet:
nothing live changes them.

## 4. Starting helical codes, like notes and chords

[definition; formal-checked where named] In the helical code a chord is a simultaneous reading of
several frames: receivers of coprime periods `m` and `n` reading one lifted clock meet in exactly
one position per pair of residues within one product period: below `m·n`, equal residues force equal
positions (`HNN/Prediction.joint_residue_determines_position`;
`Geometry/PairResonance.diagonal_step_generates_the_coprime_torus`). Beyond it the residues fix the
lift only modulo `m·n`, and the absolute position needs the whole winding or a declared fundamental
domain. The joint residue is not a sum of marginal faces (`HNN/Prediction.joint_class_not_additive`;
the [guide](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode), part 3).

[proved-standard; computational-witness] **Twelve pitch classes.** `ℤ/12 ≅ ℤ/3 × ℤ/4`: each class is
the meet of its residue mod 3 (which of the three diminished-seventh chords holds it) and its
residue mod 4 (which of the four augmented triads); the map `x ↦ (x mod 3, x mod 4)` is a bijection.
The circle of fifths is the relabelling `x ↦ 7x`, a unit since `7·7 = 49 = 4·12 + 1`, visiting
`0, 7, 2, 9, 4, 11, 6, 1, 8, 3, 10, 5`: the same chart under a relabelling, so a located code length
is unchanged (`Compression/Relabelling.codeLength_relabel`). The duplex already runs a
twelve-pitch-class chart with the tritone pairing `x ↦ x + 6` (the tests of
`compression::keys::duplex`), and the helical record's acceptance includes notes on a pitch helix.

[definition; agent-inferred] **A starting helical code for language** is read the same way. It
declares frames, coprime periods on one lifted clock that give each position a residue chord, and an
initial key; it declares no morphemes and no meanings. Notes and chords that shift as the system
runs are then exact operations: a note's frame stays while its key is located from receipts; a chord
is a joint residue; and changing fluidly is key location revising the configuration, deposition
revising the port, and the population's births, deaths, merges and splits revising the families. The
same frames read text, pitch and amplitude (the duplex's three charts), so nothing here is
language-specific.

[proved-derived] **An equivariant founding for a paired carrier.** A paired carrier needs its source
port to commute with the pairing, `B E = E Σ_σ`, and the founded sign matrix has neither that
equivariance nor its descent (the
[helical record](2026-10-08_THE_HELICAL_CODE_IS_HOW_HOLONS_HOLARCHIES_EPOCHS_AND_AEONS_ENCODE.md),
§5). An equivariant founding is task-neutral and exact: declare one column per `σ`-pair and set the
partner's column by `E_0(σ(a)) = B E_0(a)`. It is consistent because `B² = 1` and `σ² = 1` give
`E_0(a) = B E_0(σ(a)) = B² E_0(a)`. It encodes only the pairing's symmetry. It stays plastic only if
deposition preserves the equivariance, or the paired consumer re-admits it after each deposit and
refuses with the failing column when it breaks.

[proved-standard; formal-checked where named] **Learned pairing.** `σ` is a fixed-point-free
involution, a perfect matching of the letters: on `2n` letters there are `(2n)!/(2ⁿ n!)` of them,
which is `1, 3, 15, 105, 945, 10395` for `2, 4, 6, 8, 10, 12` letters; on four letters the three are
the Klein types (`Transport/HelicalCode.card_free_involutions_fin4`, `helical.klein-four-letters`).
At the letter level a contact slips exactly where a letter was substituted against its intact
partner (`Transport/HelicalCode.slipped_contacts_eq`, `helical.inner-code-slips`). Reading that slip
as zero power through `Transport/HelicalPairInteraction.lock_iff_zero_power` needs the declared
embedding of letters into contact velocities (`v₋ = v₊∘σ`, `v₊` injective), which the guide marks
owed (#62). [agent-inferred] So learning `σ` is key location over that menu by loop closure of
contact receipts: on twelve letters a menu of 10395 matchings pruned by contradictions, instead of a
declared tritone.

## 5. Merge and split: what plasticity can and cannot do

[proved-derived; computational-witness] **A merge transports by a continuation square.** Let
`π: A → A′` merge letters, and let a new chart `(E′, Ĝ′)` satisfy

```text
E′∘π = P∘E,     Ĝ′P = PĜ,     the clock unchanged (on the located route, A′∘π = A)
```

for a linear `P`. Then `m′(π∘u) = P m(u)` for every word, since `Ĝ′⁻¹P = PĜ⁻¹` makes each term
`Ĝ′(τ(k))⁻¹ E′(π(u_k))` equal `P Ĝ(τ(k))⁻¹ E(u_k)`. The retained moment carries over to the merged
chart without re-reading the source. Checked over `ℚ` on a three-dimensional witness, four letters
merged to two by `π = (0, 0, 1, 1)`: `E` has columns `e₁, e₁ + e₃, e₂, e₂ + e₃`, `E′` has columns
`e₁, e₂`, `Ĝ = [[0, −1, 0], [1, 0, 0], [5, 7, 1]]`, `Ĝ′ = [[0, −1], [1, 0]]`, and `P` drops the
third coordinate; the square held on a hundred random words with the uniform tick, and again on the
located route with advances `A = (1, 1, 3, 3)` and `A′ = (1, 3)`.

[counterexample; computational-witness] **A split cannot be read from a merged face.** In the same
witness the one-letter words `0` and `1` have different moments and the same merged moment, so the
merged face fixes only the fibre `P⁻¹(m)` on the reached span.

[definition; source-inspected] This is the retention contract's recoverability: a collapse reopens
for a wider admitted future exactly when what it retained suffices to rebuild every member the wider
future separates (§8 of the [objects](../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract)). The
species collapse keeps every member's seed and splits exactly
(`Compression/Landmark/Context/Evolution.species_split`), and the priced merges keep each member's
counts, so a block splits exactly (`receiver::population::merge`). The field's moment keeps no seed.
A split of a founded class is therefore a forward founding from later passages, with the merged
moment kept on its own chart until an aeon boundary and the fibre held meanwhile.

[historical] **A founding is a path.** Before the reset, two founding orders over one starting panel
reached the same partitions and founded different receivers: founding does not commute
([August 9](2026-08-09_THE_PANEL_GROWS_AT_ITS_OWN_BLINDNESS_AND_THE_FOUNDING_ORDER_DOES_NOT_COMMUTE.md),
§4). A provisional founding carries its order, and revising it is part of that path, not its
erasure.

## 6. What the repository already owns

- The kickstart's necessity and margin: the two `hnn::tests::receiving` tests,
  `Constitution::initial`, `CodecBootstrap`.
- What is founded and what moves: the owners in §3's table.
- The laws governing any founding: the HNN formula's source contract item 10, THE_MACHINE guard 9,
  the September 29 lessons §4, CLAUDE.md's "No catered machinery".
- Frames and chords: `HNN/Prediction.{joint_residue_determines_position, joint_class_not_additive}`,
  `Geometry/PairResonance`; the duplex's pitch chart; `Transport/HelicalCode`, including
  `slipped_contacts_eq`.
- The founding's reference and its readers: `hnn::constitution::NormalLaw`,
  `hnn::executed::pair_slip`, `hnn::prediction::closed_pairs`.
- Merge and split: the retention contract, `species_split`, `receiver::population::merge`, Lean
  `Compression/Landmark/Context/Merge`.

## 7. The joins owed

1. **The merge square at the moment owner.** `m′(π∘u) = P m(u)` under `E′π = PE`, `Ĝ′P = PĜ` and
   `A′π = A`, with its consumer the source moment re-charted at an aeon boundary, onto which the
   continuing state then restores. Lean, owed in #62 beside `Objects/SourceHolon`.
2. **A split as a forward founding.** The refined chart is founded by `Encoding::found` on later
   passages; the merged moment stays on its chart and the fibre `P⁻¹(m)` is held. A split asked of a
   merged face with no seed is refused with that fibre as its reason (#73).
3. **The equivariant founding** `E_0(σ(a)) = B E_0(a)`, admitted by the paired carrier and
   re-checked after each deposit (#386).
4. **Learned pairing** by key location over the matching menu, with the contact's slip receipts as
   the menu, replacing the declared `σ` of `compression::keys::duplex::Pairing` by a located one
   with its fibre (#386, #73).
5. **The founding comparison**, fixed before any run: two lawful foundings that differ in one
   operand only (two prior scales, two grains, or two frame families), on the same world, the same
   update law and the same encounters, reading the committed changes, the later responses and the
   accounted work, with the decoder, fibre and carry kept. Falsifier: a founded constituent that no
   admitted encounter moves was a frozen inventory. A changed objective or a changed grouping is not
   a bootstrap (#73, #148).
6. **The founding's reference stays declared** (decided here; `agent-inferred`, from its consumers).
   The normal law already carries its centre and its precision together, the map `W` and the Gram
   `H` founded at `W_0 = E_0` and `H_0 = I` (`hnn::constitution::NormalLaw`), so for that law the
   reference is already absorbed, and re-founding it would lose nothing. The declared reference has
   a second consumer that re-founding would break. The pair contact reads the learned part against
   it, `Δ_y = U B e_y − (E − B) e_(f(y))` with `B = E_0` (`hnn::executed::pair_slip`), and the
   release reads which contacts the port holds closed from the columns where `E` differs from `B`
   (`hnn::prediction::closed_pairs`). With `B` replaced by the learned `E`, every learned part would
   read zero and every located contact would reopen: an admitted future reading would change, which
   the retention contract forbids of any retention. The reference therefore stays fixed as declared
   material, and its revisability is the evidence's growing weight against its fixed unit precision
   (§3). Changing the reference itself is a new declaration with its own identity, which re-reads
   the located pairs.

**Recorded failures checked.** An authored routine standing in for learning (failure 1 and lesson 5
of the
[September 29 lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
whose §1 numbers the failures and §3 the lessons; the antipattern record): the founding declares
frames, a symmetric port and an initial key, never morphemes, meanings or a task's routine.
Recitation or an index counted as generation (failure 2; lesson 4): no count-priced founding, which
was retired on September 29. Pseudo-random signs presented as located keys (the September 29 §4):
the declared `E_0` is a prior and is never called a key. Text as the exception (failure 3; lesson
2): the same frames read text, pitch and amplitude. A refusal answered with a larger limit (failure
9; lesson 9): raising `LABEL_CEILING` or `HELIX_PERIOD_CEILING` to fit a larger vocabulary is not
the repair; located constituents and their merges are. A located cause carried into a new consumer
(lesson 3): §2 states that a founding does not repair a deposit that lands below its grain.
