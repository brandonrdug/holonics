# Mutual contact: the comparison is a pair contact that moves the produced face and the target's encoding

Refs #404 #405 #73 #410. Status: [design fixed before the build; agent-inferred, October 29].
Claude (opus), the second item of the order fixed in the
[October 29 audit](2026-10-29_THE_CODEX_LEAD_OF_OCTOBER_27_AND_28_AUDITED_THE_THEORY_STAYS_THE_TEXT_SURFACES_ARE_WITHDRAWN_AND_PARTICIPATION_IS_NEXT.md#4-the-order-now).
Owners it joins: the loss law ([CLAUDE.md](../../CLAUDE.md), "Loss is the logarithm of a ratio of
Holons"); the pair contact ([objects §5](../../docs/ELEMENTARY_OBJECTS.md), atlas
`pair.feature-complete-return`, `pair.beat-is-slip`, `hnn.tower-pair-contact`); joint reception
(`holonics::receiver::reception`, Lean `Holarchy/Reception`); the tower's face and encoding
(`holonics::hnn::tower`, `holonics_cuda::hnn::tower`, `kernels/tower.cu`); the echo record
(`wave.echo-stretch-and-delay`).

## 1. What is asked

Paraphrased; Brandon's words stay in the conversations.
- **October 25.** A comparison is an echo: the log of its stretch is the loss chart, and both sides
  of it move. That is how he babbles and learns, pathways checking one another's charts.
- **October 26 to 29.** Success is mutual: two Holons compare through a contact and both change.
  It is not a one-sided prediction.
- **The audit's order (October 29).** After participation, mutual contact. Joint reception returns
  its covector and its deposit to both participants, and the continuation re-solves with the
  changed resistance. The comparison then becomes the echo, not a one-sided prediction of the next
  class.

## 2. The learner now, read against it

[source-inspected] The tower compares its top face `x = x^L_t` with the arriving class `u_(t+1)`
through an authored one-sided readout, `z = U x + c`, `p̂(a) = 2^(z_a)/Σ_b 2^(z_b)`. The covector
`δz = p̂ − q` moves `U`, `c` and, through `Uᵀ δz`, the tower. The target never moves. Its encoding
`E(u)`, the face the bottom level reads (`x⁰_t = E(u_t)`), meets the comparison nowhere: `U`'s row
`a` is a second, separate face of class `a`. The loss law requires the produced Holon and the target
to be compared encoded through the same `E`. The tower breaks that, and its comparison is the
one-sided prediction the audit names.

[source-inspected] `JointLaw::interact` returns its pullback and deposit as declared absences
(`Component::Absent`, `receiver/reception.rs`). That is the same gap at the exact owner.

## 3. The law

**The comparison is a pair contact.** Its participants are the produced face `x` and the candidate
target's encoding `E_a`. The contact's slip is

```text
Δ_a = J x − E_a,        Q_a = ⟨Δ_a | Δ_a⟩,        the pair contact J = [J | −I]
```

`J` (`d × d`) is the contact's geometry, the lock. The produced face is the key: it fits where its
slip against the target vanishes. The face is the Gibbs face of the slips,

```text
z_a = −β Q_a + c_a = β (2⟨J x, E_a⟩ − ‖E_a‖²) − β‖J x‖² + c_a,     p̂(a) = 2^(z_a) / Σ_b 2^(z_b)
```

`‖J x‖²` is common to every class, so it is the face's gauge and is dropped. What remains is

```text
z_a = β (2⟨y, E_a⟩ − ‖E_a‖²) + c_a,        y = J x
```

`c_a` is the class's own constant (the pair contact's constant block). `β = 2^(−b)` is declared,
with `b = 2` (agent-inferred: the scale participation's pairing uses, so that a founded encoding's
`2⟨y,E⟩` spans a few bits of face).

**Both participants move, equal and opposite.** With `DQ_a = 2 Jᵀ Δ_a` toward the produced face
and `−2 Δ_a` toward the target, and with `δz = p̂ − q` (the comparison's logit covector, in bits),

```text
G_y   = 2β Σ_a δz_a E_a            the produced face's covector through the contact
G_x   = Jᵀ G_y                     into the tower, as Uᵀ δz was
G_J   = G_y xᵀ                     the contact's geometry: δs = (δJ) x + J δx
G_E_a = 2β δz_a (y − E_a)          the target's encoding: the reaction
G_c_a = δz_a
```

The target `t` has `δz_t = p̂_t − 1 < 0`, so descent moves `E_t` toward `y`. Every class the face
over-predicts moves away from it. Over the slip, `y` moves toward `E_t` by the same `Δ`. This is the
echo: the stretch is the slip, its logarithm is the loss chart, and its covector is returned to both
sides. `E` is the encoding the source enters through. The target's reaction therefore changes how the
next source is heard. The comparison and the input path sum into one family, as the loss law
requires.

**Opening.** `J` opens at zero, so `y = 0` and `z_a = −β‖E_a‖² + c_a`. `c_a` is founded as the
negation of the face's own release of `−β‖E_a‖²`, so every class sits at `z = 0` exactly and the
tower opens on the flat face, as the plain tower does with its readout at zero. The contact joins a
founded tower before its first section and before any part that reads the readout; a rotor and a
news clock read no readout and may join after it (agent-inferred). The first section moves `J` (`G_J = G_y xᵀ ≠ 0`) and `E`. While `J = 0` the
tower below receives no covector. That is a contact that has not yet closed.

**Not a store.** Nothing is written to be looked up. `E_a` is the class's own face, the same one it
enters through. The contact is its geometry. The face is recomputed from the present produced face.

**The continuation.** A deposit changes `J`, `E` and the tower together. The next section is read
under the changed contact and encoding, and the certificate rereads the section under them. That is
the re-solve with the changed resistance, the term the audit names.

**The exact owner.** For `JointLaw`'s implicit-midpoint step
`(I − (h/2)(J − R)Q) x' = (I + (h/2)(J − R)Q) x + h B u`, a covector `g'` on `x'` returns the
adjoint state `λ = M⁻ᵀ g'`, `M = I − (h/2)(J − R)Q`. It returns `Aᵀλ` to the opening state
(`A = I + (h/2)(J − R)Q`) and `G_R = −h sym(λ ēᵀ)` to the resistance, with `ē = Q x̄` the midpoint
effort. A deposit `R' = R − η G_R` must be certified `R' ⪰ 0` (passivity proved, never assumed).
The first build states this and leaves it owed, in #410 and at `JointLaw`. Its live consumer is the
tower's contact above. A Rust version with no learner calling it would be unconsumed.

## 4. Grains

The face and the encoding are on `2^(−16)`, `J` on the material's `2^(−24)`, and the covector `δz`
on `2^(−24)`.
- `y = J x` is released to `2^(−16)`.
- `z_a` is `2⟨y, E_a⟩ − ‖E_a‖²` on `2^(−32)`, released by `16 + b`, plus `c_a`.
- `G_y` is `Σ_a δz_a E_a` on `2^(−40)`, released by `15 + b` to `2^(−24)`. `G_x` is released by
  `24`, as the readout's return was.
- `G_J` sums `G_y ⊗ x` on `2^(−40)`, the readout's grain.
- `G_E_a` is released cell by cell, `release(δz_a (y_j − E_aj), 15 + b)` on `2^(−24)`, the grain of
  the input path's `δx⁰`. The two paths sum in one family.

Every release happens cell by cell, before any sum over cells or streams, so the host and the card
sum the same integers in any order.

## 5. Acceptance, fixed before the build

1. **Host law.**
   - (a) A mutual tower opens on the flat face, every class at `z = 0`.
   - (b) Its covector matches the code difference on a small tower for `J`, `c`, `E`, and the
     moves, gates, pushes and reads below. This is the pattern of the participation test.
   - (c) Before `J` opens, only `J`, `c` and `E` carry a covector.
   - (d) Its text restores whole.
2. **Card.**
   - Parity at the race's declaration (width 64, 128 modes, 256 contacts, four levels, sections of
     128 classes) on the race passage: every face, covector entry, learner and state equal, host
     against card.
   - The tower_pass suite stays whole.
3. **The measurement.**
   - The plain race's passage, keys, declaration and laps, with the comparison the only change,
     lap for lap beside the plain race (lap 45: 1.691 training, 1.850 held out, GSM8K 1.800, prose
     1.888).
   - Its writings are shown whole at chosen laps.
   - Bits decide nothing beside the writings. Nothing is claimed before it runs.

## 6. What the first build leaves, by name

- **The exact owner's covector** (§3), owed at `JointLaw` and in #410.
- **Joins beside it.** The pair face, the ring face, the strands' comparison and participation read
  `U` or join after it. They are refused beside a mutual contact until each is re-derived. The
  measurement changes one thing.
- **The tension reading** reads the readout's covector. Under a mutual contact it is refused.

## 7. The recorded failures this design could repeat

- **An authored routine standing in for learning.** None is written. The comparison is the loss
  law's own, its geometry is learned, and the target is the class's own face.
- **A store.** None: the class's face is the one it enters through, and the address is the slip.
- **Text on its codec's grain.** The contact compares faces of any declared alphabet, the same for
  text, image, acoustic or motor classes.
- **An uncertified deposition step.** The certificate rereads the section under the moved contact
  and encoding.
- **Bits read as progress.** The writings are shown beside the bits.
- **The card.** The part enters a learner run only with its card realization and parity.

## 8. Built, and what it measured

- **Host law** (`Tower::join_mutual_contact`, `Tower::mutual_face`, `Tower::mutual_return`). The
  readout's place holds `J` (`w × w`) and the readout's bias holds `c`. The text carries
  `mutual-contact b` after the material. Acceptance 1 passes in the host tower suite (105 tests, the
  build container, no card):
  - (a) and (c): `a_mutual_tower_opens_flat_and_only_its_contact_and_encoding_move_before_it_closes`.
    Its passage is not uniform in the classes, since on a passage where each class is the target
    equally often the constants' summed covector cancels.
  - (b): `the_mutual_covector_matches_the_code_difference`, for `J`, `c`, `E` and every family
    below.
  - (d): `a_mutual_tower_restores_from_its_text_and_refuses_what_is_not_derived`.
- **Card** (`kernels/tower.cu`, `TowerCard`). The forward keeps `y` per cell. `tower_reverse_top`
  forms `G_y` and returns `Jᵀ G_y`. `J` takes the outer sum `Σ G_y xᵀ`. `tower_encoding` adds each
  cell's `G_E_u` to the encoding's covector and sums `c`'s. The card refuses the contact beside a
  rotor, a news clock, a pair or ring face, strands or participation. Its parity cases are
  `the_cards_mutual_pass_is_the_hosts_for_thirty_two_sections` and
  `the_cards_pumped_mutual_pair_contact_holds_an_uncompared_place_as_the_host_does`, plus
  `tower_pass parity … mutual` at the race's declaration. On the RTX 4080 SUPER at `fae03c54f`
  (B-PC): `tower_pass` 34 of 34 in 20.0 s, both mutual cases among them; the parity at the race's
  size (4 sections at 320 streams, mutual) equal in all 163,840 faces and 1,274,116 covector
  entries, host 18,671 ms, card 1,899 ms.
- **The race entry** is `train-two-ladder-mutual-tower-classes`: the plain race's command, with the
  contact joined at the founding.
- **The race** (acceptance 3), on the RTX 4080 SUPER at `fae03c54f`, laps 0 to 45 complete, every
  lap 726 of 726 deposits certified. Held out, bits a class, beside the plain race:

  | lap | 0 | 4 | 10 | 15 | 20 | 30 | 40 | 45 |
  |---|---|---|---|---|---|---|---|---|
  | mutual | 2.569 | 2.103 | 2.016 | 1.986 | 1.974 | 1.955 | 1.949 | 1.944 |
  | plain | 2.356 | 2.004 | 1.918 | 1.901 | 1.886 | 1.862 | 1.857 | 1.850 |

  At lap 45 the mutual tower reads 1.774 on training and 1.944 held out (GSM8K 1.908, prose 1.971),
  against the plain race's 1.691 and 1.850 (1.800, 1.888). The gap closes from 0.21 at lap 0 to
  about 0.09 by lap 15 and holds there to lap 45; the train–held-out spread is 0.17 against the
  plain race's 0.16. Laps took 131–180 s, the widest 32-section window 5,799–7,964 ms. The writings
  at laps 0, 1, 2, 4, 8, 16, 32 and 45 were shown whole and stay outside the repository: the same
  record-shaped prose with invented words and GSM8K-shaped problems with wrong arithmetic as the
  plain race's. [agent-inferred] A gap that stops closing while both towers still descend reads as
  a held capacity, not a slower course: the contact reads every class through the encoding `E`
  that also carries the passage in, so at width 64 one material serves both ports where the plain
  readout has its own `U`. The measurement decides nothing beside the writings.
