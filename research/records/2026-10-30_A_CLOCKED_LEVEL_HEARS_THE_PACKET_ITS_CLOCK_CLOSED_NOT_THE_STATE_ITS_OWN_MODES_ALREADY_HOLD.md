# A clocked level hears the packet its clock closed, not the state its own modes already hold

Refs #404 #406. Status: [the measurement in §1; the law and its acceptance fixed before the build;
agent-inferred, October 30].
Claude (opus), design lead. Read beside
[the clocked levels' contacts](2026-10-29_A_CLOCKED_LEVELS_CONTACTS_HEAR_THE_PASSING_CURRENT_AT_EVERY_ARRIVAL_WHILE_ITS_MODES_MOVE_ON_THEIR_OWN_CLOCK.md)
(whose §9 is §1's measurement) and
[the radix record §1](2026-10-29_A_VALUE_IS_A_RADIX_MOVE_THE_FREE_ENERGY_IS_THE_CODE_THAT_FOUNDS_AND_POLARITY_IS_THE_ONE_REVERSIBLE_NEGATION.md#1-a-value-is-a-radix-move-and-the-towers-modes-are-registers-in-their-own-radices),
which states the packet law this record builds. Owners it joins: `Tower::step` (a clocked level's
input), `Tower::reverse_joined` (the fine level's scan), the state's text, the card
(`kernels/tower.cu`, `TowerCard`).

## 1. What the stacked clock's race measured

[measured, RTX 4080 SUPER, October 30] Six levels, the clock `B = 8`, `r = 2` from level 4 with the
passage (C), read 0.010 to 0.017 bits a byte worse held out than the four arrival levels beneath
it alone (2.156 against 2.139 at lap 1, 2.032 against 2.020 at lap 3), and better than six plain
levels at every lap. A training pass took C 276 to 282 s, the four-level tower 166 s. So two
clocked levels cost less than two arrival levels and still add nothing the hour reads.

## 2. The located cause

[agent-inferred] At its tick a clocked level `l` takes the passing current `x_l(t)` as its input:
one arrival's encoding with the returns of the levels below, each read from that level's whole
state `h_(l−1)(t)`. Over a packet `P` (the arrivals since the level's last tick) the fine level's
state is

```text
h_(l−1)(close) = T_P h_(l−1)(open) + m_P,     T_P = Π_(t∈P) λ_t^(Δτ_t),     m_P = Σ_(t∈P) (Π_(s>t) λ_s^(Δτ_s)) (Σ_(j<Δτ_t) λ_t^j) γ_t P x_t
```

`T_P h(open)` is the history the coarse level already received as earlier packets and holds in its
own modes; only `m_P` is the packet's news. Read through the whole state, the coarse level hears
its own past again at every tick, transported by the fine level's moves, and the news it should
hold is a small part of what it hears. This is the radix record's statement that the coarse level
receives the packet `(T_P, m_P)`, not `h_close`.

## 3. The law

[definition; agent-inferred, October 30] **A clocked level hears the packet its clock closed.** On a
tower whose news clock begins at level `F`, each level `l ≥ F` carries the open packet `a_l`, the
fine level's recurrence from rest since the level's last tick, moved by the fine level's own step
at every arrival:

```text
a_l ← λ_t a_l + γ_t P_(l−1) x̃_(l−1)(t)        Δτ_(l−1)(t) times (the fine level's own moves and push)
x̃_l(t) = r̂(Re(C_(l−1) a_l))                    at a tick of level l (Δτ_l(t) ≥ 1); then a_l ← 0
```

`x̃_l` is the input of level `l`'s push, gate and turn at its ticks, read through the fine level's
own read `C_(l−1)` and normalized as the fine level's read is (its scale is a gauge). A level below
`F` takes `x̃ = x` as before. The passing current `x_l(t)` still crosses the level's contacts
through the passage, and the residual stream is unchanged. The packet adds no material: it reads
the fine level's moves and read. An arrival that ticks the level several times holds its packet
through them, as the clock holds the arrival.

At the stream's opening every packet rests. Across learner sections the open packets are carried
as the modes are, and the opening's packets are constants in the reverse (the truncation the modes
already take there).

**The reverse.** The coarse level's push, gate and turn covectors reach `x̃_l` at its ticks
instead of `x_l`; `x̃`'s ratio adjoint reaches `C_(l−1)` against the packet's face and returns
`G_a(t) = C_(l−1)ᵀ δr(t)` at each tick. The fine level's scan then carries two states with one
move: beside `G_h(t) = read covector + conj(λ_(t+1))^(Δτ) G_h(t+1)` it carries
`G_a(t) = G_a,tick(t) + [no tick of l at t] conj(λ_(t+1))^(Δτ) G_a(t+1)`, the reset cutting the
packet's covector at each tick. Since `a` and `h` share `λ_t`, `γ_t` and the push, their covectors
of the move, of `γ_t` and of the push are summed: `conj(h_(t−1)) G_h(t) + conj(a_(t−1)) G_a(t)` for
`λ_t`, and `G_h + G_a` for the push.

**Not a store.** `a_l` is the fine level's present motion since the coarse level's last tick,
released at the tick; nothing is written to be looked up. It is the same carrier as the modes, on
the coarse level's clock.

## 4. Acceptance, fixed before the build

1. **Unchanged without packets.** Every tower test passes unchanged; a state's text carries
   `packets -` without them.
2. **The packet.** On four levels clocked from level 2 with packets, levels 0 and 1 read face for
   face as the stacked tower's; at each tick of a clocked level its packet `a` and the fine level's
   states agree, `h(close) − T_P h(open) − a` within the rounding of the packet's moves; an arrival
   that ticks no time leaves a clocked level's modes as they were and advances its packet.
3. **Refusals.** Packets are refused without a news clock, beside participation (whose sites are
   then the packets; the joined consumer is the next loop's if this one earns its place), and on a
   learner after its first section.
4. **The covector.** The covector matches the code difference on three levels clocked from level 2
   with packets, with and without the passage, at steps of `2^(−9)` units.
5. **The state.** The state's text carries the open packets and restores whole; a passage read in
   carried sections is the passage read whole.
6. **The card.** Parity at the race's declaration with packets (six levels clocked from 4, the
   passage), host against card, every face and covector entry equal; and the card's clocked level
   between its ticks computes only its contacts, the faces unchanged.
7. **The race.** One hour on the card: C with packets (C′) beside the four-level tower. The claim:
   C′ reads no worse held out than the four-level tower at laps 1 and 3 (2.139 and 2.020). Short of
   that, clocked levels above four arrival levels do not earn their place at this declaration, and
   the clock's work goes to participation's reach alone (radix record §1), not to the tower's
   depth. Each lap's card time is reported beside the bits.

## 5. The recorded failures these choices could repeat

- *Bits read as progress*: the claim is fixed against the control the question needs, the four
  arrival levels beneath the clocked ones (the stacked clock's claim was fixed against six plain
  levels, and passed while the clocked levels added nothing).
- *A located cause carried unrepaired into a new consumer*: participation's sites at the coarse
  levels are the packets; participation is refused beside packets until the packets are measured.
- *A design thought in the programming language*: the packet is the fine level's motion since the
  coarse level's tick, stated as the transport `T_P` and the face `m_P`, not as a window.
- *Text as the exception*: nothing reads a class or a boundary; the clock is the tower's own news.
- *A refusal answered with a larger limit*: the race keeps the hour and the lap rule.

## 6. What was built

[built; agent-inferred, October 30] **The host.** `Tower::join_packets` and the learner's, the open
packets in `TowerState::packets` and the state's text, the forward in `Tower::step` (the packet
moved by the fine level's step, read and rested at the next level's tick) and the reverse in
`Tower::reverse_joined` (the read's ratio adjoint, `G_a` carried by the fine level's scan and its
move covectors summed with the modes'). Acceptances 1 to 5 hold on the host: the tower's tests pass
(231 in `hnn::tower`), and the packet's covector matches the code difference with and without the
passage.

**A still level computes only its contacts.** At an arrival that ticks a clocked level no time,
its push and gate are not read, on the host as on the card: the state stands, so their covectors
are zero there and skipping them changes no face and no covector, and a refusal (a value outgrowing
its carrier) can then arise only where both realizations compute. The card also holds a still
level's read from its last tick when no participation reads the level (its state has not moved
since); with participation the read is computed, since its current is read beside it.

**The card.** `kernels/tower.cu` carries the packets: each stream's open packets resident beside
its modes, the packet moved in the fine level's mode loop and read at the next level's tick
through the fine level's read, the push, gate and turn covectors of a hearing level returned to
the packet's read (`pk_dx`), `tower_reverse_packet` returning the read's ratio adjoint to the
packet's covector, the fine level's scan carrying it, and the read's outer sums added onto the fine
level's read (`accumulate`). Its parity with the host (acceptance 6) is owed on the RTX 4080 SUPER
(`the_cards_clocked_packets_are_the_hosts_for_thirty_two_sections`), then the race (acceptance 7).

