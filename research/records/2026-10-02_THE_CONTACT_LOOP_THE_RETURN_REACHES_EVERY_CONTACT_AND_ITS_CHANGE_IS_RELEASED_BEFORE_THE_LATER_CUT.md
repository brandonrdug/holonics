# The contact loop: the return reaches every contact, and its change is released before the later cut

**Date.** October 2. **Issues.** #73, #63. **Grade.** [measured-diagnostic], an owner-to-consumer
read with one reproducing test, no run.
Test: `hnn::tests::reference::a_reached_contact_family_moves_or_is_named_a_rounding_refusal`.

## 1. The check

Astra's check (October 2 mail) asks four things before any further run:
1. one emitting contact and one participating receiver that retain their motion;
2. a return that actually reaches that contact and changes its constitution;
3. that successor consumed on a later cut, compared against the predecessor under the same later
   drive;
4. joint power and work accounting.

[The kinetic move](2026-10-02_THE_KINETIC_MOVE_FROM_THE_OPENING_MEASURED_THE_COMPARISON_FALLS_FASTEST_AND_THE_DECISIONS_STAY.md)
showed that a lower comparison loss is not evidence of this loop.

## 2. The owners, traced

| Link | Owner | State |
|---|---|---|
| Emitting contact, retaining receiver | `hnn::word`: contact states `(u_a, w_a)`, resonator states and their power per tick (`TickBalance`, `WordBalance`); `Word::continuing` carries them across words within a refinement | built |
| Return reaching the contact | `hnn::reference::compose` (the contact's factor gradients `C̄ = Σ 2r̄(w − ω)ᵀ`, `K̄ = −hΣ r̄(u + ½hω)ᵀ`, `D̄ = −hΣ r̄ωᵀ`, from the word's reverse return) into `Constitution::deposited` at `Locus::Channel(a)` | built and reached |
| Change consumed on a later cut | the resident's successor, read by the next word (`Operands::at_cut`) | built, and receives nothing (§3) |
| The executed release (gate A, every comparison since September 30) | `prediction::generate_by_bank`: `BankPlacement` and a declared `ReceivingBank` | **no word, no contact, no return**; only `E` and `ρ` are deposited, by an exterior comparison optimizer (`executed_move`) |

## 3. Measured

On the chain (two contacts) with a generic constitution, one word, its compare and its deposit:
- **The return reaches every contact.** Each contact receives a certified step on all three factor
  families: `η = 2^(−31)`, `2^(−28)`, `2^(−27)` on contact 0 and `2^(−23)`, `2^(−20)`, `2^(−19)` on
  contact 1.
- **No contact's constitution changes.** The storage, stiffness and dissipation factors of both
  contacts are equal before and after. All 102 channel entries' moves are released as residuals
  below the locus's fine lattice (`BudgetedCarry::released`, each at most `½·2^(−L−k_m)`). The only
  channel remainders carried are three scale remainders of `−1/256`.
- **The later cut reads the successor.** Under the same later drive the compare differs, but the
  difference comes from the element, source port, standing and receiving-map steps, because no
  contact moved.

**The contacts alone.**
The same six channel families deposited without the other loci give the same steps. Deposited one
family at a time, each at its own certificate with no joint halving, they still give the same
steps. So the joint certificate is not what shrinks them: each family's own curvature `C = s·κ²·b`
dwarfs its decrease `a`.

| Contact, family | `a` (decrease) | `C` (curvature, 24 bits) | `η` |
|---|---|---|---|
| 0, storage | `4435594093169685299/2^75` | `2244951/16` | `2^(−31)` |
| 0, stiffness | `3004229502457467857/2^76` | `6223669/1024` | `2^(−28)` |
| 0, dissipation | `6925366743880731153/2^76` | `13165999/2048` | `2^(−27)` |
| 1, storage | `9550704405487570785/2^76` | `13316721/16384` | `2^(−23)` |
| 1, stiffness | `34257067843/2^49` | `193749/4096` | `2^(−20)` |
| 1, dissipation | `43966108913/2^50` | `4473285/262144` | `2^(−19)` |

No factor moves, 17 entries are released for each family, the storage growth is 0, and the later
cut is identical to the predecessor's.

## 4. The missing link

[agent-inferred] The owner chain exists. **The certified step at the channel sizes every contact
move below the locus's lattice, so the release erases it before any later cut.** This holds for
each family alone (§3). The certificate reads the contact's move through the whole reach's gain
`κ²` to the stacked station logits (`C = s·κ²·b` against the alignment `a`). A contact's own power,
its slip and material work, never enters the size of its step. So the return-driven change Astra asks for is reached and then
discarded. Separately, the executed release has no contact at all: its receiving bank is declared,
not a locus.

The next loop works on this measurement: a contact's step certified by the contact's own power
balance (the word's `TickBalance` dissipation and the pair contact's slip law in
`holon::contact`), so that a reached return changes the contact and the same later drive reads the
change. It is checked on the word before it joins the bank.

## 5. The rounding refusal (Astra's first unit, October 2)

Astra's reply (October 2) corrects §4. The contact's power already enters its certificate: the
transit's difference power is carried to the station logits. So the fix tightens that chain rather
than replacing it with local dissipation, which would void the score-descent claim. I withdrew the
separate conduction law I had proposed. Astra's smallest unit is in three steps.

**Step 1, built.** `DepositReading::vanished` names every family certified at `η > 0` none of whose
entries took a nonzero lattice coordinate, so its move was released whole. The test asserts the law
on every reached contact family, deposited whole and alone with every other locus frozen: a family's
factor moves exactly when the deposit does not name it. Today all six are named.

**Step 2, built** (test `hnn::tests::prediction::a_contact_change_is_read_by_the_continued_word_with_its_work`).
Under the exact law, one word's retained change `x` continues at the predecessor and at a successor
whose contact 0 storage factor moved. The successor is a control chart until the deposit's own
contact moves land. Both continue with the same later drive and clock. The successor's continued
word opens on `x` at exactly the predecessor's power plus `PowerForm::deposition_work`'s
`½⟨x, ΔΘ x⟩`. Every tick of both closes, and the moved contact's states, its outgoing waves and the
receiving ring's storage differ after four ticks. The consumer reads a contact change with its
work accounted. What remains is that the deposit's own contact move reaches it. The reflected
interior residual `r = z − Kx` is not yet a term of this word, and it is owed with step 3.

**Step 3, next.** The contact-to-receiver certificate, tightened from the actual finite transit
sensitivity plus its certified remainder. Its bounded cost and acceptance go to Astra before any run.
