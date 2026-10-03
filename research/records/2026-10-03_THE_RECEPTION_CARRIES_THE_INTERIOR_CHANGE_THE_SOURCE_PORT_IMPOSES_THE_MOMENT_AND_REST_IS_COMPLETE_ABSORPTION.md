# The reception carries the interior change, the source port imposes the moment, and rest is complete absorption (pinned before any code)

**Date.** October 3. **Issues.** #73, #63 (THE_REBUILD U6), #62 (the owed Lean). **Grade.**
[definition; agent-inferred] for the carry law and its choices (§2, §3); [proved-derived;
implemented-exact] for the owners it reuses, held by their tests (§1); the build of October 3 and
its tests are §6 [implemented-exact]; the chained balance and the law it satisfies are §2.3
[proved-derived; implemented-exact]. Code follows this record. The production default stays rest.

**Occasion.** The review of October 3 located that every production reception opens at rest. The
path is `Reference::refine` (`reference.rs:1147`) → `PendingRatio::read_charted` → `open_charted`
(`pending.rs:184`, `:152`) → `Word::open_charted` (`word.rs:770`) → `Word::on_operands` →
`EndChange::rest` (`word.rs:809`). `tests/word.rs:33` pins it ("nothing of the earlier change
persists"). The card does the same: the device word zeroes its resonator states on every
invocation (`holonics-cuda/src/hnn/readout.rs:421-423`). So window `k`'s end change never becomes
window `k+1`'s opening.

The momentum the [throw](2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md)
carries (#240's `Flight`) lives between U6's parameter moves, not between receptions. The native
continuation (`word/continuation.rs:48`→`:354`) carries motion only within a refinement, across a
contact deposit. It is consumed only in a test (`reference.rs:4347`), refuses every non-contact
deposit (`continuation.rs:265-286`) and deposits nothing at `R = 0`. This record derives what must
carry from one reception to the next, and how, so that today's behaviour is the exact limit.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches three:
- **the tube**: the receptions become one clocked span instead of a sequence of fresh impulses;
- **the pair**: the contact states `[u, w]` and the arriving waves carry across the boundary;
- **the helix**: a declared resonator's pump phase reads the field's own elapsed ticks.

Faces and placement (the moment's placement), the cell holonomy and the tower thread stay attached
unchanged.

## 0. The recorded failures this could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **2, an index of contexts or a window.** The carried change is the field's own state, of the
  field's fixed shape, overwritten at every reception. It is not a list of past windows, and no
  depth enters.
- **3, text as the exception.** Nothing here reads a codec; the carry is the same for any boundary
  chart.
- **5, an uncertified deposition.** A deposit between two receptions does work on the carried
  change. That work is read exactly by the owner that already reads it (§2.3). The chain's balance
  is read exactly at every reception, and the law it satisfies is derived and stated (§2.3), with
  the stronger reading that fails it, never assumed.
- **6 and 7, seen as unseen; bits as progress.** Exposure stays prequential (the corrected §7 of
  [the refit record](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)).
  No score decides the carry: it is a declared opening whose laws are derived and checked exactly
  (§2.3, §4), and the production default stays rest.
- **The retention law (no tape).** The adjoint stops at the opening (§2.5). No word outlives its
  compare, and nothing of a consumed word is kept except the end change it leaves.

## 1. What the owners already state

- **The rest limit is a theorem of the owner.** `Word::continuing(field, operands,
  &EndChange::rest(..), injection, 0)` equals `Word::on_operands(field, operands, injection)` in
  change and in every tick balance (`tests/prediction.rs:66`). Today's reception is therefore the
  continuing word opened on the rest change at tick zero.
- **The change is the whole state.** `EndChange` (`word.rs:333`) holds the storage waves per ring,
  the arriving waves per contact, the contact states `[u, w]`, the resonator states and the phase
  each resonator's form is read at. Two words of two ticks, the second opened on the first's change
  with nothing injected, end on the change of one word of four ticks (`tests/prediction.rs:93`).
- **The commit's work on the end change is already read.** `WordBalance::commit` (`word.rs:612`)
  carries every word's balance across the deposit that follows it: the deposition work
  `½⟨x, ΔΘ x⟩` on the end change `x`, and `x`'s power under the committed constitution
  (`CommitWork`; Lean `HNN/Word.field_commit_deposition`). Exposure reads the form before the
  deposit at the word's cut for exactly this (`reference.rs:4006`).
- **The source enters as a state.** The opening storage `s_g(0) = P_g^(τ_g) m̃_g` is the
  normalized, phase-binned moment of the whole passage ingested so far (`moment.rs`, module
  header). It is the source's sufficient quotient, not an increment: exposure keeps one moment over
  the whole cut and ingests each window into it (`reference.rs:3869`, `:4075`).

## 2. The carry law

### 2.1 What carries

[definition; agent-inferred] At reception `k+1` the word opens on

```text
x_(k+1)(0) = Π_int x_k(end)  +  s_(k+1)(0)
```

where:
- `x_k(end)` is the end change of reception `k`'s word, taken when its compare consumes it;
- `Π_int` keeps every interior coordinate (the storage of the non-source rings, every arriving wave,
  every contact state, every resonator state) and sets each source ring's storage to zero;
- `s_(k+1)(0)` is today's open storage from the moment after window `k`'s ingest. It is nonzero
  only on the source rings.

**Why the source rings are replaced and not added.** The moment is the whole passage's normalized
state, re-read at every reception. Adding it to the source ring's evolved storage would count the
passage once per reception: the history would enter both through the carried motion and through the
moment. The source port is an imposed port. Its ring takes the moment's storage, and the ring's
outgoing end storage is absorbed by the source. The interior has no such source, so its motion
carries.

[definition] **Realization through the existing owner.** Zero the source rings' storage in
`x_k(end)`, then call `Word::continuing(field, operands_(k+1), &that, &s_(k+1)(0), t_(k+1))`.
Since `s_(k+1)(0)` is zero off the source rings, the addition there leaves the carried storage
unchanged, and on the source rings it imposes. `Word::continuing` itself does not change.

### 2.2 The exact limit

Let `A` be the absorption of the boundary at a word's end:
- `A = I` (complete absorption): every interior coordinate is emitted at the end, as today's
  release states (`word.rs`, module header, "release").
- `A = 0`: nothing is absorbed beyond what the field's own conductances dissipate within the ticks.

The opening is `(I − A) Π_int x_k(end) + s_(k+1)(0)`. At `A = I` it is `EndChange::rest` plus the
injection, at tick zero, which is today's word exactly by `tests/prediction.rs:66` on a field
with no declared resonator (§2.4).

[agent-inferred] The law built is `A = 0`. An intermediate absorption would need a declared exterior
admittance at the receiver's section, a new locus of the constitution with its own deposition. None
exists, and choosing a value for it would be an unjustified literal. It stays unbuilt unless a
measurement under `A = 0` locates the need for it.

### 2.3 How the carried change crosses the deposit and the ingest

Between the end of word `k` and the opening of word `k+1` the medium changes twice. Both are read on
the same physical coordinates of the carried change, by one owner, `PowerForm` (`word.rs:352`):
1. **The deposit**: `Θ → Θ'` at the lift `λ`. Its work on the carried change is
   `CommitWork::deposition = P_(Θ',λ)(x) − P_(Θ,λ)(x)`, already read today (§1).
   - Deposits on `E`, on the transport modulus `ρ`, on the receiving tree and on landmarks change
     only the injection or the reading. Their work on the carried change is zero.
   - Deposits on a contact's storage, stiffness or dissipation, and on a resonator's gains, do work.
2. **The ingest**: `λ → λ'` at `Θ'`. Each cell's selective step moves the lift point, which moves
   every contact's conductance at the lift. Its work on the carried change is
   `P_(Θ',λ')(x) − P_(Θ',λ)(x)`. The step is the exterior source acting, so this work is the source
   port's, entered in the balance beside the source's imposition.

[definition; proved-derived] **The chained balance, on one baseline.** Let `x = x_k(end)` be the
carried change, `y = Π_int x` its interior, `s = s_(k+1)(0)` the moment the source port imposes, and
`E_S(z) = (h/4) Σ_(g∈𝒮) Y_g |z_g|²` the source rings' storage. The power form is additive by ring
and the ring admittances are field constants, so `P_(Θ,λ)(x) = P_(Θ,λ)(y) + E_S(x)` under every
form, and the deposit and the ingest act only on the contacts, so they read `x` and `y` alike. The
source rings' end storage `E_S(x)` is absorbed through the source port at the reception and is
subtracted once:

```text
P_open(k+1) = P_(Θ,λ)(y) + deposition_k + ingest_k + E_S(s)
E_end(k+1)  = P_open(k+1) − L_(k+1) + Π_c + pump + interconnection + residual,   |residual| ≤ bound
```

with `L = dissipation − resist + resonator dissipation ≥ 0` the next word's certified loss (each term
signed by its own owner). The first line is exact by the two decompositions above; the second is the
word's own balance (`WordBalance::closes`). Written on the whole end power instead, the same identity
is `P_open(k+1) = P_(Θ,λ)(x) + deposition_k + ingest_k + E_S(s) − E_S(x)`: the two forms are one
baseline, and an earlier draft of this section, which wrote `P(y)` and also subtracted `E_S(x)`,
subtracted it twice. At `A = I` the carried change is the rest, so the interior and the work on it
vanish, the whole end power is absorbed, and the opening is `E_S(s)` alone: today's opening power,
so today's balance is the limit of this one.

[proved-derived] **The law the carry satisfies: dissipativity with respect to its declared supply.**
The ingest is the source port's work (2. above), and the deposition, the imposition, the contrast,
the pump and the interconnection are each a declared port's. From the two lines and `L ≥ 0`, at
every reception

```text
E_end(k+1) ≤ P_(Θ,λ)(y) + deposition_k + ingest_k + E_S(s) + Π_c + pump + interconnection + bound
```

and summed over a chain, the end storage never exceeds the first interior plus everything the ports
supplied plus the residuals' bounds. Nothing enters except through a declared port.

[measured-exact; the failing law] **The stronger reading is not a law.** It was stated here before
the read as the sufficient condition: at every reception, `deposition_k + ingest_k ≤ L_(k+1)`, the
work done on the carried change between the words within the next word's loss. On the chain fixture
(`chain_of(cut_length())`, source `source(length, 81)`, a 24-window deadline, `Carry(Nothing)`;
nine compares, so eight chained readings) the deposition is zero at every reception, and:

| Reception | `deposition + ingest` | `L` | Holds |
|---|---|---|---|
| 1 | `0` | `0` | yes |
| 2 | `0` | `18142115297891599265251270759039205961/2¹²⁸` | yes |
| 3 | `10531030011859400337/2⁷⁵` | `57557220820183899053671/2⁸¹` | yes |
| 4 | `0` | `255451355697484121789559/2⁸²` | yes |
| 5 | `−2448376125/2⁴²` | `81862029179669344589161/2⁸¹` | yes |
| 6 | `1144389765/2⁴²` | `234498858861794171536969/2⁸²` | yes |
| 7 | `5048657427/2³²` | `2104128050508906045512109/2⁸²` | **no**, by `3580154876230715732256339/2⁸²` |
| 8 | `−15407359260789375224895/2⁷⁶` | `357753753096119191965200943566167177049/2¹³⁰` | yes |

Summed, the work is `73408221214458413523171/2⁷⁶` against the loss's
`1238976393826823334276250846524291252349/2¹³⁰`, so the summed reading also fails from reception 7
on. The cause is the ingest: each cell's selective step moves the lift and re-reads every contact's
conductance at the lift, and at reception 7 that re-reading does more work on the carried arriving
waves than the next word dissipates. The work is the source port's, so the reading that fails is the
one that counted it as interior. An earlier pass of this read compared the work with the dissipation
alone, omitting the element's passive term `−resist`; it failed at receptions 3, 6 and 7. That was
a slip in the loss, not a property of the carry. Both checks are now receipts
(`ChainedBalance::{dissipative, within_loss}`), and the fixture's test pins the failure of the
stronger one, exactly, rather than tuning anything to make it pass.

[owed in #62] The Lean statement of the chained balance and its dissipativity, and of the rest case
as its limit (`HNN/Retention`).

### 2.4 The clock

[definition; agent-inferred] The carried state is read on the field's own elapsed ticks.
`Word::continuing` takes `opened_at`. Under the carry, `t_(k+1)` is the sum of the ticks every
earlier word of the chain executed, so a declared resonator's pump phase continues across
receptions.

Today every reception re-phases the pump to zero, a reset of the pump clock that the carry removes.
The rest case of `tests/prediction.rs:66` opens at tick zero, while the carry opens at the
cumulative tick. On a field with a declared resonator the two differ in the pump's phase even when
the carried change is at rest, unless the cumulative tick at the opening is a multiple of every
pump period.

[definition; agent-inferred] **The exact limit is claimed for fields with no declared resonator.**
That is U6's default (`resonator none` in `hnn_exposure.rs`) and every field the exposure and the
U6 reads run today. There `A = I` is today's word exactly, whatever the cumulative tick. On a field
with a declared resonator the carry keeps the cumulative clock, and no exact limit is claimed: the
pump phase is a second carried quantity, and a read under such a field compares it as such. A
clock reset at every opening is not taken: it would restore the hidden restart of the pump that
the carry exists to remove.

### 2.5 The adjoint stops at the opening

[definition] Each word's return reads its own ticks only. The covector reaching the carried
opening, `∂ℓ/∂x(0)`, would continue into reception `k`'s word, but that word was consumed at its
compare. So it is returned as a reading and deposited nowhere: deposition reads only covectors that
reached their locus, and no tape of words is kept. Learning shapes the carry through `Θ`, which
governs every word's motion, including the motion the next word carries.

### 2.6 Where the carried change lives

- **The resident, not the current.** Guard 16 ("`Current` holds the lift point and nothing else";
  `mod.rs:104`) stays. Under the carry, the resident holds one `EndChange` and its tick. The
  refinement's return writes them when it consumes its word (a compare, or a discard at the budget
  stop: the motion happened either way, and a discard carries no deposition work).
- **One chain.** A refinement opened while another refinement is pending would have no defined
  predecessor, so under the carry the refine refuses that opening. Exposure holds one pending at a
  time.
- **The saved state.** The carried change and its tick are part of the continuing state, written
  inside its check (built, §6). A state at rest writes none, so every state written before the carry
  reads back at rest, which is today's law.
- **The card.** The device word owes the same opening: the carried change resident on the card,
  read by the next word, with host-card parity. Receptions were already sequential (a deposit
  separates each pair), so carrying them costs no co-presence.

## 3. What it is not

- **Not the throw.** The throw carries momentum `P = dH` in the parameter coordinates between U6
  moves. The reception carry is the field's motion between receptions. They compose, and neither
  replaces the other.
- **Not `ContactCut::continue_deposited`.** That owner continues within one refinement across a
  contact deposit, certifies by the native unit certificate, and refuses other loci. The reception
  carry crosses every deposit. Loci that leave the power form unchanged do zero work, and the rest
  is read by `CommitWork`, so it needs neither the refusal nor the unit certificate's same-locus
  restriction.
- **Not a context.** Nothing about which windows preceded is carried, only the field's present
  motion. Two passages that leave the same end change open the next reception identically.

## 4. The claim fixed before the code

- At `A = I`, the carry path reproduces today's exposure receipt on the gate state byte for byte:
  every reading, deposit and balance.
- At `A = 0`, the chained balance (§2.3) closes exactly at every reception, and the chain is
  dissipative with respect to its declared supply within the residuals' certified bounds.
- Under the carry, a saved carry restores the chain's next opening exactly, and a damaged one is
  refused.

No score, seed or held-out read decides the carry. The production default stays rest; a change of
the default is a derivation and its exact checks, together with the device word's parity (§6).

## 5. Owners touched when built

`word.rs`'s module header ("Continuing motion within a refinement" becomes "within and across
receptions") and its law table row "the word opens at zero" (`mod.rs:121`, which then reads "at the
rest limit"); `pending.rs` and `reference.rs`'s refine (open on the resident's carried change);
`constitution.rs`'s `ContinuingState`; the device word; `tests/word.rs:33` (it states today's law and
becomes the `A = I` case); Lean `HNN/Retention.word_opens_at_zero` (the rest case) with the chained
balance owed in #62. The atlas rows for these owners update in the same commit as the code.

## 6. Built (October 3), and what the read needs first

[implemented-exact; agent-inferred where marked] The carry is built through the production path, not
a test path. Today's reception is unchanged unless a carry is declared.
- **The switch.** `Reference::with_reception(Reception::Carry(absorption))`; the default is
  `Reception::Rest`, which keeps `Word::open_charted` exactly. `Absorption::{Complete, Nothing}` are
  `A = I` and `A = 0` (§2.2); nothing in between is built.
- **The opening.** `Reference::refine` → `PendingRatio::read_on` → `Word::open_received`, which
  zeroes each source ring's storage in the carried change (`Π_int`) and calls the unchanged
  `Word::continuing` with the moment's open storage at the carried tick (§2.1, §2.4). The compare's
  re-read at a later commit, the deposit's re-read at the successor (`Arrived`) and `release` open on
  the same opening, which the pending slot holds beside the ratio, never inside it (guard 3).
- **The carry.** The compare writes the resident's one carried change (`Resident::carried`) from the
  word its return consumes (`Word::reception_end`: the end change and `opened_at` plus the word's
  junction steps), after the boundary's absorption (`ReceptionCarry::absorbed`). A discarded pending
  ratio carries its refine's word's end (§2.6). A refinement opened while another is pending is
  refused (one chain). The resident's state bits count the carried change's nonzero values and its
  tick.
- [agent-inferred] **A declared resonator under `A = 0` is refused.** The last junction step
  advances the hop clock without a pump step, so the carried resonator state, measured at its last
  pump tick's phase, does not fit the next opening's clock (`Word::continuing`'s check). The pump's
  carry across receptions is owed; under `A = I` a resonator opens at rest in the carried clock.
**The acceptance read** (`crates/holonics/src/hnn/tests/reference.rs`, "the reception carry";
`tests/lock_face.rs`):
- at `A = I` the prequential exposure on the chain field returns every reading, deposit, balance
  and curve point of the exposure at rest, bit for bit; only the resident's state bits read more, by
  the carried tick;
- under `A = 0` every compare writes its consumed word's end at the summed junction steps, and the
  next refine's faces are exactly the read on that opening, opened from the carry as written and
  read back (`ReceptionCarry::{write, read}`); the carried interior moves the read;
- under `A = 0` the chained balance (`ChainedBalance`, read in `expose_from` at every reception
  opened on the previous word's end) closes exactly at all eight readings, the chain is dissipative
  at all eight, and the stronger reading fails at reception 7 only, by
  `3580154876230715732256339/2⁸²` (§2.3);
- `ContinuingState` carries the reception's end (`with_carry`, `carry`) inside its check, before its
  clock line, so the stamp still replaces only what follows the storage product; a state at rest
  writes no carry and reads back at rest; one byte changed inside the carry is refused as damage;
  `Constitution::continued` does not read the carry, which is resident motion, and
  `Reference::mount_carried` mounts it beside the declared constitution, refused at rest or on
  another field's shape.

[agent-inferred] The carry's restore is exact at the word it opens, which is what the carry
determines. The rest of the reference resident (its open moments and the aeon in progress) is not a
saved object of this path; it is restored only where the executed path's continuing state already
restores it.

Still owed: the device word with host-card parity (the card's port tests read the reference at its
default, rest, so they are unchanged), and the Lean statement (#62). Guard 16 of
[THE_MACHINE](../../docs/THE_MACHINE.md) reads that no change outlives its word or its refinement;
under `A = 0` the end change outlives its refinement into the next reception's opening, as this
record derives. The guard's wording owes that join in its owner.
