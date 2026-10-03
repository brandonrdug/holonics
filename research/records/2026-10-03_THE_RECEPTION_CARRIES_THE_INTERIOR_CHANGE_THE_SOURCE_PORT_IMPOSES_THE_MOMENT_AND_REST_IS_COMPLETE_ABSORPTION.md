# The reception carries the interior change, the source port imposes the moment, and rest is complete absorption (pinned before any code)

**Date.** October 3. **Issues.** #73, #63 (THE_REBUILD U6), #62 (the owed Lean). **Grade.**
[definition; agent-inferred] for the carry law and its choices (§2, §3); [proved-derived;
implemented-exact] for the owners it reuses, held by their tests (§1); nothing here is built or
measured. Code follows this record, and every build or read under it passes the
[pre-launch checks](../runs/u6/PC_QUEUE.md) (a) to (f) first.

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
  change. That work is read exactly by the owner that already reads it (§2.3), and the chain's
  passivity is stated as a certificate per reception, not assumed.
- **6 and 7, seen as unseen; bits as progress.** Exposure stays prequential (the corrected §7 of
  [the refit record](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)).
  Whether the carry is kept is decided by a paired held-out read (§4), never by development bits.
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

[definition] **The chained balance.** For the interior change `y = Π_int x_k(end)` the next word's
open power is

```text
P_open(k+1) = P_(Θ,λ)(y) + deposition_k(y) + ingest_k(y) + source exchange_(k+1)
```

The source exchange is `(h/4) Σ_(g∈𝒮) Y_g (|s_(k+1),g(0)|² − |x_k(end)_g|²)`: the moment's imposed
storage in, and the source ring's end storage absorbed. At `A = I` the first three terms vanish and
the source exchange is today's opening power, so today's balance is the limit of this one.

[definition; owed] **Passivity over the chain is certified, never assumed.** Sufficient: at every
reception, `deposition_k(y) + ingest_k(y)` does not exceed the word's certified dissipation. When a
reception fails that bound, it reports the excess as work entering from outside the field; it is not
refused by a cap. The Lean statement of the chained balance, and of the rest case as its limit, is
owed in #62.

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
- **The saved state.** The carried change and its tick are part of the continuing state. Under the
  carry, `ContinuingState` owes both, inside its material identity's check. Until then every saved
  state is exactly a rest-carried state, which is today's law.
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

## 4. The claim fixed before the code, and the read that decides it

- **The build's acceptance.**
  - At `A = I`, the carry path reproduces today's exposure receipt on the gate state byte for byte:
    every reading, deposit and balance.
  - At `A = 0`, the chained balance (§2.3) closes at every reception within its certified bound.
  - Under the carry, a saved state restores the chain exactly, and a foreign or damaged one is
    refused.
- **The decisive read** (only after the build's acceptance passes, and only through checks (a) to
  (f)). The decision is whether production receptions carry. Carry and rest are read on one stored
  state, the same state and lineage at an equal move count.
  - **The unit is the held-out passage, not the station.** A passage's eight station targets follow
    from its last two request cells, and they are read in one release, so its stations are not
    independent trials.
  - **One stored state.** Every held-out passage is read from that stored state, and nothing is
    deposited on a held-out passage's cells. Under carry, the motion carries across the receptions
    inside a passage and starts again from the stored state at each passage. Passages therefore
    couple only through a fixed state, and the read does not alter what it measures.
  - **The test.** For each of the 128 passages, `d_k` is carry's stations right minus rest's.
    Passages with `d_k = 0` are dropped; `b` counts `d_k > 0` and `c` counts `d_k < 0`. Carry is
    released at `P[X ≥ b | X ~ Bin(b + c, 1/2)] ≤ 1/64`, exact. Station counts are description and
    enter no tail. Development bits do not decide it.
- **Its held-out seed** is `2026100301` (order-2, 128 requests), which no run has read: it appears
  in no record, queue or receipt on `main` or on the run branches as of this record. The seed
  `2026093012` is spent (P5 in §11 and every held-out pair of §9 of the
  [refit record](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md))
  and is excluded.

## 5. Owners touched when built

`word.rs`'s module header ("Continuing motion within a refinement" becomes "within and across
receptions") and its law table row "the word opens at zero" (`mod.rs:121`, which then reads "at the
rest limit"); `pending.rs` and `reference.rs`'s refine (open on the resident's carried change);
`constitution.rs`'s `ContinuingState`; the device word; `tests/word.rs:33` (it states today's law and
becomes the `A = I` case); Lean `HNN/Retention.word_opens_at_zero` (the rest case) with the chained
balance owed in #62. The atlas rows for these owners update in the same commit as the code.
