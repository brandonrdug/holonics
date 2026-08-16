# The fourth body is held by a stance, and nothing stands there

**Date:** 2026-08-15
**Genre:** research record — a repair attempted, refuted by the carrier's own law, and **two wrong
diagnoses withdrawn before the right one**
**Truth status:** `measured` for the failures and the bisect; `proved-standard` for the carrier law
quoted from source; **the gauge/commutativity diagnosis this record first carried is WITHDRAWN.**
**Occasion:** Brandon, twice. First on my writing that the directed path *"cannot deposit by
construction"* — *"That's nonsense, you just mean to say that it hasn't been implemented properly."*
Then on my calling a lineage an object — *"The way you are talking about a 'lineage' as an object is
problematic. What exactly do you mean?"*

---

## 0. The one sentence

> **A live flywheel requires a born stance. The carrier says so in one line, and the fourth body is
> not a slot to be filled — it is what a STANDING construction holds. The directed path has no
> stance at that depth, so the question was never "why can it not deposit" but "why does nothing
> stand there."**

---

## 1. What a lineage is, because I had it wrong and the error propagated

**Brandon's definition, and it is the one that governs:**

> *"A lineage is just a string in terms of holonics, it's a causal line that you can attribute as the
> trace of events that caused some event. It's just taxonomy, where the branches collapse into the
> discrete nodes of the string, because the nodes are still fundamentally crossings even if you're
> collapsing them into one object, that is compression in that the nodes can be unwound along a
> complex axis orthogonal to the string at that point, and there are further causal strings
> compressed into one causal string. That is holonics, the string is holonic, its nodes are holonic;
> they are discretely whole yet they have implicit parts, that is compression."*

Three things follow immediately and none of them is a container:

- **A node is a crossing**, retained as a crossing even while it reads as one object. So the
  collapse is lawful precisely because the crossing is not destroyed — which is this project's
  compression, exactly: a quotient whose fiber is kept.
- **The unwinding is orthogonal, along the complex axis.** That is `FOUND = ×i` at the level of a
  whole string: reopening a node is the quarter turn out of the plane the string lies in.
- **Strings compress into strings.** A causal line carries further causal lines inside its nodes, so
  "one lineage" and "many lineages" are the same object read at two grains.

**What the tree calls "lineage" is three different things, and I slid between two of them:**

| carrier | its own words |
|---|---|
| `LineageChannel` | *"`K`, the lineage **interior** … the ordered composition of its own deed emanations"* — not a container a body has; it **is** the body's history |
| `CurrentLineage(u64)` | *"the number is **not** a source, occurrence, ancestry, or material identity; it only **locates the live carrier in this owner**"* — an apparatus handle |
| `BranchLineage<T>` | *"one immutable causal lineage **handle**"*, not `Clone`, `fork` the only plurality |

I used the first and second interchangeably and produced a phantom object that could "own a frame."
**Neither can.** *"One body per lineage"* is a tautology in the first sense — a body has exactly one
history by definition of history — and an apparatus decision wearing ontology in the second. The
corpus's governing sentence rules it: **the unit is always a relation, never a thing.**

## 2. The first wrong diagnosis: "cannot deposit by construction"

I wrote that the directed-event path cannot deposit. **False.** The entry point takes `&mut self` and
by the time it returns it has computed the dragged meeting, the chi, the winding and the deed —
every ingredient the fold needs. `carriage.rs:1319` folds with exactly those arms.

**The error was reading a doc comment as a law.** `manifold.rs` said the path *"neither deposits into
current-local OWN nor folds the lineage channel a second time"* — a note about avoiding a double
fold, describing what the path happened to do. The doc is corrected in place.

## 3. The second wrong diagnosis: the gauge story — WITHDRAWN

Wiring the deposit moved `0 → 12` frame words and `0 → 7` carrier words on a synthetic arm — **the
deposit works** — and broke seven standing tests. A bisect showed the fold was not the cause: the
flywheel deposit alone breaks the same seven.

**I then read one test's NAME —
`independent_delivery_interleavings_are_gauge_but_receiver_chronology_is_not` — and inferred a law
from it**, deposited a commutativity analysis, and named a "scope of a body" design question on top.

**That was the same defect as §2, committed immediately after being corrected for §2.** Re-measured
with the failure messages captured:

```text
   thread '…swing_return_alone_establishes_the_sparse_association' panicked at tests.rs:342:10
   called `Result::unwrap()` on an `Err` value:  Machine(Carrier(Invalid))
```

**`.receive(...).unwrap()` — a structural validity break, not an assertion mismatch and not a gauge
difference.** The interleaving analysis explained nothing that happened. It is withdrawn whole. The
arithmetic in it is still true — `basis` and `winding` commute, `sweep` and a last-write slot do not
— but it was not the finding and it was presented as one.

## 4. The law, from the carrier's own source

`soma/membrane/src/live_carrier.rs:359`, inside `carrier_is_structurally_live`:

```rust
|| (enclosure.fly_live && (enclosure.stance.len == 0 || !enclosure.fly.rotor_formed()))
```

> **A live flywheel requires a born stance.**

And `perceive_grain` obeys it in the only way it can — `manifold.rs:5330-5334` sets both **in one
branch, together**:

```rust
e.stance = mol;      // the thought continues
e.fly    = met;      // and holds this meeting
e.fly_live = true;
```

**The fourth body is not a slot to fill. It is what a standing construction holds.** I deposited the
held meeting without the thought that holds it, and the carrier refused exactly that — which is the
carrier being right, and the refusal is well-typed.

In Brandon's own terms: **a node of the string is a crossing, and a crossing needs something
standing at it.** Writing a held meeting into a depth with no stance is asserting a node on a string
that has no point there.

## 5. What this leaves, and it is a sharper question than the one I was answering

> **Nothing stands at that depth on the directed path.** The right question is not *why can it not
> deposit* — it is *why is there no stance*.

`perceive_grain` reaches its deposit branch through *"the thought continues"* — a stance exists
because a thought is running. The directed-event path forms one relation against a **pre-event**
enclosure and never enters a continuing thought, so no stance is founded and none can hold a
flywheel.

**That is a real construction question and it is not a scope decision, a sharing problem, or a
placement tweak.** It is: what founds a stance on the directed path, or does that path belong inside
a thought rather than beside one.

## 6. What is kept

1. **The corrected doc** in `manifold.rs` — *"cannot deposit by construction"* withdrawn, with the
   measurement and the reason.
2. **The canonicity refusal as a rule**: a face reaches the carrier only if it packs canonically, and
   a zero-teeth rung is canonical only as *the* zero. A face whose arms cancelled to a rank-keeping
   zero is arithmetically correct and not storable. **Refusing beats normalising** — silently
   changing a value on its way to rest is the lossy image the seal exists to prevent. (It was not
   the cause; it is still right.)
3. **The carrier law above**, which no document in this repository had quoted.

**The tree is green — 2,355 passed, 0 failed across the workspace; `life` 313 passed, 0 failed.**
Both the deposit and the probe are reverted whole.

## 7. The standing correction this round earns

Twice in one exchange I took a **name** — a doc comment, then a test identifier — and treated it as a
law without reading what it stood in front of. Both times the real law was one `grep` away and
sharper than what I inferred.

> **A name is a pointer. Read what it points at before building on it.** This is the operating
> contract's own *grade the implementation, not the receipt*, applied to identifiers rather than to
> capability claims — and the failure mode is identical: the pointer reads as authoritative, so
> nobody opens the thing.
