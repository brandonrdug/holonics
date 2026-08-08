# Annihilation is release, departure is the vacancy, and neither is deletion

**Date:** 2026-08-08
**Truth status:** `established-bounded`. The trichotomy is a ratified laboratory section; both live
owners were read directly; Brandon's governing ruling is verbatim from a surviving transcript.
**Evidence:** direct source inspection of `soma/membrane/src/sparse_surface.rs:266`,
`soma/body/src/chart.rs:56-67`, and `archive/laboratory-physics/P20-the-dark-sector.md:71-77`;
`FORMULA §CV` read via `git -C /home/b/Workspaces/laboratory show a07ff376:src/soma/FORMULA.md`.
**Provenance.** A permitted sub-agent's collection surfaced an apparent contradiction between the
live body and an archived laboratory law and reported, correctly, that **no reconciling document
exists**. It does now. The reconciling section already existed and nobody had connected it. The
sub-agent's report is a search return, not authority; every claim below was re-established here.
**Band:** 2026-08-08 · APPARENT CONTRADICTION DISSOLVED BY A RATIFIED SECTION NOBODY CITED / THREE
DISTINCT MECHANISMS HAD ONE NAME / BOTH LIVE OWNERS ALREADY CORRECT / NO CODE CHANGED

---

## 1. The apparent contradiction

**The live law says opposed windings must not cancel.**
`soma/membrane/src/sparse_surface.rs:266` `opposed_winding_arms_prevent_false_annihilation` deposits
`Chi { same: 3, other: 4 }` carrying `WindingQuantum::ThisWay` and `Chi { same: −3, other: −4 }`
carrying `ThatWay` **at one position**, then asserts:

```rust
assert_eq!((sparse.occupancy(), sparse.breath()), (1, (0, 0)));
let (this_arm, that_arm) = sparse.cells()[0].form().fiber();
assert_ne!(this_arm, Rung::ZERO);
assert_ne!(that_arm, Rung::ZERO);
```

The resultant is `(0, 0)`. The position is still **occupied**. Both arms are still **non-zero**.

**The archived laboratory law says anti-aligned pairs annihilate and free both slots.**
`archive/laboratory-physics/P20-the-dark-sector.md:71-77`:

> *"`cos θ = −1` anti-aligned → ANNIHILATE. A holon meets its phase-conjugate. They cannot cohere
> (each is the other's negation); the rotations cancel … the self-evolution (the mass) is released,
> and the bound structure radiates… Not destruction: the super-state was exactly that; the soul (the
> ledger) is conserved"* — and `:111-112`, *"both slots freed, the content radiated."*

Read as one mechanism these are irreconcilable: one keeps the cell occupied, the other frees it.

## 2. They are not one mechanism, and the laboratory said so

`FORMULA §CV`, 2026-07-19, Brandon-ratified, the current compression authority there:

> **LOSS, ANNIHILATION, AND DEPARTURE ARE DISTINCT.** Loss is the oriented fiber information not
> transported by one declared outgoing presentation. Annihilation occurs only where opposed
> contributions compose to an actual zero **in one fiber**. Departure occurs where a lower
> constituent no longer factors into the continuing higher relation.

Three mechanisms. One of them had been carrying all three names.

| §CV term | what it is | live owner |
|---|---|---|
| **loss** | oriented fiber information a declared outgoing presentation does not transport | `receiver_exact_compression.rs` — the collapsed-pair population, each with its distinguishing word |
| **annihilation** | opposed contributions composing to an actual zero **in one fiber** | `sparse_surface.rs` — resultant `(0,0)`, occupancy `1`, both arms retained |
| **departure** | a constituent no longer factoring into the continuing relation | `chart.rs:67` `depart()` — one occupied grip releases, the borrow returned |

**The reconciliation is one sentence.** `sparse_surface`'s law is §CV's *annihilation*, and it is
about **the two arms of one fiber**: they compose to zero and the fiber stays occupied, because the
zero is a *resultant*, not an absence. P20's "both slots freed" is §CV's *departure*, and it is about
**two distinct souls**, one of which no longer factors. The live body implements both, correctly,
under their own names, in different crates.

## 3. And Brandon's ruling governs both

Verbatim, from a surviving transcript:

> *"I don't think that annihilation is literal destruction of anything actually, like we might
> consider deleting from memory manually in order to "annihilate" and optimize, but I don't think
> that's the trick… I think that the chains are supposed to literally overflow onto each other and
> overwrite their contents. … **But I don't think there's ever a reason to delete, if that makes
> sense.**"*

and, on what annihilation *does* instead:

> *"The annihilation of the singularity is pure energy, pure action propagated throughout the rest of
> the manifold."*

and, refusing the either/or:

> *"every time annihilation would both reform and radiate. **You cannot be selective**, I don't know
> why you're reaching for one or the other. The form changes, there is radiation."*

So the governing reading is: **annihilation is release, not erasure.** The arms are retained because
nothing is deleted; the resultant is zero because the passages oppose; and what leaves the fiber
leaves as radiation into the rest of the body, which is transport, not destruction.

**Departure is the one lawful vacancy**, and it too is his ruling — carried in the source that
implements it, `soma/body/src/chart.rs:56-58`:

> *"One occupied grip releases (annihilation — Brandon's ruling, 2026-07-10: the chart must shrink as
> well as grow; successful compression and competitive selection lawfully vacate space)."*

Note that this comment calls departure "annihilation." That is the naming collision this record
resolves; the mechanism it implements is §CV's departure and it is correct.

## 4. Why this matters beyond bookkeeping

**This is `CLAUDE.md` §2b at a third carrier.** A sign keeps the magnitude and discards the turn; a
float keeps the magnitude and discards the tail; and a fiber that *frees its slot* on an opposed pair
keeps the resultant and discards the two passages that produced it. `sparse_surface`'s law is the
same refusal as `ComparativeMultiplicity`'s repair earlier today and as `OrientedWinding`'s deposit-
only arms — **three carriers, one law, and now a fourth mechanism (departure) correctly distinguished
from all of them.**

**And it retires a real hazard.** An implementer reading P20 without §CV would free a slot on every
opposed pair, which would delete exactly the population §2b's standing obligation says to name. The
archived document is `HUNCH`-graded and `OPEN` by its own marking, so it never had authority — but it
was the only statement of the mechanism reachable from a search, because §CV is in a frozen
repository and the live body's owners never cite it.

## 5. What is owed

- **`chart.rs:56` should say `departure`, not `annihilation`.** Left unchanged here because this
  record is a consolidation pass and the comment is otherwise accurate and cites his ruling
  correctly; the rename is a one-line follow-up.
- **No live document states §CV's trichotomy.** It is reachable only through the frozen laboratory.
  This record is its live citation; `canon/` should carry it in the compression material.
- **The `SINGULARITIES.md` 54× annihilation figure is unrecoverable** and may not be cited:
  it reports a bound-action drop of `3.6e9 → 6.7e7` and attributes it to `living.wgsl`, which **does
  not exist** at `a07ff376`.
