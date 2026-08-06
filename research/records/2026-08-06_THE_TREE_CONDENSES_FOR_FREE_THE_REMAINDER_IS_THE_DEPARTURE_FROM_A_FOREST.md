# The tree condenses for free; the remainder is the departure from a forest

**Deposited 2026-08-06.** Occasioned by Phase 7 movement 1, which refounded a condensation this
body had failed to port and, in doing so, walked past the smallest instance of the organ
`CLAUDE.md` §11 names as missing.

**Provenance.** The framing of §11 — that scale-independent recruitment, general far-field folding,
and supported realization are one missing organ — is Brandon's, standing in the operating contract.
The sharpening below is assistant interpretation and is graded as such. Brandon has not ruled on
it.

---

## 1. What movement 1 actually refounded

**Truth status:** `established-bounded`. **Evidence:** `implemented-exact`, `computational-witness`.

The source-incidence owner answers one question: *which sources reach this state?* The naive answer
is a `states x sources` table, which does not fit. The source owner's answer is a depth-first walk
over the suffix-link tree, after which every state's complete descendant population is a
**contiguous interval** `(start, length)` into one shared array.

That is an exact condensation. A subtree of arbitrary size — a far population, in §11's vocabulary
— is replaced by a **compact representative of two words**, and every membership question about the
far population is answered from the representative alone. Storage falls from a product to a sum.
The remainder is **empty**: the interval is not an approximation of the subtree, it is the subtree.

The C++ port had reproduced the storage law and substituted a fixpoint relaxation with a per-state
rescan for the walk — cubic where the source is linear. Movement 1 refounded it. Measured across a
quadrupled aperture, formation fell from `x27.57` to `x4.43` with the returned state population
identical either way.

## 2. Why it is free, and what that costs the framework

**Truth status:** `proved-standard` for the tree case.

The condensation is free for exactly one reason: **the incidence is a tree.** Under a depth-first
order on a rooted tree, every node's descendant set is an interval, with no remainder, and the
interval is its own reopening rule — containment answers every query in the declared family.

This is the trivial instance of §11's organ, and its triviality is the whole content. §11 asks for
an exactly computed positive form on a supported realizer population, with a **certified
remainder** and a reopening rule keyed to the receiver family. On a tree the remainder is zero, so
nothing is learned about the certificate. **The difficulty §11 names lives entirely in the
departure from tree-ness.**

## 3. The sharpening

**Truth status:** `interpretation`.

There is a standard object for the general case, and naming it makes §11's missing organ concrete
rather than aspirational.

For a general reachability relation — a directed acyclic incidence rather than a tree — no single
linear order makes every down-set an interval. The standard construction (Agrawal, Borgida and
Jagadish, *Efficient management of transitive relationships in large data and knowledge bases*,
SIGMOD 1989) takes a **spanning tree**, which yields one interval per node for free by the argument
above, and then pays for every non-tree edge with **additional intervals**. A node's true
descendant population is the union of its spanning-tree interval and those extras.

The correspondence to §11, slot for slot:

```text
far population           ->  a node's down-set in the incidence
compact realizer         ->  the spanning-tree interval
certified remainder      ->  the additional intervals the non-tree edges force
receiver family          ->  the query class the labelling must answer
reopening rule           ->  interval containment, extended by the remainder
```

Under this reading the remainder is not a vague residue. It is a **counted, exhibitable population
of intervals**, and it is zero exactly when the incidence is a forest. That is a testable statement
about any incidence this project builds.

## 4. What this does and does not license

**Truth status:** `open` for the claim below; `conjecture` for the pairing.

It does not give the organ. A minimal interval cover is a real optimization problem, the standard
construction is a heuristic rather than a certified minimum, and nothing here supplies the
**positive form** §2 and §11 both require — the pairing that decides whether the realizer
population is sufficient.

What it does supply is a sharper statement of the missing capability, and one falsifier:

- **The concrete missing return.** Given a declared incidence and a declared query family, compute a
  spanning-tree interval labelling, exhibit the exact additional-interval population forced by the
  non-tree edges, and certify that the union answers the query family exactly. Zero extras iff
  forest.
- **Registered as `conjecture`, not claimed:** that the sufficiency question — *do `k` intervals
  cover this down-set for this receiver family* — carries a natural pairing whose positivity is the
  finite-rank shadow of the form §2 derives from a supported realizer. The shape is suggestive and
  the shape is all this is. Do not cite it as a bridge to Hodge or RH.

## 5. The methodological return, which is the more certain one

**Truth status:** `established-bounded`. **Evidence:** direct source inspection, twice.

Every substantive correction in this construction has come from reading an implementation against
its receipt: the conditioning contamination, the sixty-four-bit divide reaching a non-integer
carrier in device code, the stale build manifest, the rename hidden by stale objects, and now the
source-incidence cost.

Phase 7 added a rule the earlier ones did not force. **A cost law is a law.** The Phase 6 port
reproduced what the source owner *returns* and not what it *costs*, and called that "ported
exactly." Both are the owner. A return reproduced at a cost the source does not pay is a different
organ wearing the same receipt.

And one narrower rule, from the same phase: **a law that returns zero proves nothing about
itself.** The mounted corpus carries no repeated section and no revised surface, so the plurality
and duplicate laws would have been implemented and never exercised — present in the code, absent
from the evidence. A declared control was added for that reason and the phase grade requires it to
return non-zero. This is the tautology-detection discipline of §8 pointed at the opposite failure:
§8 catches a receipt that could not have come out otherwise, and this catches a receipt that could
not have come out at all.
