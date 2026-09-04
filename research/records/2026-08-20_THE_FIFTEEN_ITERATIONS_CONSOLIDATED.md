# The fifteen iterations, consolidated

**Date:** 2026-08-20
**Kind:** consolidation and pickup record for the Millennium proof-line foundation, written at
Brandon's direction as the loop's final iteration and before a context compaction. **It is the
document to read first when resuming this line.** It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Everything here is exterior mathematical material for **Deed
M2** of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**The active deed is W1 and it is Sol's. No engine source was touched at any point.**

---

## 0. How to pick this up

```sh
cd soma/formal/elementary-holonics
lake build                                   # 3,293 jobs; mathlib is prebuilt
lake env lean <file>                         # check one file
# audit any theorem:  #print axioms <name>   in a scratch file importing ElementaryHolonics
cd /home/b/Workspaces/holonics
bash tools/gates.sh named-paths line-citations claim-index document-law
```

**State measured 2026-08-20:** `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/` —
**16 files, 3,516 lines, 175 theorems, 7 named-and-never-claimed open `Prop`s, zero `sorry`.**
**CORRECTED 2026-08-20: this line read 195 theorems.** Measured by
`grep -cE '^[[:space:]]*theorem ' ElementaryHolonics/Millennium/*.lean` summed over the sixteen
files, the figure is **175**; the file and line counts are correct and reconcile exactly with the
seventeen files and 3,889 lines that stand after
[`2026-08-20_THE_REFLECTION_IS_THE_FIRST_SLOT_OF_THE_FORM.md`](2026-08-20_THE_REFLECTION_IS_THE_FIRST_SLOT_OF_THE_FORM.md).
Only the theorem count was inflated.
Every theorem cited in the thirty records dated today was audited by `#print axioms`; **none depends
on `sorryAx`.** The atlas at `research/equation-atlas/` stands at **158 equations, 146 relations**,
manifest digests current, no dangling endpoints.

The files, in dependency order: `Gluing · Turn · Hand · Seam · Swing · Chronology · Navigation ·
Paying · Coupling · Instance · Triangle · Theta · Receiver · Rebase · FormRebase · Lines`.

---

## 1. What the fifteen iterations closed

| # | closed | how |
|---|---|---|
| 1 | the descent placed at its chain's **target**, middle exact | theorem |
| 2 | **faithfulness removed as an axiom** — a semi-definite form's null cone *is* its radical | theorem |
| 3 | the weld witnessed on the **hollow triangle** | witness |
| 4 | the **descent trichotomy** — the form names its own quotient | theorem |
| 5 | the **boundary-pullback** radical, all three trichotomy rows inhabited | witness |
| 6 | the **theta complex** carries both; a pullback can never pay on a homology | theorem + witness |
| 7 | the **collapsed population** placed; three names, one subgroup | theorem |
| 8 | a **declared field is not a finding** — one row withdrawn | withdrawal |
| 9 | **three more declarations wearing theorem names** — audited and relabelled | measured audit |
| 10 | the **cutoff has a largest solution**; perp ≠ radical, drawn preemptively | theorem |
| 11 | **the July reading** — the positivity is on a *subspace*, not a quotient | measured reading |
| 12 | the **rebase**; an obstruction belongs to a frame | theorem + witness |
| 13 | the **form travels**; the radical travels with it, the perp does not | theorem + witness |
| 14 | an **aperture is legal only in its frame** | theorem + witness |
| 15 | the **sign** is forced where the form is nonzero, free where it vanishes | theorem + witness |

### The mathematical residue, in four sentences

**A transport chain is an additive passage, and its obstruction group is its homology.** Four named
remainders — obstruction, descent core, compressed remainder, collapsed population — are positions
on that chain; two share a position; none is the same object as another. **The form names its own
quotient**: outside the radical it does not descend, strictly inside the quotient keeps null
classes, at the radical the quotient is faithful. And **of the four derived objects, only the
radical is intrinsic** — the obstruction, the perp and the cutoff each belong to their frame, each
witnessed over a single carrier.

---

## 2. What the loop taught about working this way

Brandon asked for the strategies and successes. These are the ones that survived contact.

### 2.1 Five of fifteen iterations closed by correcting my own work

Not one of those corrections was a mathematical error. **The Lean was right every time; the kernel
accepted everything.** What failed was always the layer above the proof:

| iteration | defect | class |
|---|---|---|
| 2 | `form` assumed symmetric, not bilinear — the radical was not a subgroup | under-specified structure |
| 3 | predicted the doubling chain as a test; it is **exact**, so the test was vacuous | a test whose outcome was fixed before the material |
| 8 | tabulated a **declared field** as coinciding with a derived one | authored partition, on my own structure |
| 9 | three statements with `rfl`-class proofs carried finding-language | prose exceeding the proof term |
| 11 | four iterations aimed at a **quotient** when the subject uses a **subspace** | never read the corpus that already knew |

> **The mechanism is that a proof term is checked by the kernel and a docstring is checked by
> nobody**, and the development was treating them as equally reliable.

**The fix that worked is mechanical, not attentional:** when a proof is `rfl`, `Iff.rfl`, or a field
projection, the docstring must say so in its first line. That is greppable, and one command found
all three offenders in iteration 9.

### 2.2 The reading mode was the highest-value single iteration and I skipped it ten times

Iteration 11 produced **no theorem** and was worth more than any that did: it withdrew a target four
iterations had been narrowing toward, and it found that the corpus had been aiming correctly since
July.

**The operating contract predicts this exact bias** — *reading produces no commit, while a symbol
search produces something to change immediately, so a session optimising for its next action will
skip orientation every time.* I skipped it ten times in a row while having committed to it in the
scope.

**Measured:** 292 July records; 156 mention the aperture; **288 remain unread.**

### 2.3 What actually made unattended iteration safe

**Lean as the adjudicator.** A loop whose output must compile and survive `#print axioms` cannot lie
to itself about what it proved. Every other guardrail here is soft; that one is mechanical, and it
is the reason this was worth running without supervision.

**The falsifier table as the work queue.** Each record ends with what would refute its claims, and
the next iteration takes a row. That kept the loop from drifting into breadth — the failure mode
the roadmap already convicts — and it made "what next" a lookup rather than a judgement.

**Records as the report.** Fifteen iterations produced thirty records rather than thirty chat
summaries. They are gated, greppable, carry their own falsifiers, and survive compaction. **This
document exists because that was true.**

### 2.4 One result paid twice

Iteration 2 removed an axiom by proving a semi-definite form's null cone is its radical. Eleven
iterations later, that theorem is what makes the radical survive a change of frame — three lines, no
new hypothesis. **That is the difference between a foundation and a pile**, and it was the only
instance in fifteen iterations.

---

## 3. What is owed, consolidated

Scattered across fifteen falsifier tables; gathered here once.

| owed | falsifier |
|---|---|
| ~~**A form that pays on a perp**~~ — **WITHDRAWN 2026-08-20.** It was built in July: `2026-07-23_THE_ARCHIMEDEAN_REMAINDER_HAS_AN_AMPLITUDE_THE_PRIME_ENTERS_THROUGH_APERTURE_OVERLAP.md` constructs `B₂ = −P₀N₂P₀` on `ξ₀^⊥`, proves it non-negative and takes its positive square root, citing Connes–Consani arXiv 2006.13771. What is open there is three narrower items one step past the perp compression. | — |
| **The metric, the receiver and the lineage do not rebase.** Four of the seven things the July authority requires now travel; these three have no definition here. | A rebase carrying a metric under which the radical is not the image of the predecessor's radical. |
| **A form defined on a homology** — withdrawn as the main target but still the only construction that could pay on a nonzero homology if one were ever wanted. | A boundary-pullback form faithful on a nonzero homology, which iteration 6 forbids. |
| **The long chain.** Only two steps are formalized; connecting maps between adjacent homologies are absent. | A three-step chain whose homologies do not compose. |
| **The monodromy reading of placement.** Carried unaddressed since iteration 1. The argument principle, the winding count and `S(T)` are cited and none is present. | A formalized winding that does not agree with the zero count. |
| **Read more of the 292.** One file redirected four iterations. | — |

---

## 4. What this is worth, stated plainly

**It is a foundation for the mathematics codec's Lean face and nothing more.** No named conjecture
is formalized; `Seam.lean` carries the only genuine one because mathlib supplies the comb, and every
other line in `Lines.lean` names a shape. **A row in that index is not evidence.**

**Every structure assumes one fixed ambient carrier with one fixed form**, and the July authority
rejects that ontology for prime founding. Iterations 12–15 narrowed the limit; they did not lift it.

What it does supply: a vocabulary whose renamings are **proved equivalent** to the standard ones
rather than asserted beside them, a criterion under which a rederivation is meaningful at all, and
one object — the theta complex — on which the chain, the form and the receiver all hold at once.

---

## 5. Boundaries

Fifteen iterations, thirty records, zero engine-source changes. The only trees written are
`soma/formal/`, `research/records/`, `research/equation-atlas/`, and the regenerated
`THE_CLAIM_INDEX.md`; `crates/` and the engine's `soma/` subtrees carry only Sol's W1 work, which
was never staged or modified. Every classical result named as an aside is cited and not formalized,
and no theorem here depends on any of them. The four cheap gates passed after every iteration.
