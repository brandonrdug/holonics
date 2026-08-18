# The work is counted, the prediction is refuted where it is wrong, and the hand was inverted

**Date:** 2026-08-17
**Truth status:** `established-bounded` for every measured return, each carrying its command;
`proved-derived` for the combinatorial cost model where the measurement confirmed it exactly, and
`refuted` for the two coordinates where it did not; `interpretation` for the reading of a committed
step as a navigation organ.
**Evidence:** `measured` — `cargo test -p holonic-engine --lib` on the touched modules and the full
gate sequence, plus two drivers run on this machine today.
**Provenance:** Brandon, 2026-08-17, setting the goal: *"Complete the plan outlined in
blueprint/THE_WORK_VECTOR_THE_HANDS_POLARITY_AND_THE_COMMITTED_STEP.md, analyze outcomes and
interpretations."* The plan itself was ordered by an external adjudication which refuted five claims
before they were deposited, and by his instruction to *"raise your standards to excellence and be
more genuinely careful with your implementation."*
**Plan:** [`blueprint/THE_WORK_VECTOR_THE_HANDS_POLARITY_AND_THE_COMMITTED_STEP.md`](../../blueprint/THE_WORK_VECTOR_THE_HANDS_POLARITY_AND_THE_COMMITTED_STEP.md),
all four stations executed. It sits under [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md).

---

## 0. The four returns

1. **`k⁴b` now comes out of counted work, not a clock.** The width-weighted price grows **16.25× per
   doubling** of the extent — `k^4.03` — from coordinates the deed reports about itself. The clock fit
   it replaces said `k^4.18` from what turned out to be two endpoints.
2. **Six of eight predicted coordinates are exact; two are refuted, in opposite directions.** A model
   that could not be exceeded would be a ceiling rather than a law.
3. **The material refuted the metric.** Every deferral was carried by the operation *count* while the
   tablet says the *width* dominates — and both are right, because a weighted **sum** cannot express a
   **product**.
4. **The hand was inverted at one call site and the audit found it**, hours after it was written and by
   me. The shared type is not overloaded; one implementor read the wrong face.

---

## 1. Station one — the work vector

`crates/holonic-engine/src/exact_work.rs`, with the counting inside
`inertia::inertia_with_work` and `exact_linear::multiply_with_work`.

**What was absent, measured 2026-08-17:**
`grep -rn "\.bits()" --include='*.rs' crates/holonic-engine/src/inertia.rs
crates/holonic-engine/src/exact_linear.rs` → **0**, against **17** across all library `src`. The two
modules whose intermediate width dominates every exact deed never took it.

**And it is a lift.** `cuda_aperture::CarrierWork` already declares `intermediate_bits` — *"the widest
intermediate this carrier had to represent exactly"* — and `order_against` already returns the
four-state `ExactOrdering` whose `Open` retains both carriers. What was absent is that it arises only
from a **device aperture receipt**: `CarrierWork::of_candidate` reads a CUDA receipt and nothing read
an elimination.

### The refusal has to be on a prediction, and the first build got that wrong

The first version admitted on **measured** work, which refuses nothing — the deed is already paid for
by the time the vector exists. The run timed out at 120 s proving it. `CarrierWork::of_cpu_authority`
already had the shape and said why: *"that this is a prediction is what makes the cost law falsifiable
— running it either confirms the predicted ordering or refutes it, and a refutation says the declared
law is wrong about this material."*

So the model is declared, the budget admits on it, and the deed runs only where admitted:

```text
    extent    predicted    verdict  dim ker A   peak bits    measured
         8         3904   ADMITTED          0        1125        4013
        16        25872   ADMITTED          0        2422       26246
        32       197696   ADMITTED          0        5006      198574
        64      1568960   DEFERRED          -           -     not run
        96      5293344   DEFERRED          -           -     not run
       128     12550656   DEFERRED          -           -     not run
```

**The deed at 64, 96 and 128 was not performed.** The refusal is typed, it names the coordinate that
carried it, and it happened before the cost did. The anti-vacuity arm holds: the metric both admitted
and deferred, and a metric that did only one has refused rather than measured.

### The prediction, and where the material refuted it

At the widest admitted extent:

```text
    additions          predicted        86368   measured        86368   exact
    multiplications    predicted        86368   measured        86368   exact
    divisions          predicted        20832   measured        20832   exact
    entries-written    predicted        24928   measured        24928   exact
    resident-entries   predicted         1024   measured         1024   exact
    dependency-span    predicted           66   measured           66   exact
    cumulative-bits    predicted     32095488   measured     16185470   OVER-predicted
    peak-bits          predicted         4128   measured         5006   UNDER-predicted
```

**Six of eight exactly.** The combinatorial half of the model — `Σ_{j<k}(k−j)² = k(k−1)(2k−1)/6` per
species, `k²` entries written once then the same sum, span `k` — is *correct*, verified against the
counted deed rather than fitted to it.

**And the two width coordinates are refuted in opposite directions**, which is more useful than either
being right. `peak-bits` under-predicts by 1.21×: the model used `k · b`, and Hadamard bounds a
`j × j` minor of `b`-bit entries at about `j(b + log₂ j)`, so the naive form was always going to fall
short — it was declared knowing that, because *a prediction that could not be exceeded would be a
ceiling rather than a law*. `cumulative-bits` over-predicts by 2×, which is a separate error in the
integration of the width over the elimination and is not the same mistake.

### ★ And the material refuted the metric itself

Every deferral above was carried by **`multiplications`**, not by width — yet
`canon/TABLET_THE_CHART.md` §3.7 says *"the dominating quantity is intermediate entry bit-length."*
Both readings are correct and a weighted sum cannot hold both:

> **The width does not dominate the COUNT. It dominates the COST OF EACH OPERATION — and that is a
> PRODUCT, which no weighted sum over the counted coordinates expresses.** Under unit weights an
> operation on a 5,000-bit rational prices the same as one on a 60-bit rational.

`ExactWork::width_weighted_operations` is the derived coordinate that does, added because the run
found the gap. Under it:

```text
    extent  unit-weight price   width-weighted price
         8               3904                2934208
        16              25872               48791552
        32             197696              799048704
        64            1568960            12984524800
```

**16.6×, 16.4×, 16.25× per doubling** — `k^4.03`, the `k⁴b` law arriving out of **counted coordinates**
rather than out of a regression on elapsed seconds. That is what §3.7's owed item asked for, and it is
the difference between a law and a fit: this one is reproducible on any machine, has no frame to
declare, and its six exact coordinates say which part of the model is doing the work.

**What remains owed on that item, stated precisely.** The width model is refuted and needs the
Hadamard form; and the derived coordinate is *derived*, named as such so a caller can tell which
coordinates the deed reported and which this module computed.

### ★ The plan's own falsifier for this station fired, and it is answered rather than dodged

The blueprint said: *"If the counted work vector orders two extents the same way the clock did, the
clock was not lying and the repair is bookkeeping — say so rather than presenting the agreement as
evidence."*

**It does order them the same way.** Both the clock and the counted work say a larger extent costs
more, and `k^4.18` against `k^4.03` is the same monotone ordering. So the ordering is not what the
repair bought, and presenting the agreement as evidence would be exactly the defect the falsifier
names. What it bought, precisely:

- **The refusal precedes the deed.** The clock's refusal was prose printed after a nine-minute
  timeout; the vector's is a typed `Admission::Deferred` that names its coordinate and fires before
  any cost is paid. Measured consequence: the driver runs in **3.3 s** where it took **47 s**, because
  it no longer performs the extent it then declines to report.
- **The exponent comes from a model verified exactly on six coordinates**, not fitted from two
  endpoints. The clock's fit telescoped — its interior measurements contributed nothing.
- **The phases separate**, which no clock can do: two matrix products and two eliminations shared one
  interval, and counted they return four vectors with different dependency spans.
- **The metric became refutable, and was refuted.** A clock has no coordinates to be wrong about.

## 1b. What a clock cannot separate, measured

At extent 32, the four phases of one deed a stopwatch reports as one number:

```text
    product-transpose-times-form     span    1   peak      62   multiplies   32768
    product-times-basis              span    1   peak     123   multiplies   32768
    elimination-source               span   32   peak       2   multiplies   10416
    elimination-pulled-back          span   32   peak    5006   multiplies   10416
```

**A product's dependency span is one; an elimination's is its pivot count.** Every output entry of a
product is independent of every other, so the whole deed is one step however many operations it
performs — and that single coordinate is the difference between a deed a card could carry and a deed
it could not. It is also the coordinate that says the two eliminations, identical in operation count,
differ by a factor of **2,503** in peak width because one of them received the product's output.

## 2. Station two — the hand's polarity

The audit was posed as an audit and not a repair, because a reading existed under which the two
apparent opposites agree. **That reading is the right one and it held**: the hand is the sign of the
**stored face** at every implementor.

```text
    soma/body/src/arrow.rs         the sign of `aim`   — its own typing calls it "what STANDS"
    traversible_chain::Crossing    the sign of `M₂₁`   — the half that came BACK, so did not transport
    leader_quadrature::Committed   the sign of the residual — what the material returned against the
                                    step's own prediction, and therefore did not transport
```

`Hand::Ortho` names the case where nothing stands and everything transports, and all three agree on
it. **The type is not overloaded and does not split.**

**But one call site was inverted, and it was mine from this morning.**
`PhasedLink::hand` read the sign of `phase.sine` and returned `Ortho` at `sine = 0` — **a whole turn,
the identity, the least turn there is** — while the variant it assigned means *the most turn there is*.
The doc comment said so out loud without noticing: *"`Ortho` at a whole turn, where nothing turns."*

A rotation's stored face is its **cosine**. Repaired, with both arms tested: the identity now reads
`Cohere` (it stores everything), the quarter turn reads `Ortho` (it stores nothing), the half turn
reads `Anti`, and a shallow turn reads `Cohere` while still turning — so the hand is not a proxy for
*does it turn at all*.

**This is what an audit is for.** The station could have been written as a repair with a foregone
conclusion; posed as a measurement it found a real defect in a different place than the one it was
looking at.

## 3. Station three — four measured document repairs

- **`CLAUDE.md`'s `P/poly` derivation.** The claim that *"a finite table is the advice model
  `NP ⊆ P/poly`"* conflated one table with a length-indexed family. A single finite table says nothing
  about `P/poly`; what would establish it is a polynomial-size circuit **for every input length,
  correct on every instance of that length**, and a full truth table is normally exponential. The
  bar's conclusion survives; its derivation is repaired.
- **`canon/THE_TRAFFIC_SYSTEM.md` asserted an absence that had expired.** It said `deferred_arrivals`
  *"is retained and never read."* Measured 2026-08-17 by
  `grep -rn "deferred_arrivals" --include='*.rs' crates soma`: `approach_front.rs` reads it —
  `front`, `closing` and `approach` are all taken over it — and `derivation_capacitance.rs` reads it
  at three sites. **The sharper statement the stale one was reaching for is that it is read and never
  routed on**, which `approach_front`'s own header states as a refusal.
- **`canon/THE_CORRESPONDENCE_ATLAS.md` could not be entered on its own junction machinery.** Measured
  before the repair: `grep -c -iE "impedance|admittance|matched junction|standing wave"` → **0** over
  the whole file. Six cards added, plus a `NON-EQUIVALENCE` recording that **a matched junction is not
  an aligned pair of directions** and that joining `T + Γ² = 1` to `cos² + sin² = 1` would be joining
  two tautologies. This is the load-bearing repair: in one day both an external sweep and the
  assistant built a false identification on the junction law, and the index that exists to prevent
  exactly that could not be entered.
- **The record of earlier today carried the refuted half-discharge**, and its §6 is corrected in place
  with the adjudication that refuted it.

## 4. Station four — the committed step

`leader_quadrature::{CommittedStep, CommittedTransport, chain_of}`.

**What was standing:** `integrate_by_leaders` has composed two determination laws since it was
written. `Found` re-reads the material at its tip and spans one grain — a closed loop. `Ride` is
licensed **only** by a run of exact agreement and then extrapolates one jet across the whole reach
**with no landing check** — ballistic, its error legible at the next tip, where the residual revokes
the licence and refounds the axis.

**What was absent**, measured 2026-08-17 by `grep -rn "impl Relating for" --include='*.rs' crates soma`
→ **3**, and neither was among them. They lived inside one integrator and `Chain::compose`,
`defect_against`, `holonomy` and `remainder` could not see the growth at all.

### The question no chain in this tree could ask, and its answer

Two growths over one material, one that never rides and one that does:

```text
    discipline     extensions    found  ridden   obstructions         area
    GrainOnly              12       12       0              2         51/8
    GermBounded             8        6       2              2         51/8

                                  winding      uninspected
    straight (never rides)           51/8                0
    through   (rides)                51/8                1

    the cocycle defect:              winding 0     uninspected −1     closed: false
    is_rebase:                       straight true     through false
```

> **The windings agree exactly and the committed remainders do not.** A chain carrying only the
> running sum would report these two growths as identical — **the difference between a closed loop and
> a ballistic commitment is invisible to the quantity being integrated.**

That is a *transport* defect rather than a value defect, and it is the determination-law mismatch the
plan asked for, returned in one coordinate by machinery that already existed.

### And the hand agrees with station two without being made to

```text
    index     kind       span        winding       residual     hand
        0    found        1/4           5/16              0    ORTHO
        1    found        1/4           7/16              0    ORTHO
        2     RIDE        1/2            5/4              0    ORTHO
        3    found        1/4          15/32          11/32   COHERE
        4    found        1/4          13/32              0    ORTHO
        5     RIDE          1              1              0    ORTHO
        6    found        1/4            5/4         −37/32     ANTI
        7    found        1/4            5/4              0    ORTHO
```

Every committed step reads `Ortho` — it stored nothing, which **is** the run of exact agreement that
licensed it — and every refounding step does not, so the hand reads the material rather than being a
constant wearing an enum. Both in-plane hands occur.

**One assumption was refuted by its own test.** The first version asserted that the step *immediately
before* a ride also reads `Ortho`. It does not: measured, a preceding step reads `Anti`. A
`RefoundingObstruction` is attributed to the extension whose **founded axis** failed, and that index is
not the index of the tip at which the failure was discovered, so the residual sits one step from where
a naive reading expects it. That offset is a fact about the growth's own bookkeeping and is reported
rather than asserted away.

## 5. What this enables, and what it does not

**Eros can now price a move before taking it.** The refusal at `k = 64` was typed, named its
coordinate, and happened before the cost. That is the precondition for cost-aware routing, and it
arrives without a governor: `ExactOrdering::Open` retains both carriers rather than tie-breaking, and
the metric that decides where the product order is `Open` is a **receiver's declaration exhibited in
the return**.

**And the FOUND/RIDE asymmetry is now measurable.** *"FOUND pays curvature; RIDE is cheap because the
terrain already paid"* is a claim about two costs and neither had ever been measured. Both organs now
count, and station four's chain composes them — so `work(FOUND)` against `work(RIDE)` on one material
is an experiment rather than a slogan. **This record does not run that experiment and does not claim
its outcome.**

**What it does not do.** It does not make anything faster; pricing a route is not taking a cheaper one.
It does not wire a prediction into a routing decision — `approach_front` refuses that in writing, and
whether a predicted crossing may determine a transport without becoming a governor is a policy
question and is Brandon's. And the `k^4.03` figure is about *this* elimination on *this* material: it
says nothing about any other organ's cost, and the width half of the model that produced it is refuted
and owed a repair.
