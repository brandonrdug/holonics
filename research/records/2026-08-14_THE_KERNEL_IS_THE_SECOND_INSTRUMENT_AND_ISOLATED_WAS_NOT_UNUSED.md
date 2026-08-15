# The kernel is the second instrument, and `isolated` was not `unused`

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `established-bounded [implemented-exact]` for all three constructions and every
control, measured this day by running them; `measured` for each census and orbit; the third item's
comparison returns **UNDETERMINED** and is recorded as such.
**Occasion:** Brandon: *"We can proceed with those, supposing you aren't drifting or hedging."*
Three items were named and all three are complete: the ratio aperture into the deposit, a later
theorem that is not a restatement, and the ground-truth cross-check.

---

## 1. The deposit is now frame-independent

`RevisionAperture` was a **count** — `minimum_asking_pairs` — and a count is a magnitude. The
2026-08-14 gauge measurement on a real kernel return had already shown what that costs: a magnitude
aperture moved under an additive shift while a ratio aperture did not.

`RevisionAperture::at_ratio(Rat)` admits a word whose asking population, **as a ratio against the
most-asked word**, clears a declared floor. It compares two members of one population rather than
one member against an absolute level, so it is blind to any common rescaling — softmax's `x → x + c`
invariance read in the multiplicative chart. The floor is carried exactly and never divided into a
float; outside `(0, 1]` it is refused.

**Measured in the owner's own tests, where the population can be scaled without touching the
material** — the clean gauge:

```text
  population [12, 6, 3, 1] scaled fourfold to [48, 24, 12, 4]
    count floor  >= 4     admission MOVES
    ratio floor  >= 1/4   admission UNMOVED, and is [true, true, true, false] either way
```

Both arms are asserted, so the contrast cannot be vacuous.

**And it retires a workaround the consuming driver had written into itself.**
`the_deposit_changes_what_unseen_material_costs` samples every body by stride to a declared common
extent, on the stated ground that *"the absolute aperture threshold is comparable"* only then. That
is the tell: a threshold that needs its material normalised before it can be compared is a
magnitude. Measured on the real material, at two extents:

```text
  stride-sampled   340 lines   count admits 102   ratio admits 5
  natural extent   371 lines   count admits 104   ratio admits 5
  across the two extents:  count MOVED    ratio UNMOVED
```

This second reading is a **material** change and not a pure gauge — the exact gauge is the unit test
above — and it is reported as the measurement it is. The ratio aperture at `1/4` is also far
narrower here (5 words against 102), which is a real difference in what it selects and is stated
rather than buried.

---

## 2. The later theorem is no longer a restatement, and the transformed one is admitted

The closed-cycle deed carried a bound: its later theorem was the first theorem's statement under
another name, so *"rides the deposit"* meant **reachability** and nothing more. Three later theorems
now run, each at a different distance from what was deposited, each with a statement that appears
nowhere in the corpus, each scoped to the self-emanated file alone.

**And closing that bound exposed a larger gap first.** The initial run returned an identical
`0 admitted of 15` for all three — *including the restated floor case, which the deposited theorem
closes outright.* The cause is the emit half of the loop:

> **The deposit changed what the BODY can reach and never reached the WORLD.**
> `receiver_load_under_capacity` was self-emanated — it lived in standing and in no file the kernel
> imports — so every path naming it failed to elaborate. A body that founds a theorem and then
> submits into an environment which has never heard of it has not closed anything.

Materialising the admitted proof into the later environment closes it, and that is not a
convenience: it is what *the deposit becomes part of the terrain later current runs on* means when
the terrain is a kernel.

```text
  the world now carries, because the body founded it:
    theorem receiver_load_under_capacity … :=
    by exact proportionalFlow_respects_capacity demand capacity incident hc hcong m

  restated     admitted  4 / 15    exact receiver_load_under_capacity demand capacity incident hc hcong m
  transformed  admitted  2 / 15    simpa using receiver_load_under_capacity demand capacity incident hc hcong m
  composed     admitted  0 / 15    15 distinct refusals
```

**The transformed row is the one that matters.** `¬ (capacity m < ∑ …)` is not the deposited
statement — no retrieval closes it, and the kernel had to supply `not_lt`. The body reached it only
because of the deposit, and the ablation removes the reach. That is conduct carried across a
statement the corpus does not contain.

**The bound that remains, stated exactly.** `transformed` is *equivalent* to the deposited theorem up
to one connective; it is nonidentical, not independent. `composed` is genuinely independent — it
needs a second corpus lemma the deposit does not carry — and it returns **15 distinct refusals and
no admission**, which is a real returned obstruction population on a statement nothing in the tree
states, and is reported as exactly that.

---

## 3. The kernel is the second instrument, and it corrected the reading

One instrument cannot audit itself. The move-species reading claims a causal structure; the kernel
answers a question that reading never consults — **is this move load-bearing?** Delete its line,
resubmit, let Lean say.

Declared before the run: *an isolated move should be removable more often than a connected one.*

```text
  FiniteTransport.lean   declarations 10 · moves 25 · arrivals 11 · connected 15 · isolated 10
  the unablated corpus checks CLEAN

  connected   removable 0   load-bearing 14   inconclusive 1
  isolated    removable 0   load-bearing  2   inconclusive 0
```

**AND THE ABLATION ITSELF WAS PARTLY MISAIMED, found by audit the same day.**
`ProofStep.line` is `form.line + offset` where `offset` indexes a line vector that skips blank,
preamble and scoping lines, so it assumes a contiguity the material does not have: **10,261 of
97,696 step lines across mathlib point at a line that does not carry the step's own former.** This
driver deletes raw source line `step.line`, so roughly one ablation in ten deleted the wrong line.
The verdict below is unchanged and its reason is now two reasons rather than one.
`blueprint/THE_TYPED_TRANSPORT_ATLAS.md` §1.4 carries it.

**UNDETERMINED, and that is the honest verdict rather than a failed prediction.** Not one decided
move in either population is removable, so this material carries **no variation in the property
under test**. Saying *"the two rates are equal"* would dress a degenerate material up as a finding —
the same defect as a check that cannot fail, wearing a verdict instead of a pass. The driver detects
the case by name and states no verdict.

The **inconclusive** arm is why the counts mean anything: deleting one line of a multi-line `have`
leaves text that does not parse, and a parse failure says nothing about load. Those are classified
from Lean's own words, counted, and excluded from both rates.

### What the instrument did return, and it is worth more than the prediction

```text
  isolated moves whose binder IS named later in the same body   5
  isolated moves whose binder is never named again              5
```

> **`isolated` is not `unused`.** The arrival graph joins step to step, and a declaration's closing
> term is not a step — so a `have` consumed only by the final tactic has no outgoing arrival and was
> being called isolated while the kernel plainly needed it.

Repaired in the owner. `MoveComplex::terminally_consumed` reads it off `local_bindings` minus the
founding occurrence minus the step-to-step arrivals — the uses no step accounts for — and
`MoveComplex::unconsumed` returns the population `isolated` was mistaken for. Re-measured on the
geometry file:

```text
  isolated 45 · unconsumed 15
  thirty of the forty-five are named by the closing tactic
```

**The earlier record's sentence — *"45 of 78 moves are founded and never used"* — is corrected in
place.** The count was right and the reading of it was wrong by a factor of three.

---

## What this does not claim

The ratio aperture is frame-independent and is **not** thereby better at selecting: it admits a much
smaller population here, and which aperture suits a deed is a receiver's declaration. The
`transformed` admission is equivalence up to one connective and is not an independent theorem. The
kernel comparison is undetermined on this material and licenses no statement about whether the
arrival graph tracks load — what it licenses is the correction in the last section, which is a fact
about the reading and was measured directly. No Millennium row grades any of it.
