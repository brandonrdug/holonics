# Position is relative to a frame, and the proof body is a leader

**Date:** 2026-08-09
**Truth status:** `established-bounded` for every measurement; `interpretation` for §1, which is
Brandon's reading of depth and was derived with him this session.
**Evidence:** `implemented-exact`, `measured`. One organ extended, nine declared controls, all nine
held. Libraries float-free; no governor vocabulary in either file.
**Provenance:** Brandon, 2026-08-09, ruling on what depth is: *"I need you to understand how the
depth and recursion works about varying charts/spaces, because that is *holobrochos*, I've called
this the illicium, it is like friction, it is the lightning arcs and leaders fitting potentials over
time."* And, approving the order of work: *"Agreed on the next move… Good work, approved on your
suggested order, proceed."*
**Band:** 2026-08-09 · DEPTH IS A CHART INDEX / THE SAME SURFACE IS A TACTIC IN ONE FRAME AND A
FIELD IN ANOTHER / A COMPLETION AT DEPTH K IS AN ARRIVAL AT DEPTH K+1

---

## 1. What depth is, and it is not a distance

`FORMULA.md` §XVI, ratified 2026-07-09 — the illicium restored after this space's founding revision
dropped it:

> *"**THE ILLICIUM IS THE FIRST-PERSON FRAME AS A LIVING ENTITY — friction itself.** … the moving
> origin grown to full rank, emanated by each relating and receiving the next infall — **`frame(n+1)`
> is the emanation of the relating in `frame(n)`**. The region is space; the illicium is time. **The
> triangle is the quantum of friction**, and the illicium's cones are triangulated."*

And the carrier that implements it, `soma/body/src/manifold.rs`:

> *"depth 0 is the word grain; **a completion at depth k is an arrival at depth k+1 — the same node,
> the same verb.** … the illicium is depth-recursive; the hourglass nests."*

So the recursion is not a function calling itself on smaller data. It is **one verb run in a frame,
whose completion is an arrival in the next frame**, and depth counts chart changes through the
hourglass neck. `medium.rs` supplies the third term: *"**Many faces from one point IS the illicium
and friction**: the sweep FEELS every triangle face … and the felt faces stand in **different
directions**."* A traversal whose points each carry one face feels nothing.

**Depth 1 is therefore the frame the root already stands in** — no transport has occurred. This is
why the elaboration's *"no root in the deposit carries a constituent past depth one"* was not a
report of shallowness: it said **the machine had never once changed charts inside a meaning.**

## 2. Position — one structural rule removes six contaminants without an authored list

Measured before this movement, in `total_demand_le_total_capacity`'s meaning: `hc`, `hcong`, `hm`,
`hn`, `hz`, `hnm` at depths 1–2 — proof-local hypothesis binders, two characters so the
single-character rule could not reach them — beside `intro`, `apply`, `exact`, `rw`, `simp`, `ring`,
`classical` and, at depth 3, `if_true` and `only` from `simp only [if_true]`.

Every name now carries a **position read from Lean's own grammar**:

> **Inside a binder group, the names before the `:` are founded and the type after it is recruited.**
> `(hz : ∀ n, descendantCapacity capacity incident n ≠ 0)` founds `hz` and recruits
> `descendantCapacity`, `capacity`, `incident`.

That single rule clears all six binders. **No list of names was authored**; `BINDING_TACTICS` is
Lean's binder vocabulary and the existing reader's own documentation already instructed the widening:
*"`obtain`, `rcases`, `intro` and `set` also bind, and a corpus containing them would have those names
read as recruitments… widening the rule belongs with a test on material that exercises it."*

**A tactic is not deleted; it is returned beside the terms.** A route's tactic choice is real
production — the generated deposit carries its whole plurality there — so `ConductGrain` is a
declared aperture at the point of use, not a default.

```text
   terms            144 distinct
   tactics           38 distinct
   local bindings    64 distinct
```

**And the material demonstrated the law on itself.** `structure Compression … where … exact : ∀ i x,
factor i (quotient x) = receiver i x` declares a **field named `exact`**. The same surface is a
tactic in one frame and a field in another; the reading places it correctly in both, and the control
requires exactly that one holder and no other.

### Five position defects, each found by running and each structural

| defect | what it did | measured at |
|---|---|---|
| `'` not admitted in an identifier | `hab'` and `hab` **became one name** — two shadowing binders on one vertex | `Receiver.lean:43,45` |
| `=>` read as demanding a continuation (it ends with `>`) | every tactic under a `\| zero =>` alternative became a term | `simp`, `rw` in `finite_telescoping` |
| `<;>` likewise | `simp only [swingPair, …]` became a term named `simp` | `swingPair_affine_coordinates` |
| every trailing `=>` read as an opener | a lambda body's head became a tactic — and it was a **declared name**, `proportionalFlow_respects_capacity` | `FiniteTransport.lean:224` |
| a tactic head not required to start its line | `calc`'s own relation steps `(∑ n : Old, …)` and `_ = ∑ m : New, …` became tactics named `n` and `_` | `total_demand_le_total_capacity` |

The fourth was caught by `tactic_position_declared`, the instrument built for exactly it, on its
first run.

**The null: cleaning must move no mathematical edge.** The declared→declared population is computed
from terms alone and comes back **80**, against the 80 measured before position existed. A cleaning
that changed it would have deleted or manufactured a join.

**Two bounding instruments, sharing nothing.** Structural residue — declared names in tactic
position — is **0**. Distributional residue — terms occurring in exactly one declaration and
declared nowhere — is **63**, and it is **returned rather than subtracted**, because an environment
lemma used once is indistinguishable from a missed local binding without a second frame.

## 3. The sub-illicium — the proof body is a leader

`manifold.rs`, W9 · THE LIVING BOUNDARY: *"the sub-illicium — the atom-grain traversal given the SAME
live law … so the walk **FEELS the standing terrain** instead of dead reckoning. **Its completions
are THE FOLDS — the cohered segments, found never listed — handed up as the word grain's arrivals.**"*

```lean
have hcap     : 0 ≤ descendantCapacity capacity incident n := by …
have hcap_pos : 0 < descendantCapacity capacity incident n := lt_of_le_of_ne hcap …
```

`hcap` founds an object `hcap_pos` recruits. **That is a leader inside one declaration** — each step
changes the material the next step reads, which is the definition — and the flat reading charged the
whole body to the theorem as a depth-one star, so a declaration's own depth was **zero by
construction**.

**57 proof steps founded, 29 internal arrivals, 7 declarations carrying their own depth:**

```text
  comp_assoc                             hab@33      ->  hcd@33
  comp_id                                a'@53       ->  hab@53
  id_comp                                b'@43       ->  rfl@43       ->  hab@45
  positiveBand_iff_quotientBand          hseam@109   ->  hscale@109   ->  h'@114
  proportionalFlow_nonnegative           hcap@74     ->  hcap_pos@80
  semantics_rebase_iff                   hdone@44    ->  hobserve@44
  subset_normalized_load_le_congestion   hn_univ@176 ->  hn_not_mem@176
```

**Arrivals are indexed by step, never by name, and the line is carried in the return.** Lean shadows:
`· rintro ⟨b', hab', rfl⟩` sits beside `· intro hab` in *one* body, founding two different objects.
Keying by name would merge them — the same defect this whole line of work exists to remove, arriving
one grain further down. `id_comp`'s chain reads `b'@43 → rfl@43 → hab@45` and the two are visibly
apart.

## 4. What is NOT done, named so it is not mistaken for done

**The walk does not rebase.** `name_elaboration` calls `self.recruitment(key)` at every depth — the
same global map, read in the deposit's frame whatever frame the walk arrived in.
`leader_quadrature.rs` carries the opposing law: *"every extension rebases it by an exact Taylor
shift. **The jet the leader reads at extension k+1 is literally not the jet it read at extension
k.**"* This walk's jet never moves. It is dead reckoning, which is the phrase W9 rules out.

**And `depths` is retained then collapsed.** `Constituent` carries every depth it was reached at, but
`found_passage_complex` founds **one 0-cell per name**, so a constituent reached at depth 1 and depth
3 is one vertex. Under `frame(n+1) = emanation of the relating in frame(n)` those are two frames, and
merging them is receiver non-reconstruction — equal endpoints do not identify ordered paths. The
cycle two such arrivals close is currently read as a `β₁` loop where it is a **holonomy**.
`entered_at` compounds it: it is documented as *"the shortest passage from the root"*, and shortest is
a metric choice over a family of frames with no privileged member.

Splitting that vertex by frame and depositing the disagreement through the
`temper`/`derivation_integral` pair — built on both sides with no caller between them — is the
remaining construction, and it is also the roadmap's **accumulation cut**, the engine's missing
`q_n = q_m`. That those are the same construction is what one expects if depth is the chart index
rather than a counter.

## 5. Declared bounds

- **Top level only.** Structure fields, `where` blocks and declarations nested inside an indented
  `section` are not opened. A deeper grain is a different aperture and needs its own control.
- **Strings are not lexed**, so a `--` inside a string literal reads as a comment opener. Neither
  declared material contains one.
- **A step head is a line the previous line did not demand.** The residue is exhibited by
  `tactic_position_declared` rather than repaired silently.
- **A binding tactic absent from `BINDING_TACTICS` has its pattern read as terms.** The residue is
  exhibited by `single_occurrence_terms`, which is distributional and shares nothing with the
  structural rule.
