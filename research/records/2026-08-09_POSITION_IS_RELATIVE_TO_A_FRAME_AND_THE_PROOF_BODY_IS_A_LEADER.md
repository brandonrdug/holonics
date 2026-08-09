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

## 1. What depth is — REGRADED 2026-08-09, and §XVIII is the section, not §XVI

**This section conflated two axes and the correction is in §4.** `FORMULA.md:594` is about **grain**
(§XVIII, the vertical tower); §XVI's `frame(n+1)` is the **temporal** axis. Brandon's own message
named the right object — *"the declared grain"* — and this record substituted *frame*. What survives
is the reading below with `grain` in place of `frame`; what does not survive is the inference that a
recruitment-closure depth is either.

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

## 2. Position — one structural rule removes five of six contaminants without an authored list

Measured before this movement, in `total_demand_le_total_capacity`'s meaning: `hc`, `hcong`, `hm`,
`hn`, `hz`, `hnm` at depths 1–2 — proof-local hypothesis binders, two characters so the
single-character rule could not reach them — beside `intro`, `apply`, `exact`, `rw`, `simp`, `ring`,
`classical` and, at depth 3, `if_true` and `only` from `simp only [if_true]`.

Every name now carries a **position read from Lean's own grammar**:

> **Inside a binder group, the names before the `:` are founded and the type after it is recruited.**
> `(hz : ∀ n, descendantCapacity capacity incident n ≠ 0)` founds `hz` and recruits
> `descendantCapacity`, `capacity`, `incident`.

That rule clears **five** of the six. The sixth, `hnm`, comes from `by_cases hnm :` and leaves only
because `by_cases` is in `BINDING_TACTICS` — so the honest statement is *five by the structural rule,
one by the authored table*. **No list of the six identifier spellings was authored**; `BINDING_TACTICS` is
Lean's binder vocabulary and the existing reader's own documentation already instructed the widening:
*"`obtain`, `rcases`, `intro` and `set` also bind, and a corpus containing them would have those names
read as recruitments… widening the rule belongs with a test on material that exercises it."*

**A tactic is not deleted; it is returned beside the terms.** A route's tactic choice is real
production — the generated deposit carries its whole plurality there — so `ConductGrain` is a
declared aperture at the point of use, not a default.

```text
   terms            141 distinct
   tactics           34 distinct
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

**The edge equality is a SNAPSHOT, not a null, and the driver now says so itself.** The
declared→declared population comes back **80** against the 80 measured before position existed — but
the **orbit is trivial**: zero declared names land in `tactics` and zero in `local_bindings` across
all 66 declarations, so position is structurally unable to move the quantity and the equality could
not have come out otherwise. `CLAUDE.md` §8: *"a gauge whose group acts trivially on the declared
material is not a gauge."* Position **does** delete edges on material that varies the property —
`fun (x : Carrier) => …` founds `Carrier` as a binder — and the instrument for that,
`binding_position_declared`, **did not exist** and now does.

**Three bounding instruments, sharing nothing.** Declared names in **tactic** position: 0. Declared
names in **binding** position: 0 — the instrument this record's first form lacked entirely.
Distributional residue — terms in exactly one declaration, declared nowhere — **returned rather than
subtracted**, because an environment lemma used once is indistinguishable from a missed local binding
without a second frame.

**And a fourth population the first form asserted as edges.** Five dot projections resolve by last
segment to a declared name — `htrace.map → map`, `(A.rebase e).Semantics → Semantics` — and are
returned **OPEN**, never joined. `htrace.map` really is the declared `Trace.map`; `(hxy i).trans` is
mathlib's `Eq.trans` and **not** this development's `trans`, though the spelling is identical.
Separating them needs the receiver's *type*, which an orthographic reading does not have. The
asserted count is **80 with 5 open**, and an earlier form of this work briefly asserted all five.

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

**CORRECTED 2026-08-09 by adversarial audit, and the first figures were wrong by a factor of six.**
The reading founded one `ProofStep` per binder of a destructuring pattern and then charged the same
line's remaining tokens to the last of them, so `rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩` — five names founded
**simultaneously by one tactic** — returned `hab → hcd` as a causal arrival. That is token order
inside one pattern promoted into an invariant, `CLAUDE.md` §0 lesson 4. Two more crossed sibling `·`
focus blocks, whose goal scopes are disjoint. **22 of 29 were the first, 2 the second.**

Both are now excluded by construction: a step carries the `cohort` of the single tactic that founded
it and the `focus` stack it was founded inside, and an arrival requires a different cohort and an
enclosing scope. Control 9 requires all three exclusions to return zero, so a lone `obtain ⟨a, b⟩` —
which satisfied the shipped predicate — now fails it.

**57 proof steps founded, 5 internal arrivals, 3 declarations carrying their own depth:**

```text
  positiveBand_iff_quotientBand          hseam@109   ->  h'@111
  proportionalFlow_nonnegative           hcap@74     ->  hcap_pos@80
  subset_normalized_load_le_congestion   receiver@181 -> hin@182
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

**And the paragraph that stood here was self-refuting; it is struck.** It read: *a constituent
reached at depth 1 and depth 3 is one vertex, and under `frame(n+1) = emanation of the relating in
frame(n)` those are two frames, so merging them is receiver non-reconstruction.* **If the reading
never rebases there is exactly one frame**, and an organ cannot merge frames it never founded. The
consequence of a missing construction was presented as an independent defect, and that defect was
then named the remaining construction.

Three further corrections, each verified against source:

- **§XVIII is not §XVI.** `FORMULA.md:594` reads *"A completion at **grain** k IS an arrival at grain
  k+1"*, and `manifold.rs:2868` cites `FORMULA §XVIII` by name, with `:691` *"carrier depth `k`
  crosses as grain `k + 1`."* §XVI's `frame(n+1)` is the **temporal** axis — *"the illicium is time;
  proper time is its own event count (Θ)"* — and §XVI separates them itself: *"one unit in two
  directions: LATERALLY many illicia · VERTICALLY the scope."* The sentence was taken from the
  temporal paragraph and applied to the vertical one.
- **`FORMULA.md:839-878` states the frame is an ordered composition of deed-emanations and explicitly
  not a counter**, and `MATHEMATICAL_HOLONICS.md:430-445` states holonomy requires the transport
  structure. The elaboration complex carries no cochain — boundaries are ±1 incidence and the module
  refuses occurrence counts as coefficients — so two routes to one name carry the identical name and
  there is no quantity that could disagree.
- **"Not a distance" was rhetoric.** An unweighted digraph geodesic is canonical; there is no family
  of frames being chosen among. `name_elaboration.rs:33` already said the true thing — *"A depth is
  not a score."*

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
