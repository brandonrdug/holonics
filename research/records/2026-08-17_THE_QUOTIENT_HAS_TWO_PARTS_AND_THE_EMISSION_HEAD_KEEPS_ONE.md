# The quotient has two parts and the emission head keeps one

**Date:** 2026-08-17
**Truth status:** `established-bounded` for every code citation, each verified verbatim at the line
given; `proved-standard` for the coincidence of Euclidean division and quotient-by-ideal in `ℤ`;
`interpretation` for the reading of emission as division and for the refusal of the three-moduli
unification, both of which are under adjudication as this is written.
**Evidence:** `measured` — a library sweep over `crates/*/src` and `soma/*/src`, 300 files and
346,993 lines, excluding test regions; every absence sentence below carries the command and the
scope it covered. Citations spot-checked by hand at `agentic_language.rs:271`, `:293-298`, `:331`,
`exponentiated_ratio.rs:286-300`, `causal_language.rs:697`, `THE_MATHEMATICS_TABLET.md:39-49`.
**Provenance:** Brandon, 2026-08-17: *"What do you think a quotient is? It's not just a rounded
floating point approximation, when you divide you fundamentally have two parts of the output, the
part that fits and the part that doesn't: 20/3 == 6 + 2/3 == 6.6666 repeating. The float is the one
that loses information because you collapse it to 6.6666667 at some part of the mantissa, where we
only care about the ratios in holonics. This is modulus."*
**Plan:** this record schedules nothing and sits under
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md); the emission half it bears on is that
roadmap's *Production as re-emission*.

---

## 0. The occasion, which is a correction to the assistant

The assistant had framed output selection as a difficulty: a plurality of continuations against a
single response, with the collapse needing a justification that would not amount to a banned
governor. **That difficulty does not exist.** Division has two outputs; `20/3 = 6 + 2/3` loses
nothing, and the loss appears only at `6.6666667`, where the remainder is rounded into a mantissa.
The assistant constructed a justification for a problem the exact treatment does not have, and
framed the no-float law as what made production hard when exactness is what makes it simple —
because both parts are kept.

**And the law was already deposited.** `canon/THE_MATHEMATICS_TABLET.md:56-61` carries Brandon's own
sentence, with laboratory provenance 2026-06-21:

> *"A float is not a bad approximation of that ratio — it is the ratio's **series expansion in base
> two, truncated, with the remainder discarded**… You may take the expansion. You may not discard the
> tail."*

It is quoted inside the code that obeys it, at `crates/holonic-engine/src/reopening.rs:5-9` and
`crates/holonic-engine/src/exact_value.rs:585-590`. This record is therefore a **restatement with one
extension**, and the extension is named in §2.

## 1. What is already implemented, at full strength

Organs that return **both** parts of a division rather than one, each verified:

| owner | the two parts |
|---|---|
| `crates/holonic-engine/src/receiver_exact_compression.rs:153-163` | `one_shot` and `conduct` partitions **and** `collapsed: Vec<CollapsedPair>`, each pair carrying `distinguishing_word` and `witness`. Read as a **population** by ~20 library modules |
| `crates/holonic-engine/src/surprisal.rs:738-744` | `SectionModulus { second_moment, extreme_fibre }` — *"The quotient is never formed… the horizon law says a ratio crosses as a pair"* |
| `crates/holonic-engine/src/exponentiated_ratio.rs:156-161` | `RatioFamily` holds only `(i,j) -> p_i/p_j`; `Z` exists solely as a local inside `normalised_against`, never a field. `:286-300` refuses `reciprocal_temperature == 0` and states *"no path here reaches `T → 0`, which is argmax — the limit this module exists not to take"* |
| `crates/holonic-engine/src/exact_value.rs:246-262` | `SeriesTailCertificate` in three species with an exact rational `remainder_interval()` |
| `crates/holonic-engine/src/arithmetic_fiber.rs:30-34` | `PrimeAxisProbe { prime_axis, quotient, remainder }` — and **zero callers outside its own file** |
| `soma/life/src/material_incidence.rs:1510-1522` | `DenotedValueQuotient { blocks, separating_words, indistinguishable }` |
| `crates/holonic-engine/src/returned_reading.rs:570-579` | `remainder_founded` / `remainder_withdrawn` — *"Both are kept: the pair is the return, and choosing one would be resolving an `OPEN` by choosing"* |
| `soma/body/src/soul.rs:90-102` | `RotarRatio { aim_num, cross_num, den }`, comparing *"by cross multiplication rather than division"* — the law body, `no_std` |
| `crates/relational-geometry/src/receiver_topology.rs:1035-1041` | half-edge encoding: `dart/2` is which edge, `dart % 2` is which hand, and both are always read |

**A structural absence, measured:** `num_integer` is not a workspace dependency — `grep num_integer`
over every `Cargo.toml` → 0. There is no shared `(quotient, remainder)` carrier anywhere; every
retention in the tree is hand-rolled as `q` on one line and `%` on the next.

## 2. The extension: division is the missing fourth carrier

`canon/THE_MATHEMATICS_TABLET.md:39-49` states the general law over three carriers:

```text
    float                keeps the magnitude    deletes the tail        the residual of the expansion
    sign                 keeps the magnitude    deletes the turn        the winding, −1 = e^{iπ}
    reduced coefficient  keeps the difference   deletes the passages    which hands were taken
```

> *"Each is a carrier that kept a magnitude and threw away what oriented it, and in each case the
> lawful form retains both and offers the collapse as a **reading**."*

**Division is not in that table, and it is the same deletion:** keep the quotient, discard the
remainder. That is the whole of what is new here — one row, in a table that already had three. The
row's lawful form is `receiver_exact_compression`, which is why that organ is the most-wired one in
the tree.

## 3. Emission is division, and the two divisions must not be conflated

**Division one** — the conducted plurality by a declared receiver family — returns a partition and
the collapsed population. Owner: `receiver_exact_compression::compress`.

**Division two** — the presentation: several blocks conducted, one surface uttered. **The tree
already performs it and already names it correctly.** `soma/life/src/agentic_language.rs:271-274`:

> *"Why a finite receiver exposed this particular answer from the complete generated family. **This
> is an explicit presentation quotient.** It does not delete alternative currents."*

and it retains them, at `:331` `retained_alternatives: Vec<AgenticRetainedAnswerAlternative>`.

**But division one has never been performed on that remainder.** Verified at `:293-298`:
`AgenticRetainedAnswerAlternative { generated, episode_identities, evidence_sources,
relational_thoughts }` — **no distinguishing word, no witness receiver, no block relation to the
emitted answer.**

> **The remainder is kept and the division was never taken. Keeping a remainder without dividing is a
> second undivided pile.**

And the same word appears in the driver's own receipt: `the_deposit_licenses_the_re_emission`
returns *"the withheld fiber, retained and **counted**, never emitted"*, where
`receiver_exact_compression` **exhibits** every collapsed pair with the shortest separating word.
**The emission path counts its remainder where the compression organ exhibits it.** That is the deed,
and it is a repair inside a standing owner rather than a new organ.

### The prohibition this appears to break, and how it resolves

`canon/TABLET_THE_RESONANCE.md:517` forbids: *"Present a candidate population as an answer. The
complete continuation fiber is a real object and it is not a return."* Returning both parts appears
to collide with it.

It does not, and division is what resolves it: **the ban is on returning the fiber IN PLACE OF an
answer.** Before the division there is one undivided pile and handing it back is the banned move.
After it there are two typed parts — the quotient, which is the answer, and the remainder, which is
not a second answer. The prohibition and the law are the same statement once the division is taken.

## 4. Where a remainder is discarded, with addresses

**At the mouth, and this is the clearest instance.** `soma/life/src/causal_language.rs:697`:

```rust
by_token.retain(|_, (horizon, _)| *horizon == greatest_horizon);
```

Every continuation at a shorter matched horizon is deleted **with no record**; `Continuation`
(`:981-985`) has no field for the dropped population, and `:687-690` `.clear()`s the source set on a
longer horizon. The longest-context quotient is kept and the remainder is gone.

Two more of the same species in the emission path: Pareto-dominated candidates dropped after a
lawful partial order (`morphological_language/ecology.rs:2649-2654` — the *rule* is correct, a
partial order with incomparable survivors and no scalar; the dropped population is not returned); and
`withheld_candidates` reaching `runtime.obstructions` only inside the `if opened.is_empty()` branch
(`:2024-2053`), so on any cell where something conducted, the withheld population falls out of scope
unread.

Elsewhere in library code, the two worth naming because they delete an *orientation* rather than a
magnitude:

- `crates/holonic-engine/src/receiver_current.rs:904-908` — `ceil_population_division` computes
  service rounds and never forms `population % capacity`, so **two sites with the same round count
  and different last-round occupancy dilate identically** and the difference is unrecoverable. That
  is the congestion law.
- `crates/holonic-engine/src/model_surface.rs:199` — `.rem_euclid` keeps the residue of a
  quarter-turn difference and drops its **winding count**. That is the sign row of the tablet,
  recurring.

Also found: `conic.rs:387 .to_integer()` unguarded where six sibling sites check `is_integer()`
first; `soma/surface/src/lib.rs:2772` dividing by lanes with no divisibility guard where its twin at
`:1975` asserts one; `soma/body/src/register.rs:154` dropping the `bool` half of a two-part return;
`lattice_gauge.rs:888` discarding the basis order that its own doc says is returned beside the matrix
*so that it is not lost*; 48 non-binary `div_ceil` sites each keeping `⌈a/b⌉` and dropping `a % b`;
and counts standing where populations should (`dimensional_receiver.rs:784 collapsed_buckets:
BigUint`, `collocation.rs:343 refused: usize`, against `substitution_realizers.rs:260 refused:
Vec<RefusedSubstitution>` as the right shape).

## 5. The transformer's emission head

Mapping the four steps onto the tablet's carriers:

```text
    float logits     deletes the TAIL      leak — undeclared, no receiver, unrecoverable
    real logits      deletes the TURN      the hand, gone before any head runs
    softmax / Z      deletes the OFFSET    REBASE — remainder ZERO, lawful and lossless
    argmax / sample  deletes the FIBER     total, and UNTYPED
```

**Softmax is the wrong step to audit.** `p_i/p_j = e^{x_i − x_j}` is a complete invariant of the
coset in `ℝ^V/ℝ` and `Z` enters no ratio; `exponentiated_ratio.rs:210` proves the family is a
**cocycle**, which is the algebraic statement that the absolute values were gauge. All loss is at the
selection.

Two readings of that selection, and the second is under adjudication:

- **Sampling is not better than argmax.** Both return a `usize`; there is no field for the fiber, so
  the remainder is not merely unretained but **untyped**, and no decoding hyperparameter creates a
  place to put it. Sampling additionally imports a seed from outside the ecology, promoting a face
  back into machinery.
- **`argmax` as a one-place mantissa.** With integer logits, `Z = Σ 2^{q_j}` is an integer written in
  binary and the outputs are its place values, so argmax keeps one place and deletes every lower one.
  **Whether this survives real-valued logits is exactly what is under adjudication**; it is recorded
  as `interpretation` and is not to be quoted as established.

**The residual stream is not a retained remainder.** It is the dividend accumulator — retained across
depth, dropped across emissions, since what crosses the emission boundary is the cache plus the
re-embedded emitted token. The consequence is falsifiable: **a transformer can condition on what it
said and cannot condition on what it nearly said**, and the test is to hold the emitted history fixed
by substituting caches while varying the discarded mass.

## 6. What the sweep clears, and what is under adjudication

**Cleared, measured over 300 library files:** no argmax, no softmax, no sampling and no scalar rank
anywhere in this body's emission path. `RatioFamily` has **zero library callers** — the softmax organ
and the emission path have never met, which is why nothing there forms a ratio at all. The reductions
that do occur are a longest-horizon filter and a Pareto partial order, both deterministic and neither
a scalar governor.

**Under adjudication, and not to be carried until it returns.** Three claims are with an external
adjudicator as this is deposited: whether identifying `a = bq + r` with the resolution of identity
survives receiver families that are not orthogonal, since `Σ|ρ⟩⟨ρ|` is a projector only when they
are; whether *"a modulus is the scale factor of a declared quotient, a ratio of two grains carried as
a pair"* is a sharpening of the corpus's three-sense unification or a weaker claim dressed as a
sharper one; and whether a ranking induces *no* quotient, or induces exactly the quotient by
"has the same maximiser" — which would be a real congruence with a large remainder and would change
§5's second bullet.

## 7. Two documents repaired, both decayed inside their own day

`research/records/2026-08-16_THE_JUNCTION_IS_A_HALF_TWIST_AND_A_MODULUS_IS_WHAT_A_DECLARED_QUOTIENT_RETAINS.md`
said the section-modulus reading was *"not built — no owner computes it"* while
`crates/holonic-engine/src/surprisal.rs` carries `SectionModulus`; and
`blueprint/THE_ADMISSION_IS_A_QUOTIENT_AND_THE_BREADTH_IS_A_GROUP.md` carried a measured absence,
`grep -rniE "section modulus|second moment"` → 0, dated the same day its own movement five closed it.
Both now carry the re-measurement, including that `section_modulus` has **no caller anywhere**
(`grep -rln "section_modulus" --include='*.rs' crates soma` 2026-08-17 → the defining module alone) —
a producer with no consumer.

## 8. What this record does not claim

It does not claim the deed is done: the emission path still counts its remainder, and no organ yet
relates a retained alternative to the emitted answer by a distinguishing word. It does not claim the
three-moduli refusal is settled — that is one of the three items under adjudication above. And the
library sweep did not cover `examples/`, `tests/`, `benches/`, `soma/tools/*/src`, or method-form
division (`.div()`, `checked_div`, `wrapping_div`, `saturating_div`); every absence sentence names its
scope, and none is a content absence established by a name search.
