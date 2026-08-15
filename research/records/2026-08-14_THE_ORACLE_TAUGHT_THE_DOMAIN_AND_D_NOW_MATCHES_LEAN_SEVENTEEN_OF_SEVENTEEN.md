# The oracle taught the domain, and `D` now matches Lean seventeen of seventeen

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `measured`; every agreement is against Lean's own `#check @d` with mathlib in
scope. The sample is **17 declarations across four modules** and that is the claim's bound.
**Movement:** *the declaration is a formulation node*, the third of
`blueprint/THE_TYPED_TRANSPORT_ATLAS.md`, **and its gate. COMPLETE, and the plan proceeds.**
**Owners:** `soma/life/src/lean_mathematics/syntax.rs`, `soma/life/src/lean_mathematics.rs`.
**Driver:** `soma/life/examples/the_declaration_is_a_formulation_node.rs`.

---

## 1. The gate was smaller than the plan declared, and that is a correction to the plan

`THE_TYPED_TRANSPORT_ATLAS.md` §1.3 said a consumer cannot type an application because 93.7% of
declarations inherit binders from a `variable` line absent from the carrier. **That is true of
`lean_development`'s `DeclaredForm.statement` and false of `LeanDeclarationOrgan.binders`**, which is
the carrier the emission actually uses: `parse_declarations` has tracked `variable` lines into a
`context` and merged them into every declaration since before today (`syntax.rs:146-152, 185`).

The plan took a limitation of one reader for a property of the material. **`D` was three defects
away, not a new reader.**

## 2. What `D` now carries

`LeanBinderChart` gains `kind` — explicit, implicit, instance, strict-implicit — and `type_text`,
the binder's type as the source wrote it. The type was previously discarded at
`content.split_once(':')`, which bound it to `_`; instance binders were not parsed at all, so any
arity computed from the chart was wrong for every declaration carrying one.

On the declared corpus every declaration now carries a fully typed domain — 7 to 13 binders each,
every one typed, each with one instance binder the reader previously could not see.

## 3. Three corrections, and the oracle taught each of them

`#check @d` makes Lean print the declaration's own type. One reader cannot audit itself; this is the
second instrument, and it disagreed three times before it agreed.

**The instrument was wrong first.** The comparison began as *names up to the first depth-zero
comma*, and disagreed on six of seven. Looking at what Lean actually printed showed why:

```text
@proportionalFlow_respects_capacity : ∀ {Old} {New} [inst] [inst_1]
  (demand : Old → ℝ) (capacity : New → ℝ) (incident : Old → New → Prop) [inst_2],
  (∀ m, 0 ≤ capacity m) → (∀ m, congestion … ≤ 1) → ∀ (m : New), …
```

**A named hypothesis whose name the conclusion never mentions is printed as an anonymous arrow.**
`hc` and `hcong` are positional arguments and Lean writes them `→`. So the domain is every explicit
group of every `∀` telescope *plus* every depth-zero arrow, and the metric is **positional arity**
with Lean's printed names required to be a subsequence of ours.

**Then the reader was wrong, twice, and the second attempt made it worse — 14 of 17 down to 11.**
Both defects were real and the oracle named both:

- **A top-level `variable` ends a declaration's chunk.** The chunk scan ran to the next
  `theorem`/`lemma` only, so every `variable` line appearing *after* the first declaration was
  swallowed into the preceding chunk and never merged. Interleaving `variable` with declarations is
  mathlib's ordinary style: `variable [DecidableEq α] (m : Multiset α) (l : List α)` inside
  `section ToMultiset` contributed nothing, and `List.card_toFinset` came back with an empty domain
  where Lean prints one argument. **This is a third defect of the species the first movement
  repaired** — a rule stated for a simple shape that mis-handles the common richer one.
- **A section variable enters a declaration's domain only if the declaration mentions it**, which is
  Lean's own rule; admitting all of them claimed arguments Lean does not take. Adding that rule
  naively broke two more, and the oracle named both conditions it needs: **a mention can be a
  projection** — `#l.toFinset` mentions `l`, and the identifier scan returns the dotted token — and
  **a declaration's own binder shadows a section variable of the same name**, so
  `{m : Multiset α}` re-bound implicitly under `variable (m : Multiset α)` is not a positional
  argument at all.

## 4. The return

```text
  sample 17   oracle unreadable 0   decided 17   agree 17   disagree 0
```

**Seventeen of seventeen**, across `FiniteTransport` and three mathlib modules —
`Algebra/Group/Basic`, `Order/Basic`, `Data/Finset/Card`. The gate condition was a *majority*; the
sample is unanimous.

**The bound is the sample.** Seventeen declarations is not 232,037, and agreement here is evidence
that the rules are right on the shapes sampled, not that no shape defeats them. The movement was
defined to complete when the disagreement population is **named**; it is named and it is empty,
which is the stronger outcome and not a different one.

## What this movement does not claim

`D` and `v` together type an application and a rewrite and nothing else. No edge has been built and
no admissibility has been decided — that is the next movement. The 622 documents the emission's
reader refuses outright still bound what any emission on it can see, and that population is
unchanged by this work.
