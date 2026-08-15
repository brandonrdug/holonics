# The emission has no chart transition between the goal's frame and the lemma's

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `measured` throughout — every claim below is read off the rendered artifacts the
runs left on disk and the corpus they were posed against, not off a count of verdicts.
**Occasion:** Brandon: *"You're only reporting numbers, I don't have any use for this information,
your analysis is shallow."* Correct, and `CLAUDE.md` §0h already forbids it: *report the causal
atlas before its scalars… never let a scalar dashboard stand in for the object.* `4 admitted of 213`
is a scalar dashboard. This record is what the artifacts say.

---

## 1. The denominator was never 213, and the mechanism says why

`213 candidates` is not 213 attempts at the mathematics. Reading the rendered files rather than the
verdict counts:

**Every recruited declaration gets the same treatment, whatever it is.** The emission produced
`rw [D]` **twenty-one times for each of the seven** recruited declarations. Of those seven, only
**two conclude in an equation** — `proportionalFlow_row_sum` and `proportionalFlow_column_sum`. The
other five conclude in `≤`.

```text
  21 × 5 = 105 paths rewrite by an inequality
  the kernel returned  105 × "Invalid rewrite argument: Expected an equality or iff proof"
```

**The two numbers are the same number.** The single largest refusal species in the whole run is not
a mathematical difficulty at all — it is the generator applying a *rebase* to something that is not
a rebase, once per (inequality, template) pair, exactly as many times as that product has members.

**And the argument list comes from the wrong frame.** Six spellings appear across the emission:

```text
  75  demand capacity incident hc m
  25  demand capacity incident m
  25  demand capacity incident hc hcong m
  25  demand capacity incident
  23  demand capacity incident hc hcong
   1  demand capacity incident hc hcong hcong
   1  demand capacity incident hc hc hcong
```

Those are **prefixes of the posed theorem's own binders**. `hc`, `hcong`, `m` are the goal's
hypotheses, not any lemma's parameters, and they are sprayed at all seven declarations. Exactly one
declaration — `proportionalFlow_respects_capacity` — has the signature
`(hc) (hcong) (m)`, and exactly that one appears in all four admitted proofs. The last two spellings
repeat a hypothesis (`hc hc hcong`), so the enumeration is not even deduplicating.

> **This is a cartesian product: {recruited declaration} × {prefix of the GOAL's binder list} ×
> {template} × {closer}. The kernel is doing the selecting.** What the four admissions demonstrate
> is that one cell of that product happened to be well-typed — not that the body identified the
> right lemma.

### Named in the project's own vocabulary, which is where the repair is

The goal has a binder frame. Each lemma has its own. Applying a lemma means carrying an argument
list **from the lemma's frame**, and the emission carries the **goal's** coordinates in unchanged.

> **The generator has no chart transition between the goal's frame and the lemma's frame.** It
> transports one chart's coordinates into another and takes no Jacobian.

That is the absolute-frame defect one level up from where this project usually catches it — not a
filesystem path folded into an invariant, but a *hypothesis list* folded into an application. And
`TABLET_THE_OPERATIONS`'s species distinction is the other half: `=` is a transport and `≤` is a
**face**, and `rw` is licensed only by the first. The emission types neither.

**What is owed is therefore exact and small:** the argument list must be derived from the recruited
declaration's own binders, and `rw` must be offered only for a declaration whose conclusion is an
equation. Both are readable from what `lean_development` already returns — `DeclaredForm::statement`
carries the binders and the conclusion. No new organ; a type the emission currently discards.

---

## 2. What the species actually names, read off its members

The move-species run reports a coarse class of ten and a causal class of two. The classes
themselves, with what the reader recovered:

```text
  coarse species — every member: downstream 1, upstream 0
     1.1  obtain    in sin_angle_mul_norm_eq_sin_angle_mul_norm
     1.3  obtain    in sin_angle_mul_norm_eq_sin_angle_mul_norm
     1.5  obtain    in sin_angle_mul_norm_eq_sin_angle_mul_norm
     1.7  have      in sin_angle_mul_norm_eq_sin_angle_mul_norm
     4.1  by_cases  in norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi   focus depth 1
     7.4  obtain    in angle_eq_angle_add_add_angle_add
    23.0  have      in dist_mul_of_eq_angle_of_dist_mul    :: dist a' c' ^ 2 = (r * dist a c) ^ 2
    24.3  intro     in dist_lt_of_angle_lt
    28.0  by_cases  in pi_div_three_lt_angle_of_le_of_le_of_ne     :: p₂ = p₁
    30.0  by_cases  in angle_lt_pi_div_three_of_le_of_le_of_ne     :: p₂ = p₁
```

**The class is nameable in words and it is not a tactic:** *a move that founds something exactly one
later move uses, and that nothing founds.* It holds `obtain`, `have`, `by_cases` and `intro`
together, across **eight different theorems** about angles, distances and norms. That is the atlas
row the deed was for — a transport pattern recurring across subjects, with the tactic name carrying
none of it.

**And the separation is entirely in the neighbourhood, which is the construction working as
designed.** All ten roots are *identical in their own coordinates* — downstream 1, upstream 0 — and
the root observes the common exposed face, so nothing about a candidate itself can split them. The
causal panel keeps `1.1` and `1.3` and departs the other eight **on what they feed**: `4.1` sits at
focus depth 1 while the survivors sit at 0, and the rest feed neighbours with different cohort and
arrival profiles. A species here is a statement about a move's *situation*, never about the move.

---

## 3. Looking at the members surfaced a reader defect the counts hid

Member `1.7` returned the statement `: V) (hx : x ≠ 0) (hy : y ≠ 0) :`, which is not a statement.
The source is:

```lean
  have h_sin (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) := by
```

`lean_development` takes the binder pattern *to the first `:`*. When the binder carries its **own
parameters**, that rule stops inside the parameter group. Two consequences, both measured:

- the reader founds **three** steps from one act — `h_sin`, and the bound variables `x` and `y`,
  which are not founded facts at all;
- the statement it records is the remainder of the binder group, and the real statement — the one
  containing the `=` — is never seen.

**How much material has this shape**, over all 7,516 mathlib files:

```text
  binding-tactic lines whose pattern before `:` carries its own binders   8,934
                                              a plain name only          98,568

  have      1,168 parametrised
  suffices  1,869 parametrised against 1,046 plain — the MAJORITY of `suffices`
  let       2,557 parametrised
```

The `have` and `suffices` rows are the clean ones. The destructuring tactics inflate the count,
because `rcases h with (a | b)` puts a parenthesis in the pattern for an alternation rather than a
parameter group, and that is over-counting rather than a second defect.

**Why this matters beyond tidiness:** every parametrised binder inflates the move population with
bound variables masquerading as moves, gives them a garbled statement, and shares a cohort with the
real one. The `Ascribed` axis then reads `true` off a fragment. It was invisible to every count and
visible immediately in ten rows of content.

---

## What this record does not claim

The chart-transition reading of the emission is `interpretation`; what is `measured` is the exact
coincidence of 105 malformed rewrites with 105 rewrite refusals, the six argument spellings and
their source, and the single declaration whose signature matches the one spelling that admitted. The
species class name is a reading of ten members and is not asserted to be the class the atlas will
finally carry. The parametrised-binder census is an upper bound for the defect, stated as such. No
repair to the emission or the reader is made here — both are named exactly, and both are small.
