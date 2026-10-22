# Retention releases only what no receiver can read, and the factor loci take the lattice rule

Refs #73 #62. Decides the retention question left open by
[the October 16 record](2026-10-16_THE_CONTACT_FACTORS_TAKE_THE_COMMON_LATTICE_LAW_AND_THEIR_RELEASE_STAYS_BELOW_HALF_THE_FOUNDING_UNIT.md)
and by the lattice rule's `[open]` note (`FieldDeclaration::lattice_by_rule`,
`crates/holonics/src/hnn/field.rs`). Status: [definition; agent-inferred, October 22], decided by
design. Epime's October 22 proposal for the same question (NativeReceiverResolutionV1) is not
adopted; the reason is below.

## The question

A deposit carries each entry by the budgeted law (`carried_entry`): the entry moves by whole units
`q·u`, the fine remainder `r` is carried, and the tail `e` below the clock's fine lattice
`2^(−L−k_m)ℤ` is released. The retention law says the retained constitution must be a quotient
sufficient for the admitted future: what is released must be a difference no admitted receiver can
read, at any later time. Is that true of the release, and what decides the lattice `L` at which it
is true?

## What already holds

Three formal-checked results answer it for every locus the word reads linearly:

- **The whole future's release is bounded.** The releases of one entry since its anchor sum below
  half the anchor unit, because the clock precisions are Elias-gamma lengths and their weights
  `2^(−k_m)` sum below one (`HNN/LatticeDeposit.{gamma_kraft_lt_one,
  release_bounded_since_founding}`, `HNN/LatticeDeposit/Rebase.history_release_lt`). The bound
  holds over any history of deposits and re-bases, so it covers every future deposit, not one cut.
- **The read value stays within one anchor unit** of the exact accumulation of everything that
  reached the entry (`within_one_unit_since_founding`, `history_within_founding_unit`).
- **The lattice rule makes one unit invisible.** `L_ℓ = ⌈log₂(2 L_R X_ℓ)⌉`, with `X_ℓ` the declared
  ℓ1 bound of the operand a read of the locus sums, makes one unit move a linear read by at most
  `1/(2 L_R)`, below the receiver's grain (`remainder_below_grain`).

So on a linear locus two histories that differ only by what was released read the same within
half a grain, at every horizon. The release is in the kernel of the admitted reads, which is what
the retention law asks. Nothing else is needed there.

The anchor is the unit at which the entry first released (its founding unit if it released there).
`history_release_lt` applied from the last state before the first release gives the bound in that
unit, because nothing was released before it and lattices only refine afterwards.

## The gap

The factor loci (`C = ccᵀ`, `K = bbᵀ`, `D = FFᵀ`, `W_s = −ffᵀ`, the slices `uvᵀ − vuᵀ`, the pair
port `e(a·x)(b·y)`) enter the word as products of their entries. The rule bounds each entry, not the
product, so `remainder_below_grain` does not reach a read through them. That is the word-level
certificate owed in #62, and it is the whole of the open question.

## The decision

The factor loci take the same lattice rule, with `X_ℓ` replaced by their word-level modulus `X_F`.

**The product rule** [derived]. Take a read through a product of `n` factor vectors, each entry
displaced by at most the anchor unit `u ≤ 1`, with the factor's entries bounded by `β_i` on the
admitted domain and operand ℓ1 norms `X_1, X_2, …`. The read moves by at most

```text
(Π_i (β_i + u) − Π_i β_i) · Π X  ≤  u · (Π_i (β_i + 1) − Π_i β_i) · Π X ,
```

since the left side is a polynomial in `u` with nonnegative coefficients and no constant term. For
one bilinear term `(xᵀa)(bᵀy)` this is `u·X_x·X_y·(β_a + β_b + 1)`. A rank-`r` factor such as
`D = FFᵀ` sums `r` such terms.

The modulus `X_F` is the product rule's factor, summed over the terms of the read. Where the factor
reaches the word through the contact's solve (storage and inertia inverted at the opening), it is
multiplied by that solve's modulus on the admitted domain. The Athena line's contact envelope
already computes the factor-box perturbation of that solve (`ContactEnvelope::tighten_norm`). It
uses it only to tighten an operator norm; the join is to expose it as a difference bound.

The rule `L_F = ⌈log₂(2 L_R X_F)⌉` then gives a read move of at most `1/(2 L_R)` for one anchor unit,
as on the linear loci. With the three results above, the factor release is in the kernel of every
admitted read at every horizon.

Two declarations make the hypothesis hold, and both already have owners:

- **The entry bound `β` is part of the locus's declaration**, as the admitted material domain. A
  deposit that would carry an entry outside it is refused, typed, like the existing domain guards.
  Refining the lattice later cannot repair it: the release already made is charged in the anchor
  unit.
- **`L_R` is the finest grain the locus's receivers declare over its admitted future**
  (`finest_grain`). A receiver whose grain refines with ingress declares its finest grain. Without
  one, the locus releases nothing and carries exactly; it never releases against a grain it will
  later outgrow.

## What is not adopted

NativeReceiverResolutionV1 certifies one declared read at the producing cut, and states that it
does not certify the admitted future. That is the one thing the retention law requires, and the
Kraft bound above already gives it for every horizon. The proposal's versioned declaration,
comparison grades, immutable issuer, proof-grade tag and policy identity in the cold state are not
built. Its factor-box and stage bounds are kept: they are the inputs of `X_F`.

## What stays open

- **The counterfactual trajectory.** How far the carried trajectory is from never-rounded learning
  is still `commit_chain_residual`'s `Σ K^(n−1−i) r_i`, which needs a Lipschitz bound `K` of the
  deposit map. It stays owed in #62. This decision bounds what the retained state reads, not the
  trajectory that unrounded covectors would have taken.
- **The composed Lean statement** (product rule, solve modulus, `remainder_below_grain` at `X_F`)
  is owed in #62.
- **Discrete releases.** A keyed draw reads through the continuous face. Where its margin is below
  `1/(2 L_R)`, the grain does not resolve it, and the existing release law already handles that
  case (probe or refusal).

## The measured case, and the one check it calls for

In the Athena fixture, the contact factors were founded at `L = 5` and re-based by hand to `L = 29`,
where their first release occurs. That makes the anchor `2^(−29)`. All 96 contact updates fell
below half the fine cell `2^(−31)` and were released, so no factor moved.

Under this rule those releases are unreadable exactly when `X_F·2^(−29) ≤ 1/(2 L_R)`. At the
fixture's declared grain `1/4` (`L_R = 4`), that is `X_F ≤ 2^26`. The check is to compute `X_F` once
for the fixture's contacts, exactly, on the host:

- If it holds (expected, agent-inferred), the releases were lawful. The learning is silent because
  each step is too small to reach a unit, not because retention discards it. The next step is then
  the learning step's size (the unit-prior trial), not retention machinery.
- If it fails, the factor loci found at `L_F` and the same updates are carried.
