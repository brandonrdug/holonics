# The monoid is aperiodic by construction, so the crystal needs the turn

**Date:** 2026-08-18
**Truth status:** `established-bounded` for every figure; `proved-standard` for the monotonicity
argument, which the measurements were designed to break and did not.
**Evidence:** `measured`. `soma/life/examples/the_transition_monoid_is_the_crystal.rs`,
`soma/life/examples/the_crystal_needs_periodic_material.rs`.
**Provenance:** Brandon, 2026-08-18: *"What would happen if we used actual inference with I/O about
an embedding space with forward and shifting throughout junctions? Emergent charts of the embedding
space… we could as operators focus the machine during its training into a perfectly crafted
**crystal** model that diffuses information on a hyper efficient scale compared to classical LMs."*

---

## 1. The object, and it is not an analogy

*Forward and shifting through junctions* is one operator. `carry` takes a forward transition when the
channel conducts and **arcs down a suffix link** when it does not, so each germ is a **total function
on every class**, and the germs generate a **transformation monoid** — the syntactic monoid of the
material.

That monoid is what a crystal is made of. A space group is a monoid; a crystal compresses because the
whole structure is a unit cell plus a **group action** rather than an enumeration of sites. So the
crystal question is exactly: **does this monoid contain a nontrivial group?**

**Nothing in the census is imposed.** No layer, no head, no dimension. Every quantity is a property
of `f_a`.

## 2. The diffusion is already extreme, and the grain decides how extreme

| grain | classes | generators | mean `\|image(f_a)\|` | contraction in **one** symbol |
|---|---|---|---|---|
| word | 25,030 | 3,125 | **8** | **3,128×** |
| character | 110,849 | 164 | 675 | 164× |

**One word collapses the state space by three thousand times.** And the grain matters in the
direction opposite to the naive one: the *coarser* grain diffuses ~19× harder per symbol, because a
word carries far more constraint than a character. Everything stabilises in at most two applications
for 3,118 of 3,125 word generators.

That is hyper-efficient diffusion, measured. It is **dissipative**, not crystalline.

## 3. Zero group content — and the periodic controls did not rescue it

Every attractor at both grains is a **single fixed point**. Orbits of length above one: **0**, over
3,289 generators.

So the question became whether that is a fact about *prose* or about the *construction*. Five
materials built to break it:

```text
  material                          classes   gens  mean image  orbits>1  longest
  periodic, period 5                   4002      5         800         0        1
  periodic, period 7                   4002      7         571         0        1
  periodic, period 12                  4002     12         333         0        1
  Z/5 additive walk                    4002     10         400         0        1
  Z/12 additive walk                   4002     24         166         0        1
  Thue-Morse (aperiodic control)       6048      2        3023         0        1
  prose (reference)                    2332    627           3         0        1
```

**Zero, including in purely periodic material with a genuine `ℤ/n` in it.**

**So the aperiodicity is a property of the construction, and the reason is a one-line theorem.**
`carry` takes the **longest matching suffix**. Both its moves are monotone in matched length —
forward increments it, an arc strictly decreases it — so iterating settles rather than returning. **A
longest-suffix map cannot permute.** The suffix automaton with fallback is aperiodic for *every*
material, and no choice of corpus, grain, or training will give it a space group.

By Schützenberger that also classifies the languages this organ can distinguish: aperiodic syntactic
monoid means **star-free**, first-order definable, with no modular counting anywhere.

## 4. What the crystal actually needs, and this repository already owns it

A group acting means reading a word returns you to a state you were in before, **permuted**. `carry`
cannot, because its state is `{class, matched_length}` and both coordinates are monotone.

**A transport that can is one that carries a phase.** The state would be `{class, matched_length,
winding}`, and the winding is where `ℤ/n` lives — it is the only coordinate that can return.

**That coordinate is exactly the one this carrier deletes**, and the corpus has said so since
2026-08-08: *the boundary kept the magnitude and discarded the turn*; *a sign is a passage, never a
state*; and `winding_inertia.rs` exists precisely to return inertia as **windings** — every passage
of a circulant form named by how far it turns. The crystal question and that record are the same
question at two altitudes.

So the finding is constructive rather than merely negative:

> **A crystal model needs a different transport law, not different material or different training,
> and the missing ingredient is the turn. `carry` is monotone and therefore amorphous by theorem; a
> transport carrying a winding alongside the match is the first thing that could be crystalline.**

## 5. What is refuted

- **Refuted:** that periodic or crystallographic *material* would make the atlas crystalline. It does
  not, at any period tested, including material whose group structure is explicit.
- **Refuted:** my own prediction, stated the same day, that character grain might exhibit group
  content where word grain did not. It does not, and the contraction moves the other way as well.
- **Withdrawn:** the reading in the first monoid census that called the union of *attractors* the set
  the machine occupies after one token. An attractor is where repeating **one** symbol forever lands.
  The set reachable in one step is the union of the **images**, which is 25,025 of 25,030 at word
  grain — nearly everything, not 3,125.

## 6. Falsifiers

- Any generator, at any grain, on any material, exhibiting an orbit of length above one refutes the
  monotonicity argument.
- A transport carrying a winding must exhibit an orbit above one on periodic material, or the turn is
  not the missing ingredient either.
- The word-grain contraction must exceed the character-grain contraction on other corpora, or the
  grain reading is specific to this material.
