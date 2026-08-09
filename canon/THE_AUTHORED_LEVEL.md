# The authored level

**Genre:** canon (`canon/THE_DOCUMENT_LAW.md` §1.1). It states the law, enumerates the population in
this tree, and gives the excision per instance. It is species **2.5** and **2.6** of
`canon/THE_CONTAMINANT_PROTOCOL.md`, which holds the reading procedure.

**Truth status:** `established-bounded`. Every instance is a direct source read at the `file:line`
given; each disposition is a reading carried per row in `meta/AUTHORED_LEVELS.tsv`.

**Provenance:** Brandon, 2026-08-09: *"you will keep saying things like 'that is the same law one
level down', when the fact is that **we are not the ones meant to be pinning levels to minimums and
maximums**."* And on the excuse: *"I have no evidence for it but I am willing to bet you are
smuggling in contamination and rigid constants there and excusing it with roundabout logic."* He was
right; §2 records what the bet found.

---

## 1. The law

> **A level is either read off the material or declared by the caller. It is never authored inside
> the organ.**

A *level* is any numeric bound that decides how far a construction goes, how much it admits, how deep
it looks, or how many it returns. Not a wire tag, not a layout offset, not an identity element, not a
theorem. The declaration form is irrelevant: a `const`, a fixed-size array, a `.take(n)`, and a `min`
against a literal are all levels.

## 2. The excuse the bet found

An earlier classification had three species: *facts*, *declared apertures that return their outside*,
and *pins*. Two of the three were doing excusing work.

- **There were no facts in the list.** `QUINTIC_DEGREE = 5` is not a label for a fact about quintics.
  `arithmetic_monodromy.rs:77` **refuses** any polynomial whose coefficient count is not six, and
  there are seven fixed-size-5 sites including `type Permutation5 = [u8; QUINTIC_DEGREE]` at `:1109`.
  The constant makes a **restriction** read as a **definition**.
- `QUADRIC_COEFFICIENT_COUNT = 10` is worse the same way. A quadric in `n` variables has `C(n+2,2)`
  coefficients, so **10 pins the ambient dimension at 3** while the name reads as a count.
  `ExactAffineVersionFiber::new` already takes the count as a parameter (`field_atlas.rs:972`) — the
  machinery is dimension-agnostic and only the caller pins it. And `field_atlas.rs:1` opens *"The
  atlas has no authored population ceiling"* immediately above the two `const`s that author one.
- **"Declared aperture that returns its outside" was the roundabout logic.** Refusing past a number
  you invented does not make the number derived. `FREE_ENTRY_APERTURE = 12` refuses with
  `GaugeApertureExceeded` rather than sampling — the refusal *shape* is lawful — and nothing whatever
  derives 12. `REFINEMENT_APERTURE = 64` is the best-argued of them and is still 64 because 64 is a
  familiar number.

`APERTURE` survives as a disposition, with a burden it did not have: **`why` must state what it would
take to derive the level from the material.**

## 3. Why the degree pins are not hygiene

`QUINTIC_DEGREE` and `QUADRIC_COEFFICIENT_COUNT` are not two rows in a cleanup list. They are the
machine being unable to do the thing the objective sentence names.

**A degree is a rung, not a category.** Depressing kills the sub-leading term; a quartic's resolvent
**is a cubic**; Bring–Jerrard is a chart change that returns or names its obstruction; `A₅` simple
says something only relative to degrees 2–4. Stellation is one figure at varying `{n/k}`; FLT is one
equation with `n` varying; fractal scaling puts the rung between the integers. Brandon, 2026-08-09:
*"every degree is relevant, the machine grows, there's no floor or ceiling to this, it's simplicial
emergent complexity."*

**The restriction deletes the mechanism the organ exists to demonstrate.**
`solvable_by_radicals` refusing at degree 5 is meaningful only against the degrees where it does not
refuse. An organ that only ever sees degree five cannot state its own theorem.

And the ladder carries a cost law the pinned organ cannot exhibit. `quintic_chart.rs`'s own header
states it at one rung — *"Three homogeneous conditions in `P^2` meet in six points by Bezout, which is
also why the classical Bring reduction costs a square root and a cube root: six is `2 * 3`."*
Generally, for a Tschirnhaus transform of degree `k` killing the top `k` coefficients, `p_1 = 0`
solves linearly for `c_0` and leaves `k-1` conditions of degrees `2..k` in `P^{k-1}`:

```text
   Bézout number  =  2 · 3 · … · k  =  k!        radicals of degree at most k
```

`k = 2` → 2 (principal form, one square root). `k = 3` → 6 (Bring, a square and a cube root). The
ladder has a structural feature at `k = 5` that is **not authored** — it is the same obstruction one
rung up. Truth status `derived`; checkable by the organ at `k = 2, 3` today.

`canon/THE_CONTAMINANT_PROTOCOL.md` §2.6 carries the full statement.

## 4. The population, 2026-08-09

```text
  180 authored numeric levels in library code
      ABI        149    wire discriminants, layout offsets, CUDA launch geometry, receiver addresses
      APERTURE     4    declared, returns its outside, and names what would derive it
      MATERIAL     3    a theorem; `why` names it
      PIN         24    contaminants
```

**MATERIAL is three, and each names its theorem.** `FLAT_COORDINATION = 6` — six equilateral
triangles tile `2π` exactly, and the angular defect is measured against it. `MAXIMUM_AVL_DEPTH = 128`
— an AVL tree over a `usize`-indexed population has depth `< 1.4405·log₂(n+2)`, which 128 exceeds for
any population addressable on a 64-bit carrier. `FOLD_CONSTANT = 2305843009213693951` — `M₆₁` is
prime, so the fold is over a field.

## 5. The twenty-four pins, and their excisions

Every row is in `meta/AUTHORED_LEVELS.tsv` with its plan. Three excision species.

### 5.1 Derive from the material — sixteen

| pin | what replaces it |
|---|---|
| `QUINTIC_DEGREE` ×2 (`arithmetic_monodromy`, `quintic_chart`) | the degree read off the polynomial; `Permutation5` → a general permutation; the transitive-group **catalogue** → the group's own computed invariants (order, transitivity, derived series). `rational_polynomial.rs` already carries general-degree resultants, Bareiss elimination and Sturm sequences, so the substrate exists. §3 is why this is first, not last. |
| `QUADRIC_COEFFICIENT_COUNT`, `AFFINE_PHASE_COEFFICIENT_COUNT` | `C(n+2,2)` and `n+1` from a declared dimension |
| `REFINEMENT_APERTURE`, `ISOLATION_APERTURE`, `MAXIMUM_ISOLATION_DEPTH` | **the root-separation bound from the discriminant** (Mahler / Davenport–Mahler). The halvings become computed, and a construction exceeding them is a genuine defect rather than a budget overrun. |
| `LEADER_WITNESS_DEPTH = 1`, `LEADER_GRAIN_RECIPROCAL` | what the material stopped the leader at. `leader_quadrature.rs` carries the law — each extension changes what the next extension reads. **A leader whose witness depth is one takes a single step; that is not a leader.** |
| `HORIZON_DOUBLINGS` | the transport law's own fixed point |
| `SCAFFOLD_LINK_FOLD` | the fold from the incidence |
| `CHANNEL_COUNT`, `COUPLED_INFORMANT_CURRENT_CHANNELS`, `COUPLED_PHASE_EXTENT` | the declared material's channel count. `COUPLED_PHASE_EXTENT = 18` is the RELAMPAGO fixture's coordinate count — **one experiment's material fixed into the organ that reads it.** |
| `SEPARATION_EXHIBIT = 512` | **return the population whole.** Truncating a returned population is what `CLAUDE.md` §9 forbids outright. |
| `WINDOW_APERTURE = 64` | the count of distinct windows the surface actually has. It truncates the population **presented to** the compression organ, so `iron_at` on a busy surface is measured on a subsample. |

### 5.2 Move to the caller — three

`FAMILY_APERTURE`, `FREE_ENTRY_APERTURE`, `DEFAULT_HORN_LOCAL_SECTION_LIMIT`.

Genuine resource declarations in the wrong place. The lawful form is a **receiver-declared aperture
supplied by the caller**, with the refusal naming what the material would have required. `DEFAULT_` in
the third name is the defect naming itself: **a default is a level the organ picked because the caller
was never asked.**

### 5.3 Unread — five

`MODES` (`soma/body/src/geom.rs`), `FLOW_TEETH`, `POOL_TEETH`, `SWEEP_TEETH` (`soma/body/src/law.rs`),
`BLOCK_LINES` (`soma/life/src/laboratory_language/repository.rs`). **Held as contaminants until read** — a level is a pin until someone shows it
is a theorem, never the reverse. `FLOW_TEETH = 13` and `POOL_TEETH = 31` are both prime and may well
be a coprimality theorem about gear periods, but saying so without reading `soma/body/src/law.rs`
would be exactly the excusing this document exists to stop.

## 6. Grading an excision

Lift the pin, re-run the declared material, exhibit the difference. The three outcomes and their
readings are `canon/THE_CONTAMINANT_PROTOCOL.md` §4. In one line: **a wave of excisions that reports
no movement anywhere has done bookkeeping**, and must say so rather than presenting a green suite as
evidence.

## 7. The registry

`meta/AUTHORED_LEVELS.tsv` carries one row per level — disposition, owner, name, value, and the `why`
that is the deliverable. It is a ledger, and the reading in §3 of the protocol is what fills it.

`tools/authored_levels.py` re-seeds and diffs it: `--write` seeds preserving dispositions, `--check`
exits nonzero on an undispositioned, moved, or departed level. It is a convenience for keeping the
ledger current, not the authority and not a precondition — **recognising a hard-coded magic number in
a library organ takes reading**, and a level the script's regex does not match is exactly as much a
contaminant as one it does. `Permutation5 = [u8; 5]` is the standing example.
