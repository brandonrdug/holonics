# The authored level

**Genre:** canon (`canon/THE_DOCUMENT_LAW.md` §1.1). It names a contaminant species, enumerates every
instance, states the excision per instance, and installs the audit that makes a new one visible the
day it lands.

**Truth status:** `established-bounded` — the census is mechanical and reproducible
(`python3 tools/authored_levels.py`); each disposition is a reading and is carried per row in
`meta/AUTHORED_LEVELS.tsv` with its burden of proof.
**Provenance:** Brandon, 2026-08-09: *"you will keep saying things like 'that is the same law one
level down', when the fact is that we already know how the network needs to work, and that **we are
not the ones meant to be pinning levels to minimums and maximums**."* And, on the excuse: *"I have no
evidence for it but I am willing to bet you are smuggling in contamination and rigid constants there
and excusing it with roundabout logic."* He was right; §3 records what the bet found.

---

## 1. The law

> **A level is either read off the material or declared by the caller. It is never authored inside
> the organ.**

A *level* is any numeric bound that decides how far a construction goes, how much it admits, how
deep it looks, or how many it returns. Not a wire tag, not a layout offset, not an identity element,
not a theorem.

## 2. Why this is a species and not a list of bugs

The project has been finding these **one at a time for weeks** — `characteristic_delay: 1` at its
only call site, `LEADER_WITNESS_DEPTH: usize = 1`, `REFINEMENT_APERTURE` of 64 — each discovered by
hand, each reported as though it were the last. That loop is itself the defect: a serial search
through a population nobody had enumerated, with each find generating a sentence about the *next*
level down.

The census ends the search. `python3 tools/authored_levels.py` enumerates every authored numeric
level in library code and requires each to carry a disposition. **An undispositioned constant fails
`--check`**, so the population cannot silently grow.

## 3. The excuse the bet found, and it was mine

An earlier classification of these constants had three species: *facts*, *declared apertures that
return their outside*, and *pins*. Two of the three were doing excusing work.

- **There were no facts in the list.** `QUINTIC_DEGREE = 5` is not a label for a fact about quintics;
  `arithmetic_monodromy.rs:77` **refuses** any polynomial whose coefficient count is not six, and
  there are seven fixed-size-5 arrays including `type Permutation5 = [u8; QUINTIC_DEGREE]`. The organ
  is hardwired to degree five and cannot see a quartic. The constant makes a *restriction* read as a
  *definition*.
- `QUADRIC_COEFFICIENT_COUNT = 10` is worse in the same way. A quadric in `n` variables has
  `C(n+2,2)` coefficients, so **10 pins the ambient dimension at 3** while the name reads as a
  coefficient count. `ExactAffineVersionFiber::new` already takes the count as a parameter — the
  machinery is dimension-agnostic and only the caller pins it. This is *"a varying number of
  dimensions and charts"* blocked by two `const` lines.
- **"Declared aperture that returns its outside" was the roundabout logic.** Refusing past a number
  you invented does not make the number derived. `FREE_ENTRY_APERTURE = 12` refuses with
  `GaugeApertureExceeded` rather than sampling — the refusal shape is lawful — and nothing whatever
  derives 12. `REFINEMENT_APERTURE = 64` is the best-argued of them and is still 64 because 64 is a
  familiar number.

The disposition `APERTURE` survives, but with a burden it did not have: **`why` must state what it
would take to derive the level from the material.** That is what keeps it from becoming the excuse
again.

## 4. The census, 2026-08-09

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

Every row is in `meta/AUTHORED_LEVELS.tsv` with its plan. Three excision species:

### 5.1 Derive from the material — fourteen

| pin | what replaces it |
|---|---|
| `QUINTIC_DEGREE` ×2 (`arithmetic_monodromy`, `quintic_chart`) | the degree read off the polynomial; `Permutation5` → a general permutation. `rational_polynomial.rs` already carries general-degree resultants and Sturm sequences, so the substrate exists. **The Tschirnhaus line is transport between degrees; pinning the degree removes the thing being transported, and `solvable_by_radicals` refusing degree 5 has nothing to contrast against.** |
| `QUADRIC_COEFFICIENT_COUNT`, `AFFINE_PHASE_COEFFICIENT_COUNT` | `C(n+2,2)` and `n+1` from a declared dimension |
| `REFINEMENT_APERTURE`, `ISOLATION_APERTURE`, `MAXIMUM_ISOLATION_DEPTH` | **the root-separation bound from the discriminant** (Mahler/Davenport). The halvings become computed, and a construction exceeding them is a genuine defect rather than a budget overrun. |
| `LEADER_WITNESS_DEPTH = 1`, `LEADER_GRAIN_RECIPROCAL` | what the material stopped the leader at. `leader_quadrature.rs` carries the law — each extension changes what the next extension reads. **A leader whose witness depth is one takes a single step; that is not a leader.** |
| `HORIZON_DOUBLINGS` | the transport law's own fixed point |
| `SCAFFOLD_LINK_FOLD` | the fold from the incidence |
| `CHANNEL_COUNT`, `COUPLED_INFORMANT_CURRENT_CHANNELS` | the declared material's channel count. `COUPLED_PHASE_EXTENT = 18` is the RELAMPAGO fixture's coordinate count — **one experiment's material fixed into the organ that reads it.** |
| `SEPARATION_EXHIBIT = 512` | **return the population whole.** Truncating a returned population is what `CLAUDE.md` §9 forbids outright: the artifact is the return, and a count is never a substitute. |

### 5.2 Move to the caller — four

`FAMILY_APERTURE`, `FREE_ENTRY_APERTURE`, `DEFAULT_HORN_LOCAL_SECTION_LIMIT`, `WINDOW_APERTURE`.

These are genuine resource declarations and the organ is the wrong place for them. The lawful form is
a **receiver-declared aperture supplied by the caller**, with the refusal naming what the material
would have required. `DEFAULT_` in the third name is the defect naming itself: a default is a level
the organ picked because the caller was never asked.

### 5.3 Unread — six

`MODES`, `FLOW_TEETH`, `POOL_TEETH`, `SWEEP_TEETH`, `BLOCK_LINES`, and one more in
`soma/body`/`soma/life`. **Held as contaminants until read**, which is the conservative direction: a
level is a pin until someone shows it is a theorem, not the reverse. `FLOW_TEETH = 13` and
`POOL_TEETH = 31` are both prime and may well be a coprimality theorem about gear periods — but
saying so without reading `soma/body/src/law.rs` would be exactly the excusing this document exists
to stop.

## 6. The audit procedure

```bash
python3 tools/authored_levels.py           # the census, by disposition
python3 tools/authored_levels.py --check   # exit 1 on undispositioned, moved, or departed
python3 tools/authored_levels.py --write   # re-seed, preserving existing dispositions
```

**Run `--check` before depositing anything that adds a `const` to a library organ.** It fails on
three conditions, and each is a real event: an **undispositioned** constant is a new pin; a **moved**
value is a level someone retuned without saying why; a **departed** one is an excision that should be
recorded rather than noticed later.

**What the tool cannot do**, stated so the gate is not over-trusted: it cannot tell a theorem from a
guess. That is a reading, it lives in the `why` column, and the column is the deliverable. The tool's
whole job is to make sure **every level has one**.

**Scope**, declared: `crates/*/src` and `soma/*/src`, excluding `#[cfg(test)]` bodies, `*_tests.rs`,
and the mount gates. A driver's literal is a declared fixture and is the right place for a number.

## 7. What this does not claim

- It does not claim the 24 are excised. They are **enumerated, dispositioned, and planned.** The
  registry is the ratchet; the excisions are work.
- It does not claim the 149 `ABI` rows were each read. They were dispositioned **by a stated rule** —
  location in `soma/abi`, CUDA launch geometry, layout offsets, receiver addresses — and the rule is
  in the `why` of every row so it can be attacked.
- It does not claim numeric constants are the only species of authored level. A `.take(n)`, a
  `min`/`max` against a literal, and a fixed-size array all pin without declaring a `const`, and the
  tool does not see them. **`Permutation5 = [u8; 5]` was found by hand, not by the census.** Widening
  the detector is owed and is named here so the census is not read as complete.
