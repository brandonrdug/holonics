# Campaign 2: the rings and contacts are lawful and add no bits on text

**Date:** 2026-09-26. **Status:** recorded (#73, campaign 2; Decisions 28–31), reviewed and
corrected the same day (§5 supersedes §2's cost and §3's causes). The campaign's predictive
criterion **fails**; its law and parity gates pass. **Commits:** `bff374db`..`e35882b0`
on main.

## 1. What was built

[proved-derived; formal-checked] Lean items 8, 13 and 14, with no `sorry`.
- **`HNN/Ring`.**
  - The ring's Cayley tick keeps its storage form, `UᵀQU = Q` with `Q = diag(K, C)`. The executed
    descriptor tick conserves `E_Q` without `C⁻¹`.
  - The denominator is nonsingular under its port. `ring_harmonic_mode_singular` shows that
    hypothesis is needed.
  - The executed balance states the pump, port, dissipation, chart and split terms.
  - The two-port reference change gives `Γ² + T = 1`, with `T` the power fraction.
  - Ring crossings are epoch ticks.
  - The pump is blind to the half-turn sheets.
- **`HNN/Contact`.**
  - The contact's transfer, trace and determinant.
  - Its kind follows the sign of `K_a` (rotation, null shear, boost) for the lossless transfer.
  - A boost's solve is certified or refused with its singular direction.
  - The signed-storage balance holds, with the counterexample `boost_grows_at_conserved_signed_storage`
    showing it does not give passivity.
  - The lock address comes from the measured winding pair.
- **`HNN/ContactBreak`.** A contact breaks when its released storage covers the gluing work,
  `R ≥ J`; Griffith is the closed-port case. A parted face returns the typed `uncancelledPower`
  gluing defect.
- **`HNN/Word`.** The executed field balance states every defect. `element_executed_balance`
  discharges `HNN/LatticeWord`'s open item.
- **`HNN/LandmarkAddress`.** Typed bundles are causal, restrict by whole bundles, and have finite
  partitions. The lock family is a box, `0 < p ≤ P`, `0 < q ≤ Q`, because a contact reads its own
  orientation. The enlarged tree codes within the cell-only tree's charge.
- **`HNN/LandmarkCarrier`.** The rebase past `u128`, with exact remainders or an enclosed released
  residual. It is tested past the old refusal, to 131,072 cells.
- **Rust and card.**
  - `hnn::{ring, contact}` and `contact_readings`, with one owner for the reading.
  - The letters are wired through `LetterReader`.
  - The tree runs on the card.
  - The resonator and the normal law's prox step run on the card as checked mirrors of the host's
    owners.

## 2. The receipt

The standing real cut: 3,074 windows and 3,074 deposits, complete, prequential. The GPU suite
passes, 38 of 38, including parity with resonators and a boost. The host and card readouts are
identical outside the wall-time table. Tick balances: 9,222 read, every one closed within its
certified bound.

**The development decision** (4,958 cells; no held-out cell read). 42 letter families were
declared: 30 clock and 12 contact.
- Each was credited only with its gain over a constant-slot control of the same width, plus its
  description.
- Every family's `Δ_letters` is decided positive: the informative contacts at `+148 + 7/16` to
  `+176 + 11/16` bits, the clock families at `+131 + 9/16` to `+179 + 15/16`.
- The choice is the cell-only family.
- Every contact read as a rotation at every commit (`C ≻ 0`, `K ≻ 0`), so the site-kind census
  contains no nulls and no boosts.

**Held out** (1,190 cells, in all, each `+ ε`):

| Reading | Campaign 2 | Campaign 1 (reviewed) |
|---|---|---|
| model − order-0 | `−1996 + 12/16` | `−1996 + 12/16` |
| model − PPM-2 | `−252 + 5/16` | `−252 + 5/16` |
| `L_C − L_T` | `−7 + 13/16` | `−7 + 13/16` |

**The criterion fails.**
- `Δ_tree < 0` fails: no letter family was admitted.
- The wave's gain equals campaign 1's and does not exceed it.

**Cost.**

| Realization | Campaign 2, a window | Campaign 1, a window |
|---|---|---|
| Card | `140 rem 265 over 3074` ms (430,625 ms in all) | `114 rem 3063 over 3074` ms |
| Host | `160 rem 636 over 3074` ms (492,476 ms in all) | `130 rem 291 over 3074` ms |

- On the card, the compare phase fell from `29` to `10` ms a window.
- The normal-law mirror added `35` ms a window without replacing the host's owner.
- The host's deposit stayed at `50` ms a window.

## 3. The located cause

[derived] The first failing term is the features' information: on this text the rings' phases and
the contacts' locks and kinds tell the tree nothing the preceding cells do not already tell it. The
physics that would change the wave is not engaged by campaign 1's declared field:
- no ring declares a resonator, so the resonators ticked zero times;
- the resonator does not load the word; its return through the word is owed in #62;
- learning never drove a contact out of rotation.

The combined face is therefore the same as campaign 1's.

[interpretation] On text at this scale the compression is the landmark tree's. The helical
machinery is lawful, exact and resident, and it earns its few bits only through the mixture.

## 4. What follows

- **The card mirror** [agent-inferred]. The normal-law mirror moves from the exposure's path into
  the GPU suite as a parity test. It costs `35` ms a window and replaces nothing.
- **The tree's prior.** Constant-slot controls code the development cells up to `133` bits below
  the cell-only tree, so the stop-weight prior of Decision 28 (`½` at each node) is not the
  code-length-optimal weighting. It is a compression gain waiting for its own decision and Lean.
- **The rings' part.** For the rings to change the face, a ring must declare a loaded resonator
  (#62) and the data must drive the contacts' kinds. Campaign 3 (release through modes) needs the
  ring modes the loaded resonator provides.

## 5. After the review (same day, `a1218a59`..`a7a8c0ad`)

[correction] The single reviewer found eight defects. Every one is fixed, the verdict stands, and
the numbers below supersede §2's cost and §3's causes where they differ.

- **The lock law.** Lean `HNN/Contact.contact_lock_address` now proves the rule the Rust runs. The
  lock is the least-denominator rate in the fibre `(m_g/(m_h+1), (m_g+1)/m_h)`, with ties broken by
  the least rate. It exists, is unique, lies in the box, and closes at its `q`.
- **The lock bound.** `Q = ∏_(j>h) d_j`, the true horizon. A one-letter family is refused, so every
  contact family now has at least two letters.
- **The criterion.** The plan's rule now credits letters against a constant-slot control. The rule
  was changed after a development run showed constant slots meeting the old rule; the change is
  disclosed in the plan.
  - Rerun on the development cells, every one of the 41 families is decided positive: clock
    families at `+131 + 9/16` to `+179 + 15/16`, contacts 0 and 1 at `+148 + 7/16` to
    `+176 + 11/16`, and contacts 2 and 3 at `+12 + 5/16` to `+12 + 8/16`.
  - Contacts 2 and 3 lock only at the closing tick, reading two to five distinct codes.
  - The choice is still the cell-only family.
- **The balance.** The deposition work `½⟨x, ΔΘ x⟩` is formed at every commit (Lean
  `field_commit_deposition`). The unloaded resonator port is named as the interconnection defect in
  one combined identity (Lean `combined_balance_unloaded_port`). The exposure checks the word
  balance at every word: 3,074 formed and committed, all closed, with the largest residual within
  its bound. Tick balances: 9,222, all closed.
- **The census.** All four contacts read rotation at all 3,075 commits: no nulls, boosts,
  reflections or degenerate readings. A boost needs a declared signature (`K = b diag(σ) bᵀ`), which
  campaign 1's field does not declare.
- **Located cause, restated.** No letter family carries information beyond the preceding cells on
  this text. No path runs from the resonator to any scored face, and the field declares no
  resonator and no signature. So the wave is campaign 1's, and the held-out readings are equal:
  model − order-0 `−1996 + 12/16 + ε`, model − PPM-2 `−252 + 5/16 + ε`, and `L_C − L_T`
  `−7 + 13/16 + ε`.
- **Parity.**
  - Each card-tree deposit is checked against the host's masses, β and stop weights.
  - The normal-law mirror runs only in the GPU suite: 119 steps carried, 25 declined (24 off the
    dyadics, one empty), 0 skipped.
  - The host and card readouts are identical outside the timing and bus sections.
- **Cost, on an idle machine.** The first timings (§2) overlapped Lean builds and are withdrawn.
  - Host: `116 rem 1087 over 3074` ms a window (357,671 ms in all).
  - Card: `101 rem 398 over 3074` ms a window (310,872 ms in all), below campaign 1's
    `114 rem 3063 over 3074`.
  - The host's deposit is `51 rem 50` ms a window and remains the largest phase.
