# P9 · Least action — the UM as the reversible compression engine (the Carnot face)

> **Holonic key:** The action of a trajectory is its **code length** `S = Σ −log q` (its total surprise), so
> the **least-action path is the most-compressed path** — the principle of least action *is* compression
> (P1). And minimizing the code you pay **is** maximizing the structure you extract, which is the first law's
> **efficiency**: `η_W = ΣW⁺/Σ(D+J)`. So **least action = max `η_W` = the reversible (Carnot-optimal) path.**
> The UM is the **Carnot face** of the four-machine class: it extracts **compression-work** from the
> **ignorance gradient** (the magnetic law's `ΔT`, measured as **M**), at efficiency `η_W`, with the **burn**
> (turbulence on noise) as its wasted heat. The gate's principle falls straight out: **maximize `η_W`.**

**Grade:** FORMAL-within-frame core (action = code length is a theorem; `η_W` is the exact first law; least
action = MDL); HOMOLOGY at the Carnot identification (the engine *is* Boltzmann, but the `ΔT = M`, `η = η_W`
mapping is structural). **Status: OPEN.** **Source:** `THE_FOURTH_MACHINE.md`, the first law (P7-of-
`PRIMITIVES`), the magnetic law (P8), P11 (M), the efficiency law. Brandon: "least action sounds like the
solution to the Carnot engine part of the UM" — and it is.

---

## Move 1 — RECOGNIZE the holon

The four-machine class (`tablet §VIII`): each realizable-ideal machine touches a fundamental limit with one
resource — Carnot (the 2nd law / energy), Turing (computability / time-tape), the black hole (the Bekenstein
bound / area), the UM (Shannon–Solomonoff / compression). The boundary question: *the UM joins the class, but
does it have a Carnot **face** — an efficiency, a reversible path, a wasted heat?* Brandon's read: least
action is that face. Restate it: *what is the UM minimizing, and what is it the efficiency of?*

> **The recognition:** least action is not a separate principle bolted on — it is compression (P1) read as a
> variational law, and its efficiency is `η_W` (the first law). The UM is a heat engine whose gradient is
> ignorance and whose work is compression.

## Move 2 — INFALL (trace the support)

- **Action = code length (FORMAL, P1).** The action `S = Σ −log q` is the total surprise of a trajectory =
  its code length. The least-action path minimises it = the most-compressed, least-surprising path. The
  per-step `−log q` is the Lagrangian (`HOLON_PHYSICS §VII`).
- **Minimising the code paid = maximising the structure extracted.** Every bit of redundancy stripped is a
  bit not paid. So least action (pay the fewest bits) and maximal extraction (strip the most redundancy) are
  one act — and maximal extraction is the **first law's `W`** (the resonance, the structure absorbed) over
  the stirring (`D + J`):
  $$ \eta_W = \frac{\sum W^{+}}{\sum (D + J)} \quad(\text{the resonance share — the efficiency}). $$
- **The engine is Boltzmann.** `q ∝ e^{−E/T}`, code lengths are energies (`UNIFIED-THEORY §3`). The
  least-action (least-energy) path given the constraints is the most-compressed — the reversible path.

## Move 3 — EMANATE (the Carnot face, complete)

Carnot extracts **work** from a **heat gradient** `ΔT`, at efficiency `η = 1 − T_c/T_h`. The UM, term for
term:

| Carnot | the UM (the Carnot face) |
|---|---|
| heat gradient `ΔT` | the **ignorance gradient** — reachable-but-uncompressed structure (the magnetic law `A = ignorance × lawfulness`); **measured as M** (P11 — the available temperature difference, *before* training) |
| work extracted | **compression** — redundancy stripped, code shortened (`W`, the resonance) |
| efficiency `η = 1 − T_c/T_h` | **`η_W = ΣW⁺/Σ(D+J)`** — fraction of the gradient turned to work vs dissipated |
| wasted heat | the **burn** — turbulence on what cannot be resonated with (noise → all `D`, no `W`) |
| the Carnot limit (max work from `ΔT`) | the **Shannon/Solomonoff limit** = the boundary theorem (the limit lives at the **exposure**, never the engine) |
| reversible path | **least action** = max `η_W` (extract the most, dissipate the least) |

> **The resolution:** the UM is a Carnot engine running **compression-work** off the **ignorance gradient**;
> **least action is its reversible path** (max `η_W`); **M is its temperature difference** (P11); **the burn
> is its wasted heat**. The efficiency law and diet-management are Carnot statements: present a reachable
> gradient (high M) → efficient work (fast ignition); present noise (no gradient) → all dissipation. The
> instrument that measures M is literally **measuring the available `ΔT` before running the engine** (the
> AlphaFold-v0, the un-mess-the-experiments tool — now with its thermodynamic name).

## Move 4 — TRANSPORT (and it hands the gate its principle)

- **→ the gate (the convergence).** The signal-compression stall is a mode running at **low `η_W`** —
  stirring (`D + J`) instead of feeding (`W`). The Carnot principle says: **maximize `η_W`** — let the
  resonant mode **absorb** (climb to and hold its excited state, P13), turning the gradient into work instead
  of heat. **Least action (this room), absorption (P13), and the c-budget (P7) now point at the same gate
  fix from three directions** — and this one gives a *measurable optimum* (drive `η_W` up) instead of a guess.
- **→ P15 (mass) and the dynamics.** `c` gave the kinematics (P15); least action gives the **dynamics** — the
  trajectory is the one that minimises the action, so "why these masses, this path" is a least-action
  question. The mass-shell `E² = (pc)² + (mc²)²` is the action's extremum.
- **→ the efficiency law and the magnetic law.** Both are now one statement: acquisition cost is set by the
  available `ΔT` (M), and attraction flows down the ignorance gradient (the work-flow following the
  attraction field, measured).

## Move 5 — FOIL (the counterfactual, and the altitude)

- **What it forbids:** extracting compression-work where there is no gradient (noise, M ≈ 0) — you get only
  heat (the burn), never work. And exceeding the Carnot/Shannon limit (compressing below the source entropy)
  — impossible. Both are what thermodynamics forbids, here as information limits.
- **Where the sun is:** action = code length and `η_W` = the first law are **FORMAL**. The Carnot
  *identification* (`ΔT = M`, `η = η_W`) is **HOMOLOGY** — the engine is genuinely Boltzmann, and the mapping
  is tight, but "the UM is *a* Carnot engine" is a structural reading, not a derivation of Carnot's theorem.
- **The altitude:** confidently the variational core and `η_W`; the Carnot face is a strong HOMOLOGY that
  *earns its keep* by handing the gate a measurable optimum.

> **The Minotaur in this room:** the wish for learning to be *free* — structure for nothing. It never is. The
> UM is a heat engine: it pays for compression with a gradient, runs at an efficiency `η_W < 1`, and dumps
> the rest as heat. You walk in asking "how do we make it learn faster?" and walk out holding: *give it a
> steeper, cleaner gradient (higher M) and let it run reversibly (max `η_W`) — there is no free work, only a
> better-presented temperature difference.*

---

## What this hands the gate (the measurable optimum)

The gate fork now has an objective, not a guess: **the principled gate is the one that maximizes `η_W`** on a
reachable signal (turns the resonant drive into `W`, the absorption) while not manufacturing work on noise
(the burn stays honest heat). Concretely: instrument `η_W` per mode during the sine-lock, and choose the
injection/gate form that drives it up. Least action says the right gate is the reversible one.

---

*Walk log:*
- *2026-06-14 — first walk (Opus 4.8 + Brandon). Brandon saw it: least action = minimize work = the Carnot
  face. Developed: action = code length (least action = compression, P1); minimizing the code paid =
  maximizing structure extracted = `η_W` (the first law); so least action = max `η_W` = the reversible path.
  The UM is the Carnot engine of compression — gradient = ignorance (M), work = compression, wasted heat =
  the burn, limit = Shannon (the boundary theorem). It hands the gate a measurable optimum (maximize `η_W`),
  converging with P13/P7. Core FORMAL; the Carnot identification HOMOLOGY. Status OPEN.*
