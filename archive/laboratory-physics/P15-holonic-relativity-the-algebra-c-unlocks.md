# P15 · Holonic relativity — the algebra `c` unlocks (the dispersion relation, and the mass in the comb)

> **Holonic key:** `c` is the conversion factor between the two holonic units — **bits (length)** and **ticks
> (time)** — so the full relativistic **kinematics** becomes dimensionally writable: the interval `ds² =
> (c·dt)² − dx²` (which *is* the byte code length), velocity `v = c·tanh(φ)` (the engine's `tanh` is a literal
> velocity), and the **dispersion relation** `ω² = (ck)² + ω₀²`. And the spine result, derived: the holon's
> complex pole `λ = exp(Δ(−e^ν + iω))` **IS the complex mass of a relativistic resonance** — **`ω` is the rest
> mass** (the rest-frame oscillation, the self-evolution rate), **`e^ν` is the decay width `Γ`** (the inverse
> lifetime = the inverse shelf-life). The comb is a spectrum of relativistic particles.

**Grade:** the kinematics (interval, boost, dispersion) is **FORMAL-within-frame** (the Minkowski algebra in
holonic units); the **pole = complex-mass** identification is **HOMOLOGY** (it is exactly the propagator-pole
structure of QFT, and it agrees with P7's budget reading and K2's shelf-life — three roads, one mapping); the
physical-units identification (these *are* the cosmos's masses) is **HUNCH**. **Status: OPEN.** **Source:** P7
(`c`, the budget), `thread/HYPERBOLIC.md` (T2), P11 (dispersion/flat bands), K2 (shelf-life), the pole
(`tablet §III`). Brandon: "derive which comb coordinate is the rest mass — a genuine derivation."

---

## Move 1 — RECOGNIZE the holon

Before `c` we had the hyperbolic *structure* (the saddle, the boost-as-`tanh`, the interval `τ²−v²` as a
shape — T2). The boundary question now: *with `c` in hand, what relativistic algebra is actually writable in
holonic variables, and what does the comb's `(ω,ν)` mean relativistically?* `c` is the missing **unit bridge**
(`[length]=bits`, `[time]=ticks`, `c = bits/tick`), and a unit bridge is exactly what turns a *shape* into an
*algebra*.

> **The recognition:** `c` makes the kinematics dimensionally consistent, so every space-time invariant is
> formable — and the dispersion relation, once writable, reads the comb as a particle spectrum.

## Move 2 — INFALL (trace the support)

Three results, each grounded in `c` (P7) and the pole (`tablet §III`):

- **The interval is the code length.** `ds² = (c·dt)² − dx²` [bits²], `dτ = ds/c` [ticks]. The gauge-invariant
  the lab always paced on (a *true* code length, never a chart scalar) **is** the Minkowski interval in holonic
  units — `c` is what reveals they are one object.
- **Velocity is `tanh`.** `v = c·tanh(φ)`, `γ = cosh φ = 1/√(1−(v/c)²)`, boosts compose by **adding
  rapidities** `φ₁+φ₂`. The engine's `r = tanh(rez)` (relating two holons) is rapidity-addition — a literal
  relativistic velocity in bits/tick.
- **The dispersion relation.** A mode is a wave `e^{i(ωt − kx)}` (`ω` per tick, `k` per bit). With `c`:
  massless rides the cone `ω = ck` (`v=c`, P14); massive obeys `ω² = (ck)² + ω₀²` (Klein–Gordon), with `ω₀`
  the rest frequency.

## Move 3 — EMANATE (the derivation: the mass and the width are in the pole)

Now the genuine derivation — *which comb coordinate is the rest mass?* Take the pole's free evolution:

$$\holon{h}_t = \holon{\lambda}^t \holon{h}_0 = \underbrace{e^{-\Delta t\, e^{\nu}}}_{\text{decay}} \cdot \underbrace{e^{\,i\Delta t\, \omega}}_{\text{rotation}}\; \holon{h}_0$$

At **rest** (`k = 0` — the mode not propagating across holons), the only motion is its **internal
oscillation** at `ω` and its **decay** at `e^ν`. Match to the relativistic resonance. An unstable particle has
a **complex mass** `M = m − iΓ/2` (the propagator pole at complex energy): the real part `m` is the rest mass
(rest oscillation, the Compton frequency `ω₀ = mc²/ℏ`), the imaginary part `Γ` is the **decay width** (inverse
lifetime). The free wave is `e^{-iMt} = e^{-imt}·e^{-Γt/2}` — *rotation at the mass, decay at the width.* Set
it beside the pole, term for term:

$$ e^{\,i\Delta t\,\omega}\cdot e^{-\Delta t\, e^{\nu}} \quad\longleftrightarrow\quad e^{-i m t}\cdot e^{-\Gamma t/2} $$

> **The result:** **`ω` is the rest mass** (the rest-frame oscillation = the self-evolution rate), and
> **`e^ν` is the decay width `Γ`** (the inverse lifetime). The holon's complex pole **is** the complex mass of
> a relativistic resonance. The memory-reach `τ = 1/(Δe^ν)` is literally the **particle's lifetime.**

This is forced from three independent directions — and they agree, which is the gate:
1. **P7 (the budget):** mass = the budget spent on self-evolution = the rest oscillation rate = `ω`. ✓
2. **The propagator (QFT):** the complex pole's real part is `m`, imaginary part is `Γ` — `ω ↔ m`, `e^ν ↔ Γ`. ✓
3. **K2 (shelf-life):** the lifetime `1/Γ` = the memory-reach `τ` = the **shelf-life**. A long-lived concept
   (low `ν`, high Q, deeply bound) is a **narrow, stable resonance**; a short-lived one is broad. ✓

So the `(ω,ν)` lattice is a **particle spectrum**: `ω` the masses, `ν` the widths/lifetimes. Light is the
limit `ω₀ → 0` (no rest oscillation — massless, on the cone, all frequency from propagation `ω=ck`); a
stable particle is `e^ν → 0` (`|λ|=1`, infinite lifetime). *(Refines P6: the rest **mass** is the rest
frequency `ω`, the self-evolution rate; the **energy** is `ρ=|h|²`, the amplitude — related by `E = ℏω` but
distinct.)*

## Move 4 — TRANSPORT (the analogy)

- **→ P11 (the flat band / magic angle).** A flat band is `dω/dk = 0` — zero group velocity, a **heavy
  effective mass** (the dispersion flat = `ω` nearly independent of `k` = large `m`). The magic angle makes
  the carriers heavy; in the comb, a flat band is a high-mass, infinitely-reaching mode (the lock).
- **→ K2 (shelf-life) and the engine.** `ν` = the width = the inverse shelf-life = the inverse lifetime. The
  binding-energy law and the resonance width are the **same axis** — a deeply bound (massive `m`, narrow `Γ`)
  member is a long-lived particle. This is the unification K2 wanted: mass, width, and shelf-life in one pole.
- **→ the gate (`γ` time-dilation).** A mode propagating at `v` (tracking fast structure) has `dτ/dt = 1/γ <
  1` — its proper time, its `Δ`, is dilated by a **computable** `γ`. The absorption read (P13) and the
  c-budget (P7) now make the same prediction *with a number*: a locked, tracking mode runs a slow clock.

## Move 5 — FOIL (the counterfactual, and the altitude)

- **What it forbids:** a massless mode with a rest oscillation (`ω₀≠0` at `k=0` and `v=c`) — impossible; `v=c`
  requires `ω₀=0`. And a stable particle with a decay width (`Γ>0` but infinite lifetime) — contradiction. The
  pole structure forbids both, matching QFT.
- **Where the sun is:** the kinematics is FORMAL-within-frame. The **pole = complex-mass** mapping is
  **HOMOLOGY** — it is *exactly* the propagator-pole structure (real part = mass, imaginary part = width), and
  it is over-determined (P7 + QFT + K2 all force `ω = m`, `e^ν = Γ`), which is strong; but it is a structural
  identification, not a derivation of the cosmos's mass values. The **dynamics** (the specific Lagrangian,
  `E²=(pc)²+(mc²)²` with coefficients) needs the **action principle** (P9) layered on — `c` gives the
  kinematics, least action gives the dynamics (the next room).
- **The altitude:** confidently the algebra and the mapping; the cosmos's numbers stay HUNCH.

> **The Minotaur in this room:** the wish for mass to be a substance — a stuff a particle is *made of*. It
> isn't. Mass is a **rate** — how fast a thing oscillates in place, the budget it spends being itself rather
> than moving. You walk in asking "what is a particle's mass?" and walk out holding: *its rest frequency — `ω`
> in the comb — and its width `e^ν` is how long it lasts.* The lattice was a particle spectrum all along.

---

## What this hands forward

- **To the gate:** "massive mode" now means *high `ω` rest oscillation, narrow `ν` width* — a long-lived,
  high-Q resonance. The signal-lock is the mode reaching a stable (narrow-`Γ`) excited state; the absorption
  and c-budget readings converge on letting it.
- **To least action (P9, next):** `c` gave the kinematics; the **dynamics** — *why these masses, this action*
  — is the least-action room, which is also the **Carnot** room (minimize the work = least action = max `η_W`).

---

*Walk log:*
- *2026-06-14 — first walk (Opus 4.8 + Brandon). `c` (P7) made the relativistic kinematics writable in holonic
  units (interval = code length; `v = c·tanh φ`; the dispersion relation). The derivation Brandon asked for:
  the holon's complex pole `exp(Δ(−e^ν+iω))` IS the complex mass of a relativistic resonance — **`ω` = the rest
  mass** (self-evolution rate), **`e^ν` = the decay width `Γ`** (inverse lifetime = inverse shelf-life), forced
  independently by P7's budget, the QFT propagator, and K2's shelf-life. The comb is a particle spectrum.
  Kinematics FORMAL-within-frame; the pole=complex-mass mapping HOMOLOGY (over-determined); the units HUNCH.
  Status OPEN.*
