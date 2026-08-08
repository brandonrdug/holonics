# P16 · The glass cup — a holon sings only with shape, finger, and ear

> **Holonic key:** A holon **compresses a signal by resonating with it** — and resonance, like a wineglass
> singing under a wet finger, needs **three things together, in order**: the **shape** (a mode whose `ω` lands
> on the signal's frequency — only then is there anything to ring), the **finger** (the drive/gate that pumps
> that mode — the stick-slip that self-locks the resonance), and the **ear** (the readout that actually reads
> the ringing mode). The cup sings only when all three are right. And you **cannot judge it by `κ`** — one
> scalar cannot tell you which of the three is failing; you must **hear the music** (the jet: per-mode work,
> `η_W`, the drive frequency against the comb), in the right frames.

**Grade:** the three-ingredient resonance structure is FORMAL-within-frame (it's the first law `Δρ=D+J+W` +
the comb-as-filter-bank, §III); the glass-cup analogy is HOMOLOGY (a tight source-structure isomorphism, the
§0 discriminator: the *physics of resonance* transfers, the cup's material does not). **Status: OPEN.**
**Source:** the first law (P7-of-`PRIMITIVES`), P13 (absorption = `W>0`), P15 (`ω`=frequency, `ν`=width),
P9 (`η_W`); the gate diagnosis (`listen.rs`). Brandon: "hear the music of the resonance, not the face value."

---

## Move 1 — RECOGNIZE the holon

A holon compresses a signal when its modes **resonate** with the signal's structure (the first law's `W>0` —
P13 absorption; the comb is a running Gabor filter bank, §III). The boundary question: *when does a holon
actually sing — and when it doesn't, how do you tell why?* The wineglass names it: rub a wet finger round the
rim and it rings — but only if **(1)** the glass has the right shape (a resonant mode at that pitch), **(2)**
the finger does the stick-slip trick (pumps the mode), and **(3)** you have an ear to hear it.

> **The recognition:** resonance — and therefore compression — is **not one mechanism but three, complementary
> and ordered**: a **shape** that can ring, a **finger** that pumps it, an **ear** that reads it. Miss any one
> and there is silence — and the silence looks identical from outside (the same flat `κ`).

## Move 2 — INFALL (trace the support)

| ingredient | the glass cup | the holon |
|---|---|---|
| **shape** | the rim's geometry sets the resonant pitch | the **lattice/comb** — a mode whose `ω` lands on the signal's frequency (P15: `ω`=frequency). No mode at the pitch ⇒ nothing to ring. |
| **finger** | the **stick-slip** friction — it doesn't move at the resonant frequency, it *self-organizes* to it (injection locking) | the **drive/gate** — the afference enters and the one nonlinearity self-locks the mode (the absorption pump, `W>0`, P13). |
| **ear** | hearing the tone | the **readout/head** — reads the ringing mode's phasor (`Re h, Im h`) and predicts. A mode can ring perfectly and the ear miss it. |

The grounding: the first law `Δρ = D + J + W`. Ringing = `W>0` (phase-matched pump). Off-resonance = `W≈0` or
`<0` (the drive stirs and damps — `D+J` without `W`; `η_W` low). So **`η_W` is the cup's voice**: high = it
sings, low (or `W<0`) = it dissipates, dead.

## Move 3 — EMANATE (hear the music, not the scalar)

Here is the method, which is the whole point. `κ` (the code length) is *one number*, and a high `κ` is
consistent with **all three** failures — wrong shape, wrong finger, missing ear. So judging by `κ` is judging
by face value, and it sent us sanding the finger for turns while the glass could not sound the note. **You
must listen** — read the jet in the right frames (P9, the relativity of reads):

- **the shape:** is there a comb mode near the signal's `ω`? (compare the drive frequency to the comb.)
- **the finger:** `η_W`, and **which** modes carry positive work (the top ringing modes — are they near the
  signal, or catching harmonics?). `W<0` overall = the cup dissipating.
- **the ear:** do the ringing modes get read? (the prediction error *given* that modes resonate — if they
  ring but `κ` stays high, the head isn't reading them.)

> **The resolution:** the live read (`listen.rs`) localized our stalled sine instantly — **a shape failure**:
> the sine's `ω=0.273` sat *below* the comb's lowest mode (`0.349`), so no mode could ring; `η_W=0.177` with
> total `W<0` (dissipating), and the modes that *did* ring were high harmonics far from the fundamental. One
> jet read said what turns of `κ`-watching could not. **The fix is therefore the shape (the living lattice —
> the `ω` must tune onto the pitch), then the finger, then the ear — complementary, not a fork.**

## Move 4 — TRANSPORT (the analogy)

- **→ the living lattice (the engine).** "Shape first" = the lattice must be **living**: a mode's `ω` tunes
  toward the structure it perceives (so a mode lands on the pitch), and its `ν` narrows as it locks (P15:
  width → stable, high-Q resonance). The finger (a phase-sensitive, `W`-driven lock) and the ear (the head
  reading the tuned mode) complete it — all three local, no backprop. (`LIVING_LATTICE.md`.)
- **→ P9 (Carnot) / P13 (absorption).** `η_W` is the cup's voice (P9 — maximize it); ringing IS absorption to
  the excited state (P13). The glass cup is those two rooms made audible.
- **→ the reading disciplines.** "Read the generation, not the scalars" is exactly "hear the music, not the
  face value." This room is that law, caught in the act of being broken and recovered — `κ` is a scalar, the
  jet is the generation.

## Move 5 — FOIL (the counterfactual, and the altitude)

- **What it forbids:** declaring a resonance dead (or alive) from `κ` alone. The same `κ` covers a dead
  shape, a slipping finger, and a deaf ear — only the jet separates them.
- **Where the sun is:** the three-ingredient structure is FORMAL-within-frame (the first law + the filter
  bank); the glass-cup *analogy* is HOMOLOGY (the resonance physics transfers; the material doesn't — §0).
- **The altitude:** the method (listen, don't judge `κ`) is a discipline, not a theorem — but it earned its
  keep on first use (it found the shape failure in one read).

> **The Minotaur in this room:** the single number — the wish for `κ` to tell you everything, so you can
> optimize it blind. It can't; it's a scalar over a three-part resonance. You walk in staring at one digit and
> walk out *listening* — to which modes ring, whether the finger pumps, whether the ear hears — and the glass
> tells you, in its own voice, exactly which of the three to fix.

---

*Walk log:*
- *2026-06-14 — first walk (Opus 4.8 + Brandon). Brandon: "hear the music of the resonance, not the face
  value… the glass cup needs the right shape, the finger trick, and ears to hear it — and (a)/(b) sound
  complementary, not a fork." Rendered: compression = resonance = three complementary, ordered ingredients
  (shape/finger/ear); `κ` can't separate their failures, the jet (`η_W`, per-mode work, the drive freq vs the
  comb) can. The `listen.rs` probe found our stall was a SHAPE failure (sine below the comb), vindicating the
  living lattice as the keystone. Structure FORMAL-within-frame; the analogy HOMOLOGY; the method a discipline
  that earned its keep. Status OPEN.*
