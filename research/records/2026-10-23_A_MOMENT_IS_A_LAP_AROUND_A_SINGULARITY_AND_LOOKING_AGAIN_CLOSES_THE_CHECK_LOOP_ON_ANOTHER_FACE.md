# A moment is a lap around a singularity, and looking again closes the check loop on another face

**Date:** 2026-10-23. **Occasion:** Brandon asked the Athena work to step back from its mechanism
vocabulary (turns, boosts, towers, parametrons, locks) and describe it abstractly. In his reading,
whatever composes with intelligence has moments to think and learn. Those moments are like
vortices: singularities of their own present, at moments such as epochs. That is how he does
mathematics, which is why Athena's near misses look familiar to him. Each answer is slightly off in
a way that suggests it would come out right if it looked again. 73+31 came out 104 in one run and
106 in the next; 71+41 came out 102 and then 112. For him, forward and backward passes and gradient
descent are just geometry and direction in a fluid.

This record states that abstraction in the objects that already own it, measures "looking again" on
both of Athena's published output sets, and says what it means for generation. The design thread
builds the lap in the machine; this record fixes the law and the ceiling it will be read against.

## 1. The vocabulary was a fluid's all along

A singularity of a planar flow has a complex strength `c = m + iΓ`: `m` is its flux (a source or
sink) and `Γ` its circulation (a vortex). A pair of them at `z₁` and `z₂` has the potential
`F = (c/2π) ℓ`, where `ℓ` is the log of the ratio `(z − z₁) : (z − z₂)`, and its velocity is the
field of the move fixing `z₁` and `z₂` at rate `conj c` (`fluid.singularity-mobius-field`). Lean
classifies the kinds (`Physics/Fluid/Singularity`, `fluid.singularity-site-kinds`):
- a **source–sink pair** (`Γ = 0`) is the boost;
- a **vortex pair** (`m = 0`) is the turn;
- a **doublet** is the null kind, the shear or free fall;
- a **spiral** (`mΓ ≠ 0`) is loxodromic, a boost and a turn at once.

So the Swing's three kinds of motion are the three singular flows. Every move factors uniquely as
turn · boost · shear, so every move of the machine is a superposition of a vortex, a source–sink
pair and a doublet. In the same words, the other nouns read as:
- a parametron is a vortex in its own phase plane (charge and current exchanging); the pump strains
  that plane periodically, and past the bifurcation the strain wins, so the flow comes to rest on
  one of two locked sheets;
- a tower is the same flow restricted scale by scale (the scale square);
- a lock is a vortex that persists: by Kelvin, circulation on a material cycle is conserved by the
  ideal flow (`fluid.kelvin-holonomy`), and a vortex around a hole can carry circulation with no
  local swirl at all (`fluid.dormant-vortex`, the dormant class).

Locally the same three kinds are how a flow deforms a small blob. With the velocity written
`w = u + iv`, a small displacement moves by `δẇ = a δz + b δz̄`, where `a = ∂_z w = ½(div + iω)`
and `b = ∂_z̄ w = ½(s_n + i s_s)`. The direct coefficient is the flow's source and vortex; the
reflected coefficient is its strain. This is the direct and reflected passage of the parametron's
phase carrier (`phase.direct-reflected-modulation`, `PhaseCarrier.modulatedCarrier`). Its
determinant `|a|² − |b|²` (`modulatedCarrier_real_determinant`) is, with no divergence, `−W/4`,
where `W = s_n² + s_s² − ω²` is the Okubo–Weiss parameter:
- where the vortex beats the strain (`W < 0`) the flow turns (elliptic);
- where the strain beats the vortex (`W > 0`) it boosts (hyperbolic);
- where they balance (`W = 0`) it shears (parabolic).

The pump is a periodic strain of the ring's phase plane. So the parametric tongue is where the
pump's strain beats the ring's turn, and its edge, where Hill's kinds shear, is the balance `W = 0`.

## 2. Learning: the loss is the potential of a singularity

The loss is the log of a ratio of Holons, `ℓ = log R` with `R = z_T / z_H` (`ratio.loss-is-log-ratio`),
the same potential as §1.
- In the chart `w = z_H` of the produced amplitude on one cell, `ℓ = log z_T − log w`. This is the
  potential of a point singularity at `w = 0`, where the produced Holon gives the target no
  amplitude and the surprise is unbounded.
- Its derivative is the learning covector, `R⁻¹dR = −(d ln|w| + i d arg w)` (`ratio.log-derivative`).
- The real part is exact, the velocity of a source, and descent flows out of the singularity. Read
  along the logits it is half the cross-entropy logit gradient `p − q` (`ratio.loss-is-log-ratio`,
  `ratio.logit-covector`).
- The imaginary part is closed and not exact, the velocity of a vortex. It carries the phase, and
  its circulation is one turn per lap around the singularity. The lap count is the branch of the
  log (`fluid.singularity-winding-jump`: circulation and flux are winding readings of the lift of
  the log ratio).
- Where both amplitudes move along one coordinate (`z_T = z − z₁`, `z_H = z − z₂`), `ℓ` is exactly
  the pair potential of §1. Read with real strength it is a source–sink pair; read with imaginary
  strength it is a vortex pair.

**Gradient descent is the flux part alone.** It is a potential flow: curl-free, the exact part of
the Hodge split. It has no circulation, so it cannot count laps or carry phase. That is the law
"the classical loss without its phase part is incomplete" read in a fluid. Learning with both parts
is the spiral, the loxodromic flow in which paths converge while they turn. Paths converging is
what a landmark is (`compression.landmarks`), so a located key is a spiral sink.

## 3. Forward and backward are one flow read from its two sides

The forward pass pushes the state (the Holon, a vector) along the flow. The backward pass pulls the
covector (the coholon) back along the same flow by the adjoint:
`⟨Ĝ*Ȟ | H⟩ = ⟨Ȟ | ĜH⟩` (`navigator.adjoint`), in reverse order along a composed passage
(`holon.chain-rule-adjoint`). In a fluid:
- a material line element is carried forward by the flow's Jacobian;
- the normal of a level set is carried back by its transpose;
- their pairing, how often the line crosses the level sets, is kept.

That is all backpropagation is: the transport of a level set's normal backward along the flow that
carried the state forward. Emanation and infall are the same flow seen from the two sides of the
pairing. Direction is the only thing that distinguishes them.

## 4. A moment is a lap around a receiver's singularity

Elapsed time is already defined this way (`aeon.pairing`). A receiver reads a passage `γ` through
its clock form, `t_R(γ) = ⟨ω_R | γ⟩ = n_R + r_R`, whole windings plus an open phase. For the clock
`ω_R = dθ_R`, that form is closed and not exact: it is the velocity of a point vortex at the
receiver's own singularity.
- A **cycle** is a whole lap.
- An **epoch** is the interval between crossings of the receiver's section, and a **moment** is
  one crossing.
- Each receiver circulates around its own singularity, so each has its own present. This is
  Brandon's "contemporary singularities", and why no clock is privileged.

**Thinking needs laps.** A pass that crosses each section once has one moment. To think, the
passage has to come round again: return to the same section with its winding carried, and meet what
it produced. **Learning** is what those laps deposit. The circulation that persists is a located
key, dormant until a fitting passage meets it.

## 5. Looking again closes the check loop on another face

Take operands `a`, `b`, an operation `T` and a release `r`. On a cheap ring `ℤ/q` of the base, the
operands' faces compose to `T_q(q(a), q(b))`, which is one crossing on the rings 9, 10 and 11
([near-miss record](2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md), §§3 and 7).
Going round from the operands to the release and back to the faces gives the defect

`δ_q = q(r) − T_q(q(a), q(b))  (mod q)`,

which is the circulation of that check loop.
- The release is right exactly when every loop closes: if `r` lies in the size window `W` and
  `δ_q = 0` for every `q` in a family whose least common multiple exceeds the window's width,
  then `r = T(a, b)` (Chinese remainder theorem).
- A near miss is a loop that encloses a singularity on the faces it lost.
- **Looking again is one more lap.** It reads `δ` on one more face and narrows the release to the
  fibre where every loop read so far closes.

Measured exactly on both of Athena's published output sets (`laps.py`). The earlier set is the 13
held-back draws of the near-miss receipts; the later set is the pumped tower's 21 lines on unseen
pairs. The size window is the lengths and one leading digit of each operand. Lap `k` reads ring
10, 9, 11 and then 101, in that order.

| Set | Wrong | Caught on lap 1 (ring 10) | Caught by lap 3 (rings 10, 9, 11) | Closed to the right answer by lap 3 |
|---|---|---|---|---|
| earlier | 9 of 13 | 5 | 9 | 9 |
| later | 9 of 21 | 4 | 9 | 9 |

Every miss in both sets fails a check loop on ring 10, 9 or 11. In every case the release window
holds exactly one number that passes those three loops, and it is the right answer. Brandon's
examples:
- **73+31=106** fails the units loop: `3 + 1` gives 4 and the line has 6. Its defect is 2 on every
  ring, because 106 − 104 = 2.
- **71+41=102** keeps the units and loses the tens across the carry (`7 + 4 = 11`, the additive
  caustic). Its digit sum 3 fails the ring-9 loop, where `8 + 5 ≡ 4`. With the units 2, the size
  window `[110, 128]` and digit sum 4, only 112 remains.

Over every two-digit operand pair, the number of laps that closes the release:

| Operation | 1 lap | 2 laps | 3 laps | 4 laps (ring 101) |
|---|---|---|---|---|
| sum (8,100 = 2²·3⁴·5²) | 810 | 7,290 | | |
| difference (4,095 = 3²·5·7·13) | 855 | 3,240 | | |
| product (8,100) | | | 7,100 | 1,000 |

The two runs also show why answers move between runs. Of the 13 questions in both sets:
- four went from wrong to right (71+41, 23+51, 56+3, 99-56);
- two went from right to wrong (73+31, 8+82);
- two stayed right;
- five stayed wrong with a different value (74-72 and the four products).

Each run draws from the fibre of the faces it kept, so a changed field keeps a different set of
faces. In the later set, every product miss stays in the size window, four of the five keep the
units, and all five lose rings 9 and 11. A look that reads the loops holds the faces fixed instead of redrawing them all.

This is an exterior count. It says what the faces determine, the ceiling of a look; it is not the
machine's result. Brandon's impression holds within that ceiling: each published miss would be
corrected by laps on faces she can in principle locate. The design thread reads her product
parity right in 193 of 193 and mod 9 in 37 of them (about 21 by chance), so the ring-9 and ring-11
loops are where she is short.

## 6. What looking again means for generation

Agreed with the design thread, which builds it:
- Generation runs in laps. After a line is written, she reads it back through the same field from
  the state the line left (the design thread's stream read).
- Her located ring modes compose the operands' faces. The defect on each face is the circulation of
  its check loop, and the release is redrawn inside the fibre where every loop she can read closes.
- The laps continue until the release stops moving, a fixed point of the look. No lap count is
  chosen by hand.
- The same defect is the covector the lap deposits, so the lap that corrects also learns.
- `T_q` must be her own located modes: lag-residue modes with no turn, a half-turn and a
  quarter-turn (near-miss record §6). An authored calculator, digit table or carry routine is the
  catered machinery the antipattern record refuses. The count in §5 is only the ceiling those faces
  allow.
- The look has a certificate (from Epime's review). Over a written line, the pumped mode's transport
  composes to `h_t = a h_0 + b h̄_0 + c` (`modulatedCarrier_compose`): `(a, b)` carry the word's turn
  and reflection, and `c` the state the line forced. The map `h ↦ a h + b h̄` has singular values
  `|a| + |b|` and `||a| − |b||`. So when `ρ = |a| + |b| < 1`, reading the same line again,
  `h ↦ a h + b h̄ + c`, has exactly one fixed point, and each lap brings the state at least the factor
  `ρ` closer to it. That is the vortex settling. At a declared grain `g`, a state at distance `D`
  stops moving once `ρⁿ D < g`, so `ρ` and the grain set the number of laps. A closed lap starts and
  ends in one frame, so a change of frame `G M G⁻¹` conjugates the map and carries its fixed point
  with it.
- Acceptance, fixed before the build: on unseen pairs, the lines right after the lap against before
  it, by operation, with the closure of each loop reported per face.

## 7. Owed

- Lean (#410):
  - **Check-loop closure decides the release.** For moduli `Q` with `lcm Q` above the window's
    width, `r ∈ W` and `T(a, b) ∈ W` with `r ≡ T(a, b)` modulo every `q ∈ Q` give `r = T(a, b)`.
    The loop composes, `q(T(a, b)) = T_q(q(a), q(b))` for `+`, `−` and `·`.
  - **The loss chart's singularity.** In the produced amplitude's chart,
    `R⁻¹dR = −(d ln|w| + i d arg w)`. Its real part is exact, and its imaginary part is closed with
    circulation `2π` per lap around `w = 0`, joined to `Physics/Fluid/Singularity` and
    `Objects/Ratio`.
  - **The look settles.** For `ρ = |a| + |b| < 1`, `L(h) = a h + b h̄ + c` has one fixed point `h*`
    and `|Lⁿh − h*| ≤ ρⁿ |h − h*|`, beside `PhaseCarrier.modulatedCarrier_compose`. A velocity
    gradient's direct and reflected parts are `∂_z w` and `∂_z̄ w`, and its determinant is `−W/4`
    with no divergence (Okubo–Weiss).

## Receipts

[`2026-10-23_A_MOMENT_IS_A_LAP_receipts/`](2026-10-23_A_MOMENT_IS_A_LAP_receipts/): `laps.py`, its
output `laps.json` (each line's defects, fibre after every lap and laps to close; the questions
shared by both runs; the lap census over two-digit operands) and `RUN.md`. Exact integer work.
