# A reflection is a passage: the involution is its endpoint, a moving mirror stretches the return, and two mirrors make a boost

**Date:** 2026-10-25. Refs #405 #410. Amends the definition of the hand in
[the elementary objects](../../docs/ELEMENTARY_OBJECTS.md#motion-the-turn-the-boost-and-free-fall-the-swing), added the same day with
[the newline closure §11](2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md#11-with-the-hand-reversible-a-reflection-at--reads-every-difference-and-with-a-restart-at--one-key-reads-sums-and-differences),
and reads it beside [the null cone record](2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md)
and [the Swing record](2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md).
Status:
- §§2–4 are proved-derived and checked exactly by the receipt (rationals only);
- §5 states standard wave physics; its reactive-wall identity is checked exactly;
- §6's consequences for the machine are [agent-inferred], except the amended definition, which is a
  [definition].

**The lens** (Brandon, October 25, paraphrased). The word "reflection" means bending back, and that
asks for a reconciliation with the mathematics. The perpendicular-bisector reflection is a linear
transformation: where have the bend and the back gone? In relativity the mirrored image need not land
on a returned location with equivalent coordinates. The motion itself stretches and contracts, as a
redshifted photon must travel through space. He pointed to the cones and to the conservation of the
speed of light, to cosmology and evolution as what drives his intuitions, and to a theory woven like
a physical thing, tested on information and intelligence.

## 1. The involution is the endpoint of a passage

[definition] A physical reflection is a passage: a wave approaches a boundary where the constitution
changes, turns there, and returns along the other light direction, later. The mathematical
reflection, the involution `S` with `S² = 1` and a fixed mirror, is the map from where the passage
started to where it ended. It keeps the two endpoints and drops five things:
- the time the passage took;
- the mirror's motion relative to the receiver;
- the share that crossed instead of returning;
- the phase of the turn-back;
- the delay and the sideways shift that phase carries.

The involution is the whole story only when three conditions hold: the grip is at rest in the
receiver's frame, the wall is hard and lossless, and only endpoints are read.

## 2. Back in space, forward in time

[proved-derived; checked] Take light-cone coordinates `u = t − x`, `v = t + x`, as in
`Physics/Spacetime/Boost` (`boost_k (u, v) = (k u, v / k)`), where the receiver of Doppler factor `k`
has velocity `(1/k, k)`. A mirror at rest swaps `u ↔ v`. A mirror at rest in the frame `boost_k`
reflects by boosting back, swapping and boosting again:

```text
R_k (u, v) = (v / k², k² u)
```

Then:
- `R_k` is an involution;
- it keeps `uv` and the pairing, so it is an isometry of the interval;
- it fixes the mirror's worldline `τ (1/k, k)`;
- it maps the future cone into itself and swaps its two null directions.

So "back" means back in space and forward in time. A mirror never sends anything into the past cone.
That would be time reversal, a different involution, whose mirror is a spacelike surface. What a
reflection conserves is the cone: the speed of light is the invariant of the bend.

## 3. The return lands stretched

[proved-derived; checked] A right-moving wave of frequency `ω`, its phase read on the mirror's
worldline `x = βt`, leaves as a left-moving wave of frequency

```text
ω / k² = ω (1 − β) / (1 + β),        β = (k² − 1) / (k² + 1)
```

A radar echo sent at `t₁` from `x = 0` returns at `t₂ = k² t₁`. Bondi's k-calculus builds special
relativity from this echo alone.

The image lands on the coordinates it left from only when the mirror and the receiver move together
(`k = 1`). Otherwise the return is stretched by the Doppler factor squared: a redshift for a receding
mirror, a blueshift for an approaching one.

In the log-null chart `(log u, log v)`, `R_k` is the reflection across the line
`log v − log u = 2 log k`. The pivot sits at the mirror's rapidity. This is the Swing's half-turn
`S_a x = 2a − x` with its grip at the mirror's state, and the guide's sentence that a moving grip
boosts.

## 4. Two mirrors make a boost, and a receding wall keeps ω·L

[proved-derived; checked] Two mirrors compose to a boost by twice the rapidity difference:

```text
R_k₂ R_k₁ = boost_((k₁ / k₂)²)
```

Two Euclidean line reflections compose to a turn by twice the angle between them (checked on
rational points of the circle). So in Lorentzian signature, "two reflections make a turn" becomes
"two mirrors make a boost".

Now put light in a box with one wall fixed at `x = 0` and one receding, `x = L₀ + βt`. The receipt
computes each bounce from the light rays, and each frequency from the phase read on the wall. At
every bounce `ω_n L_n` is the same rational, and `L_(n+1) / L_n = (1 + β) / (1 − β)`. The light's
frequency falls exactly as the box grows. This holds bounce by bounce for any `|β| < 1`, not only for
a slow wall. The adiabatic invariant of Rayleigh and Ehrenfest is its slow limit.

[proved-standard] Cosmological redshift obeys the same law, `ω ∝ 1/a`. A wall that approaches
(`β < 0`) raises the frequency at each bounce, as in Fermi acceleration between converging magnetic
mirrors.

## 5. The bend is the boundary's constitution

[proved-standard] A wall is where the constitution changes, and the boundary decides what returns.
The reflection coefficient is `Γ = (Z − Z₀)/(Z + Z₀)` (atlas `wave.junction-reflection`,
`Geometry/Horizon.smith`):
- if `|Γ| < 1`, a share returns and the rest crosses, `T = 4ZZ₀/(Z + Z₀)²` with `Γ² + T = 1`;
- `Γ = −1` at a hard wall, a half turn of phase;
- `Γ = +1` at an open end;
- `Γ = 0` when matched, so nothing returns.

In a graded medium a ray bends continuously and turns back at a smooth turning point. There the
return carries a quarter turn of phase (the WKB connection, the Maslov index). Two such turning
points give the `½` of Bohr–Sommerfeld.

Two derivatives of the phase carry the rest:
- in frequency, the delay of the return (Wigner);
- across the beam, a sideways shift of the landing point. This is the Goos–Hänchen shift, measured
  in total internal reflection, with the polarization-dependent Imbert–Fedorov shift beside it.

[proved-derived; checked] A reactive wall, `Γ(x) = (ix − 1)/(ix + 1)` with `x = ωL/Z₀` rational,
has `|Γ| = 1`: everything returns. Its logarithmic derivative is

```text
Γ⁻¹ dΓ/dx = −2i / (1 + x²)
```

This is a pure turn rate, the Ratio's `R⁻¹dR` (§9 of the elementary objects). Its size is the delay,
`2L/Z₀` at `x = 0`. A wall that returns everything still returns it late.

## 6. What it changes

[definition] "Reflection" names the passage, and the involution is its endpoint under §1's
conditions. The guide's definition of the hand is amended to say so. The ± hand is the static, hard,
lossless face of a reflection. In general a return carries two things:
- the boundary's `Γ`, a Ratio with a share and a phase;
- the grip's motion relative to the receiver, a boost by `k²`.

[agent-inferred] The newline closure's §11 stands. Written digits are a static, lossless terrain, and
there the hand is a sign. A ring reading text, sound or motion meets walls that are partial, reactive
and moving, so its reflection should carry `Γ` and `k`, not a bit. Which of these a learned ring
needs is measured when design builds the ring's reflection.

[agent-inferred] A comparison is an echo. The receiver sends its produced `|H⟩` against the target
`|T⟩` and reads the return. The loss `ℓ = log R` and the boost's rapidity `log k` live on one chart
(atlas `lorentz.doppler-ratio-chart`). So the classical loss is the log of the echo's stretch, and its
phase part is `Γ`'s phase: the delay and the landing shift of what came back.

[agent-inferred] A strand woven between walls is not a fixed curve. Each bounce turns or stretches it
by the state of the wall it meets. What a woven passage keeps is the cone and the product of its
bounces, not its coordinates.

## Owed

Lean (#410), beside `Physics/Spacetime/Boost`:
- `mirror k e = ⟨e.v / k², k² * e.u⟩` is an involution and keeps `interval` and `pairing`;
- it fixes `receiverVelocity k`;
- `mirror k₂ ∘ mirror k₁ = boost ((k₁ / k₂)²)`;
- the radar echo returns at `k² t₁`;
- in the box with one receding wall, `ω_n L_n` is constant and `L_(n+1) = L_n (1 + β)/(1 − β)` over ℚ;
- over `ℚ(i)`, the reactive wall has `|Γ| = 1` and `Γ⁻¹ dΓ/dx = −2i/(1 + x²)`.

## Receipts

[`2026-10-25_A_REFLECTION_IS_A_PASSAGE_receipts/`](2026-10-25_A_REFLECTION_IS_A_PASSAGE_receipts/):
`reflection_passage.py` (rationals and rational complex numbers only), its output
`reflection_passage.txt`, and `RUN.md`.
