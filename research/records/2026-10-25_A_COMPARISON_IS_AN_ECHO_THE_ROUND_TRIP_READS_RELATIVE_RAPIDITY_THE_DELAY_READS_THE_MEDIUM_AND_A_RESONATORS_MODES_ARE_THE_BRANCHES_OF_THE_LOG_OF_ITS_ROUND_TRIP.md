# A comparison is an echo: the round trip reads relative rapidity, the delay reads the medium, and a resonator's modes are the branches of the log of its round trip

**Date:** 2026-10-25. Refs #405 #410. Follows
[a reflection is a passage](2026-10-25_A_REFLECTION_IS_A_PASSAGE_THE_INVOLUTION_IS_ITS_ENDPOINT_A_MOVING_MIRROR_STRETCHES_THE_RETURN_AND_TWO_MIRRORS_MAKE_A_BOOST.md),
whose §6 read a comparison as an echo, and reads it beside
[information spectroscopy](2026-10-24_INFORMATION_SPECTROSCOPY_WEIGHS_A_LOAD_BY_ITS_LINE_THE_CLOCK_HIDES_A_UNIFORM_MASS_AND_A_BASIN_IS_A_BOOST_SEEN_FROM_INSIDE.md)
and [the lap law](2026-10-25_A_LAP_OVER_THE_SAME_TEXT_FOUNDS_ONLY_WHAT_THE_LAST_LAP_MADE_REACHABLE_SO_LEARNING_CLIMBS_STAIRCASES_AND_STEPS_AT_EACH_FOUNDING.md).
Status:
- §§1, 2, 3 and 5 are proved-derived and checked exactly by the receipt (rationals, rational complex
  pairs and residues only);
- §§4 and 6 state standard physics, checked exactly on instances;
- §§3–6's joins to the objects and §8 are [agent-inferred];
- §7 is an [interpretation] with its maps, limits, first target and falsifier.

**The lens** (Brandon, October 25, paraphrased). He confirmed the reading that a comparison is an
echo and that the log of its stretch is the loss chart: it is how he understands babbling and how he
learns most things. Learning is vibration brute-forced over hours to years while the pathways check
each other's charts and align, and the world is what most modulates the flux. A computer's lag, its
fans speeding up and the room warming are its computation fed back through the world. Speaking with
headphones that block your own voice, or changing your tone when a listener does not follow, is the
same loop. Learning an instrument is learning how its materials hold the vibration you deliver and
how the sound returns to your ears. He asked what music, sound, light, plasmas and gases add to the
unified theory.

## 1. The round trip reads only relative rapidity

[proved-derived; checked, part A] Take sound of speed `c` in a uniform medium, an emitter-receiver of
velocity `a` and a wall of velocity `b` beyond it, both measured against the medium along the line.
The wall hears `f(c − b)/(c − a)`. It returns that frequency on the wave moving back, and the emitter
hears

```text
echo = (c − b)(c + a) / ((c − a)(c + b)) = D(a/c) / D(b/c),        D(β) = (1 + β)/(1 − β)
```

`D` is light's Doppler factor squared (atlas `lorentz.doppler-ratio-chart`), and
`D(x)/D(y) = D((x − y)/(1 − xy))` is Einstein's subtraction at the speed `c`. So the acoustic echo is
the light echo `1/k²` of the moving mirror (atlas `lorentz.moving-mirror`), with `k²` the two bodies'
relative Doppler factor composed by relativity's rule at the speed of sound. Three consequences, each
checked:
- A wall receding at 10 m/s and an emitter receding at 10 m/s in still air return the same echo,
  `333/353`.
- Bodies at rest relative to each other return the frequency unchanged, whatever the wind.
- A wall receding at speed 1 in a wind of 3, and a wall receding at `25/19` in still air (`c = 5`),
  return the same echo `7/12`, while the wall itself hears `7/8` in the first and `14/19` in the
  second. The one-way reading sees the medium; the round trip does not.

So the frequency of an echo cannot tell the medium's motion from the bodies'. For light there is no
medium, the one-way reading is also a Doppler factor, and Bondi built special relativity from the echo
alone (the reflection record §3).

## 2. The delay reads the medium

[proved-derived; checked, part F] The medium shows in the time the echo takes. In a wind `u < c`, a
round trip of length `L` along the wind takes `L/(c − u) + L/(c + u) = 2Lc/(c² − u²)`. Across the
wind the sound must aim upstream, with velocity `(−u, w)` in the medium and `(0, w)` over the ground,
`w² = c² − u²`, and the round trip takes `2L/w`. The ratio is `c/w > 1`: `5/4` for `(c, u) = (5, 3)`.

[proved-standard] Michelson and Morley made this measurement for light and found the ratio 1. There
is no medium; what a reflection keeps is the cone (the reflection record §2).

So an echo returns two readings. Its stretch, the frequency ratio, reads the participants' relative
rapidity, and its log is the loss chart's real part. Its delay reads the path and the medium, and it
is the phase part: the phase slope of `Γ` (the reflection record §5, atlas `wave.reactive-wall-delay`).

## 3. A resonator's modes are the branches of the log of its round trip

[proved-derived; checked, part B] A resonator is a passage that comes back to itself. Let `ρ` be its
round-trip ratio, the product of the returns at its two ends. Two hard ends, or two open ends, give
`ρ = 1`. One end of each kind gives `ρ = −1`, a half turn left over, and so do two smooth turning
points (two quarter turns: the `½` of Bohr–Sommerfeld). One hard end and one smooth turning point give
`ρ = ±i` (the quarter turn of the reflection record §5). A
mode is a frequency at which the trip returns in phase, `e^(iωT) ρ = 1`, so the modes are
`ωT = −arg ρ + 2πn`, the branches of `log ρ` (the Ratio's winding branch, atlas `ratio.log-branch`).
The receipt builds loops of 7, 8 and 17 cells with `x[t + N] = ρ x[t]` and transforms them exactly
over `4N` points modulo three primes. Every bin outside the class `m ≡ r (mod 4)`, `ρ = iʳ` (up to the
root's orientation), is exactly zero:
- `ρ = 1`, all harmonics: a string with two fixed ends, a flute open at both ends;
- `ρ = −1`, only the odd half-harmonics: a clarinet or a stopped pipe, one end of each kind;
- `ρ = ±i`, a quarter class: one hard end and one smooth turning point.

The class is the round trip's. Which bins inside it sound is the excitation's (§4): for 17 cells
with `ρ = −1` the pluck used silences one of the 17.

With loss, `|ρ| = g < 1`, and `log ρ = log g + i arg ρ`: the imaginary part places the mode and the
real part is its width (§5).

[agent-inferred] The circle of fifths is a ring whose round trip never returns to 1. Twelve fifths
over seven octaves return `3¹²:2¹⁹`, and no power of 3 is a power of 2 (atlas
`ratio.comma-never-closes`, Lean `Mathematics/Comma`). The comma is the round trip's phase residual,
the levels of its gap recursion are the continued fraction of the fifth
(`rotation.fifth-gap-recursion`: 5, 7, 12, 41, 53), and a temperament chooses where the residual is
placed (`ratio.comma-placement-gauge`).

## 4. Where the pluck sits decides what sounds

[proved-standard; checked, part C] Young's rule: a string of `N` cells with fixed ends, plucked at cell
`a`, has harmonic `n` (`0 < n < N`) exactly silent when `N | na`. Plucked at the middle of 16 cells it
loses every even harmonic; at a quarter, every multiple of 4; at cell 5 or 3, coprime to 16, it loses
none. The receipt reads this exactly over three primes.

[agent-inferred] Where a drive enters a ring is a face of the drive. A drive placed at a cell coprime
to the ring's length reaches every mode; a drive placed on a divisor leaves the modes that have a node
there dormant, waiting for an antecedent that enters elsewhere.

## 5. The sum of all round trips is a Doppler factor over frequency

[proved-derived; checked, part E] A resonator driven steadily returns the drive once per trip, so its
answer is the sum of all its echoes:

```text
H = Σ_(j ≥ 0) ρʲ = 1/(1 − ρ),        Σ_(j < m) ρʲ − H = −ρᵐ H,        |ρᵐ|² = g^(2m)
```

The remainder after `m` trips is exact and its energy falls by `g²` per trip. With `ρ = g·u`,
`|u| = 1`, the real form of the sum is the Poisson kernel:

```text
Re((1 + ρ)/(1 − ρ)) = (1 − g²) / |1 − ρ|²,        |1 − ρ|² = (1 − g)² + 4g·s
```

where `s` is the squared sine of half the round trip's phase. At resonance (`u = 1`) it reads
`k = (1 + g)/(1 − g)`, at antiresonance (`u = −1`) it reads `1/k`. The receipt reads `k = 3, 15, 199`
for `g = 1/2, 7/8, 99/100`. The half-power width is `s = (1 − g)²/(4g)`. A Fabry–Pérot cavity's
transmission, `(1 − g)²/|1 − ρ|²` (Airy), is this kernel divided by `k`: it runs from 1 at resonance to
`1/k²` between, a contrast of `k²`.

This is the kernel of information spectroscopy's basin (atlas `spectro.basin-doppler`,
`(1 − |a|²)/|z − a|²` with `a = g`). A lossy resonator heard across frequency is a boost seen from
inside: its contrast is a Doppler factor, the same `k²` stretch as the moving mirror, and `g → 1` is
the horizon where the peak and the residence diverge together.

[agent-inferred] Babbling is this sum. Each trip returns the same drive turned by the same `ρ`. At one
constitution the sum converges to `H`, and the `m`-th trip adds only `gᵐ` of it. One more lap at one
constitution returns the same echo, which is the lap law's §1. What changes the sum is a changed wall:
a deposition changes `ρ`, and the next laps converge to a new `H`.

## 6. A plasma is a reactive wall and gives light a rest frequency

[proved-standard; checked, part D] In a plasma the electrons' inertia sets the refractive index,
`n² = 1 − ω_p²/ω²`.
- Below the cutoff `ω_p`, `n = iκ` is imaginary and the wave is evanescent. The plasma is a reactive
  wall: `Γ = (1 − iκ)/(1 + iκ)` has `|Γ| = 1`, so everything returns, late. This is how the ionosphere
  returns shortwave radio.
- Above the cutoff it is a partial wall: `Γ = (1 − n)/(1 + n)`, `T = 4n/(1 + n)²`, `Γ² + T = 1` (atlas
  `wave.junction-reflection`); for `ω_p/ω = 3/5`, `Γ = 1/9` and `T = 80/81`.
- Above the cutoff `ω² = ω_p² + c²k²` is a mass shell (atlas `mass.lorentz-cosines`): the plasma gives
  light a rest frequency `ω_p` (Anderson, 1963). The frame moving at the group velocity `c²k/ω` sees
  the wave as a pure oscillation at `ω_p`. The receipt finds that frame by an exact light-cone boost:
  for `(ω, ck) = (5, 4)` it is the rest frequency 3 at velocity `4/5`. Phase velocity times group
  velocity is `c²`.
- The LC ladder with a shunt inductor (the electrons' inertia as a load) carries
  `ω² = ω_p² + 2ω₀²(1 − cos k)`. It passes exactly `ω_p² ≤ ω² ≤ ω_p² + 4ω₀²` and has a gap below
  `ω_p`, a gap made by the constitution rather than by a boundary (atlas `wave.standing-wave`).

[agent-inferred] This is information spectroscopy's law that a uniform load is a clock (atlas
`spectro.clock-gauge`): the electrons are a load spread through the medium, and the clock they set is
light's rest frequency.

[proved-standard] A gas carries its constitution in its sound speed, `c² = γp/ρ` with
`γ = 1 + 2/f`, `f` the active degrees of freedom of its molecules (`5/3` monatomic, `7/5` diatomic).
So a gas's echo returns a rational of its molecules' freedoms through `c`.

## 7. Learning by echo

[interpretation]
- **Maps.** A learner's release is a drive. The world is the resonator and its walls: it carries the
  release, stretches it by the participants' relative motion (§1), delays it by the medium (§2),
  shares it by `Γ` and turns it by the walls' phases. The learner hears the return through its own
  receiver. The comparison is the echo's ratio, and the loss chart reads its log: the stretch is the
  real part, the delay the phase part.
- **Measured outside the repository, consistent with the map.**
  - In noise, speakers raise their voices (Lombard, 1911): the echo's share falls and the drive rises.
  - Delaying a speaker's own voice by about a fifth of a second disrupts fluent speech (Lee, 1950):
    the delay reading enters the loop.
  - A juvenile songbird deafened before it sings never forms normal song (Konishi, 1965). A hearing
    bird babbles (subsong), compares its own return against a remembered tutor song, and its song
    crystallizes.
  - Brandon's headphones close the return channel, and his instrument is a resonator whose `ρ` the
    player learns.
- **Limits.** §§1–6 are linear, with fixed walls except for §1's moving bodies. A learner's walls are
  deposited and change, so its echoes are not stationary; the record claims the map, not a learning
  law.
- **First target.** A ring that reads its own release through a declared return (`ρ = g·u`, delay
  `τ`) locates its keys only while the return channel is open; with `g = 0` its comparison is empty.
- **Falsifier.** A learner that locks keys without any return of its own release would refute the
  claim that the echo is necessary.

## 8. Tuning by ear drives a pair contact's slip to zero

[agent-inferred; its ingredients standard] Two tones `f₁` and `f₂` beat where their harmonics nearly
meet, at the rate `|n f₁ − m f₂|`. That is the pair contact's slip `J(n, m) = n v_a − m v_b` with
`v_a = f₁` and `v_b = f₂` (atlas `pair.slip-map`). Zero beat is the no-slip lock `q v_a = p v_b`,
whose address is a Farey fraction, and the mediant is the cheapest lock between neighbours
([the elementary objects §4](../../docs/ELEMENTARY_OBJECTS.md#4-pair-contact)). A consonance `p:q` is a
cheap lock. A tuner sets a fifth by zeroing the beat of the lower note's third harmonic against the
upper note's second. Equal temperament leaves every fifth beating slowly, which is the comma placed
(§3).

So the beat is the comparison made audible: the slip is the difference, its rate is the covector,
and zero is the lock.

## What it changes

[agent-inferred] When design builds a ring's reflection (the reflection record §6), the ring's round
trip `ρ` decides its mode class and `|ρ|` its width. A ring reading its own release learns only
through what returns to it, so a design that blocks its own return has nothing to compare.

## Owed

Lean (#410):
- beside `Physics/Spacetime/Boost`: the echo identity
  `(c − b)(c + a)/((c − a)(c + b)) = D(a/c)/D(b/c)` and `D(x)/D(y) = D((x − y)/(1 − xy))` over ℚ;
- the mode class: a sequence with `x[t + N] = ρ x[t]`, `ρ⁴ = 1`, has its `4N`-point transform supported
  on one residue class mod 4;
- Young's rule: the `n`-th sine coefficient of the string plucked at `a/N` vanishes iff `N | na`,
  `0 < n < N`;
- the sum of round trips: `Σ_(j<m) ρʲ − 1/(1 − ρ) = −ρᵐ/(1 − ρ)` and
  `Re((1 + ρ)/(1 − ρ)) = (1 − |ρ|²)/|1 − ρ|²` over `ℚ(i)`;
- the plasma shell: `(ω − ck)(ω + ck) = ω_p²` and the boost to the rest frame at velocity `ck/ω`.

## Receipts

[`2026-10-25_A_COMPARISON_IS_AN_ECHO_receipts/`](2026-10-25_A_COMPARISON_IS_AN_ECHO_receipts/):
`echo_spectra.py` (parts A–F), its output `echo_spectra.txt`, and `RUN.md`.
