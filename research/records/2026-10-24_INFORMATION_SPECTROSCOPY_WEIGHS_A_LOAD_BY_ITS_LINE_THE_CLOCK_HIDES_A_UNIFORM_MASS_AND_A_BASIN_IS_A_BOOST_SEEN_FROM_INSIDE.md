# Information spectroscopy weighs a load by its line: the clock hides a uniform mass, and a basin is a boost seen from inside

Refs #404 #410. Extends [the receiver quotients the spectrum](2026-08-05_THE_RECEIVER_QUOTIENTS_THE_SPECTRUM_CAUSALITY_LOCKS_ITS_FACES.md)
(§7, information spectroscopy: lines are poles, colour is the receiver's quotient, metamers its
kernel) and joins [a moment is a lap](2026-10-23_A_MOMENT_IS_A_LAP_AROUND_A_SINGULARITY_AND_LOOKING_AGAIN_CLOSES_THE_CHECK_LOOP_ON_ANOTHER_FACE.md),
[code length is a field](2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM_ITS_BINDING_SHOWS_ONLY_THROUGH_CONTACTS_AND_THE_PRIMES_HAND_SITS_ON_THE_FLOOR.md),
[faces read on cycles](2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md)
and the leverage law of [the effective tension record](2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md) §9.
Status:
- the identities of §1 to §6 are proved (standard, or derived here by short algebra) and every one
  is checked exactly in the receipts;
- the physical instances are proved-standard and cited;
- the readings of information, of the tower and of the dictionary in §7 and §8 are
  [interpretation; agent-inferred, October 24].

Brandon's lens (paraphrased, October 24): think of something like the Doppler method of
spectroscopy, to gauge information as something massive whose structure and shape change, with
mass and viscosity; it is also like a singularity or a basin, a thing of the space-time fabric;
read it with breadth across the intuitions and Holonics.

## The result in one paragraph

A mode of any constitution is one complex line `s = −γ + iω`, and the logarithmic derivative of
its ratio is boost rate plus `i` times turn rate. A load moves the line: mass and stiffness move it
along the turn, viscosity along the boost (§1). A receiver's clock (its motion, a redshift, a lapse)
moves every line by one common factor, so it is invisible in every line ratio and every loss angle;
a load that is uniform across the modes is exactly such a clock, and no receiver reading only its
own lines can tell a uniformly heavier constitution from its own clock (§2). What survives the clock
is the shape: the dimensionless numbers, the line ratios and loss angles. Mass in the absolute sense
is therefore a ratio of two receivers' clocks. In the multiplier disk a basin (a pole) is a point
of the hyperbolic plane; the receiver's clock is a boost of that disk; the basin's residence time
over the receiver's frequencies is exactly the Doppler factor of a boost, peak `k`, trough `1/k`,
total one tick per basin (§3). The count of basins is the rest mass: no motion changes it, and it is
read as a winding. The configuration of basins modulo motion is the shape (§4). A receiver that
reads only magnitude (bits) is blind to the basins hidden in the phase: they are an all-pass factor,
and in the stored series they are the coefficient of `log z` and a two-sided tail (§5). The receiver
itself has a mass along each reading, the inverse of its leverage, and one reading adds one unit
(§6).

## 1. One line, two numbers

`[proved-standard]` For the quadratic pencil `P(s) = s²C + sD + K` (symmetric `C ≻ 0`, `D ⪰ 0`,
`K ⪰ 0`) with a simple line `s` and mode `v` (`P(s)v = 0`; the left vector is `vᵀ` because `P` is
symmetric), a load `(ΔC, ΔD, ΔK)` moves the line at first order by

```text
δs = − vᵀ(s² ΔC + s ΔD + ΔK)v / vᵀ(2sC + D)v .
```

On a lossless line (`D = 0`, `s = iω`) the three loads separate exactly:

```text
mass        δs = −i ω ΔC_v / (2 C_v)     the turn slows, the boost is untouched
stiffness   δs = +i ΔK_v / (2 ω C_v)     the turn quickens, the boost is untouched
viscosity   δs = − ΔD_v / (2 C_v)        the decay grows, the turn is untouched
```

with `X_v = vᵀXv`. So `δω/ω = ½(ΔK_v/K_v − ΔC_v/C_v)` weighs mass against stiffness and
`δγ = ΔD_v/(2C_v)` weighs viscosity. On a lossy line the loads mix: a mass load also lowers the decay
rate, the same drag spread over more inertia.

Exact witness (receipts, A): `C = I`, modes `(3,4)/5` and `(−4,3)/5`, `K` with `ω² = 25, 169`,
Rayleigh damping `D = (191/36)C + (1/36)K`; the lines are `−3 ± 4i` and `−5 ± 12i`. For a mass
at site 0, a viscosity at site 1, a stiffness coupling and all three together, `det P_ε(s + εδs)`
has no `ε⁰` and no `ε¹` term, and the shifts add. On the lossless lines `±5i`, `±13i` the mass at
site 0 moves them by `−9i/10` and `−104i/25`, the viscosity by `−4/25` and `−9/100`, the coupling
by `+12i/125` and `−12i/325`.

`[proved-standard]` The quartz-crystal microbalance is this law as an instrument
(Sauerbrey 1959; Kanazawa and Gordon 1985; Johannsmann 2015). In the small-load approximation the
complex shift is `Δf* = Δf + iΔΓ = (i f₀/(π Z_q)) Z_L`, with `Z_L` the load's acoustic impedance:
a rigid film (`Z_L = iωm`) drops the frequency and leaves the bandwidth; a Newtonian liquid
(`Z_L = √(iωρη)`) gives `ΔΓ = −Δf`, the shift at 45°; a pure dashpot only broadens. The overtones
read the shape: for a rigid film `Δf_n/f_n` is the same on every overtone `n`, for a Newtonian
liquid it falls as `n^(−1/2)`, and a viscoelastic film lies between.

## 2. The clock hides a uniform mass

`[proved-derived]` Read on a clock `τ` with `t = λτ` (`λ > 0`), the same constitution is
`(C, λD, λ²K)`, because

```text
det(s²C + sλD + λ²K) = λ^(2n) det((s/λ)²C + (s/λ)D + K),
```

so every line moves to `λs`. This is the Doppler factor, the gravitational redshift by a lapse, and
any change of the receiver's tick: they are one operation on the lines. Its invariants are the line
ratios `s_i/s_j` and the loss angles of each line (the projective class of `s` under positive
scaling; `γ²/|s|²` is a rational witness, and `Q = ω/2γ` its classical form). These are exactly the
dimensionless numbers of the constitution: `Q`, frequency ratios, and for a fluid mode `ω/νk²`, its
Reynolds number.

Consequences, each checked exactly (receipts, B):
- **Equivalence.** A lossless proportional mass load `C ↦ μC` is the clock `λ = μ^(−1/2)`
  exactly: with `μ = 4/9` the characteristic polynomial is `μ²` times that of the clock `3/2`.
  Heavier is redder: no receiver that reads only these lines can separate a uniformly heavier
  constitution from a redshift, a slower clock or a receding source.
- **Viscosity breaks it.** With the viscosity held, the same load multiplies every loss invariant
  by `1/μ` (with `μ = 4/9`, `9/25 ↦ 81/100` and `25/169 ↦ 225/676`): the same drag over another
  inertia changes how many turns each ring lasts. The clock leaves them unchanged.
- **Shape is the differential part.** At first order a lossless mass load moves the ratio of two
  lines by the difference of its modal Rayleigh quotients:
  `δ log(s₁/s₂) = −½(ΔC_(v₁)/C_(v₁) − ΔC_(v₂)/C_(v₂))`. Mass at site 0 has quotients `9/25`,
  `16/25` and moves the ratio by `7/50`; a uniform load moves it by `0`; and so does the
  non-proportional load `I + v₁v₂ᵀ + v₂v₁ᵀ`, whose quotients agree. The ratios are blind at first
  order exactly to loads that weigh every mode alike.

`[interpretation]` So a single receiver reads a load in three parts. The part common to all its
lines is a clock: motion, redshift and uniform mass are one reading, and only a comparison with a
receiver whose clock the load does not touch separates them. That comparison is the undivided rate
of two clocks that [`clock.redshift-production`](../../docs/atlas/physics.tsv) already owns, and
around a loop spanning both it is the carry of `gr.redshift-loop`. The part that differs between
lines is the load's shape. The rotation of each line off its axis is its viscosity. Mass in the
absolute sense is never a property read in one frame; it is a ratio of clocks, one per two.

`[proved-standard]` Three instruments confirm the split:
- **The microbalance.** A rigid film shifts every overtone by the same fraction (above), which is
  why it is weighed against a reference crystal's clock.
- **Black-hole ringdown.** At fixed spin every quasinormal frequency scales as `1/M`, and a source at
  redshift `z` is read with the detector-frame mass `(1 + z)M`: mass and redshift are one clock, the
  spin is read from the ratios and quality factors (gravitational-wave spectroscopy; Berti, Cardoso
  and Will 2006; Berti, Cardoso and Starinets 2009). The distance from the amplitude, a second
  receiver, breaks the degeneracy.
- **The radial-velocity method.** A star's lines shift periodically by its wobble; the unseen
  companion is weighed through the mass function `f = P K³/(2πG) = (m sin i)³/(M + m)²`. It needs
  the orbital period, a second clock, and it leaves the inclination open: the wobble sees only the
  line-of-sight part.

## 3. A basin is a boost seen from inside

The receiver's lines are poles of its response. In discrete time they are multipliers per tick, and
a stable one lies in the unit disk.

`[proved-derived]` **The Cayley chart.** `z = (1 + s)/(1 − s)` takes the left half plane onto the
unit disk and conjugates the clock `s ↦ ks` to the disk boost

```text
φ_a(z) = (z − a)/(1 − az),   a = (k − 1)/(k + 1),   (1 + a)/(1 − a) = k,   2a/(1 + a²) = (k² − 1)/(k² + 1).
```

`a` is the half-rapidity velocity of the boost, and `2a/(1 + a²)` is the velocity
`β(k) = (k² − 1)/(k² + 1)` of `lorentz.doppler-ratio-chart`. In this chart, the rational chart of
the multipliers that `parametron.floquet-placement` uses, the receiver's clock is a hyperbolic
motion of the multiplier disk. In the exponential chart `λ = e^s` the same clock is `λ ↦ λ^k`,
exact for an integer `k` (reading every `k`-th tick).

`[proved-derived]` **The basin's residence is a Doppler factor.** For a basin at `a` (`|a| < 1`),
the lossless response `H_a(z) = (1 − āz)/(z − a)` is, for real `a`, exactly `1/φ_a`: the basin's
response is the boost read as one tick. Replacing every tick of a receiver by `H_a` is the classical
frequency warping (Oppenheim and Johnson 1972), and the warped receiver ticks at the Doppler factor.
On the circle `H_a` has the group delay

```text
τ(z) = −Re(z H_a'/H_a) = (1 − |a|²)/|z − a|²,
```

the Poisson kernel. For real `a`, with `β = 2a/(1 + a²)`,

```text
τ(ω) = √(1 − β²)/(1 − β cos ω),     τ(0) = k,     τ(π) = 1/k,     (k + 1/k)/2 = 1/√(1 − β²),
```

which is the Doppler factor of the boost `β` seen at angle `ω`: the basin delays the receiver most
at its own line (peak `k`) and least opposite it (trough `1/k`), and the mean of peak and trough is
the Lorentz factor. Exact witnesses (receipts, D): `a = 1/2` gives `k = 3`, `β = 4/5` and the Lorentz factor `5/3`;
`a = 7/9` gives `k = 8`, `β = 63/65`; a complex basin `a = (3 + 4i)/10` of modulus `1/2` delays by
exactly `3` at its line `(3 + 4i)/5` and `1/3` opposite.

`[proved-derived]` **A ring of N channels.** On the `N`-th roots of unity,

```text
Σ_(ζ^N = 1) (1 − |a|²)/|ζ − a|² = N · Re((1 + a^N)/(1 − a^N)),
```

from the logarithmic derivative of `∏(z − ζ) = z^N − 1`. A ring of `N` channels reads the basin
through `a^N`, the basin's multiplier over one lap: for real `a > 0` the total is `N` times the peak
residence of the lap. As `N` grows the total tends to `N`, one tick per channel; the excess
`N(Re((1 + a^N)/(1 − a^N)) − 1)` is the basin's echo returning once per lap. Checked in
`Q(ζ_M)`, `M = lcm(N, 4)`, for `N = 1, …, 12` and four basins (receipts, E).

`[proved-standard]` **The horizon.** As `|a| → 1` the peak residence `(1 + |a|)/(1 − |a|)` and the
boost velocity `2|a|/(1 + |a|²) → 1` diverge together: a basin with no viscosity holds forever and
moves at the speed of light relative to the receiver. The disk with the metric
`2|dz|/(1 − |z|²)` is relativistic velocity space, whose composition is the Möbius addition of
`landmark.c-velocity-addition`; a basin's distance from the receiver's centre is the rapidity
`log k`, and the circle is the horizon at infinite rapidity. This is the arrival of
`fluid.singularity-arrival-singular-aeon` (finite physical time, unbounded navigator clock) and the
lapse `N → 0` of a static horizon.

`[proved-standard]` **Wave and particle.** The basin is a point (a particle); its Poisson kernel on
the circle is its wave, and the wave determines the point (the peak sits at `a/|a|` with value
`k`). The powers `P_a^s` are the hyperbolic plane's eigenwaves (Helgason), unitary exactly on
`Re s = ½`.

## 4. The count is the rest mass, the configuration is the shape

`[proved-standard]` The number of basins inside the circle is the winding of the response's phase
around it (the argument principle; Levinson's theorem counts bound states by the scattering phase at
threshold, and Friedel's sum rule the displaced charge). Every motion of the disk keeps it:

```text
1 − |φ(a)|² = (1 − |a|²)(1 − |c|²)/|1 − c̄a|²,     φ(z) = u (z − c)/(1 − c̄z), |u| = 1,
```

so no basin crosses the horizon under any change of the receiver's clock or frame. The count is the
mass no motion changes, and each basin carries one tick of residence: the total delay of `n` basins
over the circle is `n` ticks.

`[proved-standard]` The configuration of basins modulo the motions is the shape. Its invariants are
the pseudo-hyperbolic distances

```text
δ(a, b)² = |a − b|²/|1 − āb|²,
```

and moving `a` to the centre puts `b` at distance `δ(a, b)`. One basin has no shape (a motion
centres it); `n ≥ 2` basins have `2n − 3` invariants. The relative Doppler factor between two
basins is `(1 + δ)/(1 − δ)`: `0` and `1/2` are at relative Doppler `3`. Checked for three motions
and five Gaussian-rational basins (receipts, F).

## 5. The basins the magnitude cannot see

`[proved-standard]` A causal stable response factors as `H = H_min · B` (inner–outer; Beurling):
`H_min` is minimum phase, determined by `|H|` on the circle, and `B` is an all-pass, a Blaschke
product of hidden basins, with `|B| = 1` on the circle. The magnitude face cannot see `B` at all. In
the stored series this is exact and needs no transform: for minimum phase `log H_min = c₀ + Σ_(k≥1)
c_k z^(−k)` is one-sided, so the log-magnitude `Σ c_k cos kω` and the phase `−Σ c_k sin kω` share one
term list (the discrete Kramers–Kronig and Bode relations, the causal complex cepstrum; Oppenheim
and Schafer). The hidden basins appear as what does not fit that list: an integer coefficient of
`log z`, which is their count, and a two-sided tail, which is their place.

Exact witness (receipts, G): `H = (z − 2)/(z − 1/3)`, `H_min = (2z − 1)/(z − 1/3)`,
`B = (z − 2)/(2z − 1)`.
- `|H| = |H_min|` everywhere on the circle, `H = H_min B`, `|B| = 1`.
- `z B'/B = −Σ_(k∈ℤ) 2^(−|k|) z^k`, minus the Poisson series at `1/2`: two-sided, constant term
  `−1`, the winding of one hidden basin.
- `z H_min'/H_min = Σ_(k≥1) (2^(−k) − 3^(−k)) z^(−k)` is one-sided, so
  `c_k = (3^(−k) − 2^(−k))/k` (`−1/6, −5/72, −19/648, …`).
- Both series are checked through the exact aliasing of their samples on the `N`-th roots of unity.
- On `N = 8` channels the delay totals are `335923/41820` for `H` and `−1261/41820` for `H_min`;
  their difference is `2056/255 = 8 · 257/255`, one tick per channel plus the echo.

`[interpretation]` Two receivers with identical magnitude, so identical bits, can differ by a whole
basin: here by one tick of residence in every channel. A cross-entropy, read at the receiver's face,
is the log-magnitude of the ratio; the hidden basins are its phase part, which the loss law already
names as what completes the comparison. Bits are blind to this mass. The August record's
Kramers–Kronig conjecture (§8 there) closes for rational receiving faces in the minimum-phase case:
there the absorption face determines the dispersion face term by term. Where the conjecture's
falsifier fails, it measures exactly the hidden all-pass factor, which is the informative return
that record anticipated. The boundary case of the inner factor, a singular inner function with no
zeros, is mass sitting on the horizon itself: residence with no count. It does not occur for
rational responses.

## 6. The receiver's own mass along a reading

`[proved-derived]` With the leverage `h = vᵀG⁻¹v` of a reading `v` against the receiver's Gram
`G` (effective-tension record §9), adding the reading gives `h' = h/(1 + h)`, so

```text
1/h' = 1/h + 1,     the prediction along v moves by  h/(1 + h) = m/(M + m)  of the residual,
```

with `m = 1` the reading's mass and `M = 1/h` the receiver's mass along `v`. This is the
barycentric share of a two-body wobble, and it is the Kalman gain. Every reading adds one unit of
mass in its direction. Off the range (`h` unbounded, the open part) the receiver has no mass there
and moves the whole way. Checked on a five-reading Gram (`h = 215/209`, `h' = 215/424`, share
`215/424`) and on a rank-two Gram with a reading along its kernel, where the share is `1`
(receipts, H).

`[interpretation]` The radial-velocity method read in the receiver's frame: the receiver's wobble
toward a new reading weighs the receiver against the reading, and only the supported part wobbles;
the open part is the inclination. The one tensor `G` reads as stiffness under a one-shot update (the
curvature of the bowl), as drag under gradient flow (velocity per force), and as mass under a
momentum learner; the loss angle of the learner's own line separates the three.

## 7. Where the machine already carries it

`[interpretation; agent-inferred]` The moment tower ([`hnn::tower`](../../crates/holonics/src/hnn/tower.rs))
is a field of basins. Each mode `λ` is a pole of its level's response, one tick per byte; its
passivity bound `|h| ≤ √((1 + |λ|)/(1 − |λ|)) max|Bx|` is the square root of the basin's peak
residence; its deposit moves in the chart `(ln(1 − |λ|), arg λ)`, which is viscosity and turn; and
its gated mode's closed gate sends `|λ_t| → 1`, the horizon, where the push is not admitted and the
mode is dormant. The spectroscopic reading of a deposit is, per mode, the ratio `λ'_i/λ_i` (boost
part `|λ'_i/λ_i|`, turn part its argument). A deposit that is a pure clock maps every `λ_i` to
`λ_i^k`; what is not a clock is shape; and the hidden basins of a receiving face are the winding of
its phase beyond what its log-magnitude series determines. No construction is scheduled by this
record.

## 8. Breadth: one reading across the domains

`[interpretation]` Each row reads the same line in another medium. Grades of the physical facts are
those of §1 to §6 and their citations.

| Medium | The line | Mass reads as | Viscosity reads as | Shape reads as | Basin and horizon |
|---|---|---|---|---|---|
| Microbalance | crystal overtones | frequency drop, `Δf_n/f_n` flat for a rigid film | bandwidth `ΔΓ` | overtone dependence | the film's acoustic load |
| Star and planet | the star's spectral lines | the wobble's amplitude over the orbital clock | — | eccentricity, `sin i` open | the barycentre |
| Black hole | quasinormal modes | the common scale `1/M`, one with redshift | the damping of each mode | spin, from ratios | the horizon; its membrane has `η/s = 1/4π` (Kovtun, Son and Starinets 2005) |
| Scattering | phase shift | bound states counted by the phase (Levinson, Friedel) | resonance width | relative positions of poles | Wigner delay at a resonance |
| Fluid singularity pair | `c = m + iΓ` | circulation `Γ`, the turn | flux `m`, the drain | the site kind: boost, rotation, spiral | finite-time arrival, singular aeon |
| Parametron | Floquet multipliers | the turn per period | the modulus | multipliers' ratios | the bifurcation circle |
| HNN tower | modes `λ` | `arg λ` | `1 − \|λ\|` | ratios across modes | `\|λ\| → 1`, dormancy |
| Code-length field | octave density | the uniform part is a lapse, `1 + z = 2^(−(1+w))` | the learning part | per-region `w` | the floor `w = −1` |
| Receiver of readings | leverage | `1/h`, plus one per reading | drag under gradient flow | supported against open part | the open part, no mass |

Two joins follow. Kelvin's circulation is conserved on material cycles without viscosity
(`fluid.kelvin-holonomy`): the turn, the mass, is conserved, and viscosity produces entropy. And
viscosity keeps only the harmonic part (faces read on cycles): the basins viscosity cannot drain are
the dormant ones at the horizon, the harmonic classes. The space-time fabric of the lens is the
multiplier disk itself: basins are its points, rapidity is its distance, the receiver's clock is a
motion of the whole fabric, and a uniform load is a lapse, read only across a loop that spans a
lapse difference.

## 9. Owed Lean

One box in #410:
- the clock gauge of the pencil, `det(s²C + sλD + λ²K) = λ^(2n) det((s/λ)²C + (s/λ)D + K)`, and the
  equivalence of a lossless proportional mass load `μC` with the clock `μ^(−1/2)`;
- the first-order line shift `δs = −vᵀ(s²ΔC + sΔD + ΔK)v / vᵀ(2sC + D)v` at a simple line;
- the Cayley conjugation of `s ↦ ks` to `φ_a`, `a = (k − 1)/(k + 1)`;
- the basin's group delay `−Re(zH_a'/H_a) = (1 − |a|²)/|z − a|²` on the circle, and for real `a`
  its Doppler form `√(1 − β²)/(1 − β cos ω)`, `β = 2a/(1 + a²)`;
- the ring sum `Σ_(ζ^N=1) (1 − |a|²)/|ζ − a|² = N Re((1 + a^N)/(1 − a^N))`;
- `1 − |φ(a)|² = (1 − |a|²)(1 − |c|²)/|1 − c̄a|²` and the invariance of `δ(a, b)` under disk
  motions;
- for rational causal stable `H`, `|H| = |H_min|` on the circle with `H = H_min B`, `B` a finite
  Blaschke product whose degree is the winding deficit.

## Sources

Sauerbrey (1959), *Z. Physik* 155; Kanazawa and Gordon (1985), *Anal. Chim. Acta* 175; Johannsmann
(2015), *The Quartz Crystal Microbalance in Soft Matter Research*; Berti, Cardoso and Will (2006),
*Phys. Rev. D* 73; Berti, Cardoso and Starinets (2009), *Class. Quantum Grav.* 26; Levinson (1949);
Friedel (1952); Wigner (1955); Kovtun, Son and Starinets (2005), *Phys. Rev. Lett.* 94; Bode (1945);
Oppenheim and Schafer, *Discrete-Time Signal Processing* (the complex cepstrum); Oppenheim and
Johnson (1972), *Proc. IEEE* 60 (frequency warping); Helgason,
*Groups and Geometric Analysis* (the Poisson transform). External sources establish only their
declared results.

## Receipts

[`2026-10-24_INFORMATION_SPECTROSCOPY_receipts/`](2026-10-24_INFORMATION_SPECTROSCOPY_receipts/):
`spectroscopy.py` (checks A to H) and its output `spectroscopy.json`; `RUN.md`. Exact rationals,
Gaussian rationals and cyclotomic fields throughout.
