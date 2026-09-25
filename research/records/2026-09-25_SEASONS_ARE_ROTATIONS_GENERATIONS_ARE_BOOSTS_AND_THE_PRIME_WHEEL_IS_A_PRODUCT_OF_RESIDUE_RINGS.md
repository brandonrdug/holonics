# Seasons are rotations, generations are boosts, and the prime wheel is a product of residue rings

**Date:** 2026-09-25. **Occasion:** Brandon asked the following, with two figures of egg
constructions: Hügelschäffer's rays, and circle chains inside eggs shrinking by `0.618`, `0.382` and
`0.236` around a pentagon:
- how the frequencies of primes and of zeta zeros vary over partitions;
- for "geometrically addressed partitions", a "binary combinatorial thing" in the spirit of prime
  wheels;
- for natural algebraic cycles like *seasons* and *generations*, covering orbits, as cycles in
  entropic modes: sleep, winter, spring, wakefulness, and twin primes as generations;
- where the universe's 13.8 billion years come from, and how that bears on the cosmological
  constant.

It builds on:
- the ratified [wheel record](2026-07-17_THE_WHEEL_RECURS_THE_ZERO_WAVE_CARRIES_THE_PRIME_CURRENT.md):
  gap words, `COPY → CUT → JOIN`, Ramanujan sums, the explicit formula in `u = log x`;
- the [cosmological-constant record](2026-08-25_THE_COSMOLOGICAL_CONSTANT_IS_INFERRED_THROUGH_PLURAL_RECEIVER_FIBRES_AND_A_PRINTED_DECIMAL_IS_NOT_THE_MEASUREMENT.md),
  with Lean `Physics/HolonicCosmologicalInference`;
- the aeon, null-cone and egg records.

**Truth discipline:** `[proved-standard]` classical; `[proved-derived]` checked here;
`[conjecture]`; `[interpretation]` for correspondences; `[established-bounded; measured]` for
observations.

Audited by Sol (GPT-6) the same day; the corrections are folded in below and listed at the end.

## 1. The geometric address: the wheel is a product of prime residue rings

`[proved-standard]`; `[proved-derived]` in `HolonicsResearch/Mathematics/TwinWheel`.
- **The address.** For a squarefree primorial `W = ∏_(p∈S) p`, the Chinese remainder map is the ring
  isomorphism `ℤ/W ≅ ∏_(p∈S) ℤ/p`. An integer's address is `(n mod p)_(p∈S)`.
- **Not a torus.** This is a product of finite residue rings, not a topological torus. Calling its
  cyclic coordinates "prime circles" keeps the address and supplies no continuous rotation
  `[interpretation]`.
- **The spokes and their binary faces.**
  - The candidate spokes are the units, `φ(W) = ∏(p − 1)` of them.
  - At each prime the divisibility bit `[p ∣ n]` is one binary face.
  - On an odd prime's units, the Legendre sign `(n/p) = ±1` is a second. At `p = 2` there is no
    quadratic sheet.
- **Two kinds of character.** The multiplicative characters of `(ℤ/W)^×` (Dirichlet's) differ from
  the additive Fourier characters of the whole ring (the wheel's Ramanujan sums).

`[proved-derived]` **Generations of the wheel** (wheel record §II; atlas `prime.wheel-copy-cut`,
`coupling.twin-wheel`).
- Admitting a new prime `q ∤ W` gives every old residue `q` lifts modulo `qW`, exactly one of which
  `q` divides.
- Copy the lifts, cut that one, and join its two neighbouring gaps. Each new gap is an ordered sum of
  consecutive old gaps.
- For the twin displacement `2`, the surviving slots multiply by `q − 2`:
  `twinSlots(qW) = (q − 2)·twinSlots(W)` (proved in `TwinWheel`).
- `[interpretation]` The HNN's carry chain of rings and a CRT address are one finite population only
  once a map commuting with their stepping laws is supplied.

## 2. How the frequencies of primes vary over the wheel's partitions

- **Equidistribution** `[proved-standard]`.
  - Dirichlet (1837): each unit class `a mod W` contains infinitely many primes.
  - With the zero-free region of Hadamard and de la Vallée Poussin (1896),
    `π(x; W, a) ∼ Li(x)/φ(W)` for each fixed `W`.
  - This does not make each finite interval or spoke equal.
- **Seasons in logarithmic time** `[proved-standard]` for the explicit formula, `[interpretation]`
  for "seasons".
  - The deviation on a spoke expands over the multiplicative characters `χ mod W` through
    `−L′(s,χ)/L(s,χ)`. It brings in the zeros of the Dirichlet `L`-functions, not a partition of the
    Riemann zeta's zeros among spokes.
  - With `u = log x`, a zero `ρ = β + iγ` contributes a term proportional to `e^(βu) e^(iγu)/ρ`, with
    endpoint conventions, principal-character terms, conductors and a truncation remainder attached.
  - Under GRH for the declared modulus every such term has the envelope `e^(u/2)`.
  - One term has formal period `2π/|γ|` in `u`; the joint population need not close on one cycle.
  - The character-indexed progression receiver, with its complete remainder, is the missing term.
- **Chebyshev's bias** `[proved-standard]` for the mechanism, conditional for the density.
  - Modulo 4 there are two unit classes, 1 and 3; odd prime squares all lie in class 1. Removing
    prime powers from the weighted count gives a drift favouring class 3, and the `L`-zeros supply
    the oscillations that sometimes reverse the lead.
  - Assuming GRH and the linear independence of the zero ordinates, the logarithmic density of
    `{x : π(x;4,3) > π(x;4,1)}` is about `0.9959` (Rubinstein and Sarnak 1994). It is neither an
    unconditional value nor a natural density.
- **Twins** `[proved-derived]` for the local factors, `[conjecture]` for the asymptotic.
  - For `p > 2` the proportion of residues admitting both `n` and `n + 2` is `(p − 2)/p`.
  - Relative to two independent unit densities, its factor is `p(p−2)/(p−1)² = 1 − 1/(p−1)²`. At
    `p = 2` the factor is 2.
  - Hardy–Littlewood predict `π₂(x) ∼ 2C₂x/(log x)²` with `C₂ = ∏_(p>2) (1 − (p−1)⁻²)`.
  - Zhang (2013) first bounded infinitely recurring gaps; Maynard (2015) gave 600; Polymath8b (2014)
    gave 246. None proves infinitely many gaps of 2.
- **Smooth and rough generations** `[proved-standard]`.
  - Dickman's `ρ` (`ρ = 1` on `[0,1]`, `uρ′(u) = −ρ(u − 1)` beyond) counts the smooth integers
    `n ≤ x` whose largest prime factor is at most `x^(1/u)`: `Ψ(x, y) ∼ xρ(u)`.
  - Buchstab's `ω` (`ω = 1/u` on `[1,2]`, `(uω(u))′ = ω(u − 1)` beyond) governs the rough integers
    with no prime factor below `y`. It stays positive and tends to `e^(−γ)`; its deviation
    `ω(u) − e^(−γ)` oscillates.
  - Each is a delay equation in which one generation of scale (`u − 1 → u`) drives the next, with
    `u = log x/log y`.

## 3. How the zeta zeros vary over partitions

- **The count** `[proved-standard]` (Riemann–von Mangoldt, regardless of RH):
  `N(T) = (T/2π) log(T/2π) − T/2π + O(log T)`. The mean density is `log(T/2π)/2π`, the mean spacing
  `2π/log(T/2π)`. This partitions height, not wheel spokes.
- **Pair correlation.** Montgomery (1973), assuming RH, proved the pair-correlation transform on
  `|α| < 1`, matching the GUE two-point expression for test functions of that restricted support.
  This is `[proved-standard]` within that support. Odlyzko's comparisons at large heights are
  `[established-bounded; measured]`. The full GUE spacing law, "the zeros repel", is `[conjecture]`.
- **Families** `[proved-standard]` for restricted support, `[conjecture]` in general.
  - Katz and Sarnak's family statistics concern low-lying zeros near the central point as the
    conductor grows, not the high zeros of one function.
  - The primitive quadratic Dirichlet family is predicted symplectic, with restricted-support
    agreements proved.
  - A quadratic character `χ_d` is indexed by a fundamental discriminant; it is not one Legendre bit at
    a fixed wheel prime.

## 4. Seasons, generations and the lock

`[proved-derived]`; `[interpretation]` for the names.
- For `M ∈ SL₂(ℝ)`, `|tr M| < 2` is elliptic (a rotation: a season), and `|tr M| > 2` is hyperbolic
  (a boost: a generation). `|tr M| = 2` covers a parabolic shear and the scalars `±I`: the lock, and
  site kind alone certifies no action (`Compression/Landmark/SiteKind`).
- The Fibonacci step `[[1,1],[1,0]]` has determinant `−1` and eigenvalues `φ` and `−φ⁻¹`: it is the
  orientation-reversing reflection kind, although one magnitude grows.
- Its square, the cat map `[[2,1],[1,1]]`, is the determinant-one boost with eigenvalues `φ^(±2)` and
  entropy `log φ²`.
- The egg figures' shrinking factors need a constructed scale map before they prove a boost. The
  pentagon and the icosahedron share `φ`, but a shared number is not yet a transport between them.

`[proved-standard]` **Complex dimensions and RH**, with hypotheses.
- A self-similar string's geometric zeta has denominator `1 − Σ_j r_j^s`.
- For `m` equal contractions `r`, its uncancelled poles include `D + 2πin/log(1/r)` with
  `D = log m/log(1/r)`: log-periodic seasons in scale.
- General lattice strings can have several vertical progressions, and nonlattice strings do not have
  one period.
- Lapidus and Maier (1995): for each fixed `D ∈ (0,1)`, their inverse spectral problem `ISP_D` holds
  exactly when `ζ` has no zero on `Re s = D`. It fails at `D = ½`, where zeros are known, and RH is
  equivalent to `ISP_D` for every `D ∈ (0,1) ∖ {½}`.
- It does not say that hearing an arbitrary fractal packing is equivalent to RH.
- Joining it to `Foundation/FractalPacking` needs a length-string construction, a spectral boundary
  problem and the factorization `ζ_spectral = ζ·ζ_geometric`, none of which the reflected integral
  supplies yet.

## 5. Cycles in entropic modes

- **Entrainment** `[proved-standard]` for a declared forced circle-map family; `[interpretation]` for
  organisms.
  - Rational rotation-number plateaus occur inside Arnold tongues. The devil's staircase belongs to a
    specified family and coupling regime (the critical sine circle map), not to every pair of clocks.
  - At zero coupling the rigid rotation has no locking (atlas `lock.rigid-rotation-no-staircase`).
  - `aeon::lock::TwoClocks` proves rational Farey locks and near returns, not tongues.
- **Cycle entropy** `[proved-standard]` for a genuinely cyclic state.
  - With heat into the system at boundary temperature `T_b` and `dS = δQ/T_b + σ dt`, `σ ≥ 0`, one
    exact return gives `∮δQ/T_b = −∮σ dt ≤ 0`.
  - A calendar day alone does not guarantee a return. A periodic production rate needs a periodically
    driven steady state, whose maxima and inflections the constitutive solution sets.
  - On a one-dimensional circle a nonzero cycle integral is harmonic, and there is no coexact 1-form.
    A coexact production reading needs a higher-dimensional complex (`Aeon/Production/HodgeTime`).
    `Physics/Thermal/ChainAxes` already carries a periodic entropy affinity on a ring.
- **Spring** `[interpretation]`. Ideal day length at latitude `ϕ` and declination `δ` is proportional
  to `arccos(−tan ϕ tan δ)`, and the solstices are the declination extrema. "Fastest change at the
  equinox" holds at midlatitudes on a near-sinusoidal model, not in general: at the equator day length
  is constant, and polar day and night change the derivative.
- **Cold** `[proved-standard]` for activated channels only. Arrhenius `k = A(T)e^(−E_a/(k_BT))`
  governs activated transitions, and other channels (quantum ones among them) remain. The third law
  concerns the equilibrium `T → 0` limit, and degeneracy can leave residual entropy. "Causality
  dwindles in the cold" is `[interpretation]`.
- **The Earth's gradient.** Lineweaver and Egan (2008) balance one absorbed solar photon against
  roughly twenty lower-energy infrared photons in an order-of-magnitude energy comparison. It is not
  an exact photon census. `[interpretation]` grounded in that estimate.
- **Sleep** `[established-bounded]` for the observations, a hypothesis for the mechanism,
  `[interpretation]` for the HNN.
  - Tononi and Cirelli's synaptic homeostasis hypothesis proposes net waking potentiation and
    sleep-associated down-selection. Supporting ultrastructure exists, and its relation to replay
    consolidation is debated.
  - Sleep certifies an aeon boundary only once a receiver family and a future-sufficient quotient are
    shown.
- **Winter and spring** `[interpretation]`. Dormant modes and fitting antecedents: germination
  resonates an existing mode, and founding is spring's diversification.

## 6. The age of the universe

- **The definition** `[proved-standard]` within flat FLRW ΛCDM.
  - Cosmic age is proper time along the comoving family from the model's `a = 0` boundary to `a = 1`:
    `t₀ = ∫₀^∞ dz / ((1+z)H(z))`, with
    `H(z) = H₀√(Ω_r(1+z)⁴ + Ω_m(1+z)³ + Ω_Λ)` and `Ω_r + Ω_m + Ω_Λ = 1`.
  - `dt` is an exact cosmic-time form in that chart. Other paths and clocks read differently.
  - Conformal time `∫dt/a` and the e-folds `log a` are different typed readings, not alternative
    ages. The integral derives the age from the expansion history; `Λ` alone does not fix it.
- **The measurement** `[established-bounded; measured]`.
  - Planck (2018) samples `(ω_b, ω_c, θ_MC, τ, ln(10¹⁰A_s), n_s)` and derives the age:
    `13.797 ± 0.023` Gyr for TT,TE,EE+lowE+lensing, and `13.787 ± 0.020` Gyr with BAO added.
  - `θ*` is fixed to about 0.03%, and the `Ω_m–H₀` correlation is approximately a constraint on
    `Ω_m h³`. That the age stays nearly constant along it is an inference from the posterior, not a
    theorem of Knox and Millea.
- **The tension** `[established-bounded; measured]`.
  - Planck's `H₀ = 67.36 ± 0.54` against SH0ES's `73.04 ± 1.04` km/s/Mpc: about 4.85σ for that
    comparison, treating the uncertainties as independent Gaussians.
  - DESI DR2: BAO alone prefers `w₀w_a` over ΛCDM at 1.7σ, BAO with CMB at 3.1σ, and with Pantheon+,
    Union3 or DESY5 supernovae at 2.8σ, 3.8σ or 4.2σ.
  - Its fitted `w₀w_a` combinations recover an `H₀` lower than Planck's ΛCDM value, so this extension
    does not resolve the ladder discrepancy.
- **In the objects** `[proved-derived; formal-checked]` for the algebra, `[interpretation]` for the
  disagreement.
  - `HolonicCosmologicalInference` proves `Λ = 3Ω_Λ H₀²/c²` in a constant-`Λ` chart, its non-injective
    fibre, a finite weighted pushforward, the difference identity and the constant-gluing test.
  - It does not ingest the Planck or DESI likelihoods, nor establish that the two posteriors are
    readings of one scalar section with a physical gluing defect.
  - That needs model, calibration, covariance, prior and shared data transported into a common chart
    (cosmological-constant record). A cross-entropy face follows only once the actual likelihood and
    prior are named.

## Corrections made in audit

- The wheel is a product of finite residue rings, not a torus, and modulo 4 has two unit classes, not
  four spokes.
- Dickman counts smooth integers, Buchstab rough ones, and it is `ω − e^(−γ)`, not `ω`, that
  oscillates.
- The Fibonacci step is the reflection kind; its square is the boost.
- The complex-dimension progression needs equal contractions (lattice strings), and Lapidus–Maier's
  statement is pointwise in `D`.
- Planck's `13.787` Gyr includes BAO; the degeneracy claim is not Knox and Millea's.
- DESI's significances depend on the dataset.
- The equinox, Arrhenius and circle-map claims are scoped.

## Obligations

- **Rust and Lean (#145):**
  - the wheel as a product of residue rings with its divisibility and Legendre sheets, keeping the
    additive (Ramanujan) and multiplicative (Dirichlet) characters apart;
  - the Ramanujan-sum Fourier faces (wheel record);
  - the twin singular series as a product of local wheel densities.
- **The zeta target line:**
  - the explicit-formula seasons in `u = log x` as a receiver;
  - the Lapidus–Maier bridge between fractal strings and RH, joined to `Foundation/FractalPacking`
    and the natural-grain record's reflected integration.
- **K1 (#72) follow-up:** entrainment as `aeon::lock` with the devil's staircase; the daily
  production as a Hodge-split clock.
- **The cosmology line:** the tension as a gluing defect between receiver families, over
  `HolonicCosmologicalInference`.

Sources:
- [Scientific American, the Hubble tension](https://www.scientificamerican.com/article/the-hubble-tension-is-becoming-a-hubble-crisis/)
- [phys.org, evolving dark energy and the tension (March 2026)](https://phys.org/news/2026-03-framework-dark-energy-evolving-linked.html)
- [What current data can say about evolving dark energy](https://arxiv.org/pdf/2502.10264)
- [Planck 2018 results VI, Table 2](https://arxiv.org/abs/1807.06209)
- [DESI DR2 results II](https://arxiv.org/abs/2503.14738)
- [Lapidus and Maier (1995)](https://doi.org/10.1112/jlms/52.1.15)
