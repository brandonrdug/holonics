# The natural grain is the future quotient, and reflection integrates a fractal packing

**Date:** 2026-09-25. **Occasion:** Brandon's message on the HNN deposition question. He wrote that
bits per tick is "not a learning law, it's a statement about differences relative to each other,
appealing to coarse graining", and that `c` is "more like a translation barrier between grains of
space and time". He also asked:
- when one thing becomes two, and when we can hear the music;
- the locus as the location of a lineage of causality;
- probability clouds on hyperspheres and hyper-ellipses;
- knots, strings and dimension folding;
- sphere packing into fractal packing through integration by reflection;
- black holes;
- the zeta function's zeros and the Navier–Stokes singularities.

**Authors.** Claude derived this jointly with Sol (GPT-6, through Codex), Claude's read-only
derivation partner. Sol worked in three threads against the repository's records and owners, and
Claude checked and integrated the results. Sol's corrections to three earlier records are applied in
those records.

**Truth discipline:**
- Classical results are `[proved-standard]`.
- Arguments checked here are `[proved-derived]`.
- Correspondences are `[interpretation]`.
- Proposed statements are `[conjecture]`, and missing proofs are `[open]`.

## 1. When one thing is two: the natural grain

`[proved-derived]` **The exact answer is receiver-qualified.**
- Let navigators `T_w` act on `X`, and let admitted receivers `ρ` read faces. Write
  `F(x)(ρ, w) = ρ(T_w x)`.
- Two states are one to that family exactly when `F(x) = F(y)`.
- In the linear case the kernel is `⋂_(ρ,w) ker(ρ T_w)`, and `X/ker F` is the coarsest
  future-sufficient retention. Every navigator descends to it.
- This is `Compression/Core/FaceMap` (Lean) and `compression::face_map` (Rust). The music is what
  that quotient keeps.
- The quotient is natural because the admitted future fixes it. No tolerance is chosen.

Three further senses of "natural", each conditional:
- **Model versus noise** `[proved-standard]`. Kolmogorov's structure function
  `h_x(α) = min{log₂|S| : x ∈ S, K(S) ≤ α}`, and algorithmically sufficient models with
  `K(S) + log₂|S| = K(x) + O(1)` (Gács, Tromp and Vitányi 2001), separate regularity from residual.
  The separation is relative to a universal interpreter, it is uncomputable in general, and a bit
  that looks random can still decide a future lock. It joins retention only through a declared codec
  and a proof that every admitted face factors through the statistic.
- **Spectral separation** `[proved-derived]`. Under `e^(−tP)` with a gap `γ` between `a` and
  `a + γ`, the upper modes shrink by `e^(−(a+γ)t)`. This is a horizon-qualified grain. Finite decay
  does not put a mode in the exact relevance kernel. Renormalization's relevant and irrelevant
  directions are likewise relative to a fixed point, a scale map and an observable (Wilson and Kogut
  1974).
- **An event** `[proved-standard]`.
  - When a single neck reaches zero radius and separates, `H₀` goes from rank one to rank two.
  - Persistence is stable: diagrams move at most `η` in bottleneck distance when the filtering
    functions move by `η` (Cohen-Steiner, Edelsbrunner and Harer 2007).
  - Droplet pinch-off is a finite-time singularity with a local similarity profile (Eggers 1997).
    Day, Hinch and Lister (1998) found an inviscid capillary pinch whose lengths scale as
    `(t_* − t)^(2/3)`, with a limiting double cone independent of the initial shapes they tested,
    within those constitutive assumptions.
  - The egg's vanishing cycle is an `[interpretation]` of the shared topology. It is not a fluid
    solution.

**Bits per tick belongs here** `[proved-standard]`. Under an invariant measure, Kac gives a mean
return to a section `A` of `1/μ(A)` fine ticks, and Abramov gives induced entropy `h(T)/μ(A)` per
coarse tick. A rate needs that law, its section and its receiver. Stated so, it is the coarse-graining
law Brandon described, not a learning law.

## 2. `c` between partitions

- **Per medium** `[proved-standard]`.
  - In a homogeneous, isotropic, linear, nondispersive medium, the wavefront speed is `(εμ)^(−½)`.
  - A general local constitution gives a quartic Fresnel surface; one metric cone needs no
    birefringence (Hehl, Itin and Obukhov 2006). Each partition carries its own constitutive cone.
- **Across an interface** `[proved-standard]`.
  - A stationary planar interface conserves frequency `ω` and tangential covector `k_∥`: the shared
    face.
  - Each side's dispersion fixes the normal part. With `|k_i| = n_i ω/c`, this is Snell's law
    (`Transport/JunctionLaw.snell_squared`, partly formal). A moving interface need not conserve
    `ω`.
- **Across a gravitational field** `[proved-derived]`.
  - In a stationary region with Killing field `ξ`, the photon's `E_ξ = −p·ξ` is constant along its
    null geodesic.
  - Each static receiver reads `hν = E_ξ/N`, so `ν_rec/ν_em = N_em/N_rec`.
  - `Physics/Spacetime/NonClosedClock` proves the proper-time rate `N_em : N_rec`; the frequency rate
    is its inverse. The Killing-energy carrier joining the two readings is missing.
- **The chord** `[proved-derived]`.
  - A common shift `a` multiplies every line, `log ν_obs = log ν_rest + log a`. So frequency ratios,
    that is log-frequency intervals, are invariant: an emission spectrum is a chord under
    transposition.
  - One unidentified line carries no invariant. One securely identified line with a known rest
    frequency gives `a`. Several lines identify the source and test that the shift is common (NIST
    atomic line practice).
- **Grades.**
  - "Translation barrier between grains" is a sound `[interpretation]` of how a phase covector
    crosses between constitutions.
  - It does not repeal the local causal cone. No signal outruns its local null cone, which is the
    ordinary speed limit on massive motion.
  - Brandon's point that `c` does not limit how much causality occurs is right: a star's cascade of
    concurrent emissions is not throttled.
  - Developing the grain-translation reading beyond this is a `[conjecture]` that must reproduce null
    transport and the observed spectra.

## 3. The gap between two loci

- **The world function and focusing** `[proved-standard]`. In a convex normal neighbourhood,
  Synge's world function `σ(x, x′)` is half the signed squared geodesic interval, and the van
  Vleck–Morette determinant `Δ(x, x′)` reads the focusing of nearby geodesics. Past caustics the gap
  is multivalued. These are two-point faces of a metric constitution, not a free-standing
  higher-dimensional distance.
- **The heat kernel** `[proved-standard]`. Locally,
  `K(t; x, x′) ~ (4πt)^(−d/2) e^(−σ/2t) Δ^½ 𝒫 Σ a_j t^j`, where `𝒫` is the parallel transport
  (Hadamard, DeWitt). The spectral zeta `ζ_P(s) = Γ(s)⁻¹ ∫ t^(s−1)(Tr e^(−tP) − dim ker P) dt` needs
  the global trace. A two-locus gap alone determines no spectral zeta (Vassilevich 2003).
- **Selberg** `[proved-standard]`. On a compact hyperbolic surface, Selberg's trace formula pairs the
  Laplacian's eigenvalues `¼ + r_j²` with that surface's primitive closed geodesics, which play the
  primes.
  - Its zeros sit at `½ ± i r_j`.
  - The eigenvalues below `¼` give zeros off the line, including the constant mode.
  - `HolonicsResearch/Geometry/GraphTrace` already forbids promoting its finite Ihara witness to
    Selberg or RH.
- **Self-adjointness alone places nothing** `[proved-derived]`. On a circle of length `L` the
  Laplacian is positive and self-adjoint, yet `ζ_Δ(s) = 2(L/2π)^(2s) ζ(2s)`. A law "self-adjoint
  implies zeros on a line" would assume RH, rescaled.
- **"27 from 3 by a cube"** `[open]`. `3³ = 27` because the transport was given. For `ξ`, the
  derivation begins when an independently defined positive or self-adjoint carrier is built whose
  trace has the complete prime-power weights, the archimedean term and the multiplicities, and whose
  placement is proved without assuming RH. The support-aperture record (July 20) names that missing
  carrier.
- **De Bruijn–Newman** `[proved-standard]`. The zeros of `H_t` are all real exactly for
  `t ≥ Λ_DN`, and Rodgers and Tao proved `Λ_DN ≥ 0` (2020), so RH ⇔ `Λ_DN = 0`. The flow is backward
  heat in the zero variable, `∂_t H_t = −∂_z² H_t`. Calling it the overdamped end of an LC
  constitution is a resemblance until an operator intertwines the two.

## 4. Loci of causal lineage

`[proved-derived]` **A locus is the set of places where a transported source meets a receiver's
condition.** Write it `L(h, P) = {b : P_b(T_γ h)}`. It keeps the path, the connection and any
monodromy; when two paths transport differently, the locus carries that fibre. A Hodge locus, a zero
divisor, a fluid singular set and a horizon are four different receiver conditions. The shared word
supplies no map between their constitutions.

- **Hodge** `[proved-standard]`.
  - In a polarizable variation of Hodge structure, a class transported flatly by Gauss–Manin (its
    lineage) keeps type `(p,p)` on an algebraic locus (Cattani, Deligne and Kaplan 1995).
  - Flat transport keeps the class but not its type; the Hodge locus is where the type holds.
  - `[open]` The target asks more: an actual codimension-`p` cycle whose class is the transported
    class. CDK certifies the type locus, not a cycle source. That source is the missing term in
    `HolonicsResearch/Hodge/{HodgeConjecture, HodgeMonodromyPrimitivePropagation}`.
- **Zeta** `[proved-standard]`.
  - The zeros form a divisor. A contour closes around them: `(2πi)⁻¹ ∮ ξ′/ξ` counts them with order.
  - The functional equation pairs zeros into quartets, and the critical line is the fixed locus of
    `s ↦ 1 − s̄`. An invariant set need not consist of fixed points.
  - "The zeros are loci that close" means divisor landmarks around which the logarithmic-derivative
    receiver winds. It does not mean returning paths: that would need a dynamical system, an
    orbit-to-zero map and a trace identity.
- **Navier–Stokes** `[proved-standard]`.
  - Caffarelli, Kohn and Nirenberg (1982): the singular set of a suitable weak solution has zero
    one-dimensional parabolic Hausdorff measure.
  - Beale, Kato and Majda (1984) is an Euler continuation criterion; Escauriaza, Seregin and Šverák
    (2003) give the `L^∞_t L³_x` criterion for Navier–Stokes.
  - Sulem, Sulem and Frisch (1983) is a numerical diagnostic of the analyticity strip, not a theorem
    that real blow-up is a complex singularity reaching the reals. With merely `C^∞` forcing a
    solution need not continue holomorphically at all.
  - "Complex Navier–Stokes" names two operations: continuing the spatial variable of a real solution,
    and complex-valued velocities, which change the energy pairing (`HOLONIC_FLUID_CONSTRUCTION`,
    `U = a + ib`). Issue #32's source map is the missing equation between a neck chart and a PDE
    analyticity strip.

## 5. Brandon's Navier–Stokes prediction, with this month's evidence

`[proved-standard]` The official problem offers alternatives:
- (A, B): global smoothness with zero forcing, on `ℝ³` or the torus;
- (C, D): breakdown with a permitted smooth forcing.

`[open; claim under evaluation]` The September claim:
- On September 8, 2026, OpenAI announced an analytic proof with a Lean formalization. Its claim: for
  every viscosity, a fluid starting at rest under a `C^∞` compactly supported force develops a
  singularity at finite time with bounded energy. That is Clay's breakdown alternative.
- Buckmaster and Alpöge posted related blow-up results hours earlier.
- On September 11 the Clay Institute wrote that the problem "has apparently been settled" and began
  its unhurried evaluation.
- The unforced question (A, B) remains open.
- Constantin, Ignatova and Vicol (arXiv 2609.20803, September 17) prove that, under their Type II
  and axisymmetric-core hypotheses, a real-analytic forcing forces regularity at the candidate point.
  Constructions of that class need forcing that is non-analytic, or does not vanish, near the
  singularity.

So Brandon's prediction, that the problem as stated is false, is supported for the forced breakdown
alternative, pending verification. "Complexity necessary" has one rigorous reading here: the
mechanism needs structure (scale, orientation, pressure, non-analytic forcing) that coarser
receivers and analytic data cannot carry. No theorem says that real blow-up requires complex values.

Sources:
- [Clay announcement](https://www.claymath.org/news/navier-stokes-announcement/)
- [Quanta, September 8](https://www.quantamagazine.org/ai-has-solved-one-of-maths-1-million-millennium-prize-problems-20260908/)
- [OpenAI manuscript](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- [Constantin–Ignatova–Vicol](https://arxiv.org/abs/2609.20803)

## 6. Probability clouds, hyperspheres and hyper-ellipses

- **Fock** `[proved-standard]`. At fixed negative energy, stereographic projection of momentum space
  onto `S³` exposes the hydrogen atom's `SO(4)`. The `n²` degeneracy is the dimension of the harmonic
  polynomials of degree `n − 1` on `ℝ⁴`. The sphere carries momentum, not the position density
  (1935).
- **Kepler** `[proved-derived]`.
  - With `L = r × p` and the Runge–Lenz vector `A = p × L − mk r̂`, both are conserved.
  - Their brackets are `{L_i, L_j} = ε L`, `{L_i, A_j} = ε A` and `{A_i, A_j} = −2mH ε L`, so `L`
    and `A/√(−2mH)` close as `𝔰𝔬(4)` on a negative-energy shell.
  - The orbit is `r = (L²/mk)/(1 + e cos θ)`, and the velocity traces a circle, Hamilton's hodograph.
  - Moser (1970) regularizes the negative-energy Kepler flow as the geodesic flow of `S³`.
- **Hopf** `[proved-derived]`. On `S³ ⊂ ℂ²`, `h(z₁, z₂) = (2z₁z̄₂, |z₁|² − |z₂|²)` has fibres
  `(e^(it)z₁, e^(it)z₂)`. Fixing `|z₁|` gives the Clifford tori, on which each fibre is a `(1,1)`
  circle, and any two fibres link once: toroidal and helical geometry inside the hypersphere.
- **Radii** `[proved-standard]`.
  - `V_N(R) = π^(N/2) R^N / Γ(N/2 + 1)`, and the surface area is `dV_N/dR`. These are
    Gamma-constraint identities, with no float.
  - For a positive form `G`, `xᵀGx ≤ R²` has volume `V_N(R)/√det G`: a hyper-ellipse.
  - A Gaussian receiver law has ellipsoidal level sets `(x − μ)ᵀ Σ⁻¹ (x − μ) = c`. General hydrogen
    superpositions have nodes and need not.
- **Higher derivatives** `[proved-standard]`.
  - Jets keep velocity, acceleration and higher derivatives. The helix is the curve of constant
    Frenet curvature and torsion.
  - A nondegenerate higher-derivative Lagrangian has an Ostrogradsky Hamiltonian unbounded in its
    momenta. That is why physics avoids them, unless degeneracy or constraints intervene (Woodard
    2015).
- **The cloud** `[interpretation]`. A Holon's constituted motion supplies a clocked jet. Its receiver
  supplies a positive form and a probability reading, whose quadratic sections are ellipsoid faces,
  and a navigator transports them between frames. Fock, Moser and Hopf are exact instances of that
  map. None of them identifies a hydrogen cloud with a parametron or an egg.

## 7. Knots

- **Torus knots** `[proved-derived]`. `γ_(p,q)(t) = (a e^(ipt), b e^(iqt))` on a torus closes for
  integral `p, q`. It is one embedded circle exactly when `gcd(|p|, |q|) = 1`; otherwise it is a
  torus link. Its lift is `(p, q)`, and `p/q` is the pair's Farey lock address, which
  `Geometry/HolonicTorusKnots` already proves for coprime slopes.
- **Primes** `[proved-standard]`.
  - `T(p, q)` with coprime `|p|, |q| > 1` is a nontrivial prime knot, and `T(1, q)` is the unknot.
  - Two Hopf fibres form the Hopf link.
  - Every tame knot is a connected sum of prime knots, uniquely up to order, with the unknot as
    identity (Schubert 1949).
- **Knots and primes** `[interpretation]`. Mazur and Morishita compare primes with knots and
  Legendre symbols with mod-2 linking (Morishita 2012). This is a dictionary with precise
  cohomological analogues, not spatially linked primes. The prime-return record (July 23) already
  shows that knot monodromy need not sit on the RH seam.

## 8. Strings and folded dimensions

- **Kaluza–Klein** `[proved-standard; formal-checked]`. A circle of radius `R` gives modes `e^(iny/R)`,
  with momentum `n/R`. The Kaluza–Klein connection becomes a gauge coupling, and Routh reduction keeps
  the compact kinetic term (`Physics/CompactifiedModeTransport`).
- **T-duality** `[proved-standard; formal-checked]`. `(R, n, w) ↦ (α′/R, w, n)` exchanges momentum and
  winding, keeping `p_L` and reversing `p_R`. It is already owned (`quantum.t-duality`). Reading the
  pair as circle plus carry is an `[interpretation]`. Radius inversion is one duality, not the general
  ratio-inversion law.
- **Further theory** `[interpretation; theory-conditional]`.
  - M-theory's circle grows with the coupling, `R₁₁ = g_s ℓ_s` (Witten 1995).
  - Calabi–Yau Hodge numbers `h^(1,1)`, `h^(2,1)` count particular massless multiplets in a
    specified compactification, and mirror pairs exchange them.
  - Born–Infeld's `|E| < b` is the field domain of the purely electric branch. Calling it "a `c` for
    fields" is an interpretation, not a universal field limit.
  - None of this is empirical evidence of extra dimensions.

## 9. Integration by reflection, into a fractal packing

- **Lattices and quotients** `[proved-standard]`.
  - Poisson summation: `Σ_Λ f(λ) = covol(Λ)⁻¹ Σ_(Λ*) f̂(ξ)`. It gives the theta reflection
    `Θ(t) = t^(−N/2) Θ(1/t)`, and through Mellin, with the pole terms kept, the functional equation
    (`HolonicsResearch/Mathematics/ThetaReflection`).
  - On a quotient by a free, properly discontinuous group of isometries, the heat kernel is the image
    sum `Σ_γ K(t, x, γ y)`. Reflecting boundaries add signs.
  - A self-similar map that changes scale is not an isometric deck transformation, so its orbit sum
    is not automatically a heat kernel.
- **Sphere packing** `[proved-standard]`.
  - Descartes: `(Σb)² = 2Σb²`. Soddy–Gossett: `(Σ₅b)² = 3Σb²`.
  - Replacing one sphere reflects its bend, `b_i′ = Σ_(j≠i) b_j − b_i`.
    `HolonicsResearch/Geometry/SpherePacking` proves this replacement involutive, preserving the
    defect and non-commuting in order. It carries bends and lineage, not centres or an infinite
    packing.
  - Cohn and Elkies bound density by Fourier positivity. Viazovska (dimension 8) and Cohn et al.
    (dimension 24) supplied the optimal functions.
  - For a realized planar Apollonian packing, the inversions generate a Kleinian group whose limit
    set is the residual gasket. For geometrically finite actions, the Patterson–Sullivan exponent
    equals its Hausdorff dimension (Sullivan 1979), and Boyd (1973) showed the radius-summability
    exponent equals it too.
- **A first exact theorem: integration over a fractal packing by conjugate reflection**
  `[proved-derived]`.
  - Let `S₀(x) = x/3` and `S₁(x) = (x+2)/3`, with the reflection `J(x) = 1 − x`, so that
    `S₁ = J S₀ J`. Let `μ` be the equal-weight self-similar measure.
  - For bounded continuous `f`:

    ```text
    ∫ f dμ = ½∫ f∘S₀ dμ + ½∫ f∘S₁ dμ = 2^(−n) Σ_(|w|=n) ∫ f∘S_w dμ
    ```

  - For Lipschitz `f`, replacing each inner integral by `f(S_w x₀)` costs at most `Lip(f)·3^(−n)`,
    since each `S_w` contracts by `3^(−n)`.
  - `[formal-checked]` Proved the same day in `Foundation/FractalPacking`:
    - the maps: `cantorMap_right_eq_conj` (`S₁ = J S₀ J`), `reflect_reflect`, `wordMap_sub`
      (exact `3^(−n)` contraction), and `descend_root_eq_wordMap`, joining the maps to the
      existing cells;
    - the word averages: `abs_wordAverage_sub_le`, `wordAverage_succ_restrict`,
      `wordAverage_add_restrict`, `abs_wordAverage_sub_wordAverage_le` (`K·3^(−min(n,m))`),
      `tendsto_wordAverage`;
    - the integral: `reflectedIntegral` as the limit, `abs_wordAverage_sub_reflectedIntegral_le`
      (the grain's residual), `reflectedIntegral_self_similar`, `reflectedIntegral_eq_sum`;
    - integration by reflection: `reflect_wordMap_reflect`, `wordAverage_reflect`,
      `reflectedIntegral_reflect` (the integral of `f∘J` equals that of `f`);
    - the witness: `reflectedIntegral_id = ½`.

    The finite laws hold in any ordered field, so they are exact over `ℚ`; only the limit uses `ℝ`.
    The identification of `reflectedIntegral` with the self-similar measure's integral is `[open]`.
    It is a measure integral, not yet a heat equation.
- **The Apollonian extension** `[open]`.
  - It needs centres, disjointness, a coding of admissible reduced reflection words, conformal
    derivatives, and the weighted transfer operator `𝒫_δ f(x) = Σ_i |φ_i′(x)|^δ f(φ_i x)`.
  - Anomalous diffusion needs a Dirichlet form and its heat-kernel scaling. Barlow and Perkins' gasket
    diffusion is a different constitution.
- **Lightning** `[interpretation]`. Dielectric-breakdown growth gives branching fractal fronts
  (Niemeyer, Pietronero and Wiesmann 1984). A leader's channel carries the return stroke; heating
  launches the thunder's shock. The spheres (loci-centred collisions radiating radially) and the
  packing fractals join a derivation only through moving contact incidence, a material energy ledger
  (`em.streamer-drift`) and an electromagnetic and acoustic receiving boundary.

## 10. Black holes

- **What is standard** `[proved-standard]`.
  - Birkhoff: a spherical vacuum exterior is Schwarzschild. Stationary Einstein–Maxwell uniqueness
    characterizes the exterior by `(M, J, Q)` (Chruściel, Costa and Heusler 2012). Dynamic holes ring
    transiently, and other matter can carry hair.
  - `S = A/4` (Bekenstein 1973) and `T = κ/2π` (Hawking 1975). Wald's Noether charge generalizes the
    entropy to other gravitational constitutions.
  - Quasinormal ringdown is a chord for black-hole spectroscopy (Berti, Cardoso and Starinets 2009).
  - Jacobson (1995) derives Einstein's equation from `δQ = T dS` on all local Rindler horizons.
  - The Penrose process is a boundary balance of Killing energy.
- **The lapse** `[proved-derived]`. On Schwarzschild's static exterior,
  `N = √(1 − 2GM/(c²r))` and `ν_∞ = N ν_local`, so `N → 0` at the horizon: the extreme translation
  between static receivers. An infalling receiver crosses the horizon in finite proper time, so this
  is a statement about static clocks, not a failure of the local cone.
- **The globe** `[interpretation]`. No-hair makes the exterior a coarse receiver quotient that reads
  conserved charges, which makes a black hole a candidate globe. `Objects/RelativeCompleteness` also
  needs a membrane bounding the interior, actual coupling, and distinct interiors with persistent
  motion in one exterior fibre. No-hair does not supply the last two.

## 11. Compression is intelligence is navigation, in the objects

- **Compression** `[proved-derived]` is `X/ker F`: keep exactly what the admitted future face map
  reads (`Compression/Core/FaceMap`). Cost carries the decoder (`Core/Cost`), and
  `Core/Resonance` splits a drive into a constituted mode and its residual.
- **Navigation** `[proved-derived]` contains a genuine work-free sublaw.
  - For skew `J`, `Ḣ = ⟨∇H, J∇H⟩ = 0`, and the Cayley step of a frozen skew operator is an isometry
    (`Holon/{Dirac, Cayley}`).
  - The magnetic force curves without work: `v·(v × B) = 0`.
  - This is Brandon's "we cannot stop, but we can curve".
- **What is not a theorem** `[interpretation]`.
  - "Navigation = work-free curvature" names this steering part, not all of navigation. Ports
    exchange power, and dissipation, sources, pumps and deposition enter the ledger.
  - The missing theorem joins keys to reachable faces under a complete power ledger:
    `Compression/Core/Keys` proves loop-closure pruning, not steering.
  - "Intelligence" names the joint program. The step from compression to intelligence is where
    machine-independent optimality is known to fail (Leike and Hutter 2015; the August 14 record).

## 12. The neck is an exchange

Brandon: “It’s not that there’s literally nothing there, it’s an exchange/transport … a volumetric and surface area kind of exchange … volumes of entropy and energy flux converge into singularities, and they diverge again in-time.”

**[proved-standard; proved-derived in the finite owners] The governing ledger.** A neck is a constituted interface of a world tube. Its flow/effort ports pair to power. With signs oriented from ingress to egress, its complete balance is
```text
Ė_stored + P_out + D = P_in + P_active
```
The Dirac interconnection is power neutral; `D ≥ 0` requires the stated resistive law. The two sides’ interface powers cancel when they are joined. Over a spacetime control volume, Stokes includes initial and final storage sections, all side flux, and every source. Equal flux through two neck sections follows only when accumulation, side flux and sources vanish. Entropy uses a separate balance with production `Σ ≥ 0`; its flux is generally not conserved. Existing owners are `Holon/Element.PortHolon.power_balance`, `Transport/HolonicChain.port_power_balance`, `Holarchy/View.blockFlux_stokes`, `Physics/ObserverBoundaryCurrent.observerCurrentDivergence_eq`, and the thermal production owners.

**[proved-standard for this chart] Topology.** The index-one Morse function `f=x² + y² − z²` has a one-sheeted level for `f > 0`, a double cone for `f = 0`, and two sheets for `f < 0`. This is a local fission/fusion chart. Its use for a physical pinch is **[interpretation]** until a material evolution produces that chart. The Lorentz mass shell `|p|² − (E/c)² = −m²c²` has two timelike sheets for real `m > 0` and a null cone for `m = 0`; a one-sheeted spacelike level would require negative mass-squared. Neither quadric supplies an energy current by itself.

**[established-bounded; numerical] Capillary pinch.** Day, Hinch and Lister’s inviscid axisymmetric, surface-tension-driven similarity has local length scale `τ^(2/3)`, `τ = t_* − t`. Its characteristic velocity scale is `τ^(−1/3)`; hence `r²v` has characteristic scale `(γ/ρ)τ`, with its coefficient and even its value at the minimum section determined by the similarity profile and frame. This is **[proved-derived]** dimensional accounting from the stated scales, not a conserved nonzero throat flux. For a moving incompressible section, `∂_t A + ∂_z Q = 0`; its shrinking area and changing stored volume account for the difference between nearby fluxes. [Day, Hinch and Lister (1998)](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.80.704).

**[proved-standard, scoped] The optical chart.** A lossless paraxial ray map is symplectic in `(x,nθ)`; its one-transverse-dimensional ABCD determinant is one. In `(x,θ)` across a refractive interface the determinant is `n_in/n_out`. The associated finite ray bundle conserves canonical phase-space area, and in two transverse dimensions étendue has the `n²cos θ·dA·dΩ` measure. A point source has zero initial phase-space area; imaging it to zero transverse extent does not demonstrate positive étendue passing through zero area. A bundle with positive finite étendue cannot have zero spatial extent and bounded angular spread under an invertible ray map. This ray invariant is not, by itself, energy conservation. [Kogelnik and Li (1966)](https://dielslab.unm.edu/sites/default/files/Kogelnik66_2.pdf).

**[proved-standard for free paraxial propagation; proved-derived for the coordinate identity] The Gaussian waist.** A Gaussian beam with `w₀,z_R>0` has
```text
w(z)=w₀√(1 + (z/z_R)²).
```
Thus `z=z_Rsinh χ` gives `w=w₀cosh χ`, and
```text
ζ(z)=arctan(z/z_R)=arctan(sinh χ)=gd(χ).
```
The last equality follows from equal values at zero and derivative `sechχ`. This hyperbolic coordinate is **[interpretation]** as a physical boost. Across the full waist, `ζ` changes by `π`; the fundamental Gaussian’s Gouy-phase magnitude is `π/2` per transverse coordinate, with sign fixed by the complex-field convention. The waist remains positive within this Gaussian model.

**[proved-standard, scoped] Modes and caustics.** In homogeneous free paraxial propagation, a matched `HG_(mn)` carries Gouy order `m + n + 1`, and `LG_(pℓ)` carries `2p + |ℓ| + 1`. Each retains its mode *index* while its width, curvature and amplitude evolve; a general neck can mix modes. In semiclassical propagation a simple signed caustic crossing contributes a Maslov factor `e^(−iπμ/2)`, with integer crossing index `μ`; uniform wave analysis replaces the singular ray formula at the caustic. The claim that a constituted Holonic neck implements these optical maps remains **[open]** until its wave equation, boundary ports and modal transport are supplied. [Allen et al. (1992)](https://www.sciencedirect.com/science/article/pii/003040189290424P), [Horváthy (2007)](https://arxiv.org/abs/quant-ph/0702236).

**[proved-standard within named singularity classes] Singularities.** Arnold’s simple isolated critical-point germs have types `A_k, D_k, E₆, E₇, E₈`; this does not classify every neck or caustic. Complex du Val surface singularities are `ℂ²/Γ` for finite `Γ ⊂ SU(2)`; their minimal exceptional curves have ADE tree incidence, with branches in `D,E`. The binary tetrahedral, octahedral and icosahedral groups supply the three exceptional Platonic cases. The complex `A₁` ordinary double point `x² + y² + z² = 0` has a real-four-dimensional Milnor fibre homotopy equivalent to `S²`. It is related by complex coordinate change to the complexification of the Morse quadratic form, but is not the real hyperboloid neck. The Platonic reading of a physical exchange is **[interpretation]** until a source map preserves the incidence and material law. [Arnold (1972)](https://m.mathnet.ru/php/archive.phtml?jrnid=faa&option_lang=eng&paperid=2531&wshow=paper), [du Val (1934)](https://doi.org/10.1017/S030500410001269X), [Milnor (1968)](https://djvu.online/file/kCFrJq27uCPRi).

**[proved-standard, scoped; interpretation for this neck] Radiation and return.** An accelerated charge can radiate under Larmor’s electromagnetic assumptions; an arbitrary converging or diverging flow need not. A complete stationary lossless scattering map is unitary on its propagating power ports and can mix modes. Levinson’s relation counts bound states through a partial-wave phase-shift difference only for a specified suitable scattering operator and threshold conditions; no such operator is yet attached to this neck. The egg’s `I_4` fibre and `T_δ⁴` monodromy are an algebraic instance of converging and diverging sheets. Its regular-differential egg period has leading value `2χ/(ab)`; reading it as elapsed physical time is **[interpretation]** until a clock is constituted. [Levinson (1949)](https://gymarkiv.sdu.dk/MFM/kdvs/mfm%2020-29/mfm-25-9.pdf).

**[interpretation]** “The neck is an exchange” names the shared port and boundary picture. The conservation claim belongs to the complete power ledger; the Morse, optical, fluid, singularity and scattering charts contribute their own hypotheses and residuals.

(Audited and rewritten by Sol, September 25: the first version treated flux as constant through an unsteady pinch, gave a point source positive étendue, called ADE the finite classes of every neck, and conflated repeated-root, trace-2 and Lorentz-null.)

## 13. Ricci flow: a constituted geometric neck

Brandon: “Ricci flow?” The [July 19 record](2026-07-19_THE_RICCI_TRACE_CHANGES_THE_RECEIVER_THE_SINGULAR_NECK_REBASES_THE_BODY.md) gives the Riemannian source map: for a declared metric and Levi-Civita connection, Ricci is the transverse trace of geodesic deviation. Ricci flow changes that metric. The claims below keep smooth flow, singular rescaling, surgery, topology accounting and physical transport distinct.

- **The smooth flow** `[proved-standard]` (Hamilton 1982, 1988; Chow 1991).
  - On a smooth Riemannian manifold, `∂_t g = −2 Ric(g)`. Scalar curvature obeys `∂_t R = ΔR + 2|Ric|²`; this is diffusion **with a quadratic curvature term**, rather than pure heat flow. Volume obeys `∂_t dV_g = −R dV_g`, so unnormalized flow does not generally conserve volume. Smooth flow keeps the manifold’s topology fixed while the solution exists. [Hamilton (1982)](https://projecteuclid.org/journals/journal-of-differential-geometry/volume-17/issue-2/Three-manifolds-with-positive-Ricci-curvature/10.4310/jdg/1214436922.pdf).
  - For volume-normalized flow on a closed `n`-manifold, `∂_t g = −2 Ric + (2/n) R̄ g`, with `R̄` the mean scalar curvature. A literal fixed metric satisfies `Ric = (R̄/n)g`, and conversely: it is Einstein. A soliton may instead recur only after a diffeomorphism and scaling.
  - On a closed surface, the area-normalized flow converges to a constant-curvature metric in the initial conformal class, with the sphere case completed by Chow. This surface theorem does not classify three-dimensional singularities. [Hamilton (1988)](https://cir.nii.ac.jp/crid/1360855570560549376), [Chow (1991)](https://scispace.com/pdf/the-ricci-flow-on-the-2-sphere-41gyy494nh.pdf).

- **The shrinking-cylinder model** `[proved-derived for the product; proved-standard for the stated examples]`.
  - For `k ≥ 2`, put `g(t) = ds² + r²(t)g_(Sᵏ,unit)` on `ℝ × Sᵏ`. Since the unit sphere has `Ric = (k−1)g_(Sᵏ,unit)`, the flow gives `d(r²)/dt = −2(k−1)`, hence `r²(t) = 2(k−1)(T−t)` when it vanishes at `T`. This is exact for the product cylinder; `k=1` has no such Ricci-driven shrinkage.
  - Angenent and Knopf (2004) construct an open class of rotationally symmetric metrics on `S^(k+1)`, `k ≥ 2`, developing a Type-I neckpinch whose parabolic rescalings approach that cylinder. A curved neck is not literally §12’s one-sheeted hyperboloid, and its unscaled product cylinder collapses toward an axis, not a Morse double cone. The hyperboloid comparison is `[interpretation]`. [Angenent–Knopf (2004)](https://people.math.wisc.edu/~angenent/preprints/MRLrevision2.pdf).
  - Perelman’s three-dimensional canonical-neighbourhood theory controls sufficiently high-curvature regions, at their curvature scale, by `ε`-close neck/cap and compact positively curved **types** arising from κ-solutions and surgery models. It does not reduce them to a finite table of exact metrics. Surgery cuts suitable `S² × I` necks and caps their `S²` ends under its scale and curvature hypotheses. [Perelman (2002)](https://arxiv.org/pdf/math/0211159), [Perelman (2003)](https://arxiv.org/pdf/math/0303109).

- **The topology receipt** `[proved-standard for three-manifold topology; interpretation for retention]`.
  - Kneser–Milnor gives a finite connected-sum decomposition of each closed connected orientable three-manifold into prime factors, unique up to order and diffeomorphism; the unit is `S³`. The existence and uniqueness statements concern the **original manifold**. [Milnor (1962)](https://doi.org/10.2307/2372800).
  - A geometric `S²` surgery neck need not be a selected prime-decomposition sphere. Some surgeries are topologically trivial. For a separating `S²`, cutting and capping yields `M_before ≅ M₁ # M₂`; for a nonseparating `S²`, reconstruction can require an `S² × S¹` factor. Discarded components also enter the reconstruction. Perelman shows that the topologically nontrivial surgeries are finite in the finite-extinction argument; he does not identify every surgery cut with one unique prime factor. Long-time geometrization of nonextinct pieces additionally requires thick/thin and JSJ analysis. [Perelman (2003), finite extinction §1](https://arxiv.org/pdf/math/0307245), [Morgan–Tian (2007)](https://www.claymath.org/resource/ricci-flow-and-the-poincare-conjecture/).
  - The parallel with integer factorization and Schubert knot sums is `[interpretation]`: all three have qualified unique decompositions, with different objects and composition laws.

- **The aeon and retention reading** `[interpretation; local derivation open]`.
  - Smooth Ricci-flow intervals are continuations of one metric-bearing Holon. A surgery can be an epoch crossing **only for a declared receiver section and clock**; it can end or found an aeon only when that aeon’s causal boundary is supplied. Calling every program-selected interval between surgeries an aeon would violate the time vocabulary.
  - Prime factors are unchanged during each smooth interval, but topology changes at surgery. The conserved consequence of the *proof* is the ability to reconstruct the original topology from a receipt carrying capped outputs, separating or nonseparating gluing, and discarded-component types. That receipt is not an archive of earlier metrics. To call its quotient retention, construct a source map `q` and successor maps `U` such that `q T_w = U_w q` and every admitted future face satisfies `ρ T_w = ρ̄ U_w q`; retain the reconstruction fibre when a later receiver separates it. Neither Perelman’s theorem nor the current finite triangle flow supplies this Holonics square automatically.

- **Perelman’s geometric functionals** `[proved-standard under their coupled hypotheses]`.
  - On a closed Riemannian manifold with `ρ = e^(−f) > 0` and `∫ρ dV_g = 1`, `𝓕(g,f) = ∫(R + |∇f|²)ρ dV_g`. Its second summand is the **spatial relative Fisher information** `∫|∇logρ|²ρ dV_g` for the contemporary metric and volume measure. It is not a Fisher-information matrix for an unspecified statistical parameter. [Perelman (2002) §1](https://arxiv.org/pdf/math/0211159).
  - Set `u = (4πτ)^(−n/2)e^(−f)`, `∫u dV_g = 1`, and `𝒲 = ∫[τ(R+|∇f|²)+f−n]u dV_g`. If `∂_t g = −2Ric`, `∂_tτ = −1`, and `∂_t f = −Δf + |∇f|² − R + n/(2τ)`, then
    `d𝒲/dt = 2τ∫|Ric + Hess f − g/(2τ)|² u dV_g ≥ 0`.
    Its derivative vanishes exactly when `Ric + Hess f = g/(2τ)` on the weighted domain: the gradient shrinking-soliton equation. The zero class includes more than necks and round spheres. Calling this derivative aeon A10’s `P` is `[interpretation]` until the aeon, receiver, normalization and its production law are joined. [Perelman (2002) §3](https://arxiv.org/pdf/math/0211159).
  - From a chosen spacetime basepoint, reduced distance is `ℓ(q,τ) = (1/(2√τ)) inf_γ ∫₀^τ √s (|γ̇|² + R) ds` along backward-time paths. Reduced volume is `Ṽ(τ) = ∫(4πτ)^(−n/2)e^(−ℓ(q,τ)) dV_(t₀−τ)(q)` and is nonincreasing in backward time under Perelman’s hypotheses. This is a Gaussian **comparison kernel** on an evolving metric, not generally the conjugate heat kernel or a freely chosen two-locus loss. [Perelman (2002) §§6–7](https://arxiv.org/pdf/math/0211159).
  - For a smooth closed-manifold flow on a fixed finite interval, Perelman supplies `κ>0`, depending on the initial metric and interval, such that balls of radius `r` below the stated scale with `|Rm| ≤ r^(−2)` **throughout the ball** have `Vol B_t(x,r) ≥ κrⁿ`. The spacetime version also bounds curvature on a backward parabolic neighbourhood. This rules out *local collapse under those hypotheses*; it neither forbids every long-time collapse nor requires a topology change. [Perelman (2002) §§4, 8](https://arxiv.org/pdf/math/0211159).

- **Two separate scale and packing applications** `[proved-standard within their source models; Holonics join open]`.
  - Friedan’s perturbative two-dimensional nonlinear sigma model has a target-metric beta function whose leading curvature term is `β^G_ij = α′ Ric_ij + O(α′²)`, subject to RG sign and parameter convention, field redefinitions, and any `B`-field or dilaton terms. Ricci flow is recovered from that leading metric term after the stated rescaling and gauge choice. RG scale is not target-space elapsed time, and a Ricci singularity has no automatic T-dual continuation. [Friedan (1980)](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.45.1057), [Friedan (1985)](https://www.physics.rutgers.edu/~friedan/papers/Annals_of_Physics_163_2_318_1985.pdf).
  - Chow–Luo assign positive radii `r_i` to vertices of a weighted triangulation of a **closed surface**, derive edge lengths from those radii and intersection angles, and set combinatorial curvature `K_i = 2π −` the sum of incident triangle angles. Their normalized Euclidean flow is `dr_i/dt = −(K_i−K_av)r_i`. It converges exponentially to a constant-combinatorial-curvature circle-packing metric **iff** the required Thurston link inequalities/existence condition holds; their hyperbolic theorem has its own conditions. It is not a flow on the five oriented sphere bends of `Geometry/SpherePacking`. “Packing is an equilibrium of curvature diffusion” is `[interpretation]` until that surface’s incidence, radii, curvature and flow are constructed as a consumer. [Chow–Luo (2003), Theorems 1.1–1.2](https://sites.math.rutgers.edu/~fluo/mpapers/combinatorial%20Ricci%20flow%20in%20dimension%202.pdf).

- **Current formal boundary** `[proved-derived; source audit]`. `Geometry/Ricci` proves its rational three-cell flow and variance identities, not smooth Ricci flow, Perelman `𝒲`, κ-noncollapsing, or surgery. `Objects/RelativeCompleteness.ricci_fails` is a counterexample in that finite flow. `HolonicsResearch/Geometry/PoincareConjecture` names the solved external theorem, while `PoincareOfficialBridge.thePoincareConjecture_of_finishLine` proves only the implication from a supplied construction and reconstruction. A kernel-checked Perelman proof is not present. The concrete next source terms are a Riemannian metric/curvature evolution, conjugate-heat carrier, curvature-scale neighbourhood map, actual capped post-surgery manifolds with gluing and discarded-component receipts, and the admitted-future factorization required for retention.

(Audited and rewritten by Sol, September 25. The first version called the cylinder law every neck's, canonical neighbourhoods a finite table of metrics, and surgery spheres the prime-decomposition spheres; it also used a wrong cylinder radius.)

## 14. The nine-loop amplitude: exact arithmetic at scale, and three joins

Brandon supplied the same day's [Anthropic account](https://www.anthropic.com/research/yes-claude-can-do-nine-loops)
and [the computation's notes](https://smsharma.io/cosmic-nine-loops/): the six-gluon MHV amplitude
of planar `𝒩 = 4` super-Yang–Mills at nine loops, bootstrapped by Claude. The route was the
three-point form factor, mapped to the amplitude by antipodal duality. The results were certified
over the rationals from 31-bit prime images, and the eight-loop result was reproduced as a control.
`[established-bounded; source-inspected]`

- **Exact arithmetic at scale is prime images with a decoder.**
  - Exact rationals were computed as images at several 31-bit primes and lifted by rational
    reconstruction, then checked.
  - History already owned this law for our linear algebra: `13f8c734`
    `crates/holonics/src/prime_image_algebra.rs` (atlas `linalg.prime-image-certificate`,
    `linalg.mersenne-ring`). Its return is owned by verification over `ℚ`, never by a modulus.
  - Its header measured textbook rational Gauss–Jordan at 7, 168 and 568 s for 72, 120 and 180
    coordinates, the cost campaign 1 hit. It was not ported in step 1 and is being ported into
    `ratio::linear` for the compare.
  - A residue is an exact representation with its decoder (CRT and rational reconstruction) and
    its residual (the verification), under CLAUDE.md's exact-representation law.
- **The bootstrap is compression by constraints** `[interpretation]`. It starts from a finite space
  of candidate functions (symbols over a fixed alphabet at a given weight) and eliminates candidates
  by symmetry, physical limits and boundary data until one remains. This has the shape of locating
  keys by loop closure (`Compression/Core/Keys`): the answer is a landmark located by the faces it
  must satisfy, not searched for.
- **The antipode is the reversal** `[proved-standard]` for the algebra.
  - A symbol is an iterated integral: a word in its alphabet. The coproduct deconcatenates words,
    and the antipode reverses them with sign `(−1)ⁿ`.
  - For a path's signature, the antipode is the signature of the reversed path.
  - So antipodal duality is a reversal, the same operation as aeon A6's `Rγ` in
    `σ = D(P_γ‖P_(Rγ))`, and a reflection in the Swing's sense `[interpretation]`.
- **Symbols, signatures and the source moment.**
  - `[proved-standard]` Chen's iterated integrals: a path's signature is multiplicative under
    concatenation (Chen's identity). It determines a bounded-variation path up to tree-like
    equivalence (Hambly and Lyons 2010). Linear functionals on it multiply by the shuffle product.
  - `[interpretation]` The HNN's source moment `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)` is a transported
    level-one term of such a signature, and the pair port `E^(δ)` a fixed-offset level-two term.
  - The signature is a complete, tape-free, order-aware summary: a retention whose kernel is
    tree-like equivalence. It is a candidate object for campaign 5's context, owed as a derivation
    before any use.

## 15. Division, inverse, and constituted return

Brandon: division has a direction and a remainder; unequal parts can still return a conserved whole. These are operations on the ratio, navigator, constitution and receiver, with different hypotheses.

- **The logarithmic inverse chart** `[proved-standard]`. For an invertible complex scalar or invertible complex matrix `A` with a chosen logarithm `L` satisfying `exp L = A`, define `A^z := exp(zL)` on that chart. Since `e^(iπ)=−1`, `A^(e^(iπ)) = exp(−L) = A⁻¹`. The final inverse is independent of the chosen scalar log branch, although the path `z ↦ exp(zL)` is not. `A^(1/2)=exp(L/2)` selects **one** square root and depends on the branch; the square roots of `e^(iπ)=−1` include both `i` and `−i`. A real matrix need not have a real logarithm; zero and noninvertible operators have no multiplicative inverse. A Swing `S` with `S²=I` is its own inverse, but that geometric involution is a separately typed operation. Identifying the two requires a source map into this logarithmic chart. `[interpretation]` The inversion/half-turn picture is useful after that map, not a definition of division for every tensor or Holon.

- **What discrete integration actually conserves** `[proved-derived; formal-checked in Holon/Cayley]`. For a finite skew-Hermitian `K`, real `h`, and a mode with eigenvalue `iλ`, the explicit multiplier `1+ihλ` has norm `√(1+h²λ²)`; it is strictly greater than one only when `hλ ≠ 0`. The implicit multiplier `(1−ihλ)⁻¹` has reciprocal norm. The full midpoint/Cayley multiplier `(1−ihλ/2)⁻¹(1+ihλ/2)` has norm one. Thus the **full** Cayley step `C=(I−hK/2)⁻¹(I+hK/2)` is isometric; the inverse denominator alone is not. With a resistive part `R ⪰ 0`, midpoint instead satisfies `ΔE = −h⟨x̄,Rx̄⟩ ≤ 0`. Other exact norm-preserving updates, including `exp(hK)`, exist; conservation does not occur *only* through inversion. [Holon/Cayley.lean](../../lean/Holonics/Holon/Cayley.lean:100).

- **An inverse needs its image and kernel** `[proved-standard; finite form formal-checked]`. A finite linear equation `Kφ=ρ` has a solution exactly when `ρ` annihilates `ker K*`; when solvable, its solutions are one particular solution plus `ker K`. On a compact connected Riemannian manifold **without boundary**, `Δφ=ρ` is solvable for smooth `ρ` exactly when `∫ρ dV=0`, and `φ` is unique modulo constants. Hence writing `K⁻¹ρ` is justified only on an invertible restriction or as an explicitly chosen Green/pseudoinverse with its kernel fibre retained. A nonzero net source is incompatible with that *stationary closed Poisson equation*; in a time-dependent constitution it may instead accumulate, and with ports it may leave. The [finite Fredholm owner](../../lean/Holonics/Holon/Port.lean) and `Foundation/HodgeReceiver` do not yet prove the stated smooth-manifold theorem.

- **Division is not automatically emanation** `[interpretation]`. Solving a constituted field equation can redistribute an already admitted mode. It is FOUND/emanation only when the declared navigator and terrain require a new off-resonance mode or source relation; the consumer must show that from its source, port, kernel and residual. Ordinary rational division and a Green solve do not establish it.

- **Unequal slices and an equal area face** `[proved-standard]`. For a uniformly measured circular disc, choose an interior point `P` and make `N` concurrent full-line cuts through `P`, producing `2N` equal-angle sectors. Color successive sectors alternately. If `N ≥ 4` is even, the two area sums are equal for every `P`: this includes `8,12,16,…` sectors. For other `N`, equality holds **exactly when the disc centre lies on one cut**; thus “fails off centre for 2,4,6,10,14” is too strong. This is a geometric signed-area identity, not conservation under time evolution or a theorem about arbitrary shapes/densities. [Goldberg (1968), original solution](https://www.jstor.org/stable/2687962); [Mabry and Deiermann (2009), exact equality conditions](https://citeseerx.ist.psu.edu/document?doi=e1523332e672d23c9c20c07212ad67e5f67fea19&repid=rep1&type=pdf).

- **Distinct physical instances** `[proved-standard under their named models; joint reading interpretation]`.
  - Jeans’ linearized homogeneous, isothermal, self-gravitating fluid has `ω²=c_s²k²−4πGρ`; wavelengths `λ>λ_J=c_s√(π/(Gρ))` grow linearly. Fragmentation into particular bodies needs nonlinear evolution, boundary data and competing physics. [Jeans (1902)](https://doi.org/10.1098/rsta.1902.0001).
  - Classical homogeneous spherical nucleation assumes isotropic surface energy `γ>0` and favourable bulk free-energy density difference `−|Δg_v|`. Then `ΔG(r)=4πγr²−(4π/3)|Δg_v|r³`, whose barrier is at `r*=2γ/|Δg_v|`. It is not a universal crystallization radius for anisotropic or heterogeneous nuclei. [Turnbull (1950)](https://scispace.com/papers/formation-of-crystal-nuclei-in-liquid-metals-18mkl6c20e).
  - Cooling contraction can produce roughly hexagonal basalt columns; measured column scale varies with cooling and fracture conditions. It is an empirical material instance, not an exact sixfold law from division. [Goehring (2008)](https://agupubs.onlinelibrary.wiley.com/doi/full/10.1029/2007jb005018).
  - A critical Rayleigh number is the onset condition of a *specified* conduction state, geometry, rheology and thermal/mechanical boundary conditions. It has no universal value for mantle convection. [Kameyama et al. (2021)](https://doi.org/10.1186/s40623-021-01499-w).
  - Gutenberg–Richter is a **cumulative frequency–magnitude** relation, `log₁₀ N(M≥m)=a−bm` over its fitted catalogue range. It is not itself a power law for released strain; converting magnitude to energy or moment needs another measured relation and units. [Gutenberg and Richter (1944)](https://doi.org/10.1785/BSSA0340040185).

- **A face can end while a specified current balances** `[proved-standard for the physical channel; proved-derived for the lattice ledger]`. The channel `e⁺+e⁻→2γ` conserves total four-momentum, `p₊+p₋=k₁+k₂`; two photons are one allowed final channel, while other admitted states can yield three photons or other products. A local `∇_μT_total^(μν)=0` requires the *complete* matter-and-field stress tensor and its hypotheses; global energy conservation additionally needs the applicable symmetry/boundary. Particle number is not conserved by annihilation. In the HNN’s declared lattice rule, `applied + carried + released = exact update`, and the nonzero release has a receipt. That is an accounting identity for this representation, not a theorem that no receiver ever reads zero or that every release is physical radiation. [Holonics HNN LatticeDeposit](../../lean/Holonics/HNN/LatticeDeposit.lean:357); [three-photon annihilation channel](https://electronicsandbooks.com/edt/manual/Magazine/P/Physical%20Review/Physical%20Review%201940-1949/ROOT/DATA/PHYSREV_/PDF/PR/V75/I11/PR_V7510.PDF).

(Audited and rewritten by Sol, September 25. The first version said conservation occurs only through inversion, that division is emanation in general, that the pizza equality fails off centre for 2, 4, 6, 10 and 14 slices without exception, and that annihilation proves nothing reduces to nothing.)

## Obligations

| Owner | Statement | Consumer |
|---|---|---|
| `Compression/Core/FaceMap`, `HolonicsResearch/Foundation/TopologicalReceiver` | A quotient is lawful iff every admitted future face factors through it; a persistent feature is robust under a stated perturbation bound; the pinch as an `H₀` reading | `retain(x) = retain(y) ⇒ ρ(T_w x) = ρ(T_w y)` at release |
| `Transport/JunctionLaw`, `Physics/Spacetime/NonClosedClock` | Conserved `(ω, k_∥)` with each side's dispersion and the normal remainder; the Killing-energy frequency law `hν = E_ξ/N` | `physics::wave` interface reception; `physics::spacetime` redshift |
| `Foundation/FractalPacking` | Proved: the conjugate reflection, the word integration identity, its `Lip(f)·3^(−n)` residual and reflection invariance. Owed: the self-similar measure's identification | `view(receiver, grain, clock)` integrating an exact finite partition with its residual (a Rust consumer is owed) |
| `HolonicsResearch/Geometry/SpherePacking` | Centres and separation first; then the limit set, measure and conformal weights | a sphere-contact Holon and its receiver |
| research owner | Kepler `𝔰𝔬(4)` brackets, the hodograph circle, Hopf fibres and their linking | `geometry::screw` or a receiver that transports these faces |
| `HolonicsResearch/Hodge` | Gauss–Manin transport with its monodromy fibre, the `(p,p)` receiver and a cycle-source incidence | `cycleClass(Z_s) = T_γ h` commuting with transport |
| `HolonicsResearch/Zeta` | The divisor contour reading, and heat-flow collisions only where `H_t = ∂H_t = 0` | the explicit-formula receivers |
| fluid research owners, #32 | Complex-valued evolution kept apart from spatial continuation, and any strip theorem with its norm and forcing | the neck chart's source map |
| `Physics/Spacetime`, `Holarchy/Globe` | Horizon port (focusing, flux, area or Noether entropy), and a globe witness only when all three clauses hold | `∇·J_u` against the horizon current |
| `Compression/Core/Keys`, `Holon/Dirac` | Key steering to a reachable landmark under a complete power ledger | the HNN word's receiving call |
| geometry and wave owners | The quadric surgery family; the Gaussian neck `w = w₀ cosh χ` with Gouy phase `gd(χ)` and mode phases `(N+1)·gd(χ)`; `ABCD` determinant 1 as the conserved étendue face; the Maslov quarter-turn per caustic dimension | `physics::wave` reception through a focus; the site classification's lightlike class |

The atlas rows to add are named with their owners when each lands. `quantum.t-duality`,
`quantum.routh-reduction` and `coupling.holonic-torus-knots` already hold what §7–8 use.
