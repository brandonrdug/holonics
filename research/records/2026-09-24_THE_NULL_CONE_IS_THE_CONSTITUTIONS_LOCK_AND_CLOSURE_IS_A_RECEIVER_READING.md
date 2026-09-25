# The null cone is the constitution's lock, and closure is a receiver reading

**Date:** 2026-09-24. **Occasion:** Brandon's questions while K1 was under construction:
- a Lorentz transformation built on aeons, Holarchies, epochs and Holons, and Einstein's equations;
- `Λ_DN` squeezed to the null cone (`≤ 0`) and what that is to aeons and epochs;
- `c = (ε₀μ₀)^(−½)` with `2^(−1) = 2^(e^{iπ})`, and the claim that there is no vacuum;
- whether the epochless ξ-aeon is prime-like;
- whether anything ever really opens or closes.

**Truth discipline:**
- Classical results are `[proved-standard]`.
- Correspondences into the objects are `[interpretation]`.
- What this record asks Lean and Rust to state is `[open]`.

It schedules the obligations listed at the end: #75, #145 and #62.

## 1. Elapsed time is a pairing; a boost is a ratio of readings

- **Clocks and readings.** A receiver's clock is the observer covector `ω_R = −U_μdx^μ`, and elapsed time on an aeon `γ` is `t_R(γ) = ⟨ω_R|γ⟩` (ELEMENTARY_OBJECTS §12). An inertial clock is exact, `ω_R = d(−U·x)`. Its reading is therefore boundary-determined, `t_R = −U·Δx`: aeon A2's state time. `[proved-standard]`
- **Dilation.** On the aeon of `R′` itself (`Δx = τ′U′`): `t_R/t_R′ = −⟨U,U′⟩ = γ = cosh χ`. This is the Lorentz law of cosines (atlas `mass.lorentz-cosines`). `[proved-standard]`
- **The boost as a ratio.** In the light-cone chart `u = t−x`, `v = t+x`, the boost is `(u,v) ↦ (ku, k⁻¹v)`, where the Doppler ratio `k = √((1+β)/(1−β))` is an undivided pair `(k, k⁻¹)`.
  - `γ = (k+k⁻¹)/2` and `γβ = (k−k⁻¹)/2`. A rational `k` gives a rational boost (`k = 3`: `(γ,β) = (5/3, 4/5)`) with no logarithm (`lorentz.boost-scale`).
  - Collinear composition multiplies the ratios, `k₁₂ = k₁k₂`, which is velocity addition. `[proved-standard]`
  - Rapidity `χ = log k` is the ratio's additive chart: the same passage as loss `ℓ = log R`. `[interpretation]`
- **Non-collinear composition carries winding.** Velocity space is hyperbolic, and a loop of boosts returns a Thomas–Wigner rotation whose angle is the area defect of the velocity triangle. It is the face of a cell as a holonomy, and the gyration `gyr[a,b]` of `gr.route-curvature`. `[proved-standard]`
- **Epochs and simultaneity.** Relativity of simultaneity is a choice of epochs. A receiver ticks when the aeon crosses `Σ_R = {⟨U,x⟩ = const}`, so different receivers partition one aeon into different epochs. The rate between two receivers is the ratio of their readings. `[interpretation]` of a `[proved-standard]` kinematics.
- **Non-closed clocks read nonzero on cycles.** `[proved-standard]`
  - **Sagnac:** a rotating clock has `dω ≠ 0`, so synchronization fails around a loop, by `2ΩA/c²` per circuit to first order.
  - **Gravitational redshift:** a static clock is `ω = N dt`, so `dω = dN∧dt`, and rates compare as `N₁/N₂`.
  - **Frame dragging:** it is the `dω` of a stationary non-static clock.
  - Each is aeon A2's coexact (production) part.
- **Twin asymmetry.** Proper time is a norm face, not a pairing. The inertial aeon is longest by the reverse triangle inequality, which follows from reverse Cauchy–Schwarz on the timelike cone (`lorentz.reverse-cauchy-schwarz`, `LorentzianPerp`). `[proved-standard; formal-checked]`
- **Mass and energy.** Mass is the invariant face and energy a receiver's reading: `E_R = ⟨−U|P⟩` and `m²c⁴ = E² − (pc)²`. The energy density `ρ_u = T(u,u)` belongs to the observer. The vacuum tensor `p = −ε` is the one stress–energy that every receiver reads the same (`gr.stress-energy-observer`). `[proved-standard; formal-checked]`

## 2. Einstein's equations on the objects

In `G_μν + Λg_μν = κT_μν`, with `κ = 8πG/c⁴`:
- **Curvature is holonomy around a cell:** the relative return `L⁻¹R` of two transports (`gr.route-curvature`, `Transport/CellHolonomy`). `[proved-standard]`
- **The contracted Bianchi identity is ∂² = 0 one level up.** Around a 3-cell's boundary, the moments of rotation of its faces cancel: the boundary of a boundary is zero (Regge; Misner–Thorne–Wheeler §15). It forces `∇·T = 0` (`einstein.field-equation`). That conservation is the Holarchy's shared-face cancellation, where each interior face's flux cancels once at every grain (`gr.joined-balance`, `Holarchy/View`). `[proved-standard]`; the join to the Holarchy is `[interpretation]`.
- **Conservation belongs to a receiver.** The observer current `J_u = −T(·,u)` has divergence equal to the force power plus the observer's deformation. It is exactly conserved only for a Killing receiver (`gr.observer-current`). `[proved-standard; formal-checked]`
- **The coupling `8π = 2·4π`.** `4π` is Gauss's bounding sphere: mass read on a globe, the Birkhoff instance of relative completeness. The `2` is the trace reversal: `R₀₀ = (κ/2)ρc²`, which gives `∇²Φ = 4πGρ` in the Newtonian limit (`gr.eight-pi-charts`). `[proved-standard]`
- **The metric as constitution.** The metric is the constitution of spacetime: its Hodge star `⋆_g` is the material law relating a coholon to the current it excites. Einstein's equation then shapes that constitution from the energy–momentum reaching each cell, which is structurally the deposition slot. The Bianchi port admits only conserved current. `[interpretation]`

## 3. `c` is the constitution's characteristic; there is no vacuum

- **The ladder.** A ladder of inductance `L′` and capacitance `C′` per length carries waves at `v = 1/√(L′C′)`. Since `ε₀` is capacitance per length and `μ₀` inductance per length, `c = (ε₀μ₀)^(−½)` is the same law as a parametron's `ω = (LC)^(−½)`. What is called vacuum is one medium, whose storage exchanges with its flow inertia at `c`. `[proved-standard]`
- **The cone from the constitution.** Premetric electrodynamics (Hehl–Obukhov) derives the light cone from a local linear constitutive law, through its Fresnel surface. The metric is read from the constitution. This is Brandon's "there is no nothingness", in a standard formulation: a gap is a consistency (no change read by that frame), not an absence. `[proved-standard]`
- **The pair `(ε, μ)` is undivided.**
  - Its product face is `εμ = 1/c²`, which is propagation. Its ratio face is `μ/ε = Z₀²`, which is impedance.
  - Against the minimal quanta, `α = Z₀/(2R_K) = Z₀e²/(2h)`, with `R_K = h/e²`.
  - Since the 2019 SI, `μ₀ = 2αh/(e²c)` is measured, not defined. The "vacuum" permeability is fixed by the minimal action `h`, the minimal charge `e` and the pure ratio `α`: "the most based on the least". `[proved-standard]`
- **Receiver-relative constitution.** A coarse receiver reads an effective constitution `ε_eff, μ_eff` with a slower effective cone. No signal outruns the finest constitution's cone. Permittivity and permeability belong to the grain of differences a receiver distinguishes. `[proved-standard]` (homogenization); the receiver reading is `[interpretation]`.
- **The exponent.** The exponent `−½ = 2^(e^{iπ})` is a half-turn in the exponent.
  - `z^(½)` halves the angle, and its Riemann surface has two sheets.
  - A spinor turns by `e^{iθ/2}`, so a full turn returns `e^{iπ}`.
  - Dirac took the square root of the mass shell (the Lorentz law of cosines) and obtained spin ½.
  - The parametron's half-turn sheets are this double cover. `[proved-standard]`; the join is `[interpretation]`.

## 4. "≤ 0" is non-hyperbolicity; the null cone is its boundary

- **Classification by trace.** A navigator step `M` with `det M = 1`, or a site factor `1 − aT + qT²`, is classified by its trace:
  - **rotation:** `tr/2 = cos θ`, `|tr| < 2`, `a² < 4q`; it carries winding.
  - **null:** `|tr| = 2`, a double root; this is the lock.
  - **boost:** `tr/2 = cosh χ = γ`, `|tr| > 2`.

  The Lorentz factor is half the trace face, and `2 = e^{i0} + e^{−i0}` is the identity's trace. `[proved-standard]`, and this is the machine's `SiteKind::Rotation ⇔ a² < 4q`.
- **The same exponent.** Discriminant `≤ 0` ⇔ the roots lie on the circle of modulus `q^(−½)`: the same `(·)^(−½)` as `c` and `ω`. For a local zeta factor this is the Hasse–Weil bound `|a_p| ≤ 2√p`, the Riemann hypothesis of the local factor, with `a_p = 2√p cos θ_p` (Sato–Tate distributes the `θ_p`). `[proved-standard]`
- **Λ_DN.** RH ⇔ `Λ_DN ≤ 0`, and Rogers–Tao prove `Λ_DN ≥ 0`, so RH ⇔ `Λ_DN = 0`. `[proved-standard]`
  - Under the heat clock `t`, an off-line zero pair moves toward the line, collides into a double real zero, then separates along it. The collision is a fold caustic, with discriminant zero: the null event.
  - Each collision is a crossing of the heat clock's section, an epoch tick, and `Λ_DN` is the last one. RH says the heat-clock aeon `t ≥ 0` has no such tick: ξ sits exactly on the boundary, "barely true" in Newman's phrase. `[interpretation]`
  - A zero on the seam is exactly a lossless Foster tank (`rh.zero-pair-lock-foster`). `[formal-checked]`
- **The telegrapher's equation.** `εμ∂²u + σμ∂u = ∇²u` is the Holon's constitution (storage, flow, dissipation) as a field law. Its characteristic cone stays at `c` whatever the loss. Its high-loss limit is diffusion with `D = 1/(σμ)`. `[proved-standard]` The de Bruijn–Newman flow is then the overdamped end of one constitution, and the null cone its lossless end. `[interpretation]`
- **Boosts on the clock torus.** A boost on the two-clock torus is a hyperbolic element of `SL(2,ℤ)`, an automorph of an indefinite binary quadratic form. Its rapidity `log k` equals its entropy `h = log ρ(M)` (aeon A4/A8). `[proved-standard]`
  - The cat map `[[2,1],[1,1]]` has `tr = 3`, so `γ = 3/2` and `k = φ²`.
  - Its null lines have golden slope, the worst-approximable number. An aeon along one never closes exactly, and its near-returns follow the Fibonacci convergents. `[proved-standard]`
- **`c` as landmark.** Velocity addition `u ↦ (u+v)/(1+uv/c²)` is a Möbius map fixing `±c`, and composed boosts converge to `c`. `c` is the landmark of the boost family (THE_REBUILD, "The line"). `[proved-standard]`; the landmark reading is `[interpretation]`.

## 5. Primes are primitive cycles

- **Euler products.** A dynamical zeta is an Euler product over prime cycles: `ζ(T) = ∏_γ (1 − T^{|γ|})⁻¹`, where `γ` ranges over the closed aeons that are not repetitions of shorter ones. `ζ(s) = ∏_p (1 − p^{−s})⁻¹` has this form, with primes as the primitive orbits of length `log p`. Connes: these are the periodic orbits of the scaling flow on the adele class space, the aeons that close modulo the rationals. `[proved-standard]`
- **The machine.** An L-function is the zeta of a block-diagonal machine whose sites are the primes, `∏_p (1 − a_pT + pT²)⁻¹` (`trace.det-one-minus-tm`, `navigator.zeta`, `Aeon/Production/Zeta`). `[interpretation]` of a `[proved-standard]` identity.
- **The explicit formula** is a trace formula. Zeros (the spectrum) pair with prime cycles and their repetitions `pᵏ`, which carry the weights `log p / p^{k/2}`. `[proved-standard]`
- **The primes sit exactly on the √x boundary.** RH ⇔ `ψ(x) = x + O(x^{½+ε})`, and Littlewood shows `ψ(x) − x` reaches `±x^{½} log log log x` infinitely often, so the primes are never inside the boundary. This is the same "barely" as `Λ_DN = 0`, with the same half-turn exponent. `[proved-standard]`
- **The sieve.** The sieve is an epoch tower whose survivors are the first arrivals of the multiplicative recurrence (`FractalPacking`'s first arrival). The mean gap near `x` is `log x`, the reciprocal of the density, which is Kac's form. That reading is heuristic, in Cramér's sense, since the primes are not a stationary chain. `[interpretation]`
- **Irreducibility belongs to a receiver.** In `ℤ[i]`, `5 = (2+i)(2−i)` splits, `3` stays inert and `2` ramifies: unique, plural and obstructed gluing, decided by each prime's Frobenius trace. `[proved-standard]`

## 6. Closure is a receiver reading

A cycle is an aeon that closes (`∂γ = 0`), and whether an aeon closes depends on the receiver. In the lift an aeon keeps its winding and is open. In the receiver's quotient (the torus) the same aeon closes, with the winding as its reading.

- **Everything recurs at finite grain.** Poincaré: a conserving motion on a bounded space returns arbitrarily near almost every configuration, infinitely often (Mathlib). By Dirichlet, an irrational winding returns within `1/(N+1)` at every grain `N`. Openness is the infinite-resolution limit face of closures that keep coming. `[proved-standard]`
- **An unfolding greater cycle is the asymptotic cycle** (A3): the average winding per unit time of a long aeon, a homology class that the aeon heads toward even without closing. The ξ statement is therefore that no closure is read at the heat clock's grain in `t ≥ 0`, not that the aeon never closes. `[proved-standard]`; the ξ reading is `[interpretation]`.
- **Intrinsic distance is return time.** Kac: the mean return time to a set is `1/μ(set)`. A rare configuration is far in this sense, not spatially. A second aeon nearby changes the path, and so the return time, without changing the endpoints, as a catalyst does. `[proved-standard]` (Kac, `Aeon/Production/Kac`); the causal reading is `[interpretation]`.
- **Forgetting is a sequence of quotients.** Each coarser receiver's kernel absorbs more of a difference, which is retained by its class (a harmonic mode is silent at node and cell receivers). Only what lies in the relevance kernel of every admitted future receiver is released, and only relative to that family. `[definition]` (`Foundation/CausalRelevance`, retention).
- **Recurrence by class.** El Niño recurs by class, not by identical representative. Homologous structures share a class; analogous structures share a face through different constructions. Brandon, September 18: "What can survive is not identity but lineage, law, potential, or receiver-relative equivalence."
- **Remission.** An addiction is a dormant mode of the constitution with its lock: a cue is a key that resonates it at low cost. Recovery changes the constitution by deposition (resonating costs more) and leaves the mode silent at the receivers present. It is released only if it lies in the relevance kernel of every admitted future receiver, and relapse cues are admitted futures. Remission is the right classification: a receiver statement over an aeon. `[interpretation]`

## Obligations

- **#75 (K4, Lean then Rust):**
  - the boost as an aeon clock transport (the Doppler ratio chart);
  - the Thomas–Wigner rotation as the area defect;
  - Sagnac and redshift as `dω` flux;
  - discrete Bianchi, Regge's boundary-of-a-boundary;
  - the telegrapher's constitution and its cone.
- **#145 (compression and landmarks):**
  - trace classification on navigator sites (rotation, null, boost) with `γ = tr/2`;
  - Hasse sites as rotations;
  - boosts on the clock torus with entropy equal to rapidity;
  - the primitive-cycle Euler product of the machine zeta joined to `Aeon/Production/Zeta`;
  - the sieve as a first-arrival epoch tower;
  - `c` as the fixed point of velocity addition.
- **#62:** join Mathlib's Poincaré recurrence to the aeon's Kac and near-return owners, so that closure at every finite grain is a theorem of the objects.
