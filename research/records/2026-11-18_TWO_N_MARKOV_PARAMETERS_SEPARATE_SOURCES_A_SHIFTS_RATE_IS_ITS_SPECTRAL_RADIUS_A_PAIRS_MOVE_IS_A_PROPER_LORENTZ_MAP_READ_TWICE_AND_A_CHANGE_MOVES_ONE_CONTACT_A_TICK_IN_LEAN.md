# Two n Markov parameters separate sources, a shift's rate is its spectral radius, a pair's move is a proper Lorentz map read twice, and a change moves one contact a tick, in Lean

November 18, 22:26 UTC. The third formalization pass of the day, over boxes of #410. Six modules of
`lean/HolonicsResearch`, 265 declarations, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run. The passes before it are
[the first](2026-11-18_THE_THEORYS_CORE_STATED_IN_LEAN_RINGS_CLOSE_AT_THEIR_LCM_AND_CARRIES_AT_THEIR_PRODUCT_IDENTITY_IS_THE_MODES_SHARED_READINGS_AND_A_PROOF_IS_THE_ORBIT_OF_A_FINITE_MAP.md)
and [the second](2026-11-18_A_NUMBER_IS_THE_HOMOLOGY_OF_ITS_PLACES_A_LAW_OF_COMPOSITION_IS_ITS_CHARACTERS_A_SYMBOLS_WORD_OBEYS_KRAFT_AND_A_RETURN_MAPS_NECKLACES_ARE_COUNTED_IN_LEAN.md).

Refs #410, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Foundation/MarkovSeparation` | `MarkovTwoNSuffices`, the statement `Foundation/ReceiverAtlas` held as an unproved `Prop`: two sources of dimension `n` whose responses `C Aᵏ B` agree at the first `2n` times agree at every time, over every field. The general form: a monic `g` that annihilates both generators, with agreement below `deg g`, gives agreement at every time, so dimensions `n` and `n′` are separated by `n + n′` parameters and by `deg μ_A + deg μ_A′`. At every dimension `n ≥ 1` over ℚ a pair of sources agrees at `2n − 1` times and differs at the next, so `2n` is least. | `Foundation/ReceiverAtlas`, its section on the declared-port case | `receipt.separating-atlas` |
| `Aeon/Production/GrowthRate` | For a nonnegative matrix with a positive eigenvector at `λ`, the word count `N_k = 1ᵀMᵏ1` stands between `c·λᵏ` and `C·λᵏ`, so `(1/k) log N_k → log λ`; `Σ N_k zᵏ` converges for `z ≥ 0` if and only if `zλ < 1`; `det(1 − λ⁻¹M) = 0` and `det(1 − zM) ≠ 0` for complex `\|z\|λ < 1`. With no eigenvector: `N_k^(1/k)` tends to the spectral radius (Gelfand's formula), which is `λ` where the eigenvector stands. The golden-mean shift: `N_k = F_(k+3)`, rate `log φ`. | `Aeon/Production/Zeta`'s closing paragraph | `aeon.zeta-perron-growth`, `navigator.zeta`, `fractal.graph-directed-words`, `aeon.golden-shift-growth` (new) |
| `Physics/Spacetime/LorentzCover` | The Hermitian forms of a complex pair are `ℝ⁴` with `det = t² − x² − y² − z²`, and a move `A` acts on them by `X ↦ Aᴴ X A`: the pairing scales by `\|det A\|²`, the map's determinant on `ℝ⁴` is `\|det A\|⁴`, its time-time entry is `½ Σ\|A_ij\|² ≥ \|det A\|`, and the future cone is kept. The map is the identity if and only if `A` is a unit phase, so for determinant one `Λ(A) = Λ(B)` if and only if `A = ±B`. `diag(λ, λ⁻¹)` scales `t + z` by `\|λ\|²` and turns `x + iy` by `λ/λ̄`: the multiplier's modulus is the Doppler ratio `e^η = √((1 + β)/(1 − β))`, `β = tanh η`, and its argument the turn, with `θ + 2π` the move `−A`. | the Einstein record of November 11, §11; `Geometry/Motion` | `lorentz.pair-move-double-cover` (new), `lorentz.pair-hermitian-signature`, `lorentz.doppler-ratio-chart`, `trace.site-classification` |
| `Physics/Thermal/ManyCell` | Many cells joined by symmetric contacts: the flow keeps the total; `Σ v·Lu = −½ Σ g_ij (v_i − v_j)(u_i − u_j)`; a tick's energy falls by at least `τ(1 − τD)` times the summed squared slip where `Σ_j g_ij ≤ D`; rest is equality across every open contact, a constant on joined cells; no new extreme where `τ Σ_j g_ij ≤ 1`; the entropy production is nonnegative and zero only at rest. A chain in detailed balance is this flow in `p/π` with `g_ij = π_i k_ij`, its relative entropy falling at half the production; a heat network with capacities is such a chain; two cells are `Physics/Thermal/Exchange`. | `Physics/Thermal/Exchange`; the contact record of October 28 | `heat.many-cell-contact-flow` (new), `info.contact-kl-diffusion`, `heat.contact-diffusion-holon`, `heat.two-cell-exchange` |
| `Physics/Wave/GraphCone` | On any graph and for any local tick, linear or not: states that read the same within `n` contacts of a cell read the same there after `n` ticks. For a local matrix `(Mᵏ)_ij ≠ 0` only within `k` contacts, and with nonnegative entries positive on the diagonal and on contacts `(Mᵏ)_ij > 0` if and only if `dist(i, j) ≤ k`. Second-order schemes (the wave scheme and any damping) keep data inside the `t`-neighbourhood. The chain of `Physics/Wave/Telegrapher` is the case of a path. | `Physics/Wave/Telegrapher` | `wave.graph-cone` (new), `wave.lattice-cone`, `contact.pass-reach-gap` |
| `HNN/HeldStep` | A level that ticks `n` times on one held arrival: `h_n = λⁿ h + (Σ_(j<n) λʲ) γ u`; the reverse over the ticks sends the mode `conj(∂h_n/∂λ) G`, the gain `conj(G)·∂h_n/∂γ`, the arrival `conj(∂h_n/∂u) G` and the state before `conj(λⁿ) G`; no tick moves nothing; each tick is the passive step, so the bound `K(ρ_max)·M` is kept however long the arrival is held; for `\|λ\| < 1` the held state tends to `γu/(1 − λ)`. | the news-clock record of October 27, §2 and §6.4 | `hnn.held-step-covectors` (new), `tower.packet-input` |

The boxes of #410 these answer, by their opening words: "`MarkovTwoNSuffices`"; "`h = log ρ(M) = limsup (1/n) log
N_n`" (the rate, the radius and the determinant's first zero; the Perron vector's existence is a hypothesis
where it is used); "Many-cell diffusion"; "The light cone on a general graph" (the cone; the continuum limit
is the construction named in §3); "The held step's covectors"; and of "`PSL(2, ℂ) ≅ SO⁺(1, 3)`" the map,
its kernel `±1`, its image inside the proper maps that keep the future cone, and the Doppler reading.

## 2. What the pass corrected

1. **The `2n` bound needed neither the Hankel rank nor the Kalman decomposition.** `Foundation/ReceiverAtlas`
   stated `MarkovTwoNSuffices` as unproved and named those two as what it needs. The product of the two
   characteristic polynomials annihilates both generators, so one division and Cayley–Hamilton give it, and
   the docstrings now say so. The atlas row `receipt.separating-atlas` already read "`2n` parameters
   suffice" at `formal-checked` while Lean held only the bound `n` under a shared characteristic polynomial;
   the row is now true as written. The stronger reading, that two sources with one response have similar
   minimal realizations, does need the Hankel rank and is a separate statement.
2. **The rate needed no Perron–Frobenius theorem.** `Aeon/Production/Zeta` said the equality `h = log ρ(M)`
   needs the Perron vector, "which Mathlib does not carry". For the word count Gelfand's formula gives it
   with no eigenvector, because the entry sum of a nonnegative matrix stands within a factor of a matrix
   norm. The cycle count `tr Mᵏ` has no lower bound at every `k` (a permutation's trace vanishes off its
   period), so for it the upper bound is the whole statement at each `k`.
3. **Passes reach at most `t` contacts.** `contact.pass-reach-gap` said `t` passes "reach exactly `t` hops".
   A local matrix reaches at most `t`, and all of them where its entries are nonnegative and positive on
   the contacts and the diagonal; with signed entries terms can cancel.
4. **The gain enters the arrival's covector conjugated.** The box writes `γ Σ_j G⁽ʲ⁾ = conj(∂h_n/∂(Px)) G`.
   That holds for a real gain, which the tower's is; in general it is `conj(γ) Σ_j G⁽ʲ⁾`
   (`arrival_covector`, `arrival_covector_of_real_gain`).
5. **Two readings both called the Doppler ratio.** `Physics/Spacetime/Boost`'s `k` is the null multiplier
   `e^η`; `Physics/TwoWayField.doppler_ratio` names `(1 + β)/(1 − β) = F/G`, its square. `boostZ_doppler`
   joins them at `F = e^η`, `G = e^(−η)`.
6. **The move's side.** Lean writes a move `Aᴴ X A`, the atlas `A X A*`: the same statement with `A` and `Aᴴ`
   exchanged, but composition reverses, `Λ(AB) = Λ(B)Λ(A)`, and the rows now say which is written.

## 3. What each statement stands on, and the constructions beside it

- **Markov parameters.** The separation is a statement about one linear recurrence shared by two response
  sequences. Its consumer is the declared-port atlas: a receiver that reads `2n` times of a source of
  dimension `n` holds every later time.
- **The growth rate.** The two-sided law takes the positive eigenvector as given; for an irreducible matrix
  its existence is Perron–Frobenius, a fixed point of the map `v ↦ Mv/‖Mv‖` on the simplex. The first zero
  of the transfer determinant is placed at `1/λ` with none inside; that it is a simple pole of the continued
  series is a statement about the eigenvalue's multiplicity.
- **The Lorentz map.** Injectivity modulo `±1` and the image's three properties are proved. That every
  proper map keeping the future cone is such a move is the polar decomposition: a positive Hermitian square
  root carries the time axis to its image (`B = (X + 1)/√(tr X + 2)` for `det X = 1`), and what remains is a
  rotation of space, a half-turn about a bisector followed by a turn about an axis: the construction that
  closes the isomorphism.
- **Many cells.** The energy bound is stated at capacities one and the explicit tick; with capacities the
  same identities hold in the variable `p/π`, which `master_eq_flow` supplies.
- **The cone.** It is proved for any local law; the attained front is for a first-order nonnegative step.
  The continuum limit of the scheme is consistency with the energy stability of `Physics/Wave/Energy` on a
  refining family of grids.
- **The held step.** The partials are slopes of an affine map and a polynomial's derivative, so no analytic
  derivative enters. A gate that moves the mode between the ticks of one arrival is
  `HNN/NewsClock.state_of_moves`' case.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the six modules by name with `Holonics.Foundation.ReceiverAtlas` and
`Holonics.Aeon.Production.Zeta`, the two foundation modules whose docstrings changed, and
`HolonicsResearch.Compression.Landmark.NecklaceIntegrality`, which imports the second:
`Build completed successfully (8782 jobs)`, exit 0, no declaration elaborated with `sorry`. Projected under
10 minutes from the single-file checks (5 to 23 s a module) and the foundation modules' rebuild, deadline 30
minutes, measured 37 s of wall time on four cores; peak resident set not read. The library's aggregator
imports the six modules; the whole research library was not rebuilt.

The check ran on a cloud host at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision, for the reason the first pass's record gives (`agent-inferred`).

Three workers on disjoint owner paths wrote five of the modules (the Markov parameters and the growth
rate; the Lorentz map; the many cells and the cone), and the lead wrote the held step; each file was
re-checked by the lead before the gate, and every `L:` owner added to the atlas was read against its
module's declarations.
