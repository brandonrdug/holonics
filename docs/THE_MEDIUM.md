# The medium: one step, four faces

The front door to the computational modelling library. Everything the repository models, a fluid,
a heat flow, a wave, a clock, a learning tower, moves by one step, and every model is a choice of
four faces on a complex. The definitions are in the
[elementary objects](ELEMENTARY_OBJECTS.md#the-holon-as-one-object); the derivations of the faces
are in the [record of October 29](../research/records/2026-10-29_A_VALUE_IS_A_RADIX_MOVE_THE_FREE_ENERGY_IS_THE_CODE_THAT_FOUNDS_AND_POLARITY_IS_THE_ONE_REVERSIBLE_NEGATION.md).

## The step

```text
ẋ = (J − R + L) Q x + B u
```

`x` is what the medium holds, `Q` how it holds it, `J` how it turns, `L` how it is pumped, `R` how
it rubs, `B` where it is pushed. In Rust this is `PortHolon::medium(J, R, Q, B, active)`, stepped
exactly over ℚ by `ReferenceHolon` with the implicit midpoint, whose energy balance closes with zero
residual (`holon::law`, `holon.midpoint-resistance-balance`). Holons join into a Holarchy by gluing
their ports (`HolonLaw::interconnect`), and a tower restricts one to a coarser scale
(`HolonLaw::restrict`); the joined and the restricted are the same kind of medium.

## The four faces

**Register: what holds.** The storage `Q` and its modes. A mode is a ring that holds a value in its
own radix: a numeral is the move its digits make, `h ↦ Th + m`, and a mode with multiplier `λ` is a
register in radix `λ` (record §1). Shells, clocks, carries and windings are registers read at
their periods.

**Free energy: what it costs.** `½⟨x, Qx⟩` at the receiver's temperature, with its entropy. Read
as a code length it is the two-part code: the data term is what the flux costs, the complexity term
is what the contacts cost to keep. One test on it founds a contact, prunes it, or recharts it, and
a dormant contact costs nothing (record §2; `code.rank-one-founding`).

**Polarity: what orients.** The turn `J`, which does no work, and the pump `L`, which modulates the
constitution. `±1` is the only negation that can be undone; on an odd ring a negation lands on a tie
and re-locking pays for it. A pumped ring is a parametron, whose locks are Ising sheets (record §3;
`holon::parametron`).

**Contact and friction: where force enters and leaves.** The dissipation `R ⪰ 0` and the ports `B`:
diffusion, viscosity, conduction, resistance, slip. The contact that admits a force is the friction
that dissipates it, `1 − |λ|² = (2r/h)|g|²` (fluctuation and dissipation, `wave.cayley-push-einstein`).
A mode carries a push across `L` ticks best when its friction sets `ρ² = L/(L + 1)`, and an octave of
frictions carries every distance (`wave.matched-friction-reach`). Learning is adaptive conductance:
contacts strengthen where flux crosses and fall dormant where none does (`fluid.adaptive-conductance`;
record §4).

## The bridge between continuous and stepped media

The midpoint step is the Cayley chart: a passive rate `iω − r` is a register
`λ = (1 + h(iω − r)/2)/(1 − h(iω − r)/2)` inside the unit disk, and every register inside the disk is
a passive rate (`holon.cayley-isometry`, `wave.cayley-resonator`). So a continuous physical medium
and Athena's tower, whose modes step `h_t = λ h_(t−1) + γ B x_t` with `γ = √(1 − |λ|²)`, are the same
medium in two charts, checked exactly in
`holon::conformance::tests::a_passive_mode_is_a_register_whose_push_is_its_friction`.

## The media in the repository

Each row is one medium; the columns are its four faces. Where a face is absent the medium does not
carry it yet.

| Medium | Register | Free energy | Polarity | Contact and friction | Owner |
|---|---|---|---|---|---|
| heat exchange | internal energies, `Q = diag(1/C)` | entropy `ΔS = Σ C log(U′/U)`, production `σ` | none | `R = κ·` Laplacian, `B = I` | `physics::thermal` (`Contact::holon`); Lean `Physics/Thermal/*` |
| wave, transmission line | charges and fluxes `(CV, LI)`, `Q = diag(1/C, 1/L)` | stored energy, midpoint and staggered | `J = [[0, Dᵀ], [−D, 0]]` | leakage `R = diag(G, 0)`, node sources `B` | `physics::wave` (`WaveChain::holon`); Lean `Physics/Wave/*` |
| fluid | mass cells; Hodge modes `range d ⊕ range δ ⊕ ker Δ` | owed with the time advance (#62) | skew advection, complex Euler, singularity flows | viscous `Φ = 2μ\|Def u\|² + λ(tr G)²` | `physics::fluid`; Lean `Physics/Fluid/*`, `Fluid/NavierStokes*`, `Hodge/*` |
| noisy linear diffusion | stationary covariance `Σ = G⁻¹` | `F(p) − F(q) = k_BT D(p‖q)` | `J`, the housekeeping current | `D = 2k_BT R`: the noise is twice the friction | Lean `Physics/Thermal/LinearDiffusion` (`heat.linear-diffusion-turn-boost`) |
| spacetime | clocks, elapsed as windings and phase | stress–energy `T` | boosts, the Wigner turn | heat flux `j_U = −T·u` | `physics::spacetime`; Lean `Physics/Spacetime/*` |
| information port | levels | `F(p) − F(q) = k_BT D(p‖q)`, the cross-entropy rate | none | the bath cell | `physics::information`; Lean `Physics/Information/*` |
| parametron ring | modes `Kv = ω²Cv` | pump work | pump `−p cos(2θ − ψ)`, locked sheets | the ring's ports | `holon::parametron`, `hnn::ring` |
| pair contact | its Farey lock address | dissipated slip | the Cayley joint chart | `P(u) = ⟨Ju, wDJu⟩ ≥ 0` | `holon::contact`, `hnn::contact` |
| solenoidal cascade | LC modes `ω² = 1/(LC)`, Foster tanks | none | the pump | pair contacts | `physics::solenoidal` |
| Athena's tower | modes `λ = ρe^(iφ)` on octaves of friction | the code, in bits | turned and pumped modes | friction `1 − ρ`, push `γ`, rectifying contacts | `hnn::tower` |
| deposition | `Q` itself changes | `½⟨x⁺, (Q⁺ − Q)x⁺⟩` | the learned `L` | adaptive conductance `Θ′ = Θ + Γ(j, dφ)` | `holon::deposition`; Lean `Objects/Deposition` |

## One law, many names

The same face appears under the names of its media. Read them as one law:

- **Friction.** `⟨f, Rf⟩ ≥ 0` is the heat flow `κ(T₀ − T₁)²`, the leakage `G V̄²`, the viscous
  dissipation `2μ|Def u|²`, the contact's slip `w⟨Ju, DJu⟩` and the tower's `1 − ρ`.
- **Free energy.** `F(p) − F(q) = k_BT D(p‖q)` is the information port's work, the heat bath's free
  energy and the cross-entropy rate's flux; the two-part code is its reading in bits.
- **The noise and the friction.** `D = 2k_BT R` in a continuous diffusion and
  `1 − |λ|² = (2r/h)|g|²` in a stepped one.
- **The pump.** The ring's `K_t`, the parametron's pumped storage, the phase carrier and the time
  boundary's `A ↦ αA + β conj(A)` are one modulation of the constitution.
- **Adaptive conductance.** The leader's breakdown, the deposition law and the slime mould's tubes
  are one law: conductance grows where the flux crosses.

## Building a model

1. Choose the complex: the cells and their incidence (`geometry::complex`).
2. Choose the four faces: `Q`, `J` and `L`, `R`, `B`.
3. Step it with `ReferenceHolon` for the exact reference, or on the card for Athena's tower, whose
   realization is checked against the reference face for face.
4. Read it with receivers at its ports (`receiver::face`); a reading never drives the step.
5. Join media at their ports and restrict them by towers; the result is again a medium.

## Learning, read on the four faces

Deposition is the only change of a constitution (`holon::deposition`). It moves the registers'
frictions toward the distances answers sit from their questions, strengthens contacts where flux
crosses, founds a new contact when the code says it pays, and leaves the rest dormant. A training
pass that writes every coordinate terraforms the whole terrain; a founded contact binds only where
the current crossed (`hnn.sparse-binding`). Another model's weights are terrain like any other
passage material, and enter only through the same founding test (record §6).
