# The moving region's balance: what the Word carries, and what a deforming region adds

**Date:** October 5, 2026. **Refs:** #62, #63, #73, #74. **Grade:** [derived; owners verified on
`c1def677`, the source-opening receipt on `7ab0fdfb` (#377)]. Brandon's question, relayed by Codex
(topic `moving-region-energy`): reconcile mass and energy conservation under coarse graining, dynamic
geometry and observer frames with what the machine actually consumes; the paddle's traction making
vortical waves, the hurricane, the whip's focusing, reflection and lightning; the concern that fixed
representations are balanced while the bounded region moves and unresolved transport is dropped.

Abbreviations: CR `lean/Holonics/Transport/ChangingReceiver.lean`; FRC
`lean/Holonics/Physics/FluidReceiverClosure.lean`; PHE `lean/Holonics/Physics/PartitionedHodgeEnergy.lean`;
MO `lean/Holonics/Geometry/Motion.lean`; FT `lean/Holonics/Geometry/FrameTransport.lean`; CV
`crates/holonics/src/physics/fluid/control_volume.rs`; W `crates/holonics/src/hnn/word.rs`; FND
`docs/plans/HNN_ATHENA_FOUNDATION.md`; TUBE and STEP the two October 4 records (the smooth tube; the
finite-step work).

## 1. The balance

A fixed reference region `U` maps onto the moving region `Ω(τ)` by `X`, with `F = DX`, `J = det F > 0`
and `w = ∂_τX` (`[m s⁻¹]`); `τ` is the receiver's clock. The receiver `q` at grain `ℓ` with lift `R`
splits the state `z = Rqz + z′` (FRC:35–43). Mechanical storage under the constitution's form `Q`
(`[J per state²]`) splits into `ē + e_h + m`, with `m = ⟨Rqz, Qz′⟩` the mixed term (PHE:27). `Q` is not
the spatial metric `g = FᵀF` and not the spacetime metric `η`.

```text
d/dτ∫_Ω ē = −∮ ē(ū−w)·n + ∮ t̄·(ū−w) + ∮ t̄·w                       [W; t̄ = σ̄n in Pa]
          + ∫(ρ̄ f̄·ū + p̄ div ū) − ∫(Φ̄ + ε_h)                       [integrands W m⁻³]
          − d/dτ∫_Ω(e_h + m) − ∮(j_h − (e_h + m)w)·n + ⟨Y, Q_Y q̇z⟩
```

The thermal side, `d/dτ∫ρε = −∮(ρε(u−w) + q)·n − ∫p div u + ∫(Φ̄ + ε_h) + ∫r`; summing both sides,
`Φ` cancels and the total carries no dissipation term. The signed subgrain transfer `Π_ℓ` (backscatter
admitted) cancels between the resolved and subgrain balances.

## 2. Reconciliation

- **One physics in two charts.** In the reference chart the flux is `ĵ = JF⁻¹(j − ρw)` (TUBE §4). In
  Eulerian coefficients, `E = ½xᵀQ(τ)x` with `Q_ij = ∫_Ω(τ) ρ φ_i·φ_j`, so `½xᵀQ̇_geom x = ∮ ē w·n`:
  the moving metric's term is the `w`-part of the relative flux, counted in one chart only (the same
  once-only rule as the admission term `a_j`, FND §3). [Qualified after Codex's review] This holds for
  the domain variation with a fixed Eulerian integrand and basis and the matching energy flux; a
  transported or time-dependent basis, a changing density or a changing coarse-graining keeps its own
  bulk, basis and projection terms (`ChangingReceiver.affine_cell_transport` exposes the bulk time
  derivative as a separate operand). It is not an identity for every geometric metric change.
- **`Ġ` in `Ė = xᵀGBx + ½xᵀĠx + xᵀGf` (MO:920, 941) is four things.** `Ġ_geom`, the region's motion
  above; `Ġ_rechart`, a pure chart change, which cancels exactly (MO:963; keeping the Euclidean form
  instead invents the work `3/2`, STEP §7); `Ġ_dep`, material work at a commit (MO:980, STEP §4);
  `Ġ_pump`, the pump's matrix rate, whose finite-step energy contribution is `½⟨u, (K_t − K_(t−1))u⟩`
  (`hnn/ring.rs:18`): a rate of the form and an energy in `J` are different operands. Holding momentum instead of rate gives
  `−½⟨w′, ΔC w′⟩ − ½⟨δ, Cδ⟩` (`HolonicsResearch/HNN/MoveDirection.lean:580`): the momentum chart's
  Reynolds term with zero incoming momentum.
- **Traction.** `t·u = t·(u − w) + t·w`. The support's work `t·w` is not removed by using the relative
  flux (TUBE).
- **The gain reading** `r_v = vᵀTᵀG₁Tv / vᵀG₀v` (the joint-gain record, #365). On a moving region,
  `r_v > 1` may be transport the region swallowed, not gain: split `ΔG = ΔG_geom + ΔG_dep` before
  reading `r_v` as gain. The gap lens J6 adds that only the boost does work, and nonnormal rates
  amplify transiently.
- **Subgrain.** FRC:89–105 gives the whole hidden feedback `q(S r − B(r,Y) − B(Y,r) − B(r,r))` with the
  chart rate; paired with the resolved `Y` it yields `Π_ℓ`. A cut's mixed term satisfies `m_A = −m_B`
  even where the global `m` is zero (PHE:36–41): this local mixed term is what a moving region's
  unresolved storage must carry.

## 3. Heat, and what is not heat

- **Heat (nonnegative, entering entropy):** `Φ̄` (CV:190–204, `is_dissipative`) and `ε_h` (`ε_h ≥ 0` a constitutive hypothesis until its physical
  dissipation/thermal consumer exists, not a consequence of a signed subgrain transfer); contact and
  resonator dissipation, `resist ≤ 0` (`hnn/propagation.rs:1510–1527`); the thermal port's production
  `W/T` (`physics/thermal/port.rs:72`); the held-momentum sticking loss where `ΔC ⪰ 0` is physical
  accretion (MoveDirection:594).
- **Physical and signed, not heat:** `Π_ℓ`, `p div u`, `t·w`, `ē w·n`, `m`, the pump, the contrast port
  `Π_c`, and `reflected` (emitted, not dissipated; `Holonics/HNN/Ring.lean:582`).
- **Receiver terms:** the chart rate (FRC:249); a noncomoving observer's deformation term
  (`physics/spacetime/source.rs:334–375`); entropy change caused by a moving aperture, which is not
  production (RECEIVER_HOLARCHY).
- **Defects and enclosures, never entropy:** the Word's executed residual (`Holonics/HNN/Word.lean:861`),
  `last`, `loaded_split`, `split`, the resonator's chart and split, and `integration`, each within its
  `bound`.

## 4. Consumers

| Term | Consumer | Status |
|---|---|---|
| `∮(j − ρw)·n` on a moving affine interval | CR:180–208 | formal |
| n-D cofactor/Piola law, `∂_τJ = div(JF⁻¹w)` | CR (TUBE §4, §9) | **owed**; FT marks continuity owed |
| Section flux | FT:276 | formal, pairing only |
| Energy instance `ρ := e`, `j := ēū + q − σ̄ᵀū` | CR:180 | **owed** |
| `t·u` on a fixed cube (`w = 0`) | CV:296–330 | formal |
| `t·w` | — | **owed**: `CellReturn` has no boundary velocity (CV:206–221) |
| `p div u`, `Φ` → heat | CV:217–231 → thermal port:40–59 | formal |
| The control volume's time advance | CV:39–45 | **owed** (#74) |
| The energy pairing of `Π_ℓ` | FRC:221–245 | state law formal; energy theorem **owed** |
| Rate of `m` and `e_h` on a moving cut | PHE | fixed cut only; **owed** |
| `ε_h` → thermal port | thermal port:57 | **owed** |
| `Ġ` split into its four parts | MO:920–947 | **owed** |
| The decoder square at a chart change | STEP §6 | **owed** |
| World-tube integral of the observer current | `source.rs:334` | pointwise; **owed** |
| Cosserat rod energy law | FND §3 | derived, not in Lean |

## 5. What the Word's receipts carry, and what a deforming region adds

On one fixed field, at a fixed hop (W:1113–1120 refuses a hop change) and field-constant admittances:

```text
E_N − E_0 = Σ_words(−L + Π_c + pump + interconnection + residual)
          + Σ_cuts(deposition + ingest + imposed − absorbed − split)
```

with `L ≥ 0`, `ingest = −reflected` (W:1532), `|residual| ≤ bound`, and the source opening's receipt
`E_after − E_before = imposed − absorbed` (#377). `PowerForm` is diagonal in the field's elements, so a
partition by element carries no mixed term. A moving or deforming region adds what the fixed-cut
`ChainedBalance` cannot absorb:

- **M1, per-region port power.** Tick and field balances are field sums only; a region needs its
  boundary contacts' transit port power (`Holonics/HNN/Propagation.lean:391`).
- **M2, membership change** `ΔE_in − ΔE_out` (the discrete `∮ē w·n`): `ReceptionCarry::released`
  (W:607–650) zeroes departing loci and returns their names, not their energy.
- **M3, incoming momentum.** `held_rate` holds `C′w′ = Cw`; material entering with momentum needs
  `+π_in` and `½⟨v_in, ΔC v_in⟩`.
- **M4, `Ġ_geom`.** `PowerForm` reads `Q` only from the constitution and the lift, so geometry change
  would be booked as learning.
- **M5, the support's work `t·w` inside a tick.** Sources impose only at the cut.
- **M6, subgrain storage and `ε_h`.** The Word's remainders are lattice remainders, not subscale physics.
- **M7, exterior admittance.** Not built.
- **M8, dissipation to a thermal port.** Nothing in `hnn` joins one.

**The paddle.** The blade's work `∮t·w` (M5) goes into vortex kinetic energy (a fixed field can
redistribute it), the shed ring's energy leaving the blade's region (M1, M2), entrainment of still water
at conserved impulse (exactly held-momentum deposition with `π_in = 0`, which `deposition` books as
learning, not heat: M8), turbulence (M6) and surface waves leaving (M7). **A real risk:** `Π_c` and the
pump are sign-unconstrained (signed exact rationals with no sign law), so paddle work hidden in them still closes the balance. Only independently computed
port work (FND §3) catches it.

**The whip.** In the material chart the rod is a fixed interval, and the Word suffices once the
rod-to-contact map exists (FND §3); handle power within a tick is M5. The travelling loop
`[s_a(τ), s_b(τ)]` fits CR:180 exactly (`ρ := e`, `j := −(n·v + m·Ω)`); its continuity hypothesis
(CR:191) needs the Cosserat law, not yet in Lean. In the Word the loop needs M1 and M2; the tip's
transfer to air and the crack are M7.

**The others.** The hurricane is a moving frame plus latent storage (M6, condensation its source).
Lightning's `−½(L_t I² + C_t V²)` is `Ġ_geom` (FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS). A moving
mirror adds `t·w` to the two-port balance, which covers a stationary boundary only.

## 6. The invariant, and where the missing terms join

Source to observable: the receipts close `E_N − E_0` over the field's fixed cut exactly when every
term above has its consumer. The missing terms join at: M1–M2 at `ReceptionCarry` and the per-region
port read of `Propagation`; M3–M4 at `PowerForm` (a geometry-rate operand distinct from `Q`'s material
rate); M5 at the word's tick (a support-velocity port); M6 at FRC's energy pairing with its Rust
consumer; M7 at the exterior admittance; M8 at a thermal port joined to `resist` and to the sticking
loss. Each is owed in #62 with its owner.
