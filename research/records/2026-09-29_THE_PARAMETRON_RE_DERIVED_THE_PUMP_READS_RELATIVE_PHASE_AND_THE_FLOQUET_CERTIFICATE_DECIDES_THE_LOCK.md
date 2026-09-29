# The parametron re-derived: the pump reads relative phase, and the Floquet certificate decides the lock

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [proved-derived;
formal-checked] for the derivation (§1–2), [measured] for the receipts (§3–5), each read once at the
pinned commit `ad0281ab` ([pins](2026-09-29_THE_PARAMETRON_RE_DERIVED_PINNED_BEFORE_ITS_RUNS.md));
[agent-inferred] where marked.

**What ran.** The build is `8e094bf7`: `hnn::ring`, Lean `HNN/Floquet` and
`Objects/ParametronLock`, and the guide's §5. Brandon authorized the re-derivation: "please do not
restrict us to clearly partially implemented constructs." The guide's §5 owns the definitions; this
record keeps the derivation's reasons and its measurements.

```sh
cargo run --release -p holonics --example hnn_parametron -- rings
cargo run --release -p holonics --example hnn_parametron -- bank
```

The computational object is the helical pair interaction, with rings as complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches four:
- **the helix**: the pump's clock, `a² s^t` or a modulated schedule, and the winding as the carry;
- **the pair**: coupled locks, and the two crossing cells joined through one ring's pump;
- **faces and placement**: the locked-sheet face, and a residue's phase on the mode of the period's
  factor 4;
- **cell holonomy**: the monodromy of one pump period.

The tube (a passage over many periods, the consumer's reach over a span) and the tower thread (the
growth's enclosure at a dyadic grain) stay attached.

## 1. The derivation

**1.1 The pump is a periodic modulation of the constitution.** [definition] The pump block
`−2p R_ψ`, `R_ψ = [[cos ψ, sin ψ], [sin ψ, −cos ψ]]`, is a reflection across the axis `ψ/2`, scaled.
Its storage `½zᵀ(−2pR_ψ)z = −p Re(z² e^(−iψ))` reads the doubled phase. A pump is one carrier a tick
of its period:
- declared, `a² s^t`, over the order of `s`;
- or modulated by the cells crossing the ring's section, one tick a crossing, with the carrier
  `(a² s^t)·c_t`.

It is an element relation with its power (the switch work `½⟨u, (K_t − K_(t−1))u⟩` is in the
executed balance). It retains nothing, so it is not deposition.

**1.2 The monodromy, its placement and its certificate.** [proved-derived; implemented-exact] The
executed undriven tick is linear in `x = (u, w)`:
`T_t = [[I − h²X_tK_t, 2hX_tC], [−2hX_tK_t, 4X_tC − I]]`, with `X_t` the executed solve (the law's
inverse or the certified chart's exact matrix). One period composes `M_T = T_(T−1) ⋯ T_0`, the
holonomy of the pump's cycle.
- **Placement.** The Cayley map `μ = r(1 + s)/(1 − s)` sends the circle `|μ| = r` to the imaginary
  axis and its outside to the right half-plane. So `q(s) = (1 − s)^n χ(r(1 + s)/(1 − s)) =
  ∏_i ((r − μ_i) + (r + μ_i)s)` places every multiplier exactly by one half-plane count
  (`ratio::polynomial::half_plane_count`, Routh–Hurwitz in its Sturm form). A multiplier at `−r`
  drops `q`'s degree and counts on the circle. This is the ring's own Cayley step read backwards:
  the step sends the stable half-plane into the unit disc (`wave.cayley-resonator`).
- **Certificate.** `G ≻ 0` with `M_TᵀGM_T ⪯ ρ²G` bounds the energy in `G` by `ρ²` a period
  (`HNN/Floquet.floquet_energy_iterate`).
- **Why inertia.** The certificate is two symmetric forms, `G` and `ρ²G − M_TᵀGM_T`, and Sylvester
  inertia decides each exactly.
- **Why any attainment.** The inertia trusts nothing of how `G` was found. The exterior means offered
  is the exact Stein solve `M_TᵀGM_T − ρ²G = −ρ²I`. When every multiplier lies inside `|μ| = ρ` its
  solution is `Σ_k (M_T/ρ)^(kᵀ)(M_T/ρ)^k ≻ 0`, and it is refused when singular (`ρ² = μ_iμ_j`).

**1.3 The bifurcation.** [proved-derived; formal-checked]
- **The standing pump.** Its tick fixes a state exactly when the rate and velocity vanish and
  `Ku = 0` (`standing_fixed_point_iff`). So the multiplier is one exactly where the pumped stiffness
  is singular, which is on the in-phase axis at `k − 2p = 0` (`pumped_inphase_axis`).
- **Below it**, the storage form is itself the certificate at `ρ = 1`
  (`storage_form_certifies_passive`, from `HNN/Ring.ring_tick_port_balance`).
- **The Swing's three kinds** are its sides: a damped turn below, a shear at the edge, a boost past.
- **A rotating pump** switches its stiffness every tick, and the switch work has no sign. So the
  storage form stops certifying, and the monodromy resonates parametrically (§3).

**1.4 The sheets and phase-sensitive amplification.** [proved-derived; formal-checked in the
continuous chart]
- **The axes.** The pumped node stiffness has the in-phase axis `a = e^(iψ/2)` at `k − 2p` and the
  quadrature `ia` at `k + 2p`.
- **Past the bifurcation** the in-phase axis has the rate matrix `[[0, 1], [κ², 0]]`
  (`κ² = (2p − k)/c`). It grows `(1, κ)` at `+κ` and squeezes `(1, −κ)` at `−κ`, and its growing
  amplitude is read by the covector `(κ, 1)`. The quadrature turns, `[[0, 1], [−ω², 0]]² = −ω²I`.
  The Cayley tick keeps each eigen-axis with the multiplier `(2 + hλ)/(2 − hλ)`.
- **The sheet** the executed passage reaches is the sign of the seed's growing coordinate:
  `sign cos(φ_in − ψ/2)` for a seed on the displacement (`hnn::ring::lock`).

[re-derived] **A correction to the phrase "amplifies one phase and squeezes the quadrature".** In
the executed second-order law the in-phase axis boosts: its own phase plane holds the growing and
the squeezed quadratures, and the node plane's quadrature turns. The envelope chart's reading
(in-phase amplified, quadrature squeezed) is the same boost read in a frame rotating with the ring.

**1.5 The relative phase is read by the pump.** [proved-derived; formal-checked]
- **Parity.** A relative phase `Re(z_a z̄_b)` is even under the global half-turn
  `(z_a, z_b) ↦ (−z_a, −z_b)`, and every linear reading is odd. So no linear map followed by a
  strict threshold reads it (`no_linear_threshold_reads_relative_phase`).
- **The correction.** The primary's statement that the locked sheet is "a nonlinear (square-law,
  then threshold) reading of relative phase" holds for the sheet read against the pump, whose phase
  enters the law quadratically. It does not hold between two cells that enter as the seed: that
  reading is linear, then threshold.
- **The pump is the law's only quadratic place.** When the crossing cells modulate the carriers of
  two ticks, the monodromy composes two reflections. Their product is the turn by the carriers'
  relative phase, `R_ψR_χ = Rot(ψ − χ)` with trace `2Re(e^(iψ) e^(−iχ))`
  (`reflection_mul_reflection`, `reflection_pair_trace_carriers`), and it enters the monodromy at
  second order in the pump. This is the **square law**; the bifurcation is the **threshold**.
- **The bank of receiving parametrons at declared pump phases** (member `j`: axis `1`, step `i^j`):
  member `j`'s carriers are `(c_e, i^j c_l)`, which align exactly when `c_e = i^j c_l`. Its two
  ticks are then the standing pump's, and it grows exactly past `p = 1/2`. The misaligned members
  grow only past a strength bracketed in `(361/512, 725/1024]` (the pin's §5). At `p = 5/8` the bank
  locks at one member and certifies the rest silent.

**1.6 The lock is an Ising site.** [definition; proved-derived; formal-checked]
- **One lock.** A two-sheet lock under the bias `a` has the exchange polynomial `Π(a) = 1 + a/K`,
  its partition function read at the resting sheet. Its face `θ = aΠ′/Π = a/(a + K)` is the logistic
  of `ln a − ln K`, and its susceptibility is `a∂_aθ = θ(1 − θ) ≤ 1/4`.
- **`N` locks** have `Π = ∏(1 + a/K_i)`, with zeros exactly at the pivots `−K_i`.
- **Capacity.** The selectivity between two biases, `S = ∏(a₂ + K_i)/(a₁ + K_i)`, is a product of
  cross ratios of the two biases about each pivot and `∞`. Each lies strictly between `1` and
  `a₂/a₁`, so `S` lies strictly between `1` and `(a₂/a₁)^N`. Capacity is the lock count, not the
  coordinate count. The brief's form `(a₂/a₁)^N < S < (a₁/a₂)^N` is the case `a₂ < a₁`, where the
  sharper upper bound is `1`.
- **The carry.** On `|a| = r` the log-derivative `Σ(a + K_i)⁻¹` winds `#{K_i < r}` times (the
  argument principle, proved through Mathlib's circle integrals): as the bias's magnitude passes a
  pivot, one more lock has flipped, and the count is the carry.
- **Coupled locks (Lee–Yang).** Two locks with exchange weight `y` have `Π = a² + 2ya + 1`.
  Uncoupled, `(1 + a)²` has a double pivot on the negative real axis; coupled ferromagnetically
  (`|y| < 1`), both zeros sit on the unit circle off the axis. That is the coupled-sheet parametron.
- [interpretation] Reading a pumped ring's basins under noise as this face at a declared temperature
  is not proved.

**1.7 Modal hearing is dormancy.** [proved-derived; formal-checked] The port coefficient
`c = ⟨s, Mv⟩⟨r, v⟩` vanishes exactly when one coupling does, and a constitutive change can reopen a
silent mode. A bank's silent members are dormant. The modulation that aligns a member's pump reopens
it, and it locks.

**1.8 The consumer equation.** [proved-derived; formal-checked, implemented-exact] The
constitution's certified step reads the gain through a pumped resonator as
`|x_(τ+s)|² ≤ (γ_hi/γ_lo) max_o ρ^(2m_o) (max_t σ_t²)^(s − Tm_o) |x_τ|²`, with
`γ_lo I ⪯ G ⪯ γ_hi I` and `T_tᵀGT_t ⪯ σ_t²G` each certified by inertia at a dyadic grain
(`floquet_tick_product`, `floquet_metric_change`; `Floquet::bound`, `FloquetBound::reach`).
- In the loaded resonator's gain `κ²` (the channel's with `G = 2Y_r`), each term of
  `Σ_j Σ_(τ<T_j) (1 + ω)^(2(T_j − τ − 1))` is multiplied by `reach_r(T_j − τ)`.
- `hnn::constitution` is not edited in this loop, so a step through a pumped resonator stays refused
  (`UncertifiedGain`) until it reads this factor.

## 2. The Lean

`HNN/Floquet`, 23 theorems:
- the certificate: `energy_transport`, `certificate_reading`, `floquet_energy_step`,
  `floquet_energy_iterate`, `floquet_passive`;
- the partial period and the consumer: `floquet_tick_product`, `floquet_metric_change`;
- the pump's axes and the standing bifurcation: `pumped_inphase_axis`, `pumped_quadrature_axis`,
  `standing_fixed_point_iff`, `storage_form_certifies_passive`;
- phase-sensitive amplification: `inphase_growing`, `inphase_squeezed`,
  `inphase_growing_coordinate`, `quadrature_turns`, `cayley_eigen`, `cayley_tick_eigen`;
- the two pumps: `reflection_sq`, `reflection_mul_reflection`, `reflection_pair_trace`,
  `reflection_pair_trace_carriers`;
- the parity: `relativePairing_halfTurn`, `no_linear_threshold_reads_relative_phase`.

`Objects/ParametronLock`, 21 theorems:
- one lock: `exchange_hasDerivAt`, `lockFace_eq_bias_logDeriv`, `lockFace_logistic`,
  `lockFace_hasDerivAt`, `bias_susceptibility`, `susceptibility_le_quarter`,
  `lock_susceptibility_le_quarter`;
- many locks and capacity: `exchangeN_eq_zero_iff`, `selectivity_eq_exchange_ratio`,
  `pivotRatio_between`, `pivotRatio_between'`, `selectivity_lock_count_bound`,
  `selectivity_lock_count_bound'`;
- the carry: `logDeriv_exchangeC`, `pivot_winding_inside`, `pivot_winding_outside`,
  `winding_is_carry`;
- coupled locks: `uncoupled_double_pivot`, `coupled_zeros_leave_the_axis`;
- hearing: `modal_silent_iff`, `dormant_mode_reopens`.

None uses `sorry`, `axiom` or `native_decide`. `bash tools/lean_check.sh Holonics HolonicsResearch`
built 10,248 jobs.

## 3. Acceptance 1, the Floquet certificate on declared rings: holds

Every ring has `C = I`, `D = 0`, `Y = 16` and `h = 1`, and every decision is at the grain `2^(−8)`.
The law and the lattice word (`WordLattice::by_rule(16, 6, 6, 4)`) read the same on every ring.

| Ring | Pump | `p` | Reading (the law and the lattice word) |
|---|---|---|---|
| node | standing | `3/8` | passive, certified at `ρ = 1` |
| node | standing | `1/2` | the edge: 1 multiplier on the unit circle, none outside; certified at `257/256` |
| node | standing | `5/8` | growing: spectral radius in `[413/256, 207/128]` |
| node | quarter turn | `1/16` | passive, `ρ = 1` |
| node | quarter turn | `1/4` | growing: `[117/64, 469/256]` |
| node | half turn | `1` | passive, `ρ = 1` |
| cycle of three | standing | `1/8` | passive, `ρ = 1` |
| cycle of three | standing | `1/4` | the edge: 1 on the circle; certified at `257/256` |
| cycle of three | standing | `3/8` | growing: `[413/256, 207/128]` |
| cycle of three | quarter turn | `1/32` | passive, `ρ = 1` |
| cycle of three | quarter turn | `1/8` | growing: `[333/256, 167/128]` |
| cycle of three | half turn | `1/4` | passive, `ρ = 1` |
| cycle of three | half turn | `3/8` | growing: `[287/256, 9/8]` |

- **13 of 13 rings read as declared**, and the executed balance closed on **448 = 2⁶·7 of 448
  ticks** (8 periods of each ring, on the law and the lattice word).
- **The bifurcation strengths of the rotating pumps**, bracketed by exact bisection, with both ends
  certified:
  - the node's quarter-turn pump: in `(5/32, 163/1024]`, passive at `5/32` and growing in
    `[257/256, 129/128]` at `163/1024`;
  - the cycle's quarter-turn pump: in `(49/512, 101/1024]`, growing in `[33/32, 265/256]` at the
    upper end;
  - the cycle's half-turn pump: in `(65/256, 33/128]`, growing in `(1, 257/256]` at the upper end
    (one multiplier strictly outside the unit circle, none outside `257/256`).
- The node's quarter-turn pump has its bifurcation in `(5/32, 163/1024]`, far below the standing
  bifurcation `1/2`. Its growing multiplier is negative (the owner's test `a_rotating_pump_resonates_below_the_standing_bifurcation`):
  a half-turn with a boost, the subharmonic lock. The node's half-turn pump stays passive at `p = 1`,
  twice its standing bifurcation, because its two perpendicular axes cancel.
- The standing growth `[413/256, 207/128]` is the same on the node and the cycle: the cycle's softest
  mode at `k₀ = 1/2`, pumped at `3/8`, has the node's in-phase stiffness `k − 2p = −1/4` at `5/8`.

## 4. Acceptance 2, the bank on known truth: holds

The bank is one node with four members at `p = 5/8`, steps `i^j`, decided at the grain `2^(−6)`.
The cells are placed on the mode `k = 15` of the ring of period `60 = 3·4·5`.

| Pairs | Truths by class | The bank | Cells out of its pump (reads class 0) | The linear lock's best map | Best constant |
|---|---|---|---|---|---|
| T1, declared (seed `2_026_092_951`) | 521, 535, 502, 490 | **2,048 of 2,048** | 521 | 1,561 = 7·223 (9 sheet patterns) | 535 |
| T2, the order-2 terrain, every `(t − 2, t)` | 2,460, 4,465, 2,478, 2,373 | **11,776 = 2⁹·23 of 11,776** | 2,460 | 9,403 (9 patterns) | 4,465 |
| of which the stations (`t ≥ 40`) | 0, 2,048, 0, 0 | 2,048 of 2,048 | 0 | 2,048 (4 patterns) | 2,048 |
| of which the request's pairs (`t < 40`) | 2,460, 2,417, 2,478, 2,373 | 9,728 = 2⁹·19 of 9,728 | 2,460 | 7,373 = 73·101 (9 patterns) | 2,478 |

- **The bank read every pair's class exactly**: 13,824 = 2⁹·3³ pairs, none left without a class, one
  member locking and three certified silent on every pair. The acceptance holds.
- **Beside it, the order repair's linear readout: 866 of 2,048.** That counts a continuation's
  stations, not the classes of placed pairs, so it is not a like comparison.
- On the stations every truth is class `1` (the terrain's `x_t − x_(t−2) = 1`, with the lag `2` on
  the mode `k = 15` adding a half-turn to the placed pair's relative phase, read from the earlier
  cell). A constant reader passes there, as the pin disclosed.
- **Out of the pump, the bank reads nothing of the cells.** With its members' pumps unmodulated it
  reads class `0` on every pair: 521 of 2,048, the count of class-0 truths.
- **What the linear lock reads.** [agent-inferred, read from its patterns] Its sheets are the sum
  `c_e + c_l` read against the axes `1` and `i`. On the quarter-turn lattice that sum cancels
  exactly in known ways:
  - both sheets are held exactly when `c_e = −c_l` (class 2);
  - exactly one is held when `c_e = c_l` (class 0);
  - neither is held for classes 1 and 3, whose sum `c_l(1 ± i)` lands in a quadrant set by `c_l`.

  So its best fixed map reads classes 0 and 2 exactly and splits 1 from 3 only by chance: on T1,
  `521 + 502` exact plus 538 of the 1,025 pairs of classes 1 and 3. A held sheet is a zero test,
  which is even under the half-turn, so it is not the strict threshold that
  `no_linear_threshold_reads_relative_phase` excludes. What the linear lock cannot read is the
  orientation, class 1 against class 3, and there the pump reads it.

## 5. Time and memory

| Run | Measured | Projected | Peak resident bytes (projected) |
|---|---|---|---|
| `rings` | 12,223 ms | about 60,000 ms | 9,195,520 = 2¹²·5·449 (under 200,000,000) |
| `bank` | 26,908 ms | about 30,000 ms | 14,708,736 = 2¹²·3³·7·19 (under 500,000,000) |

Neither run reached its stop (600,000 ms) or the external bound. Both runs are complete.

**The gates**, on the build `8e094bf7`:
- `cargo check --workspace --all-targets`: clean;
- `cargo test -p holonics --lib`: 936 passed, the nine of `hnn/tests/floquet.rs` among them;
- the GPU suite, alone on the card under the shared lock
  (`cargo test -p holonics-cuda -- --include-ignored --test-threads=1`): 32 passed. The ring's
  phase construction was factored, with its behaviour unchanged.
- `bash tools/lean_check.sh Holonics HolonicsResearch`: 10,248 jobs built.

## 6. What the measurement located [agent-inferred]

- **The square law is the pump's.** The lock read against its seed is linear, then threshold. The
  relative phase of two cells is read only where they enter the pump, and there the bank reads it
  exactly at a strength inside its lock window. The window has exact ends: the standing bifurcation
  `1/2`, and the misaligned members' onset bracketed in `(361/512, 725/1024]`.
- **Two cells, not a passage.** Each cell pumped its own tick (its section crossing), so the bank read
  two placed cells, not the order repair's superposed moment. The passage's reading is the monodromy
  through every crossing cell's pump. At second order in the pump that monodromy carries every pair's
  relative phase weighted by the ring's rotation between them: the passage's spectrum at the ring's
  parametric resonance. It is the next construction in this owner, and it is not built.
- **The rotating pump is a resonator of its own.** The node's quarter-turn pump grows past a
  strength in `(5/32, 163/1024]` of its unit stiffness, and its growing multiplier is negative. The standing pump's bifurcation is not the
  threshold of a rotating pump, and the certificate, not the storage form, decides it.
- **The constitution does not yet read the bound.** The consumer equation is stated and exposed
  (`FloquetBound::reach`). The certified step's refusal through a pumped resonator stands until the
  constitution reads it.

## 7. Owed in #62

- **The rotating pump.** The Hill/Mathieu tongue boundaries of a rotating pump's monodromy, and the
  principal resonance's real multiplier below `−1` (the subharmonic lock), which this record measures
  on the quarter-turn node.
- **Modal hearing's transfer.** The spectral expansion `rᵀ(K − λM)⁻¹Ms = Σ_v c_v/(λ_v − λ)` for
  `M`-orthonormal modes.
- **The bank's arcs.** The monotonicity of a bank member's growth in `cos(Δ − θ_j)`: the arc
  hypothesis under which `N` members cut the circle of relative phase into at most `2N` classes.
- **The carried passage.** The certificate covers the executed charts' linear map. The carried
  passage's deviation from it, the per-tick split bound composed through `ρ`
  (`|x̂_m − M^m x|_G ≤ Σ_k ρ^(m−k) (split)`), is owed.
- **A passage's spectrum.** The monodromy through every crossing cell's pump, read at second order as
  the passage's spectrum at the parametric resonance.
- **The lock's temperature.** The identification of a pumped ring's basins under noise with the
  lock's exchange-polynomial face at a declared temperature (an interpretation).

## 8. The verdict

Both acceptances hold as pinned. The parametron is re-derived from its constitution, in the guide's
§5, Lean (44 theorems) and `hnn::ring`:
- **The Floquet certificate** decides every declared pumped ring exactly, below, at and past its
  bifurcation, on the exact law and the lattice word.
- **The receiving bank** reads the relative phase class of two placed cells exactly on 13,824 of
  13,824 known-truth pairs.
- **The consumer equation** for the constitution's certified step is stated and exposed.
