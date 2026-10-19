# The receiving ring locks on its standing pump, and its sheets certify on the period the Word executes

October 18, 2026. Step 1a of the revised plan (#73, #63; Lean obligations #62), with the design
review of step 1a (the saturated ring's reach, the acceptance at the listener's face). Grades: the
executed envelope, the drive margin and the tube reach are proved-derived and implemented exact;
the founding constants and the tube's scope are agent-inferred definitions; the live readings are
measured on the exact Word.

## What is built

The receiving ring's resonator (ring 2 of the listener's field) is founded saturated on a standing
pump, with no linear stage, and the listener mounts it (`examples/listener/continuing.rs::mounted`,
`Constitution::with_locking_pump`). Its two sheets are certified on the period the live Word
actually executes: the charted solve and the error-feedback split at the Word's transient lattice,
not the smooth law.

- **The executed envelope** (`holon::parametron::rounding_floor`, `ExecutedSolve`,
  `PeriodicDomain::certify_executed`). The Word's rate is `ω̂ = X̂r + ν` with `|ν|∞ < δ`; its
  velocity `w′ = ω̂` is on the lattice and its displacement split adds `|ν_u|∞ < δ`. With
  `Δ = X̂ − N⁻¹`, `B = [hI; I]`, `bI ⪰ BᵀG_next B` and `γI ⪰ (G_next)_uu`,
  `|F̂ − F|²_G_next ≤ 2bn(‖Δ‖∞ρ + δ)² + 2γnδ²`, where `ρ` bounds `‖r‖∞` over the ball through the
  per-node quartic. The inclusion becomes `η + ε_t + λr ≤ r_next`. No lattice hypothesis is placed
  on the carried state. The error feedback is not odd (ties go upward), so each sheet is certified
  by its own call.
- **The drive margin** (`DomainStep::holds`, `margin`, `response`). A drive enters the rate as
  `r(x,e) = r(x,e₀) + h(e − e₀)`, so the executed map is the exact map at the proposal's drive plus
  `D̂(e − e₀)`, `D̂ = BhX̂`, plus the same envelope term (bounded for every rate). The sheet is held
  for every `|D̂(e − e₀)|_G_next ≤ m_t = r_next − (η + ε_t + λr)`.
- **The locked pair** (`LockedPair`). The two certified balls at the pump period's closing
  boundary, disjoint (`|c⁺ − c⁻| > ε⁺ + ε⁻`), read by exact closed-ball membership
  (`PeriodicLock::contains`). The lock event that reads the pair (one event per change of ball) has
  no caller in the live learner yet, so it joins with the event clock that consumes it (step 1b),
  not with 1a; the tests read ball membership directly.
- **The founding** (`ResonatorOperands::standing_sheet`, `sheet_amplitude`, `executed_lock`).
  [agent-inferred] `d = 1/Y`, loss `r = h(d + 1/Y)`, a Stand pump of strength `p = r/(4h²)` on axis
  `Carrier(0)`, saturation `β = 2p/a²`, so `±a` on every node's in-phase coordinate with `w = 0` is
  an exact fixed point of the saturated period. Metric `G = [[I/h², −Q/(2h)], [−Q/(2h), Q + (I−Q)/4]]`
  with `Q = XC`; `ε = a/200`, `r = ε·min(1, 1/h)/2`, `λ = 24/25`, `s = 1/25`, `η = 0`. The amplitude is
  the least `a = 2^k` (`k` up to the transient exponent) whose two sheets certify. The rounding is the
  least `kδ` whose square reaches the floor.
- **The loaded return's owner** (`ResonatorOperands::reverse`, called by `Word::pull_back`). The
  quartic and saturated return moved from the port into the resonator's operands, read at the
  producing tick's own displacement: `z̄ = hū′ + c·w̄′ − (2/Y)s̄`, `r̄ = X̂ᵀz̄`, `ē = s̄ + hr̄`,
  `ū = ū′ − hH(u_t)r̄`, `w̄ = Cr̄` saturated (`c = 1`) or `−w̄′ + 2Cr̄` quadratic (`c = 2`).

## Measured on the live listener

Field periods `[33, 7, 11]`; ring 2 has 11 nodes (22 realified coordinates); `h = 1`, `Y = 2`, the
transient unit `δ = 1/32768`. Debug build; the mount takes about 4.2 s and one certify call about
0.25 s.

- Both sheets certify at amplitude `a = 4` (`k = 0` fails). Rounding `5/16384`; margin
  `971/10240000`; contraction `24/25`. The smooth law alone refuses the charted solve
  (`executed_lock(None)` is an error), and `Floquet::of` stays refused.
- Started in `B⁺` with zero drive, the live resonator stays in its ball for 16 ticks: at the centre
  every drive is zero and the state is the fixed point; offset by `64δ` the field's returned drive
  exceeds the margin on 14 of 16 ticks and the sheet holds through them.
- The margin holds an in-phase drive of `1/65536` on every node and refuses `1/32768`; one live
  resonator step at the held drive stays in `B⁺`.
- A storage wave against the sheet, through the live Word, 192 ticks: amplitude 6 leaves `B⁺` and
  returns to it (166 unlocked samples, no event); amplitude 8 flips it with one event at tick 99;
  amplitude 16 flips it at tick 118 and rings at the far ball's boundary, leaving and re-entering,
  with no further event.
- Arrivals of `1/8` at the four quarter-turn carriers, from rest, 192 ticks: `(1,0)` and `(0,1)`
  lock `+1` (at ticks 156 and 178), `(−1,0)` and `(0,−1)` lock `−1`. A half turn reflects the sheet.
  With the pump strength set to zero (saturation kept), all four are unlocked.
- On every tick of these runs whose drive the lying sheet's margin held, the next sample lay in the
  same ball. After an arrival, the field's ringing drive (about `10⁻²` per node) exceeds the margin
  (about `10⁻⁴`); the sheet then holds by the dynamics, not by the certificate.
- The return across a pumped live tick (tick 5 of a Word leaving rest under an arrival) pairs
  exactly with the exact difference of the cubic tick map, `Jv = (4D₁ − D₂)/3`. The same return
  read at tick 2's displacement does not pair.
- Every tick's `TickBalance` and `FieldBalance` close. The Stand pump's work is identically zero
  (a standing pump does no work on a period-one cycle); the port work is nonzero.

## The saturated ring's reach

With the pump mounted the certified deposit first refused at the pumped medium's reach
(`Constitution::ring_reaches`), which called `Floquet::of` on every resonator not certified passive:
a saturated period has no linear monodromy. Four listener tests failed on it; they now pass. The
reach of a saturated ring on a one-tick period (no pump, or a standing pump) is now read on a tube
about the rest point its passage stayed nearest (`hnn::ring::{TubeCentre, TubePassage, TubeMetric,
TubeReach}`). A saturated ring on a pump of several phases keeps its linear part's monodromy, as
before; its period's tube is owed (#62).

- **The passage.** The word records, for each saturated ring on a one-tick period, the running
  maximum of the node `ℓ¹` distance of every executed displacement from each rest point of its
  period: the origin, and, where a standing pump stands them, the two sheets `c^±`, the origin then
  being the saddle between them (`Word::tube_passages`). One maximum per centre, never a record of
  ticks. The compare carries it into the deposit's `Reach::passages`.
- **The tube metric** at the nearest centre (`ResonatorOperands::tube_metric`), read once per
  deposit: the tangent `J_c = J(K_φ + H_β(c))` and `J_cᵀGJ_c ⪯ ρ_J²G`, `γ_lo I ⪯ G ⪯ γ_hi I`, the
  variation's reach `aI ⪰ AᵀGA`, the drive's `d̂I ⪰ D̂ᵀGD̂`, each its dyadic bound decided by inertia.
  `G` is the sheet's own metric at every centre. [agent-inferred] The design asks the saddle's
  metric of the exact Stein solve; on 11 complex nodes that is a dense exact system in
  `2n(4n + 1) = 990` unknowns per deposit, which the cost law refuses, and the sheet's metric is
  positive at the saddle as well, so the inertia decision certifies whatever `σ` it gives.
- **The reach on a radius** (`TubeMetric::at`): `δ = 3β(2Uρ̄ + ρ̄²)`, the Young split `s = 2^j`
  minimizing `(1 + s)ρ_J² + (1 + 1/s)aδ²/γ_lo`, `σ` its square-root ceiling at the grain, and one
  inertia decision of `σ²G ⪰ (1 + s)J_cᵀGJ_c + (1 + 1/s)aδ²G/γ_lo`. The ring's reach is
  `(γ_hi/γ_lo)σ^(2t)`; its own gain families stay held.
- **The closure** (`TubeClosure`). The stepped passage must stay in the tube. The drive deviation
  at tick `τ` is bounded by the station gain at `τ + 1`, read with the readout `Y_R/Y_tube`;
  `W_t = σW_(t−1) + Σ_x η_x e_(x,t−1)` and the deviation `2d̂ max_t W_t²/γ_lo` must not exceed the
  slack `(ρ̄ − ρ_c)²`. The receiving map and the standing are skipped. Where it fails, the largest
  family share is halved until it holds.
- **The radius** climbs its dyadic ladder `ρ̄ = 2^(k + rung)` (`2^k` the least dyadic above `ρ_c`)
  while the certified decrease grows (`Constitution::certify_steps`). Declared and candidate step
  sources read rung 0 with the closure recorded, not enforced.

Measured on the live listener (debug build, this container's 4 cores), six delivered cells through
the observed deposit: cells 0 and 1 step nothing; cells 2 to 5 read ring 2 on its saddle tube, with
`ρ_c` from `871/8192` to `18045/32768`, `ρ̄` from `1/4` to `1`, `σ` from `1571/1024` to
`1773/1024`, span 2 and reach from about 29 to 48. The closure holds on every cell and the source
port's certified step is nonzero through the pumped ring. Inside the lock ball the tube contracts:
on the ball's own radius `σ = 31383/32768 ≤ λ = 24/25`. Across the saddle it amplifies:
`σ = 49833/32768`.

With the pump removed (strength zero, the saturation kept) the period's only rest point is the
origin, and the ring is read on its tube there: cells 0 and 1 step nothing; cells 2 to 5 read the
origin's tube with `ρ_J² = 1` at the grain, `ρ_c` from `1701/16384` to `923/4096`, `ρ̄ = 1/4`
(`σ = 519/512`) or `1/2` (`σ = 2157/2048`), and the source port steps. On every cell the deposit's
steps, joint step and reach equal those on the ring declared with no pump at all, the same
saturation and dissipation (`with_the_pump_removed_the_reading_reverts_to_the_unpumped_one`).

## The receiving face separates by sheet

The design's acceptance (c) is `the_receiving_face_separates_by_sheet_and_not_without_the_pump`
(`examples/listener/continuing/lock.rs`, beside the four lock tests). The receiving face is `v_R`,
ring 2's displacement at the anchor the receiver reads, and `Z = R v_R`. At the founding `R = 0`,
so `Z ≡ 0`; the test therefore first learns four cells through the observed deposit, once pumped
and once with the pump removed before the pairing places its ports, and checks that the learned
`R` is nonzero. It then runs four arrivals of `1/8` at the quarter-turn carriers, from rest, for
192 ticks through the live word on that material.

[agent-inferred] Two faces are aligned where `⟨a, b⟩ > 0` and `2⟨a, b⟩² ≥ |a|²|b|²` (within an
eighth of a turn), and four faces separate by sheet where faces of one sheet are pairwise aligned
and faces of opposite sheets pairwise opposed (aligned after a half turn). The face is read at the
station, the tick after the last lock event of the pumped arrivals. The rate `w` is not read: at a
sheet it is at the lattice's noise.

Measured. With the pump the arrivals lock `[+1, +1, −1, −1]`, the last lock event at tick 179, so
the station is tick 180. The signed `cos²` of arrivals 1, 2 and 3 against arrival 0 there, each an
exact enclosure at `2⁻¹⁵`:

| | `v_R` | `Z` |
|---|---|---|
| pumped | `+[31453/32768, 15727/16384]`, `−[8189/8192, 32757/32768]`, `−[31359/32768, 245/256]` | `+[32747/32768, 8187/8192]`, `−[32761/32768, 16381/16384]`, `−[8187/8192, 32749/32768]` |
| pump removed | `+[1353/16384, 2707/32768]`, `−[2097/16384, 4195/32768]`, `+[403/16384, 807/32768]` | `+[16839/32768, 2105/4096]`, `−[28567/32768, 3571/4096]`, `+[28797/32768, 14399/16384]` |

The pumped face separates on both readings; the unpumped one on neither: its `v_R` quarter turns
stay near orthogonal to arrival 0, and its `Z` points arrival 3 with arrival 0. Pumped, the half
turn (arrival 2) is opposed at every tick read. Unpumped it is opposed through tick 96 and not at
the station (`−[2097/16384, 4195/32768]`); [inferred] the unlocked response has decayed toward the
lattice's grain, where the ties-upward rounding is not odd. What the pump adds is that the quarter
turns join a sheet: pumped, arrival 1's `v_R` reads `+[639/16384, 1279/32768]` at tick 12,
`+[4893/8192, 19573/32768]` at tick 24 and `+[29855/32768, 933/1024]` at tick 48. The test asserts
both faces, so the acceptance vanishes with the pump.

## Owed to Lean (#62)

The executed envelope's inclusion, the drive margin's holding, and the quartic and saturated return
pairing. The tube reach adds three: the range Young bound (`J̄ = J_c + AΔL` with every block of
`ΔL` at most `δ` gives `|J̄v|²_G ≤ (1 + s)|J_c v|²_G + (1 + 1/s)aδ²|v|²/γ_lo`), the tube closure
(the stepped passage's deviation bound keeps it inside `ρ̄`), and the absorbing interval of the cubic
tick on the in-phase mode (`u′ = (3/2)u − u³/32 + e` maps `[−8, 8]` into `[−4, 4]` at `e = 0`).
