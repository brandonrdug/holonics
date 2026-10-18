# The receiving ring locks on its standing pump, and its sheets certify on the period the Word executes

October 18, 2026. Step 1a of the revised plan (#73, #63; Lean obligations #62). Grades: the
executed envelope and the drive margin are proved-derived; the founding constants are
agent-inferred definitions; the live readings are measured on the exact Word.

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
- **The lock event** (`LockedPair`, `LockSample`, `LockEvent`). Exact closed-ball membership in
  the two disjoint certified balls at the pump period's closing boundary (a standing pump: every
  tick). One event per change of ball, the first entry from no ball counting; a sample in neither
  ball is reported unlocked, with no event. The type is defined and not consumed by
  `Field::advance_of`; the event clock joins it.
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

## What refuses with the pump mounted

The listener's certified deposit reads the pumped medium's reach (`Constitution::ring_reaches`),
which calls `Floquet::of` on every resonator not certified passive. A saturated period refuses
there ("a nonlinear period needs its executed domain certificate, not a linear Floquet map"), so
every deposit through ring 2 refuses. Four of the listener's other 18 tests fail on it
(`observed_cells_keep_the_retained_pair_faces_before_pending_copies_read`,
`g3_two_sections_keep_the_exact_trunk_and_match_raw_delivery`,
`receipt_series_has_every_stable_field_and_maximum_is_delivered`,
`r6_release_line_precedes_answer_and_survives_its_horizon_refusal`). The missing term is a reach for
a saturated pumped ring: a per-tick tangent factor `J(L)ᵀGJ(L) ⪯ σ²G` over the Hessian range
`0 ⪯ L − K_φ ⪯ 3βU*²` (the same Young form as the certificate), together with a certified bound
`U*` on every state the actual and stepped trajectories visit. No such bound exists without an
absorbing-region certificate (the quartic balance does not bound the executed orbit,
`parametron.quartic-balance-not-stability`).

## Owed to Lean (#62)

The executed envelope's inclusion, the drive margin's holding, and the quartic and saturated return
pairing.
