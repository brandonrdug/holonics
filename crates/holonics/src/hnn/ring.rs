//! **The ring's parametron: its mode tick, its storage form, its pump and sheets, its clock, and its
//! junction's reference change** (campaign 2, Lean `HNN/Ring`).
//!
//! [definition] A ring is a complex parametron: it stores, oscillates and locks. Campaign 1 gave each
//! ring its rotor clock and its element (the Cayley step of the storage wave, `hnn::propagation`);
//! campaign 2 gives it its **mode storage** `Q = diag(K, C)` on the pair `(u, w)` of node flux and
//! node velocity in the ring's realified chart (node `k`'s complex amplitude is `u_(2k) + i u_(2k+1)`),
//! from the ring's [`crate::holon::parametron::Parametron`] (`C = BᵀW_C B`, `K = BᵀW_K B`, each on the
//! real and the imaginary coordinate), a dissipation `D` and its pump. It is a **resonator** at the
//! ring's storage port: at every tick the storage wave `β = b_r` the junction sends into the ring's
//! storage drives it through a port of the ring's storage admittance `Y_r`:
//!
//! ```text
//! pump       K_t = K + ⊕_k −2p [[cos ψ_t, sin ψ_t], [sin ψ_t, −cos ψ_t]]      e^(iψ_t) = a² s^t
//! solve      M_t ω = 2C w + h β − h K_t u ,   M_t = 2C + (h/Y) I + h D + (h²/2) K_t
//! state      u′ = u + h ω ,   w′ = 2ω − w                                  (split on 2^(−L_w)ℤ)
//! balance    E_(K_t)(û′, ŵ′) − E_(K_(t−1))(u, w) = pump + port − dissipation + chart + split
//!            pump = ½⟨u, (K_t − K_(t−1)) u⟩ ,   port = (hY/4)(|β|² − |β − (2/Y)ω|²)
//!            dissipation = h⟨ω, D ω⟩ ,   chart = ⟨ω, M_t ω − r⟩ ,   split = E(û′, ŵ′) − E(u′, w′)
//! bound      |chart + split| ≤ ‖ω‖₁ (δ_t ‖r‖∞ + ‖M_t‖∞ u) + (u/2)(‖C(ŵ′ + w′)‖₁ + ‖K_t(û′ + u′)‖₁)
//! ```
//!
//! [proved-derived; implemented-exact] **The executed solve's bound** ([`ResonatorStep::bound`]).
//! The phase's chart `X̂` carries the certificate every chart of the word carries (the element's
//! and the contact's, `hnn::chart`): `δ_t = ‖1 − M_t X̂‖∞`, zero for the exact inverse. The element
//! reads its chart's image unsplit, so its bound is `‖x̄‖₁ δ ‖operand‖∞`; the resonator carries its
//! solved rate on `2^(−L_w)ℤ` before the state reads it, as the contact carries its `ζ`, so the
//! bound gains the split's term: `M_t ω − r = M_t(ω − X̂ r) − (1 − M_t X̂) r`, and error feedback
//! keeps `|ω − X̂ r|∞ < u = 2^(−L_w)` (the two remainders lie in one half-open cell), hence
//! `|⟨ω, M_t ω − r⟩| ≤ ‖ω‖₁ (δ_t ‖r‖∞ + ‖M_t‖∞ u)` with `‖·‖∞` the largest absolute row sum. The
//! state's split is `E(û′, ŵ′) − E(u′, w′) = ½⟨ŵ′ − w′, C(ŵ′ + w′)⟩ + ½⟨û′ − u′, K_t(û′ + u′)⟩` with
//! each coordinate within `u`, the contact's split bound. Under the exact law both terms and the
//! bound are zero (Lean `HNN/Ring.{loaded_solve_chart_bound, loaded_state_split_bound}`). The
//! chart term no longer absorbs a wrong solve: an executed rate off the certified chart leaves its
//! chart term above the bound, and [`ResonatorStep::closes`],
//! `hnn::word::{FieldBalance, WordBalance}::closes` refuse it.
//!
//! [proved-derived; implemented-exact] **Its laws** (Lean `HNN/Ring`). Closed, lossless and unpumped,
//! the tick keeps its storage form, sign included: `UᵀQU = Q` (`ring_tick_conserves_mode_energy`),
//! and the descriptor form solved here conserves `E_Q` without `C⁻¹`
//! (`ring_descriptor_tick_conserves`). Its operator is positive definite with its port and
//! `C, D, K ⪰ 0` (`ring_cayley_denominator_nonsingular`); a pumped `K_t` may be indefinite, so each
//! pump phase is certified by its signed form `2C + hD + (h²/2) K_t ⪰ 0`, which bounds `⟨v, M_t v⟩`
//! below by `(h/Y)|v|²` (the contact's certificate, `HNN/Contact.contact_boost_solve_or_singular_direction`),
//! and refused otherwise ([`ResonatorMaterial::certify`]). The executed tick closes exactly with
//! every term stated (`ring_tick_executed_energy_balance`, [`ResonatorStep::closes`]). The pump reads
//! the doubled phase: invariant under the half-turn (`pump_half_turn_invariant`) and blind to the two
//! sheets of its axis `a = e^(iφ)`, `ψ = 2φ` (`pump_blind_to_sheets`); a node's **sheet** is its
//! amplitude's side of the axis, the threshold of its in-phase projection, the Ising face of the
//! locked sheets whose threshold is the perceptron (`locked_sheet_receiver_face`,
//! [`sheets`]).
//!
//! [definition; agent-inferred] **The resonator is loaded at the ring storage port.** The junction
//! sends `(b,c)` to the ring element, which returns `e`; the resonator is driven by that carried
//! element output and returns `s′ = e − (2/Y)ω` to the ring's next storage. The return composes the
//! resonator's two-state recurrence before the element and junction transposes. Its port work
//! `P_r = (hY/4)(|e|² − |s′|²)` cancels the field's signed loaded-port term `−P_r`; the remaining
//! split and solve-chart residuals stay explicit. The mode state is word-local and is dropped with
//! the word; the constitution's gains alone may persist through deposition. A ring without a
//! declared resonator retains the earlier element path exactly. All material is read at the
//! producing cut, and the pump selects its predeclared phase within the word:
//!
//! ```text
//! b = 2v − s, c = v − s                 junction Swing
//! e = element(b, c)                    the existing passive/skew/contrast element
//! M_t = 2C + (h/Y)I + hD + (h²/2)K_t
//! M_t ω = 2Cw + h e − hK_t u           the resonator's local solve
//! u′ = u + hω, w′ = 2ω − w
//! s′ = e − (2/Y)ω                      the returned wave reaches the next junction
//!
//! return, with covectors on (s′, u′, w′), the resonator reversed before the element:
//! z̄ = h ū′ + 2w̄′ − (2/Y)s̄′, r̄ = X_tᵀ z̄
//! ē = s̄′ + h r̄, ū = ū′ − hK_tᵀr̄, w̄ = −w̄′ + 2Cᵀr̄
//! material variation = ⟨r̄, 2δC(w−ω) − hδDω − hδK_t(u+hω/2)⟩
//! ```
//!
//! The field's wave-energy change across `e → s′` is the negative of the resonator's port work;
//! their sum closes with pump, dissipation, chart and split terms. The executed element output is
//! carried before it drives the resonator. A carried returned wave has a separate remainder and
//! wave-energy split residual in the field identity; the resonator's own state-energy split keeps
//! its meaning. The source-opening remainder stays with the element's error-feedback stream, and
//! the inserted returned-wave stream starts at zero remainder: the declared composition of the two
//! lattice charts, with every remaining and released term counted, not a uniqueness claim about
//! chart choice. `X_t` is the solve actually executed: the exact inverse law and the declared chart
//! pullback keep their separate scopes, and a rounding is not differentiated as a smooth map.
//! Reached material covectors enter the current deposition consumer and change a later word.
//!
//! [definition; agent-inferred] **The declared material family.** Each loaded ring carries four
//! real scalar amplitudes on its locus lattice: `C = g_C² C₀`, `K = g_K² K₀`, `D = g_D² D₀` and the
//! pump strength `p = g_P² p₀`. The bases, pump axis and pump step are immutable declaration
//! operands. The gain covectors contract the material variation with `2g` times its base, which
//! keeps `C, D` positive semidefinite and the signed stiffness base. A gain never reaches zero by
//! deposition: a step whose carried gain would be `≤ 0` carries it to `⌊(q + 1)/2⌋ 2^(−L)` for
//! `g = q 2^(−L)` (`g/2` for even `q`, toward `g` for odd `q`, holding at `q = 1`; Lean
//! `HNN/Ring.gain_backtrack_midpoint`), and the deposit receipt names each substitution
//! (`DepositReading::backtracks`); releasing a family belongs to campaign 3's collapse law. The gain
//! lattice follows the lattice rule with the ring's realified width as its fan-in
//! (`field::lattice_exponent`). Deposition re-certifies every pump phase before atomic publication
//! and refuses a failing candidate. This is the admitted learning family, not a claim of arbitrary
//! matrix or clock learning; the retained gains, their remainders and statistics are counted in the
//! constitution, and the next word reads them. [historical] The source: campaign 2's resonator
//! received the junction wave but returned none, and no comparison covector reached its material
//! (September 26; its receipt, the fixed source-ring family losing to the default field, is in
//! `research/records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md`).
//!
//! [definition; agent-inferred] **The pump's phases are finite.** The pump carrier advances by a
//! declared rational rotation per tick; the only rational rotations of finite order in the plane are
//! the quarter turns, so the pump's step is one of them ([`PumpStep`]) and a word visits at most four
//! pump phases, each with its own operator and chart. A pump of infinite order would give each tick
//! its own operator; it is not declared.
//!
//! [proved-derived; implemented-exact] **The clock.** The ring's rotor steps `1/d` of a turn per
//! micro-step, its clock the navigator's (`hnn::field::Ring::clock_at`); over a passage of cells its
//! arrivals on its section (the lift's multiples of `d`) are its epoch ticks, `(r + N)/d` of them
//! from residue `r` after `N` micro-steps (`ring_crossings_are_epoch_ticks`, the owner
//! [`crate::holon::parametron::ring_crossings`]). They are read by the aeon owner: the epochs of the
//! passage's aeon at the ring section (`aeon::epochs` at `aeon::ClockLift::ring_section`, read at
//! the aeon's boundary by `hnn::retention::aeon_readings`), and cell by cell they are the carries
//! the ring sends down the carry chain (`hnn::field::Field::selective_step`). [agent-inferred, U5]
//! The walk that counted them micro-step by micro-step here (`RingClock`, at `e5eb7304`) duplicated
//! that owner and had no library consumer; it is retired.
//!
//! [proved-derived; implemented-exact] **The pump's period is a cycle** ([`PumpDeclaration::clock`],
//! [`PumpDeclaration::period`]). The pump's clock is one circle of the step's order; the pump phase
//! at word tick `t` is its torus point, the carrier there is `a² s^t`, and the aeon of `t` ticks is an
//! `aeon::Cycle` exactly when the order divides `t`, exactly when `s^t = 1` (Lean
//! `pump_period_is_cycle`). The card reads the same torus point as `t mod order`.
//!
//! [definition; re-derived September 29] **The parametron re-derived** (`docs/ELEMENTARY_OBJECTS.md`
//! §5; the [record](../../../../research/records/2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md);
//! Lean `HNN/Floquet`, `Objects/ParametronLock`). **The pump is a periodic modulation of the
//! constitution** ([`PumpSchedule`]): one carrier a tick of its period, each adding the reflection
//! block `−2p R_(ψ_t)` to every node's stiffness. A declared pump is the schedule `a² s^t`
//! ([`PumpSchedule::declared`]); the cells crossing the ring's section modulate it, one tick a
//! crossing, its carrier `(a² s^t)·c_t` ([`PumpSchedule::modulated`], run by
//! [`ResonatorOperands::scheduled`] on an unpumped material, each tick certified by its signed form
//! as a declared pump's phase is).
//!
//! [proved-derived; implemented-exact] **The Floquet monodromy** ([`Floquet`]). The executed tick is
//! linear in the state `x = (u, w)`, and one period composes the transport around the pump's cycle:
//!
//! ```text
//! tick         x′ = T_t x,  T_t = [[I − h²X_tK_t, 2hX_tC], [−2hX_tK_t, 4X_tC − I]]     X_t the executed solve
//! monodromy    M_T = T_(T−1) ⋯ T_0                                                      the law's inverse, or the chart's matrix
//! placement    q(s) = (1 − s)^n χ(r(1 + s)/(1 − s)) = ∏_i ((r − μ_i) + (r + μ_i)s)      #{|μ| > r} = right(q), #{|μ| = r} = axis(q) + n − deg q
//! certificate  G ≻ 0 and ρ²G − M_TᵀGM_T ⪰ 0, each by inertia  ⇒  E_G(M_T^m x) ≤ ρ^(2m) E_G(x)
//! ```
//!
//! `G` is attained by any exterior means and certified inside exactly ([`Floquet::certify`] trusts
//! nothing of how it was attained); the exterior means offered is the exact Stein solve
//! `M_TᵀGM_T − ρ²G = −ρ²I` ([`attain_metric`]), whose solution is `Σ_k (M_T/ρ)^(kᵀ)(M_T/ρ)^k ≻ 0`
//! when every multiplier lies inside `|μ| = ρ`. [`Floquet::decide`] reads the placement at the unit
//! circle: **passive** (all inside; certified at `ρ = 1`), **the edge** (none outside, some on it; a
//! turn or a shear, certified at `ρ = 1 + 2^(−g)`), or **growing** (one outside; the spectral radius
//! enclosed at the grain by bisection on the placement, `lower` reached by a multiplier, certified
//! at `ρ = upper`). A standing pump's multiplier is one exactly where its stiffness is singular
//! (Lean `standing_fixed_point_iff`), on the in-phase axis at `k − 2p = 0`; below it the storage form
//! is itself a certificate at `ρ = 1` (`storage_form_certifies_passive`).
//!
//! [proved-derived; implemented-exact] **The consumer** ([`Floquet::bound`], [`FloquetBound::reach`];
//! Lean `HNN/Floquet.{floquet_tick_product, floquet_metric_change}`). The constitution's certified
//! step reads the gain through a pumped resonator as
//!
//! ```text
//! |x_(τ+s)|² ≤ (γ_hi/γ_lo) · max_(0 ≤ o < T) ρ^(2m_o) (max_t σ_t²)^(s − T m_o) · |x_τ|²,   m_o = ⌊(s − o)/T⌋
//! γ_lo I ⪯ G ⪯ γ_hi I,   T_tᵀGT_t ⪯ σ_t²G        each by inertia at a dyadic grain
//! ```
//!
//! where the passive medium's factor is one. The consumer equation: in the gain `κ²` of a loaded
//! resonator at ring `r` (`hnn::constitution`'s header, "resonator r", the channel's with
//! `G = 2Y_r`), each term of `Σ_j Σ_(τ < T_j) (1 + ω)^(2(T_j − τ − 1))` is multiplied by
//! `reach_r(T_j − τ)`, the resonator's certified factor over the ticks its state carries the
//! difference, and every other locus's gain through that ring by the same factor. Until the
//! constitution reads it, a linear step through a pumped resonator stays refused
//! (`HnnError::UncertifiedGain`).
//!
//! [proved-derived; implemented-exact] **Phase-sensitive amplification, read at the locked sheet**
//! ([`lock`]; Lean `pumped_inphase_axis`, `inphase_growing`, `inphase_squeezed`,
//! `inphase_growing_coordinate`, `cayley_tick_eigen`). Past the bifurcation the in-phase axis
//! `a = e^(iψ/2)` boosts (its phase plane holds the growing and the squeezed quadratures) and the
//! quadrature turns; the sheet the executed passage reaches is the sign of the seed's growing
//! coordinate, `sign cos(φ_in − ψ/2)` for a seed on the displacement. It is linear, then threshold:
//! odd under the half-turn of the seed.
//!
//! [proved-derived; implemented-exact] **The relative phase is read by the pump**
//! ([`ReceivingBank`], [`BankReading`]; Lean `reflection_mul_reflection`,
//! `reflection_pair_trace_carriers`, `no_linear_threshold_reads_relative_phase`). A relative phase
//! `Re(z_a z̄_b)` is even under the half-turn, so no linear reading followed by a threshold reads it.
//! The law's quadratic place is the pump: two ticks whose carriers the crossing cells modulate
//! compose two reflections, whose product is the turn by the cells' relative phase (trace
//! `2Re(c_a c̄_b)`), the square law; the bifurcation is the threshold. A bank of receiving parametrons
//! at declared pump phases (member `j`: axis `1`, step `i^j`, carriers `(c_e, i^j c_l)`) locks at the
//! member whose declared phase aligns the two cells, and every other member is certified silent; its
//! class is that member. [agent-inferred] The bank's strength sits in its lock window: the aligned
//! member grows exactly past the standing bifurcation (its two ticks are the standing pump's), and
//! the nearest misaligned member only past a strength bracketed in development in
//! `(361/512, 725/1024]`; the declared `p = 5/8` lies between.
//!
//! [proved-derived; implemented-exact, September 29] **The passage's monodromy: the bank reads a
//! superposed passage** ([`ReceivingBank::read_turn`], [`turn`], [`Growth`]; Lean
//! `HNN/FloquetPassage`; the [record](../../../../research/records/2026-09-29_THE_BANK_READS_A_SUPERPOSED_PASSAGE_THE_LOCKS_CONTINUE_A_SPECTRAL_LINE_AND_THE_ORDER_TWO_TERRAIN_STAYS_AT_THE_MARGINAL.md)).
//! The receiving ring holds the passage superposed: every datum placed at its residue through the
//! source port, `Σ_k P^(τ − c_k) E u_k` (`hnn::moment`). As the ring turns on, its nodes cross the
//! section one a tick, node `d − 1 − t` at tick `t` (the passage in its own time order around the
//! cycle of the turn), and each crossing pumps the receiving parametron: the reflection at the
//! node's placed amplitude `z`, scaled by `|z|` ([`PumpSchedule::placed`]). The passage's monodromy
//! is the ordered product of those pumped ticks over one turn:
//!
//! ```text
//! crossing     K_t = K − 2p R(a² s^t z_t),  R(c) = [[Re c, Im c], [Im c, −Re c]]      each tick certified by its signed form
//! monodromy    M = T_(d−1) ⋯ T_0 = N/Δ                                              on integers: T_t = N_t/L_t, Δ = ∏ L_t
//! growth       lower ≤ ρ(M) < upper,  upper − lower ≤ upper·2^(−g)                    Schur–Cohn on det(Δμ − N)
//! second order R_u Rot_v R_w = Rot(u v̄ w̄);  2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ w|² − Σ |w|²   (the kicked chart)
//! ```
//!
//! - **What the growth reads.** In the kicked chart two crossings separated by the ring's transport
//!   compose to the turn by their relative phase less the transport (Lean
//!   `reflection_transport_reflection_carriers`), and one crossing more pairs the new crossing with
//!   every earlier one (`kick_coeff_two`): over the whole passage the monodromy's second order is
//!   `Σ_(t<n) Σ_(s<t) Rot(v^(n−t) v̄^(t−s) v^s u_t ū_s)` (`passage_coeff_two`), the passage's relative
//!   phases read at the ring's parametric resonance, and at a whole turn its trace is the passage's
//!   power spectrum there (`pair_sum_power_spectrum`). The square law is the pump's; the bifurcation
//!   is the threshold. The executed law's own second order is owed (#62).
//! - **The bank's members.** The declared bank's member `j` (axis `1`, step `i^j`) reads the passage
//!   modulated by `i^(jt)`: its frequency shifted by `j` quarter turns. A member reads a turn only
//!   when its pump's period divides the turn, so the turn is a cycle of its clock and the product
//!   is a Floquet monodromy. The bank's joint monodromy is the members' block sum, and its growth
//!   the largest member's.
//! - **Known truth: a spectral line** (the owner's tests). On a line of unit cells stepping one
//!   quarter-turn class `j` a crossing, every member's reading depends only on `m − j (mod 4)`: the
//!   line's own member (a standing pump) grows, the two quarter-turn neighbours (nearest the node's
//!   parametric resonance) grow more, and the half-turn partner is certified silent, so the lock
//!   pattern names the line's class. With a crossing left open, the candidate completing the line
//!   reads the joint growth strictly above every other: the lock's flip continues the line.
//! - **The growth's realization** [definition; agent-inferred]. Every enclosure is decided on
//!   integers: the monodromy as `N/Δ`, its characteristic polynomial by the Faddeev–LeVerrier
//!   recurrence with exact divisions, the multipliers of `M` as the roots of `det(Δμ − N)`, each
//!   bisection step the Schur–Cohn test `ρ < r` (every root strictly inside the disc). The bracket is
//!   attained on the polynomial shifted to `ATTAINMENT_BITS` bits and certified by two exact tests;
//!   the turn's certificate attains its metric by the exact Stein solve of the monodromy rounded at
//!   the same bits and certifies it by inertia on the exact monodromy. What is attained is trusted
//!   nowhere.
//!
//! [historical; September 30, batch H] **The bank's face is retired from Rust** (source at
//! [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/ring.rs):
//! `ReceivingBank::{transport, chart}`, `BankChart`, `Resonance`). It read the lock at a declared
//! temperature, candidate `x` weighing the bank's second-order reading
//! `A = Σ_m p_m² (|W⁺_m|² + |W⁻_m|²)` of its passage (`W^±_m = Σ_t a_m² s_m^t ζ^(±t) z_t`,
//! `ζ = v̄²`, `v` the node's lossless Cayley multiplier `(2 + ihω)/(2 − ihω)`) and the station's
//! face `θ_x = A(x)/Σ_y A(y)`; its descent direction met the executed decision's at cosine `39/512`
//! (the [diagnosis](../../../../research/records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §3), and the release's own comparison replaced it (`hnn::executed`, the covector below). Its
//! laws stay in Lean `HNN/BankFace` (`member_amplitude_ray`, `resonance_gain`, `flip_reflection`,
//! `flip_rotation`, `sideband_pair_sum`), its readings on the spectral line in the
//! [bank's learning path record](../../../../research/records/2026-09-29_THE_BANKS_LEARNING_PATH_PINNED_BEFORE_ITS_RUNS.md).
//! What stays here: the executed growth reads a passage and its conjugate alike (Lean
//! `flip_reflection`; the owner's test `the_executed_turn_reads_a_passage_and_its_conjugate_alike`:
//! member `m` on `z` and member `−m` on `z̄` have one characteristic polynomial, where the kicked
//! chart's traces differ). The bank's members are declared (the parametron record's bank), not loci
//! of the constitution: a pumped ring's own gains are held by the certified step's law until a
//! certificate covers the monodromy along their ray (`hnn::constitution`, "The pumped medium's
//! reach"; #62).
//!
//! [proved-derived; implemented-exact, September 30] **The executed growth's covector**
//! ([`ReceivingBank::read_turn_covector`], [`dominant_multiplier`], [`MemberCovector`];
//! `hnn::executed`; Lean `HNN/ExecutedComparison`; the
//! [diagnosis record](../../../../research/records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §5). The release decides by the largest member's executed growth, so its learning signal is the
//! derivative of `log ρ(M)` through the executed tick and its solve, where it exists:
//!
//! ```text
//! variation    ΔM = Σ_t T_(>t) ΔT_t T_(<t),  ΔT_t through ΔX_t = −X_t ΔM_t X_t, ΔM_t = (h²/2)ΔK_t
//! simple root  D log|μ|[ΔM] = Re(ℓᵀ ΔM r / (μ ℓᵀ r)),   r, ℓᵀ a column and a row of adj(μ − M)
//! per crossing ∂ log|μ| / ∂ Re z_t = Re(b_tᵀ ∂T_t f_t / (μ ℓᵀr)) = Re(a_tᵀ ∂K_t r_t / (μ ℓᵀr))
//! ```
//!
//! - **Where it is valid.** Only at a certified simple dominant multiplier: its disk passes the
//!   Krawczyk test (`ratio::disk`; exactly one simple root inside), is real or disjoint from its
//!   conjugate (a conjugate pair moves its modulus together), and every other multiplier lies
//!   strictly inside a circle below its modulus (every root isolated in disjoint disks, or the
//!   exact placement count). Otherwise the member's covector is a typed refusal
//!   ([`CovectorRefusal`]): a collision (a multiple root, or roots too close for the precision), a
//!   tie in modulus, or a defective eigen-pairing. Nothing is guessed at a refusal.
//! - **The joint's active branches.** `max_m ρ_m` has a derivative only where one member attains
//!   it; every member whose enclosure reaches the joint's lower end is returned as a branch, and the
//!   max comparison's consumer reads them all (`hnn::executed`).
//! - **Exact, then enclosed.** The monodromy, its variation and its characteristic polynomial are
//!   exact; the multiplier and the eigenvectors are algebraic and enclosed in disks with exact dyadic
//!   endpoints, so every covector entry is an enclosure. Three routes of one number agree on every
//!   tested turn: the covector paired with a move, the eigen-pairing on the exact variation, and the
//!   trace `tr(adj(μ − M)ΔM)/(μχ′(μ))`; the forward (dual) and reverse (prefix–suffix) variations are
//!   equal exactly ([`ReceivingBank::turn_variation`], [`ReceivingBank::directional_routes`]).
//! - [agent-inferred] The operands are the turn's own and transient; nothing is retained.
//!
//! [proved-derived; implemented-exact] **The reference change at a junction port**
//! (`port_scattering`, the tests' reading). A wave arriving at port `p` of a junction meets the rest of the junction as
//! one reference admittance `G_rest = W − G_p`: it reflects `Γ = (G_p − G_rest)/(G_p + G_rest)` and
//! transmits the power fraction `T = 4G_p G_rest/(G_p + G_rest)²` into the other ports, `Γ² + T = 1`
//! (`two_port_reference_balance`); the executed Swing returns exactly `Γ` and `1 + Γ`.
//!
//! | Lean `HNN/Ring` | Rust |
//! |---|---|
//! | `cayley_preserves_form`, `ring_generator_qSkew`, `ring_tick_conserves_mode_energy`, `ring_descriptor_tick_conserves` | [`ResonatorOperands::step`] (closed and lossless in the tests) |
//! | `ring_cayley_denominator_nonsingular`, `ring_harmonic_mode_singular` | [`ResonatorMaterial::certify`] |
//! | `ring_tick_port_balance`, `ring_tick_executed_energy_balance` | [`ResonatorStep`], [`ResonatorStep::closes`] |
//! | `loaded_word_stage_balance`, `loaded_tick_executed_interconnection_balance` | [`ResonatorOperands::step`], `hnn::word::{FieldBalance, WordBalance}` |
//! | `loaded_tick_adjoint_pairing`, `loaded_material_rate_tangent`, `loaded_tick_material_variation` | [`ResonatorOperands::solve_transpose`], `hnn::port::Word::pull_back`, `hnn::reference::compose` |
//! | `loaded_gain_family_increment`, `loaded_gains_preserve_storage_dissipation`, `ring_material_commit_work` | [`ResonatorMaterial::with_gains`], `hnn::constitution::Constitution::deposited`, `hnn::word::PowerForm::deposition_work` |
//! | `two_port_reference_balance` | `port_scattering`, `PortScattering` (the tests' readings of the executed Swing) |
//! | `ring_crossings_are_epoch_ticks` | `aeon::epochs` at `aeon::ClockLift::ring_section`, read by `hnn::retention::aeon_readings` |
//! | `pump_period_is_cycle` | [`PumpDeclaration::clock`], [`PumpDeclaration::phase_at`], [`PumpDeclaration::period`], [`ResonatorOperands::phase_at`] |
//! | `pump_half_turn_invariant`, `pump_blind_to_sheets`, `locked_sheet_receiver_face` | [`PumpDeclaration`], [`sheets`] |
//! | `loaded_solve_chart_bound`, `loaded_state_split_bound` (with `abs_mulVec_le_rowNorm`, `abs_dot_le_l1`) | [`ResonatorStep::bound`], [`ResonatorStep::closes`] |
//! | `gain_backtrack_midpoint` | `hnn::constitution::GainBacktrack`, [`ResonatorMaterial::with_gains`] |
//! | `HNN/Floquet.{energy_transport, certificate_reading, floquet_energy_step, floquet_energy_iterate, floquet_passive}` | [`Floquet::certify`], `FloquetCertificate::energy_factor` (the tests') |
//! | `HNN/Floquet.{floquet_tick_product, floquet_metric_change}` (the consumer equation) | [`Floquet::bound`], [`FloquetBound::reach`] |
//! | `HNN/Floquet.{standing_fixed_point_iff, storage_form_certifies_passive, pumped_inphase_axis, pumped_quadrature_axis}` | [`Floquet::decide`], [`Floquet::placement`] |
//! | `HNN/Floquet.{inphase_growing, inphase_squeezed, inphase_growing_coordinate, quadrature_turns, cayley_eigen, cayley_tick_eigen}` | [`lock`], [`LockedSheets`] |
//! | `HNN/Floquet.{reflection_sq, reflection_mul_reflection, reflection_pair_trace, reflection_pair_trace_carriers, relativePairing_halfTurn, no_linear_threshold_reads_relative_phase}` | [`PumpSchedule::modulated`], [`ReceivingBank::read`], [`BankReading::class`] |
//! | `Objects/ParametronLock` (the lock's exchange polynomial, capacity as lock count, the winding as the carry, coupled locks, modal hearing) | the guide's §5; no Rust consumer beyond the bank's lock pattern |
//! | `HNN/FloquetPassage.{reflection_mul_rotation, rotation_mul_reflection, reflection_transport_reflection, reflection_transport_reflection_carriers, rotation_trace_carrier, kick_coeff_zero, kick_coeff_one, kick_coeff_two, passage_coeff_zero, passage_coeff_one, passage_coeff_two, pair_sum_power_spectrum}` (the passage's monodromy at second order, the kicked chart) | [`PumpSchedule::placed`], [`ReceivingBank::read_turn`], [`turn`] |
//! | `Objects/ParametronLock.lockFace_logistic` (`θ = a/(a + K) > ½ ⇔ a > K`) | [`Growth::exceeds`] (the lock's flip on exact enclosures), `hnn::prediction::generate_by_bank` |
//! | `HNN/BankFace.flip_reflection` (the executed turn reads a passage and its conjugate alike) | [`ReceivingBank::read_turn`] (the owner's test); the face's other laws have no Rust consumer since batch H |
//! | `HNN/ExecutedComparison.{product_deriv, simple_root_deriv, log_modulus_deriv}` (the executed growth's covector) | [`ReceivingBank::read_turn_covector`], [`ReceivingBank::turn_variation`], [`ReceivingBank::directional_routes`], [`dominant_multiplier`] |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::aeon::{ClockLift, Cycle};
use crate::hnn::HnnError;
use crate::hnn::chart::{ChartKey, ChartReading, ChartWords, WordLattice, carry, refine};
use crate::hnn::constitution::Lattice;
use crate::hnn::contact::symmetric;
use crate::holon::parametron::{Carrier, Parametron, threshold_sheet};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::{Inertia, inertia};
use crate::ratio::gaussian::GaussianRat;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::disk::{Disk, DyadicDisk, attained_roots, isolate, quotient, root_upper};
use crate::ratio::linear::vector::{add, common_denominator, dot, scale, sub};
use crate::ratio::polynomial::{RationalPolynomial, half_plane_count};
use crate::ratio::{Rat, integer};

// -------------------------------------------------------------------------------------------
// the pump

/// [definition] **The pump's step per tick**: a quarter-turn power, the rational rotations of finite
/// order (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PumpStep {
    /// The pump stands.
    Stand,
    /// A quarter turn per tick.
    Quarter,
    /// A half turn per tick.
    Half,
    /// Three quarter turns per tick.
    ThreeQuarters,
}

impl PumpStep {
    /// The pump phases a word visits: the step's order.
    pub fn order(self) -> usize {
        match self {
            Self::Stand => 1,
            Self::Half => 2,
            Self::Quarter | Self::ThreeQuarters => 4,
        }
    }

    fn quarters(self) -> u64 {
        match self {
            Self::Stand => 0,
            Self::Quarter => 1,
            Self::Half => 2,
            Self::ThreeQuarters => 3,
        }
    }
}

/// `(a + ib)(c + id)` on unit carriers.
fn compose(first: &Carrier, second: &Carrier) -> Carrier {
    Carrier::new(
        first.cos() * second.cos() - first.sin() * second.sin(),
        first.cos() * second.sin() + first.sin() * second.cos(),
    )
    .expect("the product of two unit carriers is a unit carrier")
}

/// The quarter turn `i^k`.
fn quarter_turn(k: u64) -> Carrier {
    let (cos, sin) = match k % 4 {
        0 => (1, 0),
        1 => (0, 1),
        2 => (-1, 0),
        _ => (0, -1),
    };
    Carrier::new(integer(cos), integer(sin)).expect("a quarter turn is a unit carrier")
}

/// [definition] **A ring's pump**: its strength `p ≥ 0`, its locking axis `a = e^(iφ)` (a rational
/// point of the circle, whose sheets are `φ` and `φ + π`), and its step per tick. Its carrier at tick
/// `t` is `e^(iψ_t) = a² s^t`: at `t = 0` the pump sits at twice its axis (`pump_blind_to_sheets`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpDeclaration {
    strength: Rat,
    axis: Carrier,
    step: PumpStep,
}

impl PumpDeclaration {
    pub fn new(strength: Rat, axis: Carrier, step: PumpStep) -> Result<Self, HnnError> {
        if strength.is_negative() {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a pump's strength is nonnegative",
            });
        }
        Ok(Self {
            strength,
            axis,
            step,
        })
    }

    pub fn strength(&self) -> &Rat {
        &self.strength
    }

    pub fn axis(&self) -> &Carrier {
        &self.axis
    }

    pub fn step(&self) -> PumpStep {
        self.step
    }

    /// The same pump family at a new nonnegative strength.
    pub fn with_strength(&self, strength: Rat) -> Result<Self, HnnError> {
        Self::new(strength, self.axis.clone(), self.step)
    }

    /// The pump phases a word visits.
    pub fn phases(&self) -> usize {
        self.step.order()
    }

    /// [definition; agent-inferred, U5] **The pump's clock**: one circle whose period is the step's
    /// order, one micro-step a word tick (`aeon::ClockLift`). Its torus point at tick `t` is the
    /// pump phase ([`PumpDeclaration::phase_at`]), and the aeon of one period is the pump's cycle
    /// ([`PumpDeclaration::period`]).
    pub fn clock(&self) -> ClockLift {
        ClockLift::new(vec![BigUint::from(self.phases())])
            .expect("a pump step's order is at least one tick")
    }

    /// **The pump phase at word tick `t`**: the pump's clock's torus point at `t` (Lean
    /// `Aeon/Clock/Winding.torusPoint`), whose carrier is `a² s^t` ([`PumpDeclaration::carrier`];
    /// Lean `HNN/Ring.pump_period_is_cycle`).
    pub fn phase_at(&self, tick: usize) -> usize {
        self.clock().torus_point(&[BigInt::from(tick)])[0]
            .to_usize()
            .expect("a pump phase lies below the step's order")
    }

    /// [proved-derived; implemented-exact] **The pump's period is a cycle** (`aeon::Cycle`): the
    /// aeon of one period of ticks from rest closes on the pump's clock and reads one whole
    /// winding. Its carrier returns there, `s^order = 1`, and at no fewer ticks: the aeon of `t`
    /// ticks closes exactly when the order divides `t`, exactly when `s^t = 1` (Lean
    /// `HNN/Ring.pump_period_is_cycle`).
    pub fn period(&self) -> Result<Cycle<ClockLift>, HnnError> {
        let clock = self.clock();
        let aeon = clock.forward(vec![BigInt::zero()], &[BigInt::from(self.phases())])?;
        Ok(Cycle::close(&clock, aeon)?)
    }

    /// **The pump carrier** `e^(iψ)` at phase `j`: `a² i^(j·k)`.
    pub fn carrier(&self, phase: usize) -> Carrier {
        let doubled = compose(&self.axis, &self.axis);
        compose(&doubled, &quarter_turn(self.step.quarters() * phase as u64))
    }

    /// **The node block** `−2p [[cos ψ, sin ψ], [sin ψ, −cos ψ]]` the pump adds to a node's `K`
    /// (Lean `HNN/Ring.pumpBlock`, read as `½ zᵀ K z`).
    pub fn block(&self, phase: usize) -> [[Rat; 2]; 2] {
        pump_block(&self.strength, &self.carrier(phase).as_gaussian())
    }
}

/// `−2p R_c`, `R_c = [[Re c, Im c], [Im c, −Re c]]`: at a unit carrier `c = e^(iψ)` the reflection
/// across the pump's axis `ψ/2`, scaled (Lean `HNN/Floquet.reflection`); at a placed amplitude
/// `c = |c| e^(iψ)` the same reflection scaled by `|c|` (module header, "The passage's
/// monodromy").
fn pump_block(strength: &Rat, carrier: &GaussianRat) -> [[Rat; 2]; 2] {
    let twice = integer(-2) * strength;
    [
        [&twice * &carrier.re, &twice * &carrier.im],
        [&twice * &carrier.im, -(&twice * &carrier.re)],
    ]
}

/// [definition; re-derived September 29] **The pump schedule: the pump is a periodic modulation of
/// the constitution** (module header, "The parametron re-derived"). Its strength `p ≥ 0` and one
/// carrier `e^(iψ_t)` per tick of its period: tick `t` adds the reflection block `−2p R_(ψ_t)` to
/// every node's stiffness. A declared pump is the schedule `a² s^t` over its order
/// ([`PumpSchedule::declared`]). A pump whose carriers are multiplied by the carriers of the cells
/// crossing the ring's section is modulated by them ([`PumpSchedule::modulated`]): the cells enter
/// the constitution through the pump, the only place the law reads them quadratically. The cells
/// of a passage enter at their placed amplitudes ([`PumpSchedule::placed`]), each reflection scaled
/// by its cell's `|z_t|`, and a tick no cell crosses is unpumped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpSchedule {
    strength: Rat,
    carriers: Vec<GaussianRat>,
}

impl PumpSchedule {
    /// A schedule of at least one tick at a nonnegative strength, one unit carrier a tick.
    pub fn new(strength: Rat, carriers: Vec<Carrier>) -> Result<Self, HnnError> {
        Self::of_amplitudes(strength, carriers.iter().map(Carrier::as_gaussian).collect())
    }

    /// A schedule of at least one tick at a nonnegative strength, one placed amplitude a tick.
    fn of_amplitudes(strength: Rat, carriers: Vec<GaussianRat>) -> Result<Self, HnnError> {
        if strength.is_negative() {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a pump's strength is nonnegative",
            });
        }
        if carriers.is_empty() {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a pump schedule has at least one tick",
            });
        }
        Ok(Self { strength, carriers })
    }

    /// **The declared pump as a schedule**: `a² s^t` over the step's order.
    pub fn declared(pump: &PumpDeclaration) -> Self {
        Self {
            strength: pump.strength.clone(),
            carriers: (0..pump.phases())
                .map(|phase| pump.carrier(phase).as_gaussian())
                .collect(),
        }
    }

    /// **The declared pump modulated by the crossing cells**: one tick per cell, the carrier at tick
    /// `t` the declared carrier `a² s^t` times the cell's carrier `c_t`. Its period is the cells'.
    pub fn modulated(pump: &PumpDeclaration, cells: &[Carrier]) -> Result<Self, HnnError> {
        Self::placed(
            pump,
            &cells.iter().map(Carrier::as_gaussian).collect::<Vec<_>>(),
        )
    }

    /// [definition; agent-inferred, September 29] **The declared pump modulated by a passage's placed
    /// amplitudes** (module header, "The passage's monodromy"): one tick per crossing, the carrier at
    /// tick `t` the declared carrier `a² s^t` times the amplitude `z_t` crossing the section there,
    /// `|z_t|` scaling the reflection; a zero amplitude leaves its tick unpumped. Its period is the
    /// passage's.
    pub fn placed(pump: &PumpDeclaration, amplitudes: &[GaussianRat]) -> Result<Self, HnnError> {
        Self::of_amplitudes(
            pump.strength.clone(),
            amplitudes
                .iter()
                .enumerate()
                .map(|(tick, amplitude)| {
                    pump.carrier(tick % pump.phases())
                        .as_gaussian()
                        .mul(amplitude)
                })
                .collect(),
        )
    }

    pub fn strength(&self) -> &Rat {
        &self.strength
    }

    /// The ticks of one period.
    pub fn period(&self) -> usize {
        self.carriers.len()
    }

    /// The carrier at word tick `t` (a unit carrier, or a placed amplitude): the schedule's own
    /// clock, `t mod period`.
    pub fn carrier(&self, tick: usize) -> &GaussianRat {
        &self.carriers[tick % self.carriers.len()]
    }

    /// The node block at word tick `t`.
    pub fn block(&self, tick: usize) -> [[Rat; 2]; 2] {
        pump_block(&self.strength, self.carrier(tick))
    }
}

/// `K` with a node block added on every node of the realified width.
fn stiffened(
    stiffness: &ExactRatMatrix,
    block: &[[Rat; 2]; 2],
) -> Result<ExactRatMatrix, HnnError> {
    let n = stiffness.rows();
    Ok(ExactRatMatrix::shaped(
        n,
        n,
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        let base = stiffness.get(i, j).expect("in range").clone();
                        if i / 2 == j / 2 {
                            base + &block[i % 2][j % 2]
                        } else {
                            base
                        }
                    })
                    .collect()
            })
            .collect(),
    )?)
}

/// **A node's sheet**: the half-turn sheet exactly when its amplitude lies on the far side of the
/// axis, `Re(z ā) < 0` (the threshold of its in-phase projection, `Objects/Parametron.sheetReading`
/// relative to the axis). A node on the axis's line reads its locked sheet back
/// (`sheetReading_binaryPhase`).
pub fn sheets(displacement: &[Rat], axis: &Carrier) -> Vec<bool> {
    displacement
        .chunks(2)
        .map(|node| {
            let in_phase =
                &node[0] * axis.cos() + node.get(1).map_or_else(Rat::zero, |y| y * axis.sin());
            threshold_sheet(&in_phase)
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the material

/// [definition] **A ring's resonator material** in `Θ`: its storage `C` on the rate, its stiffness `K`
/// on the displacement, its dissipation `D` on the rate (each symmetric on the ring's realified
/// width; `C, D ⪰ 0`), and its pump. The immutable base forms are declared; four squared scalar
/// amplitudes are learned at the ring's loaded port.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorMaterial {
    capacity: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    pump: Option<PumpDeclaration>,
    base_capacity: ExactRatMatrix,
    base_stiffness: ExactRatMatrix,
    base_dissipation: ExactRatMatrix,
    base_pump: Option<PumpDeclaration>,
    gains: [Rat; 4],
}

impl ResonatorMaterial {
    /// A resonator from its three forms and its pump, each form checked square and symmetric on one
    /// even width, `C` and `D` positive semidefinite.
    pub fn new(
        capacity: ExactRatMatrix,
        stiffness: ExactRatMatrix,
        dissipation: ExactRatMatrix,
        pump: Option<PumpDeclaration>,
    ) -> Result<Self, HnnError> {
        let n = capacity.rows();
        for form in [&capacity, &stiffness, &dissipation] {
            if form.rows() != n || form.columns() != n {
                return Err(HnnError::Shape {
                    what: "a resonator form (the ring's realified width)",
                    expected: n,
                    found: form.rows(),
                });
            }
        }
        if !n.is_multiple_of(2) {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a resonator lives on a realified width (two coordinates per node)",
            });
        }
        for form in [&capacity, &dissipation] {
            if inertia(&symmetric(form)?).negative != 0 {
                return Err(HnnError::Resonator {
                    ring: usize::MAX,
                    what: "a resonator's storage and dissipation are positive semidefinite",
                });
            }
        }
        symmetric(&stiffness)?;
        Ok(Self {
            base_capacity: capacity.clone(),
            base_stiffness: stiffness.clone(),
            base_dissipation: dissipation.clone(),
            base_pump: pump.clone(),
            capacity,
            stiffness,
            dissipation,
            pump,
            gains: std::array::from_fn(|_| Rat::one()),
        })
    }

    /// The trainable amplitudes of the declared storage, stiffness, dissipation and pump forms.
    /// Their squares scale immutable declared bases, so positive semidefiniteness is structural.
    pub fn gains(&self) -> &[Rat; 4] {
        &self.gains
    }

    /// Rebuild the material from its declared forms and squared scalar amplitudes. The caller
    /// certifies the candidate at its ring's hop before publication.
    ///
    /// [definition; agent-inferred] **Every amplitude is positive.** `g` and `−g` give one form
    /// (`g²`), so the positive sheet is the chart; a zero amplitude would zero its family's covector
    /// `2g·feature` for every later word, a release that deposition never makes. A family's release
    /// belongs to campaign 3's collapse law, with its receipt; a deposit step that would carry an
    /// amplitude to `g ≤ 0` backtracks instead (`hnn::constitution::GainBacktrack`). A
    /// nonpositive amplitude is refused here.
    pub fn with_gains(&self, gains: [Rat; 4]) -> Result<Self, HnnError> {
        if gains.iter().any(|gain| !gain.is_positive()) {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a resonator gain amplitude is positive (release belongs to the collapse)",
            });
        }
        let scale = |form: &ExactRatMatrix, gain: &Rat| form.scaled(&(gain * gain));
        let pump = self
            .base_pump
            .as_ref()
            .map(|pump| pump.with_strength(pump.strength() * &gains[3] * &gains[3]))
            .transpose()?;
        Ok(Self {
            capacity: scale(&self.base_capacity, &gains[0]),
            stiffness: scale(&self.base_stiffness, &gains[1]),
            dissipation: scale(&self.base_dissipation, &gains[2]),
            pump,
            base_capacity: self.base_capacity.clone(),
            base_stiffness: self.base_stiffness.clone(),
            base_dissipation: self.base_dissipation.clone(),
            base_pump: self.base_pump.clone(),
            gains,
        })
    }

    /// Immutable declared bases for the four gain coordinates.
    pub fn gain_bases(
        &self,
    ) -> (
        &ExactRatMatrix,
        &ExactRatMatrix,
        &ExactRatMatrix,
        Option<&Rat>,
    ) {
        (
            &self.base_capacity,
            &self.base_stiffness,
            &self.base_dissipation,
            self.base_pump.as_ref().map(PumpDeclaration::strength),
        )
    }

    /// The immutable declared pump chart, before its learned amplitude is applied.
    pub fn base_pump(&self) -> Option<&PumpDeclaration> {
        self.base_pump.as_ref()
    }

    /// **The parametron's resonator** (module header): `C = BᵀW_C B` and `K = BᵀW_K B` on the real and
    /// the imaginary coordinate of each node, the dissipation `d·I`, and the pump.
    pub fn of_parametron(
        parametron: &Parametron,
        dissipation: &Rat,
        pump: Option<PumpDeclaration>,
    ) -> Result<Self, HnnError> {
        let realify = |form: ExactRatMatrix| -> Result<ExactRatMatrix, HnnError> {
            let d = form.rows();
            Ok(ExactRatMatrix::shaped(
                2 * d,
                2 * d,
                (0..2 * d)
                    .map(|i| {
                        (0..2 * d)
                            .map(|j| {
                                if i % 2 == j % 2 {
                                    form.get(i / 2, j / 2).expect("in range").clone()
                                } else {
                                    Rat::zero()
                                }
                            })
                            .collect()
                    })
                    .collect(),
            )?)
        };
        let n = 2 * parametron.nodes();
        Self::new(
            realify(parametron.capacitance()?)?,
            realify(parametron.stiffness()?)?,
            ExactRatMatrix::identity(n)?.scaled(dissipation),
            pump,
        )
    }

    pub fn width(&self) -> usize {
        self.capacity.rows()
    }

    /// `C`, `K`, `D`.
    pub fn forms(&self) -> (&ExactRatMatrix, &ExactRatMatrix, &ExactRatMatrix) {
        (&self.capacity, &self.stiffness, &self.dissipation)
    }

    pub fn pump(&self) -> Option<&PumpDeclaration> {
        self.pump.as_ref()
    }

    /// The pump phases a word visits (one unpumped).
    pub fn phases(&self) -> usize {
        self.pump.as_ref().map_or(1, PumpDeclaration::phases)
    }

    /// **The pumped stiffness** `K_j`: `K` with the pump's node block added on every node.
    pub fn pumped_stiffness(&self, phase: usize) -> Result<ExactRatMatrix, HnnError> {
        match &self.pump {
            Some(pump) => stiffened(&self.stiffness, &pump.block(phase)),
            None => Ok(self.stiffness.clone()),
        }
    }

    /// **The resonator's certificate** at hop `h` (module header): at every pump phase the signed
    /// form `2C + hD + (h²/2) K_j` is positive semidefinite, so each phase's operator solves
    /// uniquely; refused with the first phase that is not.
    pub fn certify(&self, ring: usize, step: &Rat) -> Result<(), HnnError> {
        for phase in 0..self.phases() {
            if !self.signed_form_holds(&self.pumped_stiffness(phase)?, step)? {
                return Err(HnnError::UncertifiedResonator { ring, phase });
            }
        }
        Ok(())
    }

    /// `2C + hD + (h²/2) K ⪰ 0` for one phase's stiffness.
    fn signed_form_holds(&self, stiffness: &ExactRatMatrix, step: &Rat) -> Result<bool, HnnError> {
        let form = self
            .capacity
            .scaled(&integer(2))
            .add(&self.dissipation.scaled(step))?
            .add(&stiffness.scaled(&(step * step / integer(2))))?;
        Ok(inertia(&symmetric(&form)?).negative == 0)
    }

    /// `E_Q(u, w) = ½⟨w, C w⟩ + ½⟨u, K_j u⟩` at pump phase `j`.
    pub fn energy(
        &self,
        phase: usize,
        displacement: &[Rat],
        rate: &[Rat],
    ) -> Result<Rat, HnnError> {
        let stiffness = self.pumped_stiffness(phase)?;
        Ok((dot(rate, &self.capacity.apply(rate)?)
            + dot(displacement, &stiffness.apply(displacement)?))
            / integer(2))
    }
}

// -------------------------------------------------------------------------------------------
// the operands at the cut and the tick

/// The executed solve of one pump phase's operator: the exact inverse (the law) or a certified
/// lattice chart (the lattice word) with its reading.
#[derive(Clone, Debug, PartialEq, Eq)]
enum PhaseSolve {
    Exact(ExactRatMatrix),
    Chart(ChartWords),
}

impl PhaseSolve {
    fn apply(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        match self {
            Self::Exact(inverse) => Ok(inverse.apply(vector)?),
            Self::Chart(chart) => chart.apply(vector),
        }
    }

    fn apply_transpose(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        match self {
            Self::Exact(inverse) => Ok(inverse.transpose()?.apply(vector)?),
            Self::Chart(chart) => chart.apply_transpose(vector),
        }
    }

    /// The executed solve as its exact matrix: the law's inverse, or the chart's exact values.
    fn matrix(&self) -> Result<ExactRatMatrix, HnnError> {
        match self {
            Self::Exact(inverse) => Ok(inverse.clone()),
            Self::Chart(chart) => chart.to_matrix(),
        }
    }
}

/// One pump phase's operands: its stiffness `K_j`, its operator `M_j` with its largest absolute
/// row sum `‖M_j‖∞`, and its executed solve.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Phase {
    stiffness: ExactRatMatrix,
    operator: ExactRatMatrix,
    operator_norm: Rat,
    solve: PhaseSolve,
    reading: Option<ResonatorChart>,
}

impl Phase {
    /// One phase's operator `M_j = 2C + (h/Y)I + hD + (h²/2)K_j`, its largest absolute row sum and
    /// its executed solve (the exact inverse, or the certified chart on `lattice` from a cold start).
    fn of(
        ring: usize,
        material: &ResonatorMaterial,
        stiffness: ExactRatMatrix,
        admittance: &Rat,
        step: &Rat,
        lattice: Option<&WordLattice>,
        phase: usize,
    ) -> Result<Self, HnnError> {
        let (capacity, _, dissipation) = material.forms();
        let n = material.width();
        let operator = capacity
            .scaled(&integer(2))
            .add(&ExactRatMatrix::identity(n)?.scaled(&(step / admittance)))?
            .add(&dissipation.scaled(step))?
            .add(&stiffness.scaled(&(step * step / integer(2))))?;
        let operator_norm = (0..n)
            .map(|i| {
                operator
                    .row(i)
                    .expect("in range")
                    .iter()
                    .map(|x| x.abs())
                    .sum::<Rat>()
            })
            .max()
            .unwrap_or_else(Rat::zero);
        let (solve, reading) = match lattice {
            None => (PhaseSolve::Exact(operator.inverse()?), None),
            Some(lattice) => {
                let (chart, read): (ChartWords, ChartReading) =
                    refine(ChartKey::Ring(ring), &operator, None, lattice)?;
                (
                    PhaseSolve::Chart(chart),
                    Some(ResonatorChart {
                        ring,
                        phase,
                        certificate: read.certificate,
                        target: read.target,
                        steps: read.steps,
                    }),
                )
            }
        };
        Ok(Self {
            stiffness,
            operator,
            operator_norm,
            solve,
            reading,
        })
    }
}

/// [definition] **A resonator chart's reading**: the ring, the pump phase, the certificate
/// `‖1 − M X̂‖∞`, its target and the refinement's steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorChart {
    pub ring: usize,
    pub phase: usize,
    pub certificate: Rat,
    pub target: Rat,
    pub steps: u32,
}

/// [definition] **A resonator's operands at a word's cut**: its material, the ring's storage
/// admittance `Y` (its port), the hop `h`, and each pump phase's operator with its executed solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorOperands {
    ring: usize,
    material: ResonatorMaterial,
    admittance: Rat,
    step: Rat,
    phases: Vec<Phase>,
    /// A pump schedule in place of the material's declared pump ([`ResonatorOperands::scheduled`]).
    schedule: Option<PumpSchedule>,
}

/// [definition] **One executed resonator tick**: the tick's pump phase, the energy before (at the
/// previous phase's stiffness) and after (the carried state at this phase's), and every term of the
/// executed balance (module header), with the carried state and the remainders it leaves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorStep {
    /// The element output that drives this loaded port.
    pub drive: Vec<Rat>,
    /// Resonator state before the tick.
    pub input: [Vec<Rat>; 2],
    /// The exact right side of the phase solve before its executed chart.
    pub right: Vec<Rat>,
    /// The returned storage wave `drive − (2/Y) rate` before the word's carried split.
    pub output: Vec<Rat>,
    pub phase: usize,
    pub before: Rat,
    pub after: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub dissipation: Rat,
    pub chart: Rat,
    pub split: Rat,
    pub state: [Vec<Rat>; 2],
    pub rate: Vec<Rat>,
    /// **The certified bound on `|chart + split|`** (module header): `‖ω‖₁(δ‖r‖∞ + ‖M‖∞u)` for the
    /// executed solve and `(u/2)(‖C(ŵ′ + w′)‖₁ + ‖K(û′ + u′)‖₁)` for the state's split; zero under
    /// the exact law.
    pub bound: Rat,
    remainders: ResonatorRemainders,
}

/// The resonator's carried remainders: its solved rate's and its state's.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ResonatorRemainders {
    pub rate: Vec<Rat>,
    pub state: [Vec<Rat>; 2],
}

impl ResonatorRemainders {
    fn zero(width: usize) -> Self {
        Self {
            rate: vec![Rat::zero(); width],
            state: [vec![Rat::zero(); width], vec![Rat::zero(); width]],
        }
    }

    /// Every remainder, the rate's first.
    pub fn all(&self) -> impl Iterator<Item = &Rat> {
        self.rate.iter().chain(self.state.iter().flatten())
    }
}

impl ResonatorStep {
    /// **The executed balance closes exactly** (Lean `HNN/Ring.ring_tick_executed_energy_balance`):
    /// `after − before = pump + port − dissipation + chart + split`, and the executed solve's and
    /// split's residual lies within its certified bound, `|chart + split| ≤ bound`.
    pub fn closes(&self) -> bool {
        &self.after - &self.before
            == &self.pump + &self.port - &self.dissipation + &self.chart + &self.split
            && (&self.chart + &self.split).abs() <= self.bound
    }

    /// The carried remainders this tick leaves.
    pub fn remainders(&self) -> &ResonatorRemainders {
        &self.remainders
    }
}

impl ResonatorOperands {
    /// **A ring's resonator operands at the cut**: certified at every pump phase
    /// ([`ResonatorMaterial::certify`]), each phase's operator `M_j = 2C + (h/Y)I + hD + (h²/2)K_j`
    /// solved exactly (the law) or charted on the word's lattices from a cold start.
    pub fn at_cut(
        ring: usize,
        material: &ResonatorMaterial,
        admittance: &Rat,
        step: &Rat,
        lattice: Option<&WordLattice>,
    ) -> Result<Self, HnnError> {
        if !admittance.is_positive() || !step.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        material.certify(ring, step)?;
        let phases = (0..material.phases())
            .map(|phase| {
                Phase::of(
                    ring,
                    material,
                    material.pumped_stiffness(phase)?,
                    admittance,
                    step,
                    lattice,
                    phase,
                )
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(Self {
            ring,
            material: material.clone(),
            admittance: admittance.clone(),
            step: step.clone(),
            phases,
            schedule: None,
        })
    }

    /// **A ring's resonator operands under a pump schedule** (module header, "The pump is a periodic
    /// modulation of the constitution"): the material is declared unpumped, and tick `t` of the
    /// schedule's period is its own phase, with stiffness `K + ⊕ −2p R_(ψ_t)`, certified by its
    /// signed form and solved as [`ResonatorOperands::at_cut`] solves a declared pump's phase.
    pub fn scheduled(
        ring: usize,
        material: &ResonatorMaterial,
        schedule: &PumpSchedule,
        admittance: &Rat,
        step: &Rat,
        lattice: Option<&WordLattice>,
    ) -> Result<Self, HnnError> {
        if !admittance.is_positive() || !step.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        if material.pump().is_some() {
            return Err(HnnError::Resonator {
                ring,
                what: "a scheduled pump replaces the declared pump: the material is declared unpumped",
            });
        }
        let (_, stiffness, _) = material.forms();
        let phases = (0..schedule.period())
            .map(|phase| {
                let pumped = stiffened(stiffness, &schedule.block(phase))?;
                if !material.signed_form_holds(&pumped, step)? {
                    return Err(HnnError::UncertifiedResonator { ring, phase });
                }
                Phase::of(ring, material, pumped, admittance, step, lattice, phase)
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(Self {
            ring,
            material: material.clone(),
            admittance: admittance.clone(),
            step: step.clone(),
            phases,
            schedule: Some(schedule.clone()),
        })
    }

    /// The pump schedule, when the operands run one.
    pub fn schedule(&self) -> Option<&PumpSchedule> {
        self.schedule.as_ref()
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    pub fn material(&self) -> &ResonatorMaterial {
        &self.material
    }

    pub fn width(&self) -> usize {
        self.material.width()
    }

    /// `Y`, the port's admittance.
    pub fn admittance(&self) -> &Rat {
        &self.admittance
    }

    /// **The pump phase at word tick `t`**: the pump's clock's torus point
    /// ([`PumpDeclaration::phase_at`]), or the schedule's `t mod period`; an unpumped ring has the one
    /// phase.
    pub fn phase_at(&self, tick: usize) -> usize {
        match &self.schedule {
            Some(schedule) => tick % schedule.period(),
            None => self.material.pump().map_or(0, |pump| pump.phase_at(tick)),
        }
    }

    /// The pump phases the word visits.
    pub fn phases(&self) -> usize {
        self.phases.len()
    }

    /// `h`, the hop.
    pub fn hop(&self) -> &Rat {
        &self.step
    }

    /// The executed chart of pump phase `j`, when the word is on its lattices (a realization off
    /// the host executes the same chart).
    pub fn chart_words(&self, phase: usize) -> Option<&ChartWords> {
        match &self.phases[phase].solve {
            PhaseSolve::Chart(chart) => Some(chart),
            PhaseSolve::Exact(_) => None,
        }
    }

    /// The operator `M_j` of pump phase `j`.
    pub fn operator(&self, phase: usize) -> &ExactRatMatrix {
        &self.phases[phase].operator
    }

    /// The pumped stiffness `K_j`.
    pub fn stiffness(&self, phase: usize) -> &ExactRatMatrix {
        &self.phases[phase].stiffness
    }

    /// `‖M_j‖∞`, the operator's largest absolute row sum.
    pub fn operator_norm(&self, phase: usize) -> &Rat {
        &self.phases[phase].operator_norm
    }

    /// `δ_j = ‖1 − M_j X̂_j‖∞`, the executed chart's certificate; zero for the exact inverse.
    pub fn certificate(&self, phase: usize) -> Rat {
        self.phases[phase]
            .reading
            .as_ref()
            .map_or_else(Rat::zero, |reading| reading.certificate.clone())
    }

    /// Replace pump phase `j`'s executed solve by `solve`, its certificate kept: the wrong solve of
    /// the bound's own test.
    #[cfg(test)]
    pub(crate) fn with_executed_solve(mut self, phase: usize, solve: ExactRatMatrix) -> Self {
        self.phases[phase].solve = PhaseSolve::Exact(solve);
        self
    }

    /// **The executed charts with no transient split**: every phase's solve the executed chart's
    /// exact values, its certificate kept (the resonator's part of the word's executed linear map,
    /// on which a return pairs exactly: `Operands::unsplit`).
    #[cfg(test)]
    pub(crate) fn unsplit(mut self) -> Result<Self, HnnError> {
        for phase in &mut self.phases {
            if let PhaseSolve::Chart(chart) = &phase.solve {
                phase.solve = PhaseSolve::Exact(chart.to_matrix()?);
            }
        }
        Ok(self)
    }

    /// Apply the transpose of the executed phase solve to a covector.
    pub fn solve_transpose(&self, phase: usize, covector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        self.phases[phase].solve.apply_transpose(covector)
    }

    /// Apply the executed phase solve to a right-side variation.
    pub fn solve(&self, phase: usize, right: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        self.phases[phase].solve.apply(right)
    }

    /// Every chart's reading (none under the exact law).
    pub fn charts(&self) -> Vec<ResonatorChart> {
        self.phases
            .iter()
            .filter_map(|phase| phase.reading.clone())
            .collect()
    }

    fn energy_at(&self, phase: usize, displacement: &[Rat], rate: &[Rat]) -> Result<Rat, HnnError> {
        let (capacity, _, _) = self.material.forms();
        Ok((dot(rate, &capacity.apply(rate)?)
            + dot(
                displacement,
                &self.phases[phase].stiffness.apply(displacement)?,
            ))
            / integer(2))
    }

    /// **One executed resonator tick** at word tick `t` (module header): the drive `β` (the storage
    /// wave the junction sends into the ring), the state `[u, w]` and the remainders the last tick
    /// left; each image split on `lattice` (the transients', or `None` under the exact law).
    pub fn step(
        &self,
        tick: usize,
        drive: &[Rat],
        state: [&[Rat]; 2],
        remainders: &ResonatorRemainders,
        lattice: Option<&Lattice>,
    ) -> Result<ResonatorStep, HnnError> {
        let n = self.width();
        if drive.len() != n || state[0].len() != n || state[1].len() != n {
            return Err(HnnError::Shape {
                what: "a resonator's drive and state (the ring's realified width)",
                expected: n,
                found: drive.len().min(state[0].len()).min(state[1].len()),
            });
        }
        let remainders = if remainders.rate.len() == n {
            remainders.clone()
        } else {
            ResonatorRemainders::zero(n)
        };
        let phase = self.phase_at(tick);
        let previous = if tick == 0 {
            phase
        } else {
            self.phase_at(tick - 1)
        };
        let (u, w) = (state[0], state[1]);
        let h = &self.step;
        let (capacity, _, dissipation) = self.material.forms();
        let stiffness = &self.phases[phase].stiffness;
        // r = 2C w + h β − h K_j u
        let right = sub(
            &add(&scale(&integer(2), &capacity.apply(w)?), &scale(h, drive)),
            &scale(h, &stiffness.apply(u)?),
        );
        let image = self.phases[phase].solve.apply(&right)?;
        let split = |image: Vec<Rat>, remainder: &[Rat]| -> (Vec<Rat>, Vec<Rat>) {
            match lattice {
                Some(lattice) => {
                    let mut next = remainder.to_vec();
                    let carried = carry(lattice, &image, &mut next);
                    (carried, next)
                }
                None => (image, remainder.to_vec()),
            }
        };
        let (rate, rate_remainder) = split(image, &remainders.rate);
        let displacement_image = add(u, &scale(h, &rate));
        let velocity_image = sub(&scale(&integer(2), &rate), w);
        let (displacement, displacement_remainder) =
            split(displacement_image.clone(), &remainders.state[0]);
        let (velocity, velocity_remainder) = split(velocity_image.clone(), &remainders.state[1]);
        let before = self.energy_at(previous, u, w)?;
        let pump = if previous == phase {
            Rat::zero()
        } else {
            dot(
                u,
                &stiffness
                    .subtract(&self.phases[previous].stiffness)?
                    .apply(u)?,
            ) / integer(2)
        };
        let out = sub(drive, &scale(&(integer(2) / &self.admittance), &rate));
        let port = h * &self.admittance / integer(4) * (dot(drive, drive) - dot(&out, &out));
        let dissipation_work = h * dot(&rate, &dissipation.apply(&rate)?);
        let chart = dot(
            &rate,
            &sub(&self.phases[phase].operator.apply(&rate)?, &right),
        );
        let after = self.energy_at(phase, &displacement, &velocity)?;
        let split_term = &after - self.energy_at(phase, &displacement_image, &velocity_image)?;
        // |⟨ω, M ω − r⟩| ≤ ‖ω‖₁(δ‖r‖∞ + ‖M‖∞u) and |E(x̂) − E(x)| ≤ (u/2)(‖C(ŵ + w)‖₁ + ‖K(û + u)‖₁).
        let bound = match lattice {
            Some(lattice) => {
                let unit = lattice.unit();
                let solve = l1(&rate)
                    * (self.certificate(phase) * sup(&right)
                        + &self.phases[phase].operator_norm * &unit);
                let stored = capacity.apply(&add(&velocity, &velocity_image))?;
                let stiffened = stiffness.apply(&add(&displacement, &displacement_image))?;
                solve + unit * (l1(&stored) + l1(&stiffened)) / integer(2)
            }
            None => l1(&rate) * self.certificate(phase) * sup(&right),
        };
        Ok(ResonatorStep {
            drive: drive.to_vec(),
            input: [u.to_vec(), w.to_vec()],
            right,
            output: out,
            phase,
            before,
            after,
            pump,
            port,
            dissipation: dissipation_work,
            chart,
            split: split_term,
            state: [displacement, velocity],
            rate,
            bound,
            remainders: ResonatorRemainders {
                rate: rate_remainder,
                state: [displacement_remainder, velocity_remainder],
            },
        })
    }
}

/// `‖x‖₁`.
fn l1(vector: &[Rat]) -> Rat {
    vector.iter().map(|x| x.abs()).sum()
}

/// `‖x‖∞`.
fn sup(vector: &[Rat]) -> Rat {
    vector
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

// -------------------------------------------------------------------------------------------
// the Floquet monodromy and its certificate

/// [definition] **Why a Floquet certificate is refused** ([`Floquet::certify`],
/// [`attain_metric`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloquetRefusal {
    /// The declared growth `ρ` is negative.
    NegativeGrowth,
    /// The metric `G` is not a symmetric form on the state's width.
    MetricShape,
    /// `G` is not positive definite.
    MetricNotDefinite,
    /// `ρ²G − M_TᵀGM_T` has a negative direction: the energy can grow past `ρ²` in one period.
    GrowthExceeded,
    /// The exterior attainment's Stein operator is singular at the declared growth (`ρ² = μ_iμ_j`
    /// for two multipliers).
    Unattainable,
}

/// [definition] **The executed tick as a linear map of the state** (module header, "The Floquet
/// monodromy"): `x′ = T x` on `x = (u, w)`, with `X` the executed solve,
/// `T = [[I − h²XK, 2hXC], [−2hXK, 4XC − I]]`.
fn tick_map(
    solve: &ExactRatMatrix,
    capacity: &ExactRatMatrix,
    stiffness: &ExactRatMatrix,
    hop: &Rat,
) -> Result<ExactRatMatrix, HnnError> {
    let n = capacity.rows();
    let identity = ExactRatMatrix::identity(n)?;
    let solved_stiffness = solve.multiply(stiffness)?;
    let solved_capacity = solve.multiply(capacity)?;
    let blocks = [
        identity.subtract(&solved_stiffness.scaled(&(hop * hop)))?,
        solved_capacity.scaled(&(integer(2) * hop)),
        solved_stiffness.scaled(&(integer(-2) * hop)),
        solved_capacity.scaled(&integer(4)).subtract(&identity)?,
    ];
    Ok(ExactRatMatrix::shaped(
        2 * n,
        2 * n,
        (0..2 * n)
            .map(|i| {
                (0..2 * n)
                    .map(|j| {
                        blocks[2 * (i / n) + j / n]
                            .get(i % n, j % n)
                            .expect("in range")
                            .clone()
                    })
                    .collect()
            })
            .collect(),
    )?)
}

/// [proved-derived; implemented-exact] **The multipliers' placement about a circle** `|μ| = r`
/// ([`Floquet::placement`]): exact counts of the Floquet multipliers outside, on and inside it,
/// with multiplicity.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Placement {
    pub outside: usize,
    pub on: usize,
    pub inside: usize,
}

/// [definition] **A pumped ring's Floquet monodromy** (module header, "The Floquet monodromy"): the
/// executed ticks of one pump period as linear maps of the state, and their product
/// `M_T = T_(T−1) ⋯ T_0`, the transport around the pump's cycle, with its characteristic
/// polynomial.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Floquet {
    ring: usize,
    ticks: Vec<ExactRatMatrix>,
    monodromy: ExactRatMatrix,
    characteristic: RationalPolynomial,
}

impl Floquet {
    /// **The monodromy of the executed ticks** over one period of the operands' pump (the declared
    /// pump's order, a schedule's period, one tick unpumped), each tick's solve the executed one:
    /// the law's inverse, or the certified chart's exact matrix.
    pub fn of(operands: &ResonatorOperands) -> Result<Self, HnnError> {
        let (capacity, _, _) = operands.material().forms();
        let ticks = operands
            .phases
            .iter()
            .map(|phase| {
                tick_map(
                    &phase.solve.matrix()?,
                    capacity,
                    &phase.stiffness,
                    operands.hop(),
                )
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let mut monodromy = ExactRatMatrix::identity(2 * operands.width())?;
        for tick in &ticks {
            monodromy = tick.multiply(&monodromy)?;
        }
        let characteristic = monodromy.characteristic_polynomial()?;
        Ok(Self {
            ring: operands.ring(),
            ticks,
            monodromy,
            characteristic,
        })
    }

    /// `M_T`.
    pub fn monodromy(&self) -> &ExactRatMatrix {
        &self.monodromy
    }

    /// Each tick's map `T_t`, in the period's order.
    pub fn ticks(&self) -> &[ExactRatMatrix] {
        &self.ticks
    }

    /// `det(μ − M_T)`, monic.
    pub fn characteristic(&self) -> &RationalPolynomial {
        &self.characteristic
    }

    /// [proved-derived; implemented-exact] **The multipliers' placement about `|μ| = r`**. The
    /// Cayley map `μ = r(1 + s)/(1 − s)` sends the circle to the imaginary axis and its outside to
    /// the right half-plane, so `q(s) = (1 − s)^n χ(r(1 + s)/(1 − s)) = ∏_i ((r − μ_i) + (r + μ_i)s)`
    /// has the root `(μ_i − r)/(μ_i + r)` for every multiplier but `−r`, which drops its degree.
    /// The half-plane count of `q` (`ratio::polynomial::half_plane_count`, Routh–Hurwitz in its
    /// Sturm form) counts the multipliers outside, on and inside exactly; each `−r` counts on.
    pub fn placement(&self, radius: &Rat) -> Result<Placement, HnnError> {
        placement_of(&self.characteristic, self.monodromy.rows(), radius)
    }

    /// [proved-derived; implemented-exact] **The growth enclosed on either side of one** (module
    /// header, "The passage's monodromy"): `lower ≤ ρ(M_T) < upper` with
    /// `upper − lower ≤ upper·2^(−g)`, `lower` a radius some multiplier reaches or passes and every
    /// multiplier strictly inside `upper`, by exact bisection on the Schur–Cohn test. Unlike
    /// [`Floquet::decide`] it encloses a passive monodromy's radius too, so two passages' readings
    /// are ordered exactly on either side of the bifurcation.
    pub fn growth(&self, grain: u32) -> Growth {
        bisect(|radius: &Rat| !strictly_inside(&self.characteristic, radius), grain)
    }

    /// [proved-derived; implemented-exact] **The Floquet certificate** (module header): a metric
    /// `G ≻ 0`, attained by any exterior means, and a growth `ρ ≥ 0` with `M_TᵀGM_T ⪯ ρ²G`, each
    /// decided exactly by Sylvester inertia: `In(G) = (n, 0, 0)` and `ρ²G − M_TᵀGM_T` has no negative
    /// direction. Then `E_G(M_T^m x) ≤ ρ^(2m) E_G(x)` (Lean `HNN/Floquet.floquet_energy_iterate`).
    /// Refused with its reason; nothing about how `G` was attained is trusted.
    pub fn certify(
        &self,
        metric: &ExactRatMatrix,
        growth: &Rat,
    ) -> Result<FloquetCertificate, HnnError> {
        let refuse = |refusal| HnnError::UncertifiedFloquet {
            ring: self.ring,
            refusal,
        };
        if growth.is_negative() {
            return Err(refuse(FloquetRefusal::NegativeGrowth));
        }
        let width = self.monodromy.rows();
        if metric.rows() != width || metric.columns() != width || metric.transpose()? != *metric {
            return Err(refuse(FloquetRefusal::MetricShape));
        }
        if inertia(&symmetric(metric)?).positive != width {
            return Err(refuse(FloquetRefusal::MetricNotDefinite));
        }
        let carried = self
            .monodromy
            .transpose()?
            .multiply(metric)?
            .multiply(&self.monodromy)?;
        let gap = inertia(&symmetric(
            &metric.scaled(&(growth * growth)).subtract(&carried)?,
        )?);
        if gap.negative != 0 {
            return Err(refuse(FloquetRefusal::GrowthExceeded));
        }
        Ok(FloquetCertificate {
            metric: metric.clone(),
            growth: growth.clone(),
            period: self.ticks.len(),
            gap,
        })
    }

    /// [proved-derived; implemented-exact] **The exact decision** at the grain `2^(−g)` (module
    /// header, "The bifurcation"):
    /// - every multiplier strictly inside the unit circle: **passive**, certified at `ρ = 1`;
    /// - one outside: **growing**, the spectral radius enclosed in `[lower, upper]`, `lower > 1` a
    ///   radius some multiplier reaches (its placement counts one outside, or one on) and
    ///   `upper − lower ≤ 2^(−g)`, certified at `ρ = upper`;
    /// - none outside and some on the circle: **the edge** (a turn or a shear), certified at
    ///   `ρ = 1 + 2^(−g)`.
    ///
    /// Each certificate's metric is attained by the exact Stein solve ([`attain_metric`]) and
    /// certified by [`Floquet::certify`].
    pub fn decide(&self, grain: u32) -> Result<FloquetReading, HnnError> {
        let unit = Rat::one();
        let cell = dyadic(grain);
        let at_unit = self.placement(&unit)?;
        if at_unit.outside == 0 {
            if at_unit.on == 0 {
                let metric = attain_metric(self.ring, &self.monodromy, &unit)?;
                return Ok(FloquetReading::Passive {
                    certificate: self.certify(&metric, &unit)?,
                });
            }
            let edge = &unit + &cell;
            let metric = attain_metric(self.ring, &self.monodromy, &edge)?;
            return Ok(FloquetReading::Edge {
                certificate: self.certify(&metric, &edge)?,
                on_circle: at_unit.on,
            });
        }
        let mut lower = unit;
        let mut upper = integer(2);
        loop {
            let placed = self.placement(&upper)?;
            if placed.outside == 0 && placed.on == 0 {
                break;
            }
            if placed.outside > 0 || placed.on > 0 {
                lower = upper.clone();
            }
            upper *= integer(2);
        }
        while &upper - &lower > cell {
            let middle = (&lower + &upper) / integer(2);
            let placed = self.placement(&middle)?;
            if placed.outside > 0 {
                lower = middle;
            } else if placed.on == 0 {
                upper = middle;
            } else {
                // A multiplier on the circle `|μ| = middle` and none outside: the spectral radius is
                // `middle` exactly.
                lower = middle;
                break;
            }
        }
        let metric = attain_metric(self.ring, &self.monodromy, &upper)?;
        Ok(FloquetReading::Growing {
            certificate: self.certify(&metric, &upper)?,
            lower,
        })
    }

    /// [proved-derived; implemented-exact] **The bound the constitution consumes** (module header,
    /// "The consumer"): every tick's certified energy factor `σ_t²` in the certificate's metric
    /// (`σ_t²G − T_tᵀGT_t ⪰ 0`, the least dyadic at the relative grain `2^(−g)`), and the metric's
    /// certified equivalence to the state's Euclidean form, `γ_lo|x|² ≤ E_G(x) ≤ γ_hi|x|²`, each
    /// decided by inertia.
    pub fn bound(
        &self,
        certificate: &FloquetCertificate,
        grain: u32,
    ) -> Result<FloquetBound, HnnError> {
        let metric = certificate.metric();
        let width = metric.rows();
        let identity = ExactRatMatrix::identity(width)?;
        let semidefinite = |form: ExactRatMatrix| -> Result<bool, HnnError> {
            Ok(inertia(&symmetric(&form)?).negative == 0)
        };
        let mut tick = Rat::zero();
        for map in &self.ticks {
            let carried = map.transpose()?.multiply(metric)?.multiply(map)?;
            let factor = least_dyadic(grain, |value| {
                semidefinite(metric.scaled(value).subtract(&carried)?)
            })?;
            tick = tick.max(factor);
        }
        let high = least_dyadic(grain, |value| {
            semidefinite(identity.scaled(value).subtract(metric)?)
        })?;
        let low = greatest_dyadic(grain, |value| {
            semidefinite(metric.subtract(&identity.scaled(value))?)
        })?;
        Ok(FloquetBound {
            growth: certificate.growth().clone(),
            period: certificate.period(),
            tick,
            low,
            high,
        })
    }
}

/// `2^(−g)`.
fn dyadic(grain: u32) -> Rat {
    Rat::new(BigInt::one(), BigInt::one() << grain)
}

/// [proved-derived; implemented-exact] **The multipliers' placement about `|μ| = r`** of a
/// monodromy of the given degree read from its characteristic polynomial ([`Floquet::placement`]).
fn placement_of(
    characteristic: &RationalPolynomial,
    degree: usize,
    radius: &Rat,
) -> Result<Placement, HnnError> {
    if !radius.is_positive() {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let plus = RationalPolynomial::new(vec![Rat::one(), Rat::one()]);
    let minus = RationalPolynomial::new(vec![Rat::one(), -Rat::one()]);
    let powers = |factor: &RationalPolynomial| {
        let mut powers = vec![RationalPolynomial::one()];
        for _ in 0..degree {
            let next = powers.last().expect("one power at least").times(factor);
            powers.push(next);
        }
        powers
    };
    let (plus_powers, minus_powers) = (powers(&plus), powers(&minus));
    let mut image = RationalPolynomial::zero();
    let mut scale = Rat::one();
    for k in 0..=degree {
        let coefficient = characteristic.coefficient(k);
        if !coefficient.is_zero() {
            image = image.plus(
                &plus_powers[k]
                    .times(&minus_powers[degree - k])
                    .scaled(&(coefficient * &scale)),
            );
        }
        scale *= radius;
    }
    let image_degree = image.degree().unwrap_or(0);
    let count = half_plane_count(&image).map_err(HnnError::from)?;
    Ok(Placement {
        outside: count.right,
        on: count.axis + (degree - image_degree),
        inside: count.left,
    })
}

/// [proved-derived; implemented-exact] **An exact enclosure of a monodromy's spectral radius**
/// ([`Floquet::growth`]): `lower ≤ ρ(M) ≤ upper`, `lower` a radius some multiplier reaches and
/// none outside or on `upper`. A reading is ordered strictly above another exactly when its
/// `lower` exceeds the other's `upper` ([`Growth::exceeds`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Growth {
    pub lower: Rat,
    pub upper: Rat,
}

impl Growth {
    /// **The lock's flip between two readings** (`hnn::constitution`, "At a node: the lock's
    /// half-turn"; `Objects/ParametronLock.lockFace_logistic`): with the weights `a` and `K` of the
    /// two sheets, the lock turns exactly when `θ = a/(a + K) > ½`, `a > K`; on exact enclosures,
    /// exactly when this reading's `lower` exceeds the other's `upper`.
    pub fn exceeds(&self, other: &Self) -> bool {
        self.lower > other.upper
    }

    /// **The ring locks**: its growth is certified past the bifurcation, `ρ ≥ lower > 1`.
    pub fn is_locked(&self) -> bool {
        self.lower > Rat::one()
    }
}

/// [proved-standard; implemented-exact] **Every root strictly inside `|μ| < r`** (the Schur–Cohn
/// recursion, the discrete-time Routh test): a real polynomial `p = Σ c_i μ^i` of degree `n ≥ 1` has
/// every root strictly inside the unit disc exactly when `|c_0| < |c_n|` and the polynomial
/// `(c_n p(μ) − c_0 p*(μ))/μ` of degree `n − 1` has every root strictly inside, with
/// `p*(μ) = μ^n p(1/μ)` the reversed polynomial (a degree-zero polynomial has no root). Read on
/// integers at `p(rμ)`, `r = a/b` in lowest terms: `c_i a^i b^(n−i)`, each stage divided by the
/// power of two its coefficients share. It answers the one question a spectral-radius bisection
/// asks, `ρ < r`, without the Cayley map's half-plane count.
fn schur_inside(coefficients: &[BigInt], radius: &Rat) -> bool {
    let mut degree = coefficients.len().saturating_sub(1);
    while degree > 0 && coefficients[degree].is_zero() {
        degree -= 1;
    }
    let (numerator, denominator) = (radius.numer(), radius.denom());
    let mut numerator_power = BigInt::one();
    let mut stage: Vec<BigInt> = Vec::with_capacity(degree + 1);
    for coefficient in &coefficients[..=degree] {
        stage.push(coefficient * &numerator_power);
        numerator_power *= numerator;
    }
    if !denominator.is_one() {
        let mut denominator_power = BigInt::one();
        for coefficient in stage.iter_mut().rev() {
            *coefficient *= &denominator_power;
            denominator_power *= denominator;
        }
    }
    while stage.len() > 1 {
        let n = stage.len() - 1;
        let (low, high) = (stage[0].clone(), stage[n].clone());
        if low.magnitude() >= high.magnitude() {
            return false;
        }
        let mut next: Vec<BigInt> = (1..=n)
            .map(|i| &high * &stage[i] - &low * &stage[n - i])
            .collect();
        let shared = next
            .iter()
            .filter(|c| !c.is_zero())
            .map(|c| c.trailing_zeros().unwrap_or(0))
            .min()
            .unwrap_or(0);
        if shared > 0 {
            for c in &mut next {
                *c >>= shared;
            }
        }
        stage = next;
    }
    true
}

/// [`schur_inside`] for a rational polynomial, over the common denominator of its coefficients.
fn strictly_inside(characteristic: &RationalPolynomial, radius: &Rat) -> bool {
    let Some(degree) = characteristic.degree() else {
        return true;
    };
    let coefficients: Vec<Rat> = (0..=degree).map(|k| characteristic.coefficient(k)).collect();
    let common = common_denominator(coefficients.iter());
    let integral: Vec<BigInt> = coefficients
        .iter()
        .map(|c| c.numer() * (&common / c.denom()))
        .collect();
    schur_inside(&integral, radius)
}

/// **The growth enclosure** of `M = N/Δ` from the integer coefficients `c_k` of `N`'s characteristic
/// polynomial and the scale `Δ > 0`: the polynomial `q(μ) = Σ c_k Δ^k μ^k = det(Δμ − N)` has the
/// multipliers of `M` as its roots. Bracketed from one by doubling or halving, then bisected until
/// `upper − lower ≤ upper·2^(−g)`, each step decided by [`schur_inside`]: `lower` is a radius some
/// multiplier reaches or passes, and every multiplier lies strictly inside `upper`.
///
/// [definition; agent-inferred] **The bracket's attainment.** The bracket is attained on `q` with
/// every coefficient shifted right by the bits of `Δ^n` less `ATTAINMENT_BITS` (small integers,
/// cheap to test), bisected there to the grain, then certified on `q` itself by two exact tests:
/// what the shift attains is trusted nowhere. A bracket the exact tests refuse falls back to the
/// exact bracket and bisection.
pub(crate) fn growth_of(characteristic: &[BigInt], scale: &BigInt, grain: u32) -> Growth {
    let mut power = BigInt::one();
    let exact: Vec<BigInt> = characteristic
        .iter()
        .map(|c| {
            let term = c * &power;
            power *= scale;
            term
        })
        .collect();
    let leading = exact.last().map_or(0, |c| c.bits());
    let shift = leading.saturating_sub(ATTAINMENT_BITS);
    let rounded: Vec<BigInt> = exact.iter().map(|c| c >> shift).collect();
    let attained = bisect(|radius: &Rat| !schur_inside(&rounded, radius), grain);
    let reached = |radius: &Rat| !schur_inside(&exact, radius);
    if reached(&attained.lower) && !reached(&attained.upper) {
        return attained;
    }
    bisect(reached, grain)
}

/// The bits an attainment keeps below a polynomial's leading coefficient, or a matrix's largest
/// entry.
const ATTAINMENT_BITS: u64 = 128;

/// `A·B` on integer matrices.
fn integer_product(left: &[Vec<BigInt>], right: &[Vec<BigInt>]) -> Vec<Vec<BigInt>> {
    let n = left.len();
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    (0..n).fold(BigInt::zero(), |sum, k| {
                        if left[i][k].is_zero() || right[k][j].is_zero() {
                            sum
                        } else {
                            sum + &left[i][k] * &right[k][j]
                        }
                    })
                })
                .collect()
        })
        .collect()
}

/// [proved-standard; implemented-exact] **The characteristic polynomial of an integer matrix**
/// `det(μ − A)`, monic, by the Faddeev–LeVerrier recurrence `M_k = A M_(k−1) + c_(n−k+1) I`,
/// `c_(n−k) = −tr(A M_k)/k`, whose divisions are exact over the integers (every coefficient is an
/// integer).
pub(crate) fn integer_characteristic(matrix: &[Vec<BigInt>]) -> Vec<BigInt> {
    let n = matrix.len();
    let mut coefficients = vec![BigInt::one()];
    let mut standing: Vec<Vec<BigInt>> = vec![vec![BigInt::zero(); n]; n];
    for step in 1..=n {
        let last = coefficients.last().expect("a leading coefficient").clone();
        standing = integer_product(matrix, &standing);
        for (i, row) in standing.iter_mut().enumerate() {
            row[i] += &last;
        }
        let product = integer_product(matrix, &standing);
        let trace: BigInt = (0..n).map(|i| product[i][i].clone()).sum();
        coefficients.push(-trace / BigInt::from(step as u64));
    }
    coefficients.reverse();
    coefficients
}

/// A matrix with each entry rounded toward zero on the dyadic lattice `2^(e − ATTAINMENT_BITS)`,
/// `2^e` the magnitude of its largest entry: an attainment's operand, never trusted.
fn rounded_matrix(matrix: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    let largest = matrix
        .entries()
        .iter()
        .filter(|entry| !entry.is_zero())
        .map(|entry| entry.numer().bits() as i64 - entry.denom().bits() as i64)
        .max()
        .unwrap_or(0);
    let shift = ATTAINMENT_BITS as i64 - largest;
    let unit = if shift >= 0 {
        Rat::new(BigInt::one(), BigInt::one() << shift as u64)
    } else {
        Rat::from_integer(BigInt::one() << (-shift) as u64)
    };
    Ok(ExactRatMatrix::shaped(
        matrix.rows(),
        matrix.columns(),
        (0..matrix.rows())
            .map(|i| {
                (0..matrix.columns())
                    .map(|j| {
                        let entry = matrix.get(i, j).expect("in range");
                        Rat::from_integer((entry / &unit).to_integer()) * &unit
                    })
                    .collect()
            })
            .collect(),
    )?)
}

/// Bracket a monotone reading (`reached` true below the radius, false above) from one by doubling
/// or halving, then bisect until `upper − lower ≤ upper·2^(−g)`.
fn bisect(reached: impl Fn(&Rat) -> bool, grain: u32) -> Growth {
    let two = integer(2);
    let (mut lower, mut upper);
    if reached(&Rat::one()) {
        lower = Rat::one();
        upper = two.clone();
        while reached(&upper) {
            lower = upper.clone();
            upper *= &two;
        }
    } else {
        upper = Rat::one();
        lower = &upper / &two;
        while !reached(&lower) {
            upper = lower.clone();
            lower /= &two;
        }
    }
    while &upper - &lower > &upper * dyadic(grain) {
        let middle = (&lower + &upper) / &two;
        if reached(&middle) {
            lower = middle;
        } else {
            upper = middle;
        }
    }
    Growth { lower, upper }
}

/// The least value at the relative grain `2^(−g)` where a monotone predicate (false below its
/// threshold, true above) holds: doubled from one until it holds, halved while its half holds, then
/// bisected until the bracket is within `2^(−g)` of its upper end.
fn least_dyadic(
    grain: u32,
    holds: impl Fn(&Rat) -> Result<bool, HnnError>,
) -> Result<Rat, HnnError> {
    let two = integer(2);
    let mut upper = Rat::one();
    while !holds(&upper)? {
        upper *= &two;
    }
    let mut lower = &upper / &two;
    while holds(&lower)? {
        if lower.is_zero() {
            return Ok(lower);
        }
        upper = lower.clone();
        lower /= &two;
        if lower < dyadic(grain) * dyadic(grain) {
            return Ok(if holds(&Rat::zero())? {
                Rat::zero()
            } else {
                upper
            });
        }
    }
    while &upper - &lower > &upper * dyadic(grain) {
        let middle = (&lower + &upper) / &two;
        if holds(&middle)? {
            upper = middle;
        } else {
            lower = middle;
        }
    }
    Ok(upper)
}

/// The greatest positive value at the relative grain `2^(−g)` where a monotone predicate (true
/// below its threshold, false above) holds; the predicate holds at some positive value.
fn greatest_dyadic(
    grain: u32,
    holds: impl Fn(&Rat) -> Result<bool, HnnError>,
) -> Result<Rat, HnnError> {
    let two = integer(2);
    let mut lower = Rat::one();
    while !holds(&lower)? {
        lower /= &two;
    }
    let mut upper = &lower * &two;
    while holds(&upper)? {
        lower = upper.clone();
        upper *= &two;
    }
    while &upper - &lower > &lower * dyadic(grain) {
        let middle = (&lower + &upper) / &two;
        if holds(&middle)? {
            lower = middle;
        } else {
            upper = middle;
        }
    }
    Ok(lower)
}

/// [definition; agent-inferred] **The exterior attainment of a Floquet metric** (module header):
/// the Stein solve `M_TᵀGM_T − ρ²G = −ρ²I` over the symmetric unknowns, exact. When every multiplier
/// lies strictly inside `|μ| = ρ` its solution is `G = Σ_k (M_T/ρ)^(kᵀ)(M_T/ρ)^k ≻ 0`, so
/// `ρ²G − M_TᵀGM_T = ρ²I ≻ 0`. It is one exterior means among any: [`Floquet::certify`] trusts none
/// of it. A singular Stein operator (`ρ² = μ_iμ_j`) is refused.
pub fn attain_metric(
    ring: usize,
    monodromy: &ExactRatMatrix,
    growth: &Rat,
) -> Result<ExactRatMatrix, HnnError> {
    let n = monodromy.rows();
    let pairs: Vec<(usize, usize)> = (0..n).flat_map(|i| (i..n).map(move |j| (i, j))).collect();
    let position = |k: usize, l: usize| -> usize {
        let (a, b) = (k.min(l), k.max(l));
        // the packed upper triangle, row by row
        a * n - a * (a + 1) / 2 + b
    };
    let squared = growth * growth;
    let mut rows = vec![vec![Rat::zero(); pairs.len()]; pairs.len()];
    let mut target = vec![Rat::zero(); pairs.len()];
    for (row, &(i, j)) in pairs.iter().enumerate() {
        for k in 0..n {
            let left = monodromy.get(k, i)?;
            if left.is_zero() {
                continue;
            }
            for l in 0..n {
                let right = monodromy.get(l, j)?;
                if !right.is_zero() {
                    rows[row][position(k, l)] += left * right;
                }
            }
        }
        rows[row][position(i, j)] -= &squared;
        if i == j {
            target[row] = -squared.clone();
        }
    }
    let unattainable = HnnError::UncertifiedFloquet {
        ring,
        refusal: FloquetRefusal::Unattainable,
    };
    let Some((solution, kernel)) = ExactRatMatrix::new(rows)?.preimage_fibre(&target)? else {
        return Err(unattainable);
    };
    if !kernel.is_empty() {
        return Err(unattainable);
    }
    Ok(ExactRatMatrix::shaped(
        n,
        n,
        (0..n)
            .map(|i| (0..n).map(|j| solution[position(i, j)].clone()).collect())
            .collect(),
    )?)
}

/// [proved-derived; implemented-exact] **A Floquet certificate**: the metric `G ≻ 0`, the growth
/// `ρ` per period with `M_TᵀGM_T ⪯ ρ²G`, the period and the gap's inertia, each decided exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FloquetCertificate {
    metric: ExactRatMatrix,
    growth: Rat,
    period: usize,
    gap: Inertia,
}

impl FloquetCertificate {
    /// `G`.
    pub fn metric(&self) -> &ExactRatMatrix {
        &self.metric
    }

    /// `ρ`: the certified amplitude growth per period in `G`.
    pub fn growth(&self) -> &Rat {
        &self.growth
    }

    /// The ticks of one period.
    pub fn period(&self) -> usize {
        self.period
    }

    /// The inertia of `ρ²G − M_TᵀGM_T` (no negative direction).
    pub fn gap(&self) -> &Inertia {
        &self.gap
    }

    /// **`ρ^(2m)`: the certified energy factor over `m` periods** (Lean
    /// `HNN/Floquet.floquet_energy_iterate`): the tests' reading of the certificate's law against
    /// the executed passage; no consumer reads it outside them.
    #[cfg(test)]
    pub(crate) fn energy_factor(&self, periods: u64) -> Rat {
        let squared = &self.growth * &self.growth;
        (0..periods).fold(Rat::one(), |factor, _| factor * &squared)
    }

    /// `ρ ≤ 1`: the storage cannot grow over a period (Lean `HNN/Floquet.floquet_passive`).
    pub fn is_passive(&self) -> bool {
        self.growth <= Rat::one()
    }
}

/// [proved-derived; implemented-exact] **The exact reading of a pumped ring's Floquet growth**
/// ([`Floquet::decide`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FloquetReading {
    /// Every multiplier strictly inside the unit circle: the storage decays; certified at `ρ = 1`.
    Passive { certificate: FloquetCertificate },
    /// None outside and `on_circle` on it: the lossless edge (a turn, or a shear at the tongue's
    /// edge); certified at `ρ = 1 + 2^(−g)`.
    Edge {
        certificate: FloquetCertificate,
        on_circle: usize,
    },
    /// A multiplier outside: the storage grows, its spectral radius at least `lower > 1` and at most
    /// the certificate's `ρ`.
    Growing {
        certificate: FloquetCertificate,
        lower: Rat,
    },
}

impl FloquetReading {
    pub fn certificate(&self) -> &FloquetCertificate {
        match self {
            Self::Passive { certificate }
            | Self::Edge { certificate, .. }
            | Self::Growing { certificate, .. } => certificate,
        }
    }

    /// The ring locks: its storage grows past the bifurcation.
    pub fn is_locked(&self) -> bool {
        matches!(self, Self::Growing { .. })
    }

    /// The ring is certified silent: its storage decays.
    pub fn is_silent(&self) -> bool {
        matches!(self, Self::Passive { .. })
    }
}

/// [proved-derived; implemented-exact] **The bound the constitution consumes** ([`Floquet::bound`];
/// module header, "The consumer"): `ρ` per period, the period `T`, the largest tick factor
/// `max_t σ_t²` in `G`, and `γ_lo|x|² ≤ E_G(x) ≤ γ_hi|x|²`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FloquetBound {
    pub growth: Rat,
    pub period: usize,
    pub tick: Rat,
    pub low: Rat,
    pub high: Rat,
}

impl FloquetBound {
    /// **The consumer's factor over `s` ticks from any phase**:
    /// `|x_(τ+s)|² ≤ (γ_hi/γ_lo) · max_o ρ^(2m_o) (max_t σ_t²)^(s − T m_o) · |x_τ|²`, the span's first
    /// full period starting after `o` ticks (`0 ≤ o < T`), `m_o = ⌊(s − o)/T⌋` whole periods (Lean
    /// `HNN/Floquet.{floquet_tick_product, floquet_metric_change}`).
    pub fn reach(&self, ticks: u64) -> Rat {
        let period = self.period as u64;
        let squared = &self.growth * &self.growth;
        let power =
            |base: &Rat, exponent: u64| (0..exponent).fold(Rat::one(), |value, _| value * base);
        let worst = (0..period)
            .map(|offset| {
                let whole = ticks.saturating_sub(offset) / period;
                power(&squared, whole) * power(&self.tick, ticks - whole * period)
            })
            .max()
            .unwrap_or_else(Rat::one);
        &self.high / &self.low * worst
    }
}

// -------------------------------------------------------------------------------------------
// the locked sheet and the receiving bank

/// [proved-derived; implemented-exact] **The sheets a pumped resonator locks to from a seed**
/// ([`lock`]): per node, the in-phase projection's side of the axis after the executed passage, or
/// `None` exactly on the quadrature line (held); the final state; whether every executed tick's
/// balance closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedSheets {
    pub sheets: Vec<Option<bool>>,
    pub state: [Vec<Rat>; 2],
    pub closed: bool,
    pub ticks: usize,
}

/// [proved-derived; implemented-exact] **Phase-sensitive amplification read at its locked sheet**
/// (module header, "Phase-sensitive amplification"): the executed, undriven passage of `periods`
/// pump periods from the seed `(u, w)`, every tick's balance checked, then each node's in-phase
/// projection `Re(z ā)` at the axis `a`. Past the bifurcation the in-phase quadrature grows by the
/// Floquet multiplier and the rest does not, so the sheet is the sign of the seed's growing
/// coordinate: for a seed on the displacement, the sign of `⟨u, a⟩`, a `cos(φ_in − φ_a)` reading
/// (Lean `HNN/Floquet.{inphase_growing, inphase_growing_coordinate}`). It is linear, then
/// threshold: odd under the half-turn of its seed.
pub fn lock(
    operands: &ResonatorOperands,
    seed: [&[Rat]; 2],
    periods: usize,
    axis: &Carrier,
) -> Result<LockedSheets, HnnError> {
    let n = operands.width();
    let drive = vec![Rat::zero(); n];
    let remainders = ResonatorRemainders::zero(n);
    let mut state = [seed[0].to_vec(), seed[1].to_vec()];
    let mut closed = true;
    let ticks = periods * operands.phases();
    for tick in 0..ticks {
        let step = operands.step(tick, &drive, [&state[0], &state[1]], &remainders, None)?;
        closed &= step.closes();
        state = step.state;
    }
    let sheets = state[0]
        .chunks(2)
        .map(|node| {
            let in_phase =
                &node[0] * axis.cos() + node.get(1).map_or_else(Rat::zero, |y| y * axis.sin());
            (!in_phase.is_zero()).then(|| in_phase.is_negative())
        })
        .collect();
    Ok(LockedSheets {
        sheets,
        state,
        closed,
        ticks,
    })
}

/// [definition; agent-inferred, September 29] **A bank of receiving parametrons at declared pump
/// phases** (module header, "The relative phase is read by the pump"): one unpumped resonator
/// material, and per member a declared pump whose carriers the cells crossing the section modulate
/// ([`PumpSchedule::modulated`]). Each member's Floquet growth is decided exactly
/// ([`Floquet::decide`]); a member locks when its growth is certified past one and is silent when
/// its passivity is certified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingBank {
    material: ResonatorMaterial,
    pumps: Vec<PumpDeclaration>,
    admittance: Rat,
    hop: Rat,
    grain: u32,
}

impl ReceivingBank {
    /// A bank of at least one member on an unpumped material, a positive port and hop.
    pub fn new(
        material: ResonatorMaterial,
        pumps: Vec<PumpDeclaration>,
        admittance: Rat,
        hop: Rat,
        grain: u32,
    ) -> Result<Self, HnnError> {
        if material.pump().is_some() || pumps.is_empty() {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a receiving bank is one unpumped material and at least one declared pump",
            });
        }
        if !admittance.is_positive() || !hop.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        Ok(Self {
            material,
            pumps,
            admittance,
            hop,
            grain,
        })
    }

    /// The members' declared pumps.
    pub fn pumps(&self) -> &[PumpDeclaration] {
        &self.pumps
    }

    /// **The bank's reading of the cells crossing its section**: each member's pump modulated by
    /// the cells (one tick a crossing), its executed operands, its monodromy and its exact
    /// decision.
    pub fn read(&self, cells: &[Carrier]) -> Result<BankReading, HnnError> {
        let readings = self
            .pumps
            .iter()
            .enumerate()
            .map(|(member, pump)| {
                let schedule = PumpSchedule::modulated(pump, cells)?;
                let operands = ResonatorOperands::scheduled(
                    member,
                    &self.material,
                    &schedule,
                    &self.admittance,
                    &self.hop,
                    None,
                )?;
                Floquet::of(&operands)?.decide(self.grain)
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(BankReading { readings })
    }

    /// [proved-derived; implemented-exact] **The bank's reading of a passage's turn** (module header,
    /// "The passage's monodromy"): each member's monodromy through every crossing of the turn, its
    /// pump modulated by the placed amplitude crossing at each tick ([`PumpSchedule::placed`]), and
    /// its growth enclosed exactly at the relative grain `2^(−g)` ([`Floquet::growth`]); the bank's
    /// joint monodromy is the members' block sum, so its growth is the largest member's. A member
    /// reads the turn only when its pump's period divides the turn's ticks, so the turn is a cycle
    /// of its clock and the product is its Floquet monodromy; otherwise refused. Each tick is
    /// certified by its signed form as a scheduled phase is.
    ///
    /// [definition; agent-inferred] **Realized on integers.** Each executed tick map `T_t` is carried
    /// as `N_t/L_t`, `L_t` the least common denominator of its entries, so the product is the integer
    /// matrix `N = N_(T−1) ⋯ N_0` over `Δ = ∏ L_t` and the multipliers of `M_T = N/Δ` at radius `r` are
    /// those of `N` at `rΔ`: the same monodromy, without a common-denominator reduction at every
    /// product.
    pub fn read_turn(&self, amplitudes: &[GaussianRat], grain: u32) -> Result<TurnReading, HnnError> {
        let members = (0..self.pumps.len())
            .map(|member| {
                let (_, product, scale) = self.turn_monodromy(member, amplitudes)?;
                Ok(growth_of(&integer_characteristic(&product), &scale, grain))
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let joint = joint_of(&members);
        Ok(TurnReading { members, joint })
    }

    /// Member `member`'s turn: each crossing's executed tick map, and the monodromy as the integer
    /// matrix `N` over its scale `Δ` (`M_T = N/Δ`; [`ReceivingBank::read_turn`]).
    fn turn_monodromy(
        &self,
        member: usize,
        amplitudes: &[GaussianRat],
    ) -> Result<(Vec<ExactRatMatrix>, Vec<Vec<BigInt>>, BigInt), HnnError> {
        let pump = &self.pumps[member];
        if !amplitudes.len().is_multiple_of(pump.phases()) {
            return Err(HnnError::Resonator {
                ring: member,
                what: "a member reads a turn only when its pump's period divides the turn",
            });
        }
        let schedule = PumpSchedule::placed(pump, amplitudes)?;
        let n = 2 * self.material.width();
        let mut maps = Vec::with_capacity(schedule.period());
        let mut product: Vec<Vec<BigInt>> = (0..n)
            .map(|i| (0..n).map(|j| BigInt::from(u8::from(i == j))).collect())
            .collect();
        let mut scale = BigInt::one();
        for tick in 0..schedule.period() {
            let map = self.crossing(member, &schedule.block(tick), tick)?;
            let denominator = common_denominator(map.entries());
            let integral: Vec<Vec<BigInt>> = (0..n)
                .map(|i| {
                    (0..n)
                        .map(|j| {
                            let entry = map.get(i, j).expect("in range");
                            entry.numer() * (&denominator / entry.denom())
                        })
                        .collect()
                })
                .collect();
            product = integer_product(&integral, &product);
            scale *= denominator;
            maps.push(map);
        }
        Ok((maps, product, scale))
    }

    /// One crossing's executed tick map for member `member`: the unpumped stiffness with the node
    /// block of its placed carrier, certified by its signed form, solved exactly.
    fn crossing(
        &self,
        member: usize,
        block: &[[Rat; 2]; 2],
        tick: usize,
    ) -> Result<ExactRatMatrix, HnnError> {
        let (capacity, stiffness, _) = self.material.forms();
        let pumped = stiffened(stiffness, block)?;
        if !self.material.signed_form_holds(&pumped, &self.hop)? {
            return Err(HnnError::UncertifiedResonator {
                ring: member,
                phase: tick,
            });
        }
        let phase = Phase::of(
            member,
            &self.material,
            pumped,
            &self.admittance,
            &self.hop,
            None,
            tick,
        )?;
        tick_map(&phase.solve.matrix()?, capacity, &phase.stiffness, &self.hop)
    }

    /// [proved-derived; implemented-exact] **The certificate of a turn's reading**: each member's
    /// monodromy through the turn certified at the joint reading's `upper` ([`Floquet::certify`]: `G`
    /// and `upper²G − M_TᵀGM_T` decided by inertia on the exact monodromy), and the executed,
    /// undriven turn from the declared seed (node 0's real displacement one, its imaginary rate one
    /// half) under the placed schedule, every tick's balance checked.
    ///
    /// [definition; agent-inferred] **The metric's attainment.** `G` is the exact Stein solve
    /// ([`attain_metric`]) of the monodromy with each entry rounded toward zero at `ATTAINMENT_BITS`
    /// significant bits of its largest entry: the exact monodromy's entries carry every crossing's
    /// denominators, and nothing of how `G` was attained is trusted. A metric the exact inertia
    /// refuses is attained again by the exact Stein solve of the exact monodromy.
    pub fn certify_turn(
        &self,
        amplitudes: &[GaussianRat],
        reading: &TurnReading,
        grain: u32,
    ) -> Result<TurnCertificate, HnnError> {
        let width = self.material.width();
        let mut certificates = Vec::with_capacity(self.pumps.len());
        let (mut closed, mut ticks) = (0usize, 0usize);
        for (member, pump) in self.pumps.iter().enumerate() {
            let (maps, product, scale) = self.turn_monodromy(member, amplitudes)?;
            let n = product.len();
            let monodromy = ExactRatMatrix::shaped(
                n,
                n,
                product
                    .iter()
                    .map(|row| {
                        row.iter()
                            .map(|entry| Rat::new(entry.clone(), scale.clone()))
                            .collect()
                    })
                    .collect(),
            )?;
            // `det(μ − N/Δ) = Δ^(−n) det(Δμ − N)`: the coefficient of `μ^k` is `c_k Δ^(k − n)`.
            let integral = integer_characteristic(&product);
            let mut power = Rat::one();
            let mut coefficients = vec![Rat::zero(); n + 1];
            for k in (0..=n).rev() {
                coefficients[k] = Rat::from_integer(integral[k].clone()) / &power;
                power *= Rat::from_integer(scale.clone());
            }
            let characteristic = RationalPolynomial::new(coefficients);
            let floquet = Floquet {
                ring: member,
                ticks: maps,
                monodromy,
                characteristic,
            };
            let mut upper = reading.joint.upper.clone();
            let mut power = BigInt::one();
            let scaled: Vec<BigInt> = integral
                .iter()
                .map(|c| {
                    let term = c * &power;
                    power *= &scale;
                    term
                })
                .collect();
            if !schur_inside(&scaled, &upper) {
                // A reading enclosed exactly at a multiplier: one grain above it.
                upper *= Rat::one() + dyadic(grain);
            }
            let rounded = rounded_matrix(floquet.monodromy())?;
            let certificate = match attain_metric(member, &rounded, &upper)
                .and_then(|metric| floquet.certify(&metric, &upper))
            {
                Ok(certificate) => certificate,
                Err(_) => {
                    let metric = attain_metric(member, floquet.monodromy(), &upper)?;
                    floquet.certify(&metric, &upper)?
                }
            };
            certificates.push(certificate);
            let schedule = PumpSchedule::placed(pump, amplitudes)?;
            let operands = ResonatorOperands::scheduled(
                member,
                &self.material,
                &schedule,
                &self.admittance,
                &self.hop,
                None,
            )?;
            let drive = vec![Rat::zero(); width];
            let mut state = [vec![Rat::zero(); width], vec![Rat::zero(); width]];
            state[0][0] = Rat::one();
            state[1][1] = Rat::new(BigInt::one(), BigInt::from(2));
            for tick in 0..operands.phases() {
                let step = operands.step(
                    tick,
                    &drive,
                    [&state[0], &state[1]],
                    &ResonatorRemainders::zero(width),
                    None,
                )?;
                closed += usize::from(step.closes());
                ticks += 1;
                state = step.state;
            }
        }
        Ok(TurnCertificate {
            certificates,
            closed,
            ticks,
        })
    }
}

/// [definition; agent-inferred, September 29] **A turn of the receiving ring** (module header, "The
/// passage's monodromy"): the ring's storage, one complex amplitude per node
/// (`u_(2ν) + i u_(2ν+1)`), in the order its nodes cross the section as the ring turns on. The ring's
/// port map is `P = (· + 1)` and a datum of age `a` is placed at rotation `a`, so the next tick
/// brings node `d − 1` to the section (age `−1`: the first station), then `d − 2`, …, and node `0`
/// (the newest request cell) last: tick `t` reads node `d − 1 − t`, the passage in its own time
/// order around the cycle of the turn.
pub fn turn(storage: &[Rat]) -> Vec<GaussianRat> {
    let nodes = storage.len() / 2;
    (0..nodes)
        .map(|tick| {
            let node = nodes - 1 - tick;
            GaussianRat::new(storage[2 * node].clone(), storage[2 * node + 1].clone())
        })
        .collect()
}

/// [proved-derived; implemented-exact] **The bank's reading of a turn** ([`ReceivingBank::read_turn`]):
/// each member's growth enclosure and the joint (the largest member's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnReading {
    pub members: Vec<Growth>,
    pub joint: Growth,
}

/// [proved-derived; implemented-exact] **A turn reading's certificate**
/// ([`ReceivingBank::certify_turn`]): each member's Floquet certificate at the joint growth, and the
/// executed turn's ticks whose balance closed, of those run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnCertificate {
    pub certificates: Vec<FloquetCertificate>,
    pub closed: usize,
    pub ticks: usize,
}

/// [proved-derived; implemented-exact] **A bank's reading**: each member's exact Floquet reading.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BankReading {
    pub readings: Vec<FloquetReading>,
}

impl BankReading {
    /// The members that lock.
    pub fn locked(&self) -> Vec<usize> {
        (0..self.readings.len())
            .filter(|member| self.readings[*member].is_locked())
            .collect()
    }

    /// **The bank's class**: the one member that locks while every other is certified silent; no
    /// class otherwise (a plural lock, none, or an edge).
    pub fn class(&self) -> Option<usize> {
        let locked = self.locked();
        let silent = self.readings.iter().filter(|r| r.is_silent()).count();
        (locked.len() == 1 && silent + 1 == self.readings.len()).then(|| locked[0])
    }
}

// -------------------------------------------------------------------------------------------
// the executed growth's covector

/// [definition; agent-inferred, September 30] **The significant bits of the covector's disks**
/// (`ratio::disk`). Every disk is an enclosure at any precision; the precision decides only whether
/// a certificate passes (fewer bits return a typed refusal, never a wrong covector). At 192 bits the
/// passage's rounding, at most the product of the ticks' row norms times `2^(−192)` relative, stays
/// many binary orders below the readings' own grain on the declared turns (their row norms' product
/// over 60 crossings is below `2^120`).
const COVECTOR_BITS: u32 = 192;

/// The attainment's precision and iterations (an exterior means, trusted nowhere: a root it does
/// not reach fails the Krawczyk test and is refused as a collision). Newton's steps in [`isolate`]
/// carry a 96-bit attainment to the disks' precision.
const ROOT_ATTAINMENT_BITS: u32 = 96;
const ATTAINMENT_ITERATIONS: usize = 64;

/// [definition; agent-inferred, September 30] **The separation's relative grain** `2^(−48)`: every
/// other multiplier must lie inside the dominant's modulus less this fraction of it. A multiplier
/// within it is a tie at the declared grain (typed), never an ordering guessed; 48 bits lie far below
/// the growth's own grain (`2^(−16)` on the declared runs) and far above the half-plane count's
/// resolution (`2^(−96)`).
const SEPARATION_BITS: u32 = 48;

/// [definition; agent-inferred, September 30] **Why a member's growth covector is not returned**
/// (module header, "The executed growth's covector"): the largest modulus has no derivative there,
/// or its certificate did not pass at the declared precision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CovectorRefusal {
    /// No disk about the attained dominant multiplier passes the Krawczyk test (a multiple root, or
    /// roots too close for the declared precision), or the disk's modulus disagrees with the growth
    /// enclosure: a collision.
    Collision,
    /// A multiplier other than the dominant one and its conjugate lies at or outside the dominant's
    /// modulus lower bound: a tie in modulus, where `max |μ|` is not differentiable.
    Tie,
    /// The adjugate at the multiplier has no row or column clear of zero, or `ℓᵀr` or `μ` is not
    /// clear of zero: the eigen-derivative's denominator is not certified.
    Defective,
}

/// [definition; agent-inferred, September 30] **A member's dominant multiplier, certified**
/// ([`dominant_multiplier`]): a disk holding exactly one simple multiplier (the upper one of a
/// conjugate pair), in the monodromy's own units; whether it is a conjugate pair (else real); and a
/// radius `inner` below its modulus that every other multiplier lies strictly inside.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DominantMultiplier {
    pub disk: Disk,
    pub pair: bool,
    pub inner: Rat,
}

/// [definition; agent-inferred, September 30] **A member's growth covector** (module header, "The
/// executed growth's covector"): the certified multiplier and, per crossing `t` of the turn, the
/// enclosures of `∂ log|μ| / ∂ Re z_t` and `∂ log|μ| / ∂ Im z_t`; or the typed refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemberCovector {
    Resolved {
        member: usize,
        multiplier: DominantMultiplier,
        covector: Vec<[ExactInterval; 2]>,
    },
    Unresolved {
        member: usize,
        refusal: CovectorRefusal,
    },
}

impl MemberCovector {
    /// The member.
    pub fn member(&self) -> usize {
        match self {
            Self::Resolved { member, .. } | Self::Unresolved { member, .. } => *member,
        }
    }

    /// **The covector on the ring's storage** (realified node order), each entry an enclosure:
    /// crossing `t` reads node `d − 1 − t` ([`turn`]). `None` when unresolved.
    pub fn storage(&self) -> Option<Vec<ExactInterval>> {
        let Self::Resolved { covector, .. } = self else {
            return None;
        };
        let nodes = covector.len();
        let mut storage = vec![ExactInterval::point(Rat::zero()); 2 * nodes];
        for (tick, [re, im]) in covector.iter().enumerate() {
            let node = nodes - 1 - tick;
            storage[2 * node] = re.clone();
            storage[2 * node + 1] = im.clone();
        }
        Some(storage)
    }
}

/// [definition; agent-inferred, September 30] **A turn's reading with the covectors of its active
/// members** ([`ReceivingBank::read_turn_covector`]): the reading, and one covector for every
/// member whose enclosure reaches the joint's lower end (the members that may attain
/// `max_m ρ_m`: the max comparison's active branches).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnCovector {
    pub reading: TurnReading,
    pub active: Vec<MemberCovector>,
}

/// [definition; agent-inferred, September 30] **The monodromy's variation along a move of the
/// crossing amplitudes, read two ways** ([`ReceivingBank::turn_variation`]): the monodromy `M`,
/// its variation `ΔM` accumulated forward (the dual product `(P, P′) ← (T P, ΔT P + T P′)`) and in
/// reverse (`Σ_t T_(>t) ΔT_t T_(<t)` from the prefix and suffix products); exact, and equal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnVariation {
    pub monodromy: ExactRatMatrix,
    pub forward: ExactRatMatrix,
    pub reverse: ExactRatMatrix,
}

/// [definition; agent-inferred, September 30] **The directional derivative of `log |μ|` along a move,
/// read three ways** ([`ReceivingBank::directional_routes`]): the covector paired with the move, the
/// eigen-pairing `Re(ℓᵀ ΔM r / (μ ℓᵀr))` on the exact variation, and the trace
/// `Re(tr(adj(μ − M) ΔM) / (μ χ′(μ)))`; three enclosures of one number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectionalRoutes {
    pub covector: ExactInterval,
    pub eigen: ExactInterval,
    pub trace: ExactInterval,
}

impl DirectionalRoutes {
    /// Whether the three enclosures share a point.
    pub fn agree(&self) -> bool {
        let lower = self
            .covector
            .lower
            .clone()
            .max(self.eigen.lower.clone())
            .max(self.trace.lower.clone());
        let upper = self
            .covector
            .upper
            .clone()
            .min(self.eigen.upper.clone())
            .min(self.trace.upper.clone());
        lower <= upper
    }
}

/// [proved-standard; implemented-exact] **The adjugate's coefficients**: `adj(νI − N) = Σ_k ν^k A_k`
/// for `det(νI − N) = Σ_k c_k ν^k` (monic), `A_(n−1) = I`, `A_(k−1) = N A_k + c_k I`, on integers;
/// `N A_0 + c_0 I = 0` closes the recurrence (Cayley–Hamilton), checked.
fn adjugate_coefficients(
    product: &[Vec<BigInt>],
    characteristic: &[BigInt],
) -> Option<Vec<Vec<Vec<BigInt>>>> {
    let n = product.len();
    let identity: Vec<Vec<BigInt>> = (0..n)
        .map(|i| (0..n).map(|j| BigInt::from(u8::from(i == j))).collect())
        .collect();
    let mut coefficients = vec![identity; n];
    for k in (1..n).rev() {
        let mut next = integer_product(product, &coefficients[k]);
        for (i, row) in next.iter_mut().enumerate() {
            row[i] += &characteristic[k];
        }
        coefficients[k - 1] = next;
    }
    let mut closing = integer_product(product, &coefficients[0]);
    for (i, row) in closing.iter_mut().enumerate() {
        row[i] += &characteristic[0];
    }
    closing
        .iter()
        .all(|row| row.iter().all(Zero::is_zero))
        .then_some(coefficients)
}

/// [definition; agent-inferred, September 30] **The dominant multiplier of `M = N/Δ`, certified**
/// (module header, "The executed growth's covector"), from the integer coefficients of
/// `det(νI − N)` (ascending, monic), the scale `Δ` and the growth enclosure:
/// - in the chart `μ = σs`, `σ = 2^e` the least power of two above the growth's upper end, the
///   monic `p(s) = χ_M(σs)/σ^n` has every root in the unit disc; its coefficients
///   `c_k/(Δσ)^(n−k)` are held as disks by one division each ([`quotient`]);
/// - every root is attained ([`attained_roots`]) and isolated by the Krawczyk test ([`isolate`]):
///   on the real axis when its attained point is (its disk symmetric, its root real), else off it;
///   when the `n` disks are pairwise disjoint they hold the `n` roots, each simple;
/// - the dominant disk (the largest center) is real, or disjoint from its conjugate with exactly
///   one other disk (its conjugate partner) meeting its conjugate: a conjugate pair;
/// - every other disk lies strictly inside `inner`, the dominant's modulus lower bound less a
///   relative `2^(−SEPARATION_BITS)`: no other multiplier ties it in modulus.
///
/// When not every root is isolated (a small root the precision does not reach), the dominant one
/// alone is isolated and the placement at `inner` counts the multipliers at or outside it exactly
/// ([`Floquet::placement`]'s law), one (real) or two (the pair). Otherwise refused:
/// [`CovectorRefusal::Collision`] (no disk, overlapping disks, an ambiguous partner) or
/// [`CovectorRefusal::Tie`] (another multiplier at the dominant's modulus).
pub fn dominant_multiplier(
    characteristic: &[BigInt],
    scale: &BigInt,
    growth: &Growth,
) -> Result<Result<DominantMultiplier, CovectorRefusal>, HnnError> {
    let n = characteristic.len() - 1;
    let exponent = crate::ratio::disk::floor_log2(&growth.upper) + 1;
    let sigma = power_of_two(exponent);
    // p_k = c_k / (Δ^(n−k) 2^(e(n−k))), each by one division.
    let mut disks = vec![Disk::real(Rat::zero()); n + 1];
    let mut power = BigInt::one();
    for k in (0..=n).rev() {
        disks[k] = quotient(
            &characteristic[k],
            &power,
            exponent * (n - k) as i64,
            COVECTOR_BITS,
        );
        power *= scale;
    }
    let centers: Vec<GaussianRat> = disks.iter().map(|d| d.center.clone()).collect();
    let attained = attained_roots(&centers, ROOT_ATTAINMENT_BITS, ATTAINMENT_ITERATIONS);
    if attained.len() != n {
        return Ok(Err(CovectorRefusal::Collision));
    }
    let near_real = |z: &GaussianRat| -> bool {
        let grain = root_upper(&z.norm_sq())
            * Rat::new(BigInt::one(), BigInt::one() << (ROOT_ATTAINMENT_BITS / 2) as usize);
        z.im.abs() <= grain
    };
    let isolated: Vec<Option<Disk>> = attained
        .iter()
        .map(|z| {
            if near_real(z) {
                isolate(&disks, z, true, COVECTOR_BITS)
                    .or_else(|| isolate(&disks, z, false, COVECTOR_BITS))
            } else {
                isolate(&disks, z, false, COVECTOR_BITS)
            }
        })
        .collect();
    let dominant = (0..n)
        .max_by(|&a, &b| attained[a].norm_sq().cmp(&attained[b].norm_sq()))
        .expect("a root");
    let Some(mut disk) = isolated[dominant].clone() else {
        return Ok(Err(CovectorRefusal::Collision));
    };
    let mut pair = !disk.center.is_real();
    if pair {
        if disk.center.im.is_negative() {
            disk = disk.conj();
        }
        if !disk.disjoint(&disk.conj()) {
            return Ok(Err(CovectorRefusal::Collision));
        }
    }
    let inner_s = disk.modulus_lower();
    if !inner_s.is_positive() {
        return Ok(Err(CovectorRefusal::Collision));
    }
    let shrink = Rat::one() - Rat::new(BigInt::one(), BigInt::one() << SEPARATION_BITS as usize);
    let inner = crate::holon::deposition::significant(
        &(&inner_s * &sigma * shrink),
        SEPARATION_BITS,
        false,
    );
    let inner_chart = &inner / &sigma;
    let every = isolated.iter().all(Option::is_some)
        && (0..n).all(|i| {
            ((i + 1)..n).all(|j| {
                isolated[i]
                    .as_ref()
                    .zip(isolated[j].as_ref())
                    .is_some_and(|(a, b)| a.disjoint(b))
            })
        });
    if every {
        // Every root in its own disk: the conjugate partner is the one disk meeting the dominant's
        // conjugate; every other disk must lie strictly inside `inner`.
        let conjugate = isolated[dominant].as_ref().expect("isolated").conj();
        let partners: Vec<usize> = (0..n)
            .filter(|&j| j != dominant)
            .filter(|&j| {
                !isolated[j]
                    .as_ref()
                    .expect("isolated")
                    .disjoint(&conjugate)
            })
            .collect();
        if pair && partners.len() != 1 {
            return Ok(Err(CovectorRefusal::Collision));
        }
        if !pair && !partners.is_empty() {
            // A real dominant root's conjugate is itself.
            return Ok(Err(CovectorRefusal::Collision));
        }
        for j in (0..n).filter(|&j| j != dominant && !partners.contains(&j)) {
            if isolated[j].as_ref().expect("isolated").modulus_upper() >= inner_chart {
                return Ok(Err(CovectorRefusal::Tie));
            }
        }
    } else {
        // The exact count at `inner` (the slower route, read only where the precision does not
        // isolate every root).
        let rational = RationalPolynomial::new(
            (0..=n)
                .map(|k| {
                    Rat::from_integer(characteristic[k].clone())
                        / Rat::from_integer(scale.pow((n - k) as u32))
                })
                .collect(),
        );
        let placed = match placement_of(&rational, n, &inner) {
            Ok(placed) => placed,
            // A multiplier on or too near the separation circle for the exact count: a tie there.
            Err(HnnError::Polynomial(_)) => return Ok(Err(CovectorRefusal::Tie)),
            Err(error) => return Err(error),
        };
        let expected = if pair { 2 } else { 1 };
        let reached = placed.outside + placed.on;
        if reached > expected {
            return Ok(Err(CovectorRefusal::Tie));
        }
        if reached < expected {
            return Ok(Err(CovectorRefusal::Collision));
        }
    }
    pair = pair && disk.disjoint(&disk.conj());
    let upper = disk.modulus_upper() * &sigma;
    if upper < growth.lower || inner > growth.upper {
        return Ok(Err(CovectorRefusal::Collision));
    }
    Ok(Ok(DominantMultiplier {
        disk: Disk::new(disk.center.scale(&sigma), &disk.radius * &sigma),
        pair,
        inner,
    }))
}

/// `2^e`.
fn power_of_two(exponent: i64) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << exponent as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-exponent) as usize)
    }
}

/// `T v` over disks, `T` exact.
fn apply_disks(matrix: &ExactRatMatrix, vector: &[Disk], transpose: bool) -> Vec<Disk> {
    let n = vector.len();
    (0..n)
        .map(|i| {
            let mut sum = Disk::real(Rat::zero());
            for (j, v) in vector.iter().enumerate() {
                let entry = if transpose {
                    matrix.get(j, i)
                } else {
                    matrix.get(i, j)
                }
                .expect("in range");
                if !entry.is_zero() {
                    sum = sum.add(&v.scale(entry, COVECTOR_BITS), COVECTOR_BITS);
                }
            }
            sum
        })
        .collect()
}

/// `uᵀ A v` over disks, `A` exact.
fn bilinear_disks(left: &[Disk], matrix: &ExactRatMatrix, right: &[Disk]) -> Disk {
    let moved = apply_disks(matrix, right, false);
    let mut sum = Disk::real(Rat::zero());
    for (l, m) in left.iter().zip(&moved) {
        sum = sum.add(&l.mul(m, COVECTOR_BITS), COVECTOR_BITS);
    }
    sum
}

/// The eigen data of a certified multiplier: `adj(μ − M)` over disks (as the scaled
/// `adj(ν − N)/(Δσ)^(n−1)`), its chosen column `r` and row `ℓ`, and `p′(s)` at the multiplier in the
/// chart `μ = σs`.
struct EigenDisks {
    adjugate: Vec<Vec<Disk>>,
    right: Vec<Disk>,
    left: Vec<Disk>,
    slope: Disk,
    multiplier: Disk,
}

impl EigenDisks {
    fn of(
        product: &[Vec<BigInt>],
        characteristic: &[BigInt],
        scale: &BigInt,
        multiplier: &DominantMultiplier,
        growth: &Growth,
    ) -> Result<Option<Self>, HnnError> {
        let n = product.len();
        let Some(coefficients) = adjugate_coefficients(product, characteristic) else {
            return Ok(None);
        };
        let exponent = crate::ratio::disk::floor_log2(&growth.upper) + 1;
        let sigma = power_of_two(exponent);
        let s = Disk::new(
            multiplier.disk.center.scale(&(Rat::one() / &sigma)),
            &multiplier.disk.radius / &sigma,
        );
        // B(s) = Σ_k s^k (Δσ)^(k − (n − 1)) A_k by Horner over k, each entry of A_k held by one
        // division by Δ^(n − 1 − k).
        let powers: Vec<BigInt> = (0..n).map(|k| scale.pow(k as u32)).collect();
        let mut adjugate = vec![vec![Disk::real(Rat::zero()); n]; n];
        for k in (0..n).rev() {
            let depth = n - 1 - k;
            for i in 0..n {
                for j in 0..n {
                    let term = quotient(
                        &coefficients[k][i][j],
                        &powers[depth],
                        exponent * depth as i64,
                        COVECTOR_BITS,
                    );
                    adjugate[i][j] = adjugate[i][j].mul(&s, COVECTOR_BITS).add(&term, COVECTOR_BITS);
                }
            }
        }
        let size = |v: &[Disk]| -> Rat { v.iter().map(|d| d.center.norm_sq()).sum() };
        let column = (0..n)
            .max_by(|&a, &b| {
                let ca: Vec<Disk> = (0..n).map(|i| adjugate[i][a].clone()).collect();
                let cb: Vec<Disk> = (0..n).map(|i| adjugate[i][b].clone()).collect();
                size(&ca).cmp(&size(&cb))
            })
            .expect("a column");
        let row = (0..n)
            .max_by(|&a, &b| size(&adjugate[a]).cmp(&size(&adjugate[b])))
            .expect("a row");
        let right: Vec<Disk> = (0..n).map(|i| adjugate[i][column].clone()).collect();
        let left = adjugate[row].clone();
        if !right.iter().any(Disk::excludes_zero) || !left.iter().any(Disk::excludes_zero) {
            return Ok(None);
        }
        // p′(s) in the chart: Σ k p_k s^(k−1), p_k = c_k/(Δσ)^(n−k).
        let mut slope = Disk::real(Rat::zero());
        let mut power = BigInt::one();
        let mut terms = vec![Disk::real(Rat::zero()); n + 1];
        for k in (1..=n).rev() {
            terms[k] = quotient(
                &(&characteristic[k] * BigInt::from(k)),
                &power,
                exponent * (n - k) as i64,
                COVECTOR_BITS,
            );
            power *= scale;
        }
        for term in terms.iter().skip(1).rev() {
            slope = slope.mul(&s, COVECTOR_BITS).add(term, COVECTOR_BITS);
        }
        Ok(Some(Self {
            adjugate,
            right,
            left,
            slope,
            multiplier: multiplier.disk.clone(),
        }))
    }

    /// `ℓᵀr · μ`, the eigen-derivative's denominator, or `None` when it is not clear of zero.
    fn denominator(&self) -> Option<Disk> {
        let mut pairing = Disk::real(Rat::zero());
        for (l, r) in self.left.iter().zip(&self.right) {
            pairing = pairing.add(&l.mul(r, COVECTOR_BITS), COVECTOR_BITS);
        }
        let denominator = pairing.mul(&self.multiplier, COVECTOR_BITS);
        denominator.excludes_zero().then_some(denominator)
    }
}

impl ReceivingBank {
    /// **One crossing's executed tick map and its derivatives** in the crossing amplitude's two
    /// coordinates (module header, "The executed growth's covector"): with the carrier
    /// `c = w z`, `w = a² s^t`, the node block `−2pR(c)` is linear in `z`, so
    /// `∂K_t/∂Re z = −2pR(w)`, `∂K_t/∂Im z = −2pR(iw)` on every node; the operator moves by
    /// `ΔM = (h²/2)ΔK`, the executed solve by `ΔX = −X ΔM X` (the solve's derivative), and the tick
    /// `T = [[I − h²XK, 2hXC], [−2hXK, 4XC − I]]` by
    /// `ΔT = [[−h²(ΔX K + X ΔK), 2h ΔX C], [−2h(ΔX K + X ΔK), 4 ΔX C]]`.
    fn crossing_variation(
        &self,
        member: usize,
        amplitude: &GaussianRat,
        tick: usize,
    ) -> Result<(ExactRatMatrix, [ExactRatMatrix; 2]), HnnError> {
        let pump = &self.pumps[member];
        let carrier = pump.carrier(tick % pump.phases()).as_gaussian();
        let (capacity, stiffness, _) = self.material.forms();
        let pumped = stiffened(stiffness, &pump_block(pump.strength(), &carrier.mul(amplitude)))?;
        if !self.material.signed_form_holds(&pumped, &self.hop)? {
            return Err(HnnError::UncertifiedResonator {
                ring: member,
                phase: tick,
            });
        }
        let phase = Phase::of(
            member,
            &self.material,
            pumped,
            &self.admittance,
            &self.hop,
            None,
            tick,
        )?;
        let solve = phase.solve.matrix()?;
        let map = tick_map(&solve, capacity, &phase.stiffness, &self.hop)?;
        let n = capacity.rows();
        let zero = ExactRatMatrix::zero(n, n)?;
        let h = &self.hop;
        let half_square = h * h / integer(2);
        let variations = [carrier.clone(), carrier.mul(&GaussianRat::i())].map(|direction| {
            let d_stiffness = stiffened(&zero, &pump_block(pump.strength(), &direction))?;
            let d_operator = d_stiffness.scaled(&half_square);
            let d_solve = solve
                .multiply(&d_operator)?
                .multiply(&solve)?
                .scaled(&integer(-1));
            let d_solved_stiffness = d_solve
                .multiply(&phase.stiffness)?
                .add(&solve.multiply(&d_stiffness)?)?;
            let d_solved_capacity = d_solve.multiply(capacity)?;
            let blocks = [
                d_solved_stiffness.scaled(&(-(h * h))),
                d_solved_capacity.scaled(&(integer(2) * h)),
                d_solved_stiffness.scaled(&(integer(-2) * h)),
                d_solved_capacity.scaled(&integer(4)),
            ];
            Ok::<ExactRatMatrix, HnnError>(ExactRatMatrix::shaped(
                2 * n,
                2 * n,
                (0..2 * n)
                    .map(|i| {
                        (0..2 * n)
                            .map(|j| {
                                blocks[2 * (i / n) + j / n]
                                    .get(i % n, j % n)
                                    .expect("in range")
                                    .clone()
                            })
                            .collect()
                    })
                    .collect(),
            )?)
        });
        let [re, im] = variations;
        Ok((map, [re?, im?]))
    }

    /// **Whether every crossing of a turn is admissible** for every member: each tick's pumped
    /// stiffness passes the signed form `2C + hD + (h²/2)K_t ⪰ 0` ([`ReceivingBank::read_turn`]
    /// refuses a turn that does not), read without solving a tick.
    pub fn admits(&self, amplitudes: &[GaussianRat]) -> Result<bool, HnnError> {
        let (_, stiffness, _) = self.material.forms();
        for pump in &self.pumps {
            for (tick, amplitude) in amplitudes.iter().enumerate() {
                let carrier = pump.carrier(tick % pump.phases()).as_gaussian().mul(amplitude);
                let pumped = stiffened(stiffness, &pump_block(pump.strength(), &carrier))?;
                if !self.material.signed_form_holds(&pumped, &self.hop)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Every member's turn (its maps, the integer product and scale), its characteristic
    /// polynomial and its growth enclosure.
    #[allow(clippy::type_complexity)]
    fn members_turn(
        &self,
        amplitudes: &[GaussianRat],
        grain: u32,
    ) -> Result<Vec<(Vec<ExactRatMatrix>, Vec<Vec<BigInt>>, BigInt, Vec<BigInt>, Growth)>, HnnError>
    {
        (0..self.pumps.len())
            .map(|member| {
                let (maps, product, scale) = self.turn_monodromy(member, amplitudes)?;
                let characteristic = integer_characteristic(&product);
                let growth = growth_of(&characteristic, &scale, grain);
                Ok((maps, product, scale, characteristic, growth))
            })
            .collect()
    }

    /// [proved-derived; implemented-exact] **The turn's reading with its active members' growth
    /// covectors** (module header, "The executed growth's covector"). The reading is
    /// [`ReceivingBank::read_turn`]'s. A member is active when its enclosure reaches the joint's
    /// lower end (`upper_m ≥ lower_joint`: it may attain the largest growth). For each active
    /// member, its dominant multiplier is certified ([`dominant_multiplier`]); its eigenvectors are
    /// a column `r` and a row `ℓ` of `adj(μ − M)` over disks; the forward vectors
    /// `f_t = T_(t−1)⋯T_0 r` and backward `b_t = (T_(T−1)⋯T_(t+1))ᵀ ℓ` pass through the executed
    /// ticks; and crossing `t`'s entries are `Re(b_tᵀ ∂T_t f_t / (μ ℓᵀr))` in each coordinate, the
    /// simple root's eigen-derivative `D log|μ|[ΔM] = Re(ℓᵀ ΔM r / (μ ℓᵀ r))` with
    /// `ΔM = Σ_t T_(>t) ΔT_t T_(<t)`. The operands are the turn's own and transient; nothing is
    /// retained.
    pub fn read_turn_covector(
        &self,
        amplitudes: &[GaussianRat],
        grain: u32,
    ) -> Result<TurnCovector, HnnError> {
        let turns = self.members_turn(amplitudes, grain)?;
        let members: Vec<Growth> = turns.iter().map(|turn| turn.4.clone()).collect();
        let joint = joint_of(&members);
        let reading = TurnReading { members, joint };
        let active = (0..self.pumps.len())
            .filter(|&member| reading.members[member].upper >= reading.joint.lower)
            .map(|member| {
                let (maps, product, scale, characteristic, growth) = &turns[member];
                self.member_covector(member, amplitudes, maps, product, scale, characteristic, growth)
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(TurnCovector { reading, active })
    }

    /// One crossing's operands over disks: the executed solve `X_t` and the pumped stiffness `K_t`,
    /// and the stiffness's derivatives in the amplitude's two coordinates (`−2pR(w)`, `−2pR(iw)` on
    /// every node, `w = a² s^t`).
    fn crossing_disks(
        &self,
        member: usize,
        amplitude: &GaussianRat,
        tick: usize,
    ) -> Result<[Vec<Vec<DyadicDisk>>; 4], HnnError> {
        let pump = &self.pumps[member];
        let carrier = pump.carrier(tick % pump.phases()).as_gaussian();
        let (_, stiffness, _) = self.material.forms();
        let pumped = stiffened(stiffness, &pump_block(pump.strength(), &carrier.mul(amplitude)))?;
        if !self.material.signed_form_holds(&pumped, &self.hop)? {
            return Err(HnnError::UncertifiedResonator {
                ring: member,
                phase: tick,
            });
        }
        let phase = Phase::of(
            member,
            &self.material,
            pumped,
            &self.admittance,
            &self.hop,
            None,
            tick,
        )?;
        let n = stiffness.rows();
        let zero = ExactRatMatrix::zero(n, n)?;
        let disks = |matrix: &ExactRatMatrix| -> Vec<Vec<DyadicDisk>> {
            (0..n)
                .map(|i| {
                    (0..n)
                        .map(|j| {
                            DyadicDisk::real(matrix.get(i, j).expect("in range"), COVECTOR_BITS)
                        })
                        .collect()
                })
                .collect()
        };
        let d_re = stiffened(&zero, &pump_block(pump.strength(), &carrier))?;
        let d_im = stiffened(
            &zero,
            &pump_block(pump.strength(), &carrier.mul(&GaussianRat::i())),
        )?;
        Ok([
            disks(&phase.solve.matrix()?),
            disks(&phase.stiffness),
            disks(&d_re),
            disks(&d_im),
        ])
    }

    /// One active member's covector ([`ReceivingBank::read_turn_covector`]).
    ///
    /// [proved-derived; implemented-exact] **The passage by blocks.** With `C`, `K_t` and `X_t`
    /// symmetric (the material's forms are checked symmetric, the pump block is, so `M_t` and its
    /// solve are), the tick `T = [[I − h²XK, 2hXC], [−2hXK, 4XC − I]]` acts on `f = (f₁, f₂)` as
    /// `y = X(−h²Kf₁ + 2hCf₂)`, `Tf = (f₁ + y, −f₂ + (2/h)y)`, and its transpose on `b = (b₁, b₂)` as
    /// `u = h²b₁ + 2hb₂`, `a = Xu`, `Tᵀb = (b₁ − Ka, −b₂ + (2/h)Ca)`. Its variation
    /// `ΔT = [[−h²(ΔX K + X ΔK), 2h ΔX C], [−2h(ΔX K + X ΔK), 4 ΔX C]]` with `ΔX = −(h²/2) X ΔK X` pairs as
    /// `bᵀ ΔT f = aᵀ ΔK r`, `r = −y/2 − f₁`: expanding, `bᵀΔTf = −uᵀ(ΔX Kf₁ + X ΔK f₁) + (2/h)uᵀ ΔX Cf₂`,
    /// and `−uᵀΔX p = (h²/2)aᵀΔK Xp`, `uᵀXΔKf₁ = aᵀΔKf₁`, `(2/h)uᵀΔX q = −h aᵀΔK Xq` with `p = Kf₁`,
    /// `q = Cf₂`, so `bᵀΔTf = aᵀΔK(X((h²/2)p − hq) − f₁)` and `X((h²/2)p − hq) = −y/2`. So each
    /// crossing's entries are `Re(a_tᵀ ∂K r_t / (μ ℓᵀr))`.
    ///
    /// [definition; agent-inferred, September 30] **The passage runs on the exact tick maps**, held as
    /// dyadic disks ([`DyadicDisk`]), and the blocks read only each crossing's own `r_t` and `a_t`: a
    /// disk's radius grows by the absolute entries of what it passes through, and the blocks'
    /// absolute entries lose the cancellation inside `I − h²XK` (measured on a drawn turn of 60
    /// crossings: the passage by blocks widened the covector to an enclosure of width between 4 and 5, the
    /// passage by the maps to one below `2^(−56)`). Held to the exact variation, three ways, by the
    /// owner's tests (`hnn::tests::executed`).
    #[allow(clippy::too_many_arguments)]
    fn member_covector(
        &self,
        member: usize,
        amplitudes: &[GaussianRat],
        maps: &[ExactRatMatrix],
        product: &[Vec<BigInt>],
        scale: &BigInt,
        characteristic: &[BigInt],
        growth: &Growth,
    ) -> Result<MemberCovector, HnnError> {
        let multiplier = match dominant_multiplier(characteristic, scale, growth)? {
            Ok(multiplier) => multiplier,
            Err(refusal) => return Ok(MemberCovector::Unresolved { member, refusal }),
        };
        let refuse = |refusal| Ok(MemberCovector::Unresolved { member, refusal });
        let Some(eigen) = EigenDisks::of(product, characteristic, scale, &multiplier, growth)?
        else {
            return refuse(CovectorRefusal::Defective);
        };
        let Some(denominator) = eigen.denominator() else {
            return refuse(CovectorRefusal::Defective);
        };
        let Some(inverse) = denominator.inverse(COVECTOR_BITS) else {
            return refuse(CovectorRefusal::Defective);
        };
        let ticks = maps.len();
        let n = self.material.width();
        let (capacity, _, _) = self.material.forms();
        let capacity: Vec<Vec<DyadicDisk>> = (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| DyadicDisk::real(capacity.get(i, j).expect("in range"), COVECTOR_BITS))
                    .collect()
            })
            .collect();
        let h = &self.hop;
        let (h_square, twice_h) = (h * h, integer(2) * h);
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        let operands: Vec<[Vec<Vec<DyadicDisk>>; 4]> = (0..ticks)
            .map(|tick| self.crossing_disks(member, &amplitudes[tick], tick))
            .collect::<Result<_, HnnError>>()?;
        let apply = |matrix: &[Vec<DyadicDisk>], vector: &[DyadicDisk]| -> Vec<DyadicDisk> {
            matrix
                .iter()
                .map(|row| {
                    row.iter().zip(vector).fold(DyadicDisk::zero(), |sum, (m, v)| {
                        if m.is_zero() {
                            sum
                        } else {
                            sum.add(&m.mul(v, COVECTOR_BITS), COVECTOR_BITS)
                        }
                    })
                })
                .collect()
        };
        let combine =
            |a: &[DyadicDisk], x: &Rat, b: &[DyadicDisk], y: &Rat| -> Vec<DyadicDisk> {
                a.iter()
                    .zip(b)
                    .map(|(p, q)| {
                        p.scale(x, COVECTOR_BITS)
                            .add(&q.scale(y, COVECTOR_BITS), COVECTOR_BITS)
                    })
                    .collect()
            };
        let of = |v: &[Disk]| -> Vec<DyadicDisk> {
            v.iter().map(|d| DyadicDisk::of(d, COVECTOR_BITS)).collect()
        };
        let inverse = DyadicDisk::of(&inverse, COVECTOR_BITS);
        // The passage itself through each exact tick map (its entries' own cancellations kept, so
        // a disk's radius grows by the map's absolute entries, not by its blocks'); the blocks read
        // only each crossing's own terms.
        let map_disks: Vec<Vec<Vec<DyadicDisk>>> = maps
            .iter()
            .map(|map| {
                (0..2 * n)
                    .map(|i| {
                        (0..2 * n)
                            .map(|j| DyadicDisk::real(map.get(i, j).expect("in range"), COVECTOR_BITS))
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let transposed = |matrix: &[Vec<DyadicDisk>]| -> Vec<Vec<DyadicDisk>> {
            (0..matrix.len())
                .map(|j| matrix.iter().map(|row| row[j].clone()).collect())
                .collect()
        };
        // Forward: r_t = −y_t/2 − f₁ at each crossing, y_t = X_t(−h²K_t f₁ + 2hC f₂).
        let mut residues = Vec::with_capacity(ticks);
        let mut vector = of(&eigen.right);
        for ([solve, stiffness, _, _], map) in operands.iter().zip(&map_disks) {
            let (first, second) = vector.split_at(n);
            let pushed = apply(stiffness, first);
            let stored = apply(&capacity, second);
            let y = apply(solve, &combine(&pushed, &-h_square.clone(), &stored, &twice_h));
            residues.push(combine(&y, &-half.clone(), first, &-Rat::one()));
            vector = apply(map, &vector);
        }
        // Backward: a_t = X_t u_t at each crossing, u_t = h²b₁ + 2hb₂.
        let mut lifts = vec![Vec::new(); ticks];
        let mut vector = of(&eigen.left);
        for tick in (0..ticks).rev() {
            let [solve, _, _, _] = &operands[tick];
            let (first, second) = vector.split_at(n);
            let u = combine(first, &h_square, second, &twice_h);
            lifts[tick] = apply(solve, &u);
            vector = apply(&transposed(&map_disks[tick]), &vector);
        }
        let covector = (0..ticks)
            .map(|tick| {
                let [_, _, d_re, d_im] = &operands[tick];
                [d_re, d_im].map(|variation| {
                    let moved = apply(variation, &residues[tick]);
                    lifts[tick]
                        .iter()
                        .zip(&moved)
                        .fold(DyadicDisk::zero(), |sum, (a, m)| {
                            sum.add(&a.mul(m, COVECTOR_BITS), COVECTOR_BITS)
                        })
                        .mul(&inverse, COVECTOR_BITS)
                        .disk()
                        .real_part()
                })
            })
            .collect();
        Ok(MemberCovector::Resolved {
            member,
            multiplier,
            covector,
        })
    }

    /// Each crossing's variation along a move `δ` of the amplitudes:
    /// `ΔT_t = ∂T_t/∂Re z · Re δ_t + ∂T_t/∂Im z · Im δ_t`.
    fn crossing_moves(
        &self,
        member: usize,
        amplitudes: &[GaussianRat],
        direction: &[GaussianRat],
    ) -> Result<(Vec<ExactRatMatrix>, Vec<ExactRatMatrix>), HnnError> {
        let mut maps = Vec::with_capacity(amplitudes.len());
        let mut moves = Vec::with_capacity(amplitudes.len());
        for (tick, (amplitude, delta)) in amplitudes.iter().zip(direction).enumerate() {
            let (map, [re, im]) = self.crossing_variation(member, amplitude, tick)?;
            moves.push(re.scaled(&delta.re).add(&im.scaled(&delta.im))?);
            maps.push(map);
        }
        Ok((maps, moves))
    }

    /// [proved-derived; implemented-exact] **The monodromy's variation, forward and in reverse**
    /// ([`TurnVariation`]): exact, and equal by the product rule.
    pub fn turn_variation(
        &self,
        member: usize,
        amplitudes: &[GaussianRat],
        direction: &[GaussianRat],
    ) -> Result<TurnVariation, HnnError> {
        let (maps, moves) = self.crossing_moves(member, amplitudes, direction)?;
        let n = 2 * self.material.width();
        let identity = ExactRatMatrix::identity(n)?;
        let (mut product, mut tangent) = (identity.clone(), ExactRatMatrix::zero(n, n)?);
        for (map, moved) in maps.iter().zip(&moves) {
            tangent = moved.multiply(&product)?.add(&map.multiply(&tangent)?)?;
            product = map.multiply(&product)?;
        }
        let ticks = maps.len();
        let mut prefix = vec![identity.clone(); ticks + 1];
        for tick in 0..ticks {
            prefix[tick + 1] = maps[tick].multiply(&prefix[tick])?;
        }
        let mut suffix = vec![identity; ticks + 1];
        for tick in (0..ticks).rev() {
            suffix[tick] = suffix[tick + 1].multiply(&maps[tick])?;
        }
        let mut reverse = ExactRatMatrix::zero(n, n)?;
        for tick in 0..ticks {
            reverse = reverse.add(
                &suffix[tick + 1]
                    .multiply(&moves[tick])?
                    .multiply(&prefix[tick])?,
            )?;
        }
        Ok(TurnVariation {
            monodromy: product,
            forward: tangent,
            reverse,
        })
    }

    /// [proved-derived; implemented-exact] **The directional derivative of a member's `log |μ|`
    /// along a move `δ`, three ways** ([`DirectionalRoutes`]): the covector paired with `δ`
    /// (`Σ_t` of its enclosures times `Re δ_t`, `Im δ_t`), the eigen-pairing on the exact forward
    /// variation, and the trace of the adjugate against it over `μ p′`; `None` when the member's
    /// covector is refused.
    pub fn directional_routes(
        &self,
        member: usize,
        amplitudes: &[GaussianRat],
        direction: &[GaussianRat],
        grain: u32,
    ) -> Result<Option<DirectionalRoutes>, HnnError> {
        let (maps, product, scale) = self.turn_monodromy(member, amplitudes)?;
        let characteristic = integer_characteristic(&product);
        let growth = growth_of(&characteristic, &scale, grain);
        let MemberCovector::Resolved {
            multiplier,
            covector,
            ..
        } = self.member_covector(
            member,
            amplitudes,
            &maps,
            &product,
            &scale,
            &characteristic,
            &growth,
        )?
        else {
            return Ok(None);
        };
        let mut paired = ExactInterval::point(Rat::zero());
        for ([re, im], delta) in covector.iter().zip(direction) {
            for (entry, coordinate) in [(re, &delta.re), (im, &delta.im)] {
                let (a, b) = (&entry.lower * coordinate, &entry.upper * coordinate);
                paired = ExactInterval {
                    lower: &paired.lower + a.clone().min(b.clone()),
                    upper: &paired.upper + a.max(b),
                };
            }
        }
        let variation = self.turn_variation(member, amplitudes, direction)?.forward;
        let Some(eigen) = EigenDisks::of(&product, &characteristic, &scale, &multiplier, &growth)?
        else {
            return Ok(None);
        };
        let Some(denominator) = eigen.denominator() else {
            return Ok(None);
        };
        let eigen_route = bilinear_disks(&eigen.left, &variation, &eigen.right)
            .div(&denominator, COVECTOR_BITS)
            .map(|d| d.real_part());
        // tr(adj(μ − M) ΔM)/(μ χ′(μ)) = tr(B ΔM)/(μ p′(s)) in the chart (module header).
        let n = variation.rows();
        let mut trace = Disk::real(Rat::zero());
        for i in 0..n {
            for j in 0..n {
                let entry = variation.get(j, i)?;
                if !entry.is_zero() {
                    trace = trace.add(&eigen.adjugate[i][j].scale(entry, COVECTOR_BITS), COVECTOR_BITS);
                }
            }
        }
        let trace_route = eigen
            .slope
            .mul(&multiplier.disk, COVECTOR_BITS)
            .inverse(COVECTOR_BITS)
            .map(|inverse| trace.mul(&inverse, COVECTOR_BITS).real_part());
        let (Some(eigen_route), Some(trace_route)) = (eigen_route, trace_route) else {
            return Ok(None);
        };
        Ok(Some(DirectionalRoutes {
            covector: paired,
            eigen: eigen_route,
            trace: trace_route,
        }))
    }
}

/// The joint reading of the members' enclosures: the largest member's.
fn joint_of(members: &[Growth]) -> Growth {
    Growth {
        lower: members
            .iter()
            .map(|growth| growth.lower.clone())
            .max()
            .expect("a bank has a member"),
        upper: members
            .iter()
            .map(|growth| growth.upper.clone())
            .max()
            .expect("a bank has a member"),
    }
}

// -------------------------------------------------------------------------------------------
// the reference change at a junction port

/// [definition] **A junction port's reference change** (Lean `two_port_reference_balance`): the
/// reflection `Γ` and the power transmission fraction `T` of a wave arriving at the port. The
/// tests' reading of the executed Swing against it (no running consumer since batch H, September
/// 30: `propagation::Operands::port_scatterings` is the tests').
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PortScattering {
    pub reflection: Rat,
    pub transmission: Rat,
}

#[cfg(test)]
impl PortScattering {
    /// `Γ² + T = 1`.
    pub(crate) fn balances(&self) -> bool {
        &self.reflection * &self.reflection + &self.transmission == Rat::one()
    }
}

/// **The reference change at port `port` of a junction** (module header): port 0 is the ring's
/// storage port (admittance `Y`), port `1 + i` the `i`-th incident contact (conductance `G_i`). The
/// rest of the junction is one reference `G_rest = W − G_p`.
#[cfg(test)]
pub(crate) fn port_scattering(
    admittance: &Rat,
    conductances: &[&Rat],
    port: usize,
) -> Result<PortScattering, HnnError> {
    let total = conductances
        .iter()
        .fold(admittance.clone(), |sum, g| sum + *g);
    let own = if port == 0 {
        admittance.clone()
    } else {
        conductances
            .get(port - 1)
            .map(|g| (*g).clone())
            .ok_or(HnnError::Shape {
                what: "a junction port (the storage port, then each contact)",
                expected: conductances.len() + 1,
                found: port,
            })?
    };
    let rest = &total - &own;
    if !own.is_positive() || !rest.is_positive() {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let sum = &own + &rest;
    Ok(PortScattering {
        reflection: (&own - &rest) / &sum,
        transmission: integer(4) * &own * &rest / (&sum * &sum),
    })
}
