//! **The constitution `Θ`: its one owner, per locus and factored, and its deposition.**
//!
//! [definition] `Θ` is the medium (design (a), "The one object"). [`Constitution`] is its one owner:
//! every learned map, the standings `q` included, a commit counter and the bit budget `B_Θ`; every
//! locus's step, a normal law's and a factor family's alike, is certified at each deposit ("The
//! certified step" below). Its fields are private; only [`Constitution::deposited`] (the
//! successor of a staged deposit) and the collapse at an aeon boundary change it (guard 4). It holds
//! the current parameters and their normal statistics, and no list of deposits, updates, gradients
//! or producers. The guarantee is structural, the struct's own private fields; the doctest shows
//! only that no field named `deposits` exists (`E0609`, no such field), and the runtime guard
//! (`tests/guards.rs`, guard 4) reads the loci and statistics after deposits:
//!
//! ```compile_fail,E0609
//! use holonics::hnn::Constitution;
//! // No journal by that name: a constitution has no `deposits` field (guard 4).
//! fn replay(theta: &Constitution) -> usize {
//!     theta.deposits.len()
//! }
//! ```
//!
//! [definition] **Loci** ([`Locus`]). Per ring `g`: its element (the passive factor `f_g` with
//! `W_s,g = −f_g f_gᵀ`, the contrast port `W_c,g`, the skew slices `A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ`), its
//! standing `q_g`, on a source ring its source ports (`E_g` and the factored pair port `E_g^(δ)`),
//! on a receiving ring its receiving map `R` and the receiving parametron's landmark tree
//! (the landmark tree, `compression::landmark::context::Landmarks`), both at the receiving locus. Per contact `a`: its channel's
//! square factors (`C_a = c_a c_aᵀ`, `K_a = b_a b_aᵀ`, `D_a = F_a F_aᵀ`). The junction admittance `Y_g` and the
//! contact conductance `G_a` (`Y_a`, `β_a`, the screws) are declared on the field in campaign 1; the
//! collapse names them as loci, but they carry no learned value.
//!
//! [definition] **Deposition** (design (a), `deposit`; Lean `HNN/Normal`), the exact update `Δ` of
//! each locus at the predecessor's lattice-valued operands:
//!
//! ```text
//! ΔH_U = Σ_t w f_t f_tᵀ ,            ΔW_U = η_U Σ_t w g_t (H_U'⁻¹ f_t)ᵀ ,  H_U' the carried successor Gram    per linear locus (E_g, R, W_c)
//! Δh_x = Σ_t w |f_t|² ,              Δx = η_x G_x / h_x' ,                 h_x' the carried successor statistic  per factor family
//! n_s(t) += 1, β_s ← β_s k_s(t)/q    per reached comparison, on the path its address a opens (target t)       the landmark tree
//! ```
//!
//! [definition; agent-inferred, September 29] **The certified step** (the
//! [lessons record](../../../../research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
//! lesson 6; `holon::deposition::CertifiedStep`; Lean `Holon/Deposition.{certified_step_descends,
//! gauss_newton_curvature, joint_cauchy_schwarz}`, `HNN/Normal.certified_normal_step`). The declared
//! step `γ_U = 1` is retired: it moved a locus by the whole covector reaching it, which sums every
//! station and every re-entry of the source times the readout's gain, and at `K = 4` it overshot
//! (the source port's entries 1, 6, 26, 316). A normal law prepares its **unit step**
//! `D = Σ_t w g_t (X̂ f_t)ᵀ` ([`NormalLaw::prepare`]), and the deposit reads, per linear locus:
//!
//! ```text
//! a = Σ_t w ⟨g_t, D f_t⟩            the unit step's first-order decrease, checked ≥ 0 (descent after pullback and chart)
//! b = Σ_t w |D f_t|²                its feature moves
//! C = s · κ² · b                    its own curvature along the ray, s = ½
//! c = max_t |w g_t|_∞               the lattice's covector scale
//! η = the largest 2^k with η C ≤ a and η c ≤ 1, then the joint moves   (holon::deposition::{CertifiedStep, JointReading})
//! ```
//!
//! `s = ½` bounds the station score's curvature in its realified logits: the magnitude part is a
//! base-two softmax, whose Hessian is `ln 2 (diag p − p pᵀ) ⪯ (ln 2 / 2) I ⪯ ½ I`, and the phase part
//! `½ q_t Δ²` in `Δ = φ^T − Im f_t / 2` has curvature `q_t / 4 ≤ ¼` (`hnn::ratio`). `κ²` is the
//! certified gain from the locus's output to the stacked station logits, read from the deposit's
//! [`Reach`] and the medium's energy law ([`Constitution::amplitude`]): the receiving map's certified
//! spectral bound `‖R‖₂²` ("The tightened certificate" below), the admittances `Y`, and the per-tick
//! amplitude growth `1 + ω` of the word, `ω` the contrast ports' certified bound
//! (`holon::deposition::active_growth`):
//!
//! ```text
//! R_g      κ² = 1                                                   each sample one station's logits
//! E_g      κ² = d · ‖R‖² · (Y_g/Y_R) · Σ_j (Σ_(n: T_n ≤ T_j) (1+ω)^(T_j − T_n))²      d phases, re-entries T_n, stations T_j
//! W_c,r    κ² = ‖R‖² · (Y_r/Y_R) · Σ_j Σ_(τ < T_j) (1+ω)^(2(T_j − τ − 1))               every tick the port acts at
//! ```
//!
//! A station's anchor is the junction's participation mean, so `|v_R|² ≤ (4/h)P/Y_R` for the power
//! `P` its change carries; an injection `δs` at ring `g` carries `(h/4)Y_g|δs|²`, an element output
//! the same at its ring; each passive tick keeps the power and a contrast port's tick multiplies it
//! by at most `(1 + ω)²`. The gains are read at the end of each ray (the triangle on the norms,
//! `‖R + ηD‖₂ ≤ ‖R‖₂ + η‖D‖₂`, `‖W + ηD‖₁ ≤ ‖W‖₁ + η‖D‖₁`), so a step that raises another locus's
//! gain is halved until every certificate holds at its own ray (the projection;
//! [`Constitution::deposited`]). The
//! gains read the medium passive but for the contrast ports, whose growth `(1 + ω)²` they carry,
//! and the resonators not certified passive, whose growth is their Floquet reach ("The pumped
//! medium's reach", below); a declared boost's signed stiffness stores indefinite energy, so no step
//! is certified through it ([`HnnError::ActiveContact`]).
//!
//! [definition; agent-inferred, September 29] **The pumped medium's reach** (the
//! [parametron's record](../../../../research/records/2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md)
//! §1.8, its consumer equation; the
//! [reach's record](../../../../research/records/2026-09-29_THE_CERTIFIED_STEP_READS_THE_FLOQUET_REACH_PINNED_BEFORE_ITS_RUNS.md);
//! Lean `HNN/Floquet.{floquet_span_reach, partial_period_le_pow}`, `Holon/Deposition` §10). A
//! resonator is **certified passive** when it is unpumped and its stiffness `K ⪰ 0` by exact
//! inertia (`C, D ⪰ 0` by declaration): its tick keeps or dissipates `diag(K, C)`. Any other (a pump,
//! or a signed stiffness) is read by its Floquet monodromy over its pump's period on the exact law
//! (`hnn::ring::Floquet`), decided at its resonator lattice's grain `2^(−g)`, and bounded
//! (`hnn::ring::FloquetBound::reach`): a span of `s` ticks from any pump phase carries the ring's
//! state energy by at most
//!
//! ```text
//! reach_r(s) = (γ_hi/γ_lo) · max_(0 ≤ o < T) ρ^(2m_o) (max_t σ_t²)^(s − T m_o),   m_o = ⌊(s − o)/T⌋
//! ```
//!
//! with `G ≻ 0`, `M_TᵀGM_T ⪯ ρ²G`, `T_tᵀGT_t ⪯ σ_t²G` and `γ_lo I ⪯ G ⪯ γ_hi I` each decided by
//! inertia. The metric is attained by any means ([`RingReach`]): the ladder of growths
//! `ρ₀(1 + 2^k)`, `|k| ≤ g`, above the decided `ρ₀`, each attained by the exact Stein solve and
//! certified, climbed from `k = 0` toward the least reach at the longest span; each span's reach is
//! the least of the certified bounds'. [measured, the reach's record] The decided growth's own
//! metric is ill-conditioned near a multiplier on or near its circle (on the chain's edge rings
//! `γ_hi/γ_lo` lies between `2^16` and `2^17`), and the ladder lowers the reach at the longest span
//! by many binary orders there. The medium's **span factor** is
//! `F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)` over those rings (`holon::deposition::span_factors`,
//! Lean `pumped_span_factor`): a difference carried by several rings within a span of `s` ticks is
//! carried by each for at most `s`, and the running maximum does not fall. The consumer equation
//! enters every gain but the receiving map's (each sample one station's logits):
//!
//! ```text
//! E_g        κ² = d ‖R‖² (Y_g/Y_R) Σ_j (Σ_(n: T_n ≤ T_j) (1+ω)^(T_j − T_n))² F(T_j − min_n T_n)     (entry_span_gain)
//! W_c,r …    κ² = ‖R‖² (Y_r/Y_R) Σ_j Σ_(τ < T_j) (1+ω)^(2(T_j − τ − 1)) F(T_j − τ)                 (station_tick_gain)
//! ```
//!
//! and likewise every factor family's tick sum (the element's, the standing's, a channel's and an
//! unpumped resonator's): each span's energy gain is the medium's `(1 + ω)^(2(s − 1))` times the
//! rings' `F(s)` (`span_transport_compose`), and the gain over the stations and ticks is the sum of
//! the span gains (`station_tick_gain`, Cauchy–Schwarz over the ticks). With every resonator
//! certified passive there is no factor, and every gain is read exactly as before.
//! - **The ring's own gains are held.** A step of a reach-read ring's own gain families moves its
//!   monodromy along the ray, and one certificate read at the ray's start does not cover its
//!   interior; a pumped ring's stiffness is indefinite, so its storage growth has no certificate at
//!   the commit either. Those families are held (their statistic moves, their entries do not) and
//!   named ([`PumpedReading::held`]), always for a pumped ring, and for a signed stiffness unless
//!   the readout is zero along the whole joint ray (then every gain is zero, whatever the reach).
//! - **The refusal stays where no certificate exists.** A ring whose decided certificate is refused
//!   (the Stein solve singular at the decided growth, `ρ₀² = μ_iμ_j`) refuses the deposit
//!   ([`HnnError::UncertifiedGain`], with its reason). [measured, source-inspected] The exact
//!   placement leaves that only to a degenerate tie: every finite monodromy has a certificate at
//!   every growth above its spectral radius.
//! - [scope] The consumer equation reads the pumped ring's undriven reach (the executed tick with
//!   its port terminated, `hnn::ring`'s monodromy) as the transport of the difference its state
//!   carries within a span, composed with the medium's passive and contrast ticks. The loop through
//!   the field's return into the pumped ring within one span (the port's feedback, a supply-rate
//!   certificate `E_G(x′) ≤ σ²E_G(x) + supply(e, s′)` of the driven ring) is not certified here: its
//!   statement is owed in #62, with the reach along a ring's own gain ray (a tube of monodromies)
//!   and a modulated pump's passage-dependent schedule. [`DepositReading::pumped`] reports each ring's
//!   decision, bounds and reach, the span factor at the longest span and the families held.
//!
//! [definition; agent-inferred, September 29] **The factor families' certified step** (the
//! [factor step's record](../../../../research/records/2026-09-29_THE_FACTOR_FAMILIES_CERTIFIED_STEP_PINNED_BEFORE_ITS_RUNS.md);
//! Lean `Holon/Deposition.{factor_unit_step_alignment, square_ray_move, square_ray_deriv_bound,
//! contracting_resolvent, transit_difference_power}`). The declared factor step `η_x = ½` is
//! retired: it moved the standing past the entry bound on text and grew a contact's storage by up to
//! `2²⁸` in one deposit. A factor family `x` steps by the same certificate as a linear locus, in the
//! same loop and the same joint certificate. Its metric is its carried statistic `h_x′ = h_x + e`
//! (`e`, the feature energy its window adds), so its unit step is `D = G_x / h_x′`:
//!
//! ```text
//! a = ⟨G_x, D⟩ = |G_x|² / h_x′          checked ≥ 0 (factor_unit_step_alignment)
//! c = max_t |g_t|_∞                     the covector one return carries at the family's output (FactorStep::covector)
//! C = s · κ²_ℓ · b(η)                   its own curvature; b(η) the output's moves along the whole ray [0, η], read at its end
//! η = the largest 2^k with ηC ≤ a and ηc ≤ 1, halved with every other locus until each certificate and the joint one hold
//! ```
//!
//! Each family's output is its carriers applied to its feature, so its moves read the Schur test
//! `S(X) = ‖X‖₁‖X‖_∞ ≥ ‖X‖₂²` on the unit step and on the factor at the ray's end,
//! `S(X + ηD) ≤ (‖X‖₁ + η‖D‖₁)(‖X‖_∞ + η‖D‖_∞)` (the square's move along its ray,
//! `square_ray_deriv_bound`: `‖∂_t (x + tD)(x + tD)ᵀ‖ ≤ 2‖D‖(‖x‖ + η‖D‖)`):
//!
//! ```text
//! family          output per return                    b(η)                                                          κ²
//! f_g             −f fᵀ x̄_t                            4 S(D) S(f + ηD) e                                            the element's at g
//! (u_ρ, v_ρ)_g    Σ_ρ σ_ρ(u_ρv_ρᵀ − v_ρu_ρᵀ) x̄_t        8 (S(dU) S(V + η dV) + S(U + η dU) S(dV)) e                   the element's at g
//! q_g             Σ_ρ (M D)_ρ A_ρ,r x̄_t,r (lock chart)  4 |D|²_∞ Σ_r S(U_r) S(V_r) e_r over its chart's rings r        N_g · max_r the element's at r
//! c_a, b_a, F_a   2 c cᵀ(w − ω), h b bᵀ(u + ½hω), h F Fᵀ ω   (16, 4h², 4h²) · S(D) S(x + ηD) e                     the channel's at a
//! g_(r,i)         g_i² × base_i                         |D|² e ((|g_i| + η|D|) / |g_i|)²,  e from ∂(output)/∂g_i        the resonator's at r
//! (e, a, b)_(g,o) Σ_ρ e_ρ a_ρᵀ M_c b_ρ                   3 k e Σ_ρ (|De_ρ|² A_ρ B_ρ + E_ρ |Da_ρ|² B_ρ + E_ρ A_ρ |Db_ρ|²)   the source's at g
//! ```
//!
//! with `X_ρ = 2|x_ρ|² + 2η²|Dx_ρ|²` for `x ∈ {e, a, b}` (`|x + tDx|² ≤ X_ρ` on the ray), `k` the pair
//! port's rank, `N_g` the rings of the standing's lock chart whose term is nonzero (their moves add by
//! Cauchy–Schwarz), and `M` the contrast map, whose blocks are coordinate matchings, so
//! `|(M D)_r|_∞ ≤ |D|_∞`. A channel's and a loaded resonator's output is the right-hand side of their
//! solve `m ζ = r`, `m ⪰ 1` (so `|δζ| ≤ |δr|`, `contracting_resolvent`), whose difference state carries
//! at most `P |δζ|²` (`transit_difference_power`):
//!
//! ```text
//! channel a      κ² = ‖R‖² (4 / (h Y_R)) P_a Σ_j Σ_(τ < T_j) (1+ω)^(2(T_j − τ − 1)),   P_a = G_a/(2h) + ½ (G_a/h)² ‖C_a‖ + ⅛ G_a² ‖K_a‖
//! resonator r    the channel's with G = 2Y_r (one port of admittance Y_r)
//! ```
//!
//! `G_a ≤ Y_a` at every lift when `β_a ≥ 0` (`G_a = 2^(−β_a Q_a/2) Y_a`, `Q_a ≥ 0`); a channel family
//! through a contact with `β_a < 0` is refused ([`HnnError::UncertifiedConductance`]). The storage
//! norms are read at their families' rays. The element's gain is the contrast port's
//! (`(h/4)Y_r|δs|²` is its output's power, the element's solve `(I − ½K)⁻¹` a contraction), so the
//! standing's is read at each ring its lock chart moves. The standing's certificate holds in its
//! declared lock chart (Lean `HNN/Normal.standing_deposit`), where the element reads the contrast's
//! move as its classes' tangent; the element itself reads only the classes, so a class that crosses
//! its node jumps, which no curvature bounds: the standing's fold, below, holds the step in its
//! lobes and gives the crossing to the lock. No part of this reads a codec, an alphabet or a
//! terrain.
//!
//! [definition; agent-inferred, September 29] **The standing's fold: nodes, lobes, amplitudes and
//! the lock's half-turn** (the
//! [fold's record](../../../../research/records/2026-09-29_THE_STANDINGS_FOLD_PINNED_BEFORE_ITS_RUNS.md);
//! Lean `HNN/Normal` §6, "The standing's fold"). The tightened certificate's receipt located the
//! copy's regression here: the standings were founded at `q = 0`, on the fold, and the element
//! reads them only through their sheet classes, so the certified steps' crossings flipped slices'
//! signs, jumps no curvature bounds. The contrast `Δ = M q` of the lock chart ([`Field::contrast`])
//! is a standing pattern: `Δ_ρ = 0` is a **node**, the sign classes `σ_ρ = sign Δ_ρ` (`sign 0 = +1`)
//! are its **lobes**, `|Δ_ρ|` its **amplitude**, and adjacent lobes are in antiphase, so a crossing
//! is the half-turn `e^{iπ}` of the parametron's sheet.
//! - **The founding.** The standing is founded as a standing wave with declared lobes: on each
//!   connected component `C` of the chart's coordinates, `M_C q_C = k u_C 𝟙`, every slice at the
//!   component's first lattice unit in the `+1` lobe (`u_C` the coarsest standing unit among its
//!   rings, `k` the least positive integer with `k M_C⁻¹ 𝟙` integral). [agent-inferred] The `+1` lobe
//!   is the sheet the tie rule already read at `q = 0`, so the founding element `Σ_ρ A_ρ` is exactly
//!   the declared one; only the amplitude leaves the node (Lean `founding_off_node`). The prediction
//!   field's chain `0 — 1 — 2` is unimodular at every coordinate and founds at `(2, 3, 2)` units
//!   (`chain_founding`). A component whose chart is singular cannot place its declared lobes off the
//!   node: a single channel's two ends read `Δ` and `−Δ`, so its kernel fixes their sum
//!   (`channel_fixed_node`). It stays on its node, and its slices are the field's **fixed nodes**
//!   (`Constitution::fixed_nodes`, the tests' reading): no within-lobe move reaches them, and only the lock can turn
//!   them. Campaign 1's field has them (the channel between rings 2 and 3 past ring 1's width); the
//!   prediction field has none.
//! - **Within a lobe.** A standing's move is read on its carried lattice successor, exactly as the
//!   carry takes it, against the contrasts of every ring: its step stays in every lobe it reaches,
//!   with no slice carried onto its node from off it, the lattice form of `η |(M D)_ρ| < |Δ_ρ|`
//!   wherever the move points toward the node (Lean `lobe_of_step_bound`). Where the chart's
//!   certified step would leave a lobe, the families whose moves reach the crossed slices are halved
//!   together (the joint ray scaled) until none leaves; a family whose step falls below half its
//!   fine lattice's unit on its widest entry would move nothing and is dropped ([`LobeReading`]).
//!   Along such a move every class is kept (`lobe_ray_keeps_class`), so the element, and every score
//!   read through it, does not move (`lobe_move_is_null`): the standing's realized move and decrease
//!   are zero, it leaves the joint certificate, and the deposit descends by the other families'
//!   `½ Σ η a` (`lobe_deposit_descends`). Its own lock-chart certificate (`ηC ≤ a`, `ηc ≤ 1`) still
//!   rates its amplitude. [measured, the record's development reads] The joint certificate no longer
//!   counts the lock chart's decrease of a move the realized score never makes, so the other
//!   families' joint steps are those their own moves certify.
//! - **At a node: the lock's half-turn.** The crossings the chart's step offered are the lock's
//!   proposal ([`LockProposal`]): the standings at the chart's certified step, turning each proposed
//!   sheet by a half-turn. It is a separate move and a commit of its own ([`Constitution::locked`]),
//!   taken by the machine that holds the comparison's window only where the lock's exact comparison
//!   of the comparison's code at both sheets says the turned sheets are strictly better
//!   ([`crate::holon::deposition::strictly_better`]: the turned code's enclosure lies strictly below
//!   the held one's). It is the two-state lock's own decision, no threshold: with the sheets'
//!   weights `a = 2^(−ℓ_turned)`, `K = 2^(−ℓ_held)`, the lock's face `θ = a/(a + K)` exceeds `½`
//!   exactly when `K < a` (Lean `lock_face_decides`), and the strict comparison descends across the
//!   jump (`lock_flip_descends`). [agent-inferred] **The consumer equation for the parametron's
//!   lock** (`hnn::ring`, the parametron worker's target): the merged lock, reading the exchange
//!   polynomial `Π = 1 + a/K` and its face `θ = a/(a + K)` on the two sheets, turns the sheet exactly
//!   when `θ > ½`, `lock(a, K) = turn ⇔ a > K`, so `strictly_better(held, turned)` is its decision on
//!   exact code enclosures. A port that does not read the comparison twice takes the held step and
//!   no half-turn, which is lawful: nothing jumps uncertified. [historical] The linear readout took
//!   the lock through its comparison's code (`hnn::prediction::comparison_code`, read by the
//!   notebook's retired batch comparison), both retired (N2, batch H; at
//!   [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/prediction.rs)).
//!
//! [definition; agent-inferred, September 29] **The tightened certificate** (the
//! [tightening's record](../../../../research/records/2026-09-29_THE_TIGHTENED_CERTIFICATE_PINNED_BEFORE_ITS_RUNS.md);
//! Lean `Holon/Deposition.{joint_move_triangle, joint_step_descends, gram_certificate_bound,
//! adjoint_gram_certificate_bound, entrywise_error_bound}`). The factor families' certified steps sat
//! below their lattice units on the prediction field (`2⁻²³` to `2⁻⁷`) because the curvature
//! multiplied loose upper bounds. Two of them are replaced by sharper proved ones; no limit moves
//! (`ηc ≤ 1` and each family's own `ηC ≤ a` stay):
//! - **The joint moves, not the count `B`.** The families' logit moves along the joint ray add, and
//!   the count `B` charged every family as if all stepped along the worst joint direction together
//!   (`joint_cauchy_schwarz`). The cross terms are bounded instead by Cauchy–Schwarz on the joint ray
//!   (`joint_move_triangle`): with `m_ℓ = √(κ²_ℓ b_ℓ)` at its dyadic ceiling
//!   (`holon::deposition::root_ceiling`), the joint curvature term is at most `s (Σ η_ℓ m_ℓ)²`, and
//!   the certificate is
//!   ```text
//!   η_ℓ C_ℓ ≤ a_ℓ,  η_ℓ c_ℓ ≤ 1  (each family, C_ℓ = s κ²_ℓ b_ℓ)      s (Σ_ℓ η_ℓ m_ℓ)² ≤ Σ_ℓ η_ℓ a_ℓ  (jointly)
//!   ```
//!   which descends by `½ Σ η_ℓ a_ℓ` through `certified_step_descends` (`joint_step_descends`: the
//!   joint term apportioned to the families by their decreases). A family whose move is small next
//!   to its decrease no longer pays for the others' moves: the count charged it `B` times its own.
//!   [agent-inferred] The steps start at each family's own certificate and, while the joint one
//!   fails, the family whose halving gains it most, `½ η (s m (2 Σ η m − ½ η m) − a)`, is halved (the
//!   first in the deposit's order at a tie); a gain is positive for some family whenever the joint
//!   certificate fails, so the halving ends.
//! - **The readout's spectral bound, not its Schur test.** `‖R‖₂²` is read by the Gram certificate
//!   (`holon::deposition::spectral_norm`): `R` on a dyadic face of 16 significant bits,
//!   `R = 2^e N + E_f` with `|E_f| ≤ 2^(e−1)` entrywise (`entrywise_error_bound`), the Gram of
//!   `N`'s smaller side over the integers, and a rational `μ` taken only where `μ I − G ⪰ 0` is
//!   decided by exact inertia (`gram_certificate_bound`, `adjoint_gram_certificate_bound`); then
//!   `‖R‖₂ ≤ 2^e(√μ + ½√(rows · columns))`. The receiving map's unit step is read the same way, and
//!   the readout at its ray's end is `(‖R‖₂ + η‖D‖₂)²`. The contrast ports' `ω` keeps its Schur
//!   test (on the prediction field `(1 + ω)²` stays within `(1 + 2⁻⁵)²`).
//!
//! The certificate reads no codec: the same `Constitution::deposited` runs on every field.
//! [measured, the record's development reads] On the text's choosing pairs the two together raise
//! the factor families' steps by about `2⁵` (the joint moves about `2³`, the spectral readout about
//! `2²`). The stations' sum is not loose there: the stacked Gram `Σ_j P_jᵀ RᵀR P_j` of the 32
//! stations' rotations of the one anchor reads `m ‖R‖₂²` within a factor 2. The bounds that stay (by
//! source inspection, in the record): the factor families' moves read through their feature energy
//! `Σ|x̄|²` (the deposit carries no feature Gram), and `s = ½`.
//!
//! [scope] The certificate is the Gauss–Newton curvature of the section's score along each locus's
//! step, the other loci's moves entering through the joint triangle; the model's own second-order terms (the
//! bilinear coupling of `R` and `E`, a contrast port acting on its own downstream contrast, a square
//! factor's own `2D Dᵀ` along its ray, the element's and the transit's resolvents differentiated
//! twice) are not certified here: their statements are owed in #62. The executed word's deviation
//! from the exact law is the lattice word's certificate (owed in #62).
//!
//! [definition; agent-inferred, September 29] **The committed energy bound, enforced at the
//! commit** (Lean `Holon/Deposition.{committed_energy_bound, active_element_growth}`). The storage
//! a deposit changes (every contact's `C_a`, `K_a` and every unpumped resonator's `C`, `K`) is
//! certified `Q_(k+1) ⪯ (1 + ε_k) Q_k` by inertia before publication, and a deposit no dyadic
//! `ε_k` of the declared search certifies is refused ([`HnnError::UncertifiedStorage`]); the product
//! `∏(1 + ε_k)` since the founding is kept ([`Constitution::storage_product`]). The one learned
//! relation in the word that injects power is the contrast port, which is passive only at `W_c = 0`
//! (Lean `HNN/Word.contrastPort_active`), so it is not projected: its certified bound `ω` enters the
//! bound as the per-tick growth `(1 + ω)²`, read at every certified step. `E` and `R` are the
//! source's input map and the receiver's readout: `E` supplies the injection whose power the bound
//! scales, and `R` does no work on the field; both gains enter the certified step. A refinement's
//! committed energy is then at most `(1 + ε_k)` times its driven bound
//! `(Σ_n (1+ω)^(T − T_n) √P_inj + (1+ω)^T √(T · r))²`, `r` its executed residual's certified bound.
//! [historical] The linear readout read that bound after every commit
//! (`hnn::prediction::RefinementBalance::energy_bound`, retired with the readout, batch H; at
//! [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/prediction.rs));
//! the storage growth's certificate stays enforced at every commit here.
//!
//! [historical; September 29–30] **The bank's learning path, a comparison beside the logits, is
//! retired** (batch H; source at
//! [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/constitution.rs):
//! `BankReach`, its curvature and trust scale, the returns read beside the logits' samples in
//! [`NormalLaw::prepare`], `StepReading::bank`). Its second order in the certified step (the
//! curvature `C_bank = Σ (2Â₂/A₀ + (81/4) â₂/a₀)`, the trust scale `c_bank = max √(16 â₂/a₀)` and
//! the joint certificate's endpoint term) is Lean's `HNN/BankFace.{bank_score_endpoint,
//! bank_score_trust, log_one_add_ge, resonance_gain, joint_descends_beside}`; the release's own
//! comparison replaced it (`hnn::executed`, which steps `E` through
//! [`Constitution::stepped_source`]).
//!
//! [definition; agent-inferred] **The landmark tree at the receiving locus.** The receiving map `R` keeps
//! the prox step on its reached covectors (the lattice deposit and the lattice word), the covector of the ratio read on
//! the combined face (`hnn::receiving::ReceivingRead::combined`). Beside it the receiving
//! parametron stores its landmark tree (`compression::landmark::context::Landmarks`, declared from the receiver by
//! `hnn::receiving::landmark_declaration`), which each reached comparison deposits on the path its
//! causal address opens ([`LandmarkStep`], in cell order); its counts are integers of half-units
//! and its mixture ratios are carried by the owner's β chart, so no lattice carry and no clock is
//! read for it. It shares the locus's diamond row (retained always) and its collapse rule (never
//! released): Lean `Compression/Landmark/Context/Tree.release_rule` proves that nodes deeper than `D` are releasable
//! (the tree founds none) and that a retention is lawful exactly when it refines the causal
//! signature; it does not prove that no shallower merge is lawful, and the collapse attempts none.
//! The region table is retired from Rust, its laws staying in Lean `HNN/RegionCounts`; it
//! is the depth-one forced case of the whole-cell emission (`|A|`-ary masses at a node; Lean
//! `Compression/Landmark/Context/Tree.depth_one_is_the_whole_cell_table`), not of this tree, which emits the cell's odometer
//! digits (its depth-one forced case is a product of binary KT faces). The first repair's exogenous law
//! and standing read are retired: the tree's face contains the marginal (Lean `HNN/TargetFace`'s
//! finite-chart obstruction stays a theorem).
//!
//! [definition; agent-inferred] **The carrier lattice and the budgeted release** (Lean
//! `HNN/LatticeDeposit`). Exact rational deposition compounds: the maps that form each other's
//! covectors (`E`, `R`, `W_c` through the word's inverses) feed their denominators into the next
//! deposit (measured on the chain control: 1,126 → 10,883 → 623,415 bits over two deposits). By
//! CLAUDE.md's exact representation law ("when a value outgrows its carrier, it is rebased,
//! factored or re-represented with its decoder and residual"), with the Ratio's `div_rem` and the
//! carry cocycle (`Geometry/PhaseCarry.carry_cocycle`: helix = circle + carry, the lattice
//! coordinate the winding and the remainder its phase), every entry of a locus `ℓ` (its maps,
//! factors and statistics) lives on the field's declared lattice `2^(−L_ℓ)ℤ` ([`Lattice`],
//! `Field::lattice`) with a carried remainder `r`. A remainder carried exactly keeps a bounded
//! magnitude but a denominator that accumulates every update's, and releasing it at the aeon
//! collapse bounds neither its bits (an aeon is a first-passage time of the joint clock's carry
//! chain, with no upper bound) nor the drift (the releases add across aeons). The retention law
//! applied to the whole admitted future gives the budget instead: the total released since a
//! locus's founding stays below the one-unit deviation the lattice rule certifies. Each locus keeps
//! a **deposit clock** `m` ([`Constitution::clock`]): the count of epochs at the locus's section,
//! the deposits that reached it with a nonzero update. It starts at the locus's founding (the
//! field's mount, or a later founding), is not reset at an aeon boundary, and ends when the collapse
//! releases the locus whole. [definition] It is the flux reading of the aeon epoch owner at that
//! section: the constitution's commits are occurrences and its deposits the passages between them,
//! the locus's section is crossed by exactly the deposits that move it, and the section's reading of
//! the aeon since the founding is its flux, forward minus backward crossings
//! ([`crate::aeon::epochs`], [`crate::aeon::Epochs::flux`]; Lean
//! `Aeon/Clock/Epoch.{reading_eq_crossings, crossings_concat}`). Deposits only advance the
//! commits, so every crossing is forward and the flux is the count (the monotone case, as for a
//! ring section on the clock lift, `Epoch.monotone_count_is_flux`). The count is kept and the
//! ticks are not: the budgeted carry reads only `m`, so the count is the sufficient statistic of
//! the epochs for the admitted future, and it adds under concatenation across aeons
//! (`crossings_concat`). A deposit carries each entry at the precision of the Elias-gamma length
//! of `m` ([`gamma_length`], the field's own natural code) through [`BudgetedCarry`]:
//!
//! ```text
//! u = 2^(−L_ℓ) ,  k_m = 2⌊log₂ m⌋ + 1
//! y   = Δ + r_prev                                   exact
//! y   = y_f + e ,   y_f ∈ 2^(−L−k_m)ℤ nearest, ties upward ,   e ∈ [−½·2^(−L−k_m), ½·2^(−L−k_m))
//! y_f = q u + r ,   q nearest, ties upward ,   r ∈ [−u/2, u/2) ∩ 2^(−L−k_m)ℤ
//! entry += q u ;  carry r ;  release e (exact, in the deposit's reading)
//! ```
//!
//! The applied steps, the carried remainder and the released residuals equal the exact sum of the
//! updates, per entry (`lattice_deposit_accounting`); the releases of one entry since the locus's
//! founding sum to less than `u/2` (Kraft for the Elias-gamma lengths, `gamma_kraft_lt_one`,
//! `release_bounded_since_founding`), so the word always reads within one unit of the exact
//! accumulation of what reached the locus (`within_one_unit_since_founding`), which moves a linear
//! read (the normal-law maps `E_g`, `R`, `W_c`) by at most `X_ℓ 2^(−L_ℓ) ≤ 1/(2L_R)`, below every
//! admitted receiver's grain (`remainder_below_grain`); the factor loci enter the word as products
//! of their factors, and their bound is the word-level certificate owed in #62. A carried remainder is `ρ·2^(−L−k_m)` with `|ρ| ≤ 2^(k_m−1)`, so it
//! takes `O(L + log m)` bits (`remainder_numerator_bounded`, `remainder_rat_bits_bounded`). An
//! entry whose update is zero moves nothing and releases nothing (`carry_entry_zero`: its remainder
//! already lies on the finer lattice), and a deposit with no nonzero update at `ℓ` leaves the locus
//! and its clock (`carry_zero`). The aeon collapse releases no remainder of a retained locus and
//! resets no clock. Within one deposit an entry's updates compose exactly before its one release (a
//! residual staged by an earlier step of the same deposit is taken back into `y`), so each clock
//! value releases at most once per entry. [open] The counterfactual bound (how far the carried
//! trajectory is from the one whose updates are computed at never-rounded operands) is
//! `Objects/CommitRebase`'s `commit_chain_residual`, `Σ K^(n−1−i) r_i`, and needs a Lipschitz bound
//! `K` of the deposit map, which is owed. Brandon may override this choice.
//!
//! A [`NormalLaw`] keeps `W` and its Gram `H` of the locus's own width (no global Gram), each
//! carried, and the **solved chart** `X̂ ≈ H⁻¹` of the carried Gram (the lattice word, Lean
//! `HNN/LatticeWord`; [`SolvedChart`]): a lattice matrix on `2^(−L_s)ℤ` with its certified left
//! residual `δ = ‖1 − X̂H‖∞`, computed exactly, warm-started from the previous chart at each deposit
//! and refined by rounded Newton–Schulz steps until `δ ≤ δ_ℓ`, both declared by rule
//! ([`ChartRule`]) so that the prox identity's released residual moves a read by less than the
//! receiver's grain. The exact solved chart it replaces grew by the Hadamard bound of the carried
//! Gram (0.40 Mbit over 24 windows of the standing real cut, still growing). [proved-derived;
//! formal-checked] **The carried Gram stays positive
//! definite with no clamp** (Lean `carried_gram_posDef`, `carried_gram_posDef_rule`): every entry
//! of `H` is within one unit of the exact Gram `H_exact = I + Σ w f fᵀ ⪰ I`
//! (`within_one_unit_since_founding`), so `|vᵀ(H − H_exact)v| ≤ u(Σ|v_i|)² ≤ n·u·|v|²` for its
//! width `n`, and since the lattice rule's `X_ℓ` is at least `n`, `n·u ≤ 1/(2L_R)` and
//! `H ⪰ (1 − 1/(2L_R)) I` since the locus's founding. `B` is not carried: under `W H = B` it is
//! `W H`, and the prox step `W' = W + γ G X̂` (Lean `HNN/Normal.normal_prox_step` at the exact
//! inverse, `HNN/LatticeWord.prox_chart_residual` at the chart) needs only `W`, the chart of `H'` and
//! `G`. The factor carriers keep `C`, `K`, `D` and `−W_s` positive semidefinite as
//! squares, with no clamp and no projection (Lean `factorCarrier_psd`). [agent-inferred] `h_x` is a
//! statistic like `H`: it accumulates over deposits, starting at 1, so a factor step is
//! preconditioned by its family's own feature energy.
//!
//! [definition] **The budget and stop rule** (design (d), R3 §5): the successor is computed exactly
//! and its exact bits (every numerator and denominator: the lattice entries, the carried remainders,
//! the statistics and the solved charts at their lattices) are counted before publication. Past
//! `B_Θ` the deposit is refused with [`HnnError::ConstitutionBudget`], naming the loci that grew most; the predecessor
//! stays published. The lattice bounds the entries' bits (`lattice_bits_bounded`) and the clock the
//! remainders' (`remainder_rat_bits_bounded`); [`Constitution::carrier_bits`] reads the three parts
//! separately, and [`DepositReading`] the released residuals and their bits, with each chart's
//! certificate and released prox residual ([`ChartReading`]). The deposit clocks,
//! like the commit counter, are counters of `⌈log₂ m⌉` bits and are not counted against `B_Θ`.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Normal.normal_prox_step` at the carried Gram, with `HNN/LatticeDeposit.within_one_unit_since_founding` | [`NormalLaw`]: `W` is the prox iterate at the carried Gram `H'` (`B` is not carried, so `W` is not the minimizer of the accumulated `J(W)`), and `H` stays within one unit of the exact statistic `I + Σ w f fᵀ` |
//! | `HNN/Normal.normal_prox_step`, `depositLocus_solves`; `HNN/LatticeWord.{prox_chart_residual, prox_chart_certificate}` | [`NormalLaw::deposited`] (the step at the carried Gram through the executed chart, its residual released and reported: [`ChartReading`]) |
//! | `HNN/LatticeWord.{nsStep, newton_schulz_left, rounded_refinement_residual_left, rounded_refinement_certificate_left, rowNorm, latticeChart}` | [`SolvedChart`] (the certificate and the rounded refinement) |
//! | `HNN/LatticeWord.{warm_start_residual, warm_start_certificate}` | [`SolvedChart`] (why the warm start takes the window's rank-one steps) |
//! | `HNN/LatticeWord.{roundedIter_certificate, newton_schulz_iter_left, inverse_chart_deviation}` | [`ChartRule`] (the lattice `L_s`, the target `δ_ℓ`, the refinement count) |
//! | `HNN/Normal.normalStatistic_standing`, `objective_eq_statisticObjective`, for its statistic `H` only (carried on the lattice) | [`NormalLaw::gram`] (keeps `H`, never the samples) |
//! | `HNN/Normal.deposit_local`, `windowGram_apply_eq_zero` | [`Constitution::deposited`] (per locus, only its window) |
//! | `HNN/Normal.reaction_deposit_storage_unchanged`, `reaction_deposits_keep_committed_energy`; `Holon/Deposition.committed_energy_bound` | [`DepositReading::storage_growth`], [`Constitution::storage_product`] (refused when uncertified: [`HnnError::UncertifiedStorage`]) |
//! | `Holon/Deposition.{certified_step_descends, quadratic_upper_model, gauss_newton_curvature, joint_cauchy_schwarz}`, `HNN/Normal.certified_normal_step` | [`NormalLaw::prepare`] (the unit step and its readings), [`Constitution::deposited`] (the certified steps: [`StepReading`]) |
//! | `Holon/Deposition.{active_element_growth, active_energy_growth}` | [`Constitution::amplitude`] (the per-tick growth `1 + ω`) |
//! | `HNN/Floquet.{floquet_span_reach, partial_period_le_pow}`, `Holon/Deposition.{span_transport_compose, station_tick_gain, entry_span_gain, runningMax, le_runningMax, runningMax_mono, pumped_span_factor}` | the pumped medium's reach ([`RingReach`], [`MediumReach`], [`Constitution::medium_reach`], [`PumpedReading`], `Reach`'s gains, `holon::deposition::span_factors`) |
//! | `Holon/Deposition.{factor_unit_step_alignment, square_ray_move, square_ray_deriv_bound, contracting_resolvent, transit_difference_power}` with `certified_step_descends`, `gauss_newton_curvature` | the factor families' certified step ([`FactorStep`], [`Family`], [`StepReading`], [`Constitution::deposited`]) |
//! | `Holon/Deposition.{joint_move_triangle, joint_step_descends, gram_certificate_bound, adjoint_gram_certificate_bound, entrywise_error_bound}` | the tightened certificate ([`Constitution::deposited`], [`DepositReading::joint`], [`StepReading::bound`]; `holon::deposition::{JointReading, spectral_norm}`) |
//! | `HNN/Normal.factorCarrier_psd` | the factor families ([`FactorGradient`]) |
//! | `HNN/Normal.standing_deposit`, `sheetClass_locally_constant` | [`FactorGradient::Standing`] |
//! | `HNN/Normal.{lobe_of_step_bound, lobe_ray_keeps_class, lobe_move_is_null, lobe_deposit_descends}` | the lobe law ([`Constitution::deposited`], [`LobeReading`]; the standing out of the joint certificate) |
//! | `HNN/Normal.{lock_face_decides, lock_flip_descends}` | the lock's half-turn ([`LockProposal`], [`Constitution::locked`], `holon::deposition::strictly_better`) |
//! | `HNN/Normal.{founding_off_node, chain_founding, channel_fixed_node}` | the founding ([`Constitution::initial`]; `Constitution::{fixed_nodes, standing_contrasts}` the tests' readings) |
//! | `HNN/LatticeDeposit.{quot, rem, div_rem_spec, rem_bounds, quot_eq_zero_of_bounds, fine}` | [`Lattice::div_rem`] (the carry's fine split), [`Lattice::div_rem_coordinate`] (its coarse split) |
//! | `HNN/LatticeDeposit.{gammaLength, gamma_kraft_lt_one}` | [`gamma_length`] |
//! | `HNN/LatticeDeposit.{carry, release, carry_accounting, lattice_deposit_accounting, carry_zero, carry_entry_zero, carry_entry_below_grain}` | [`BudgetedCarry`], the carried deposit of every entry |
//! | `HNN/LatticeDeposit/Rebase.{Carried.rebase, rebase_value_add_rem, rebase_onLattice, history_accounting, history_release_lt, history_within_founding_unit}` | `BudgetedCarry::rebase` (crate-internal), the re-base onto a finer lattice; [`Constitution::rebased`] at a contact's channel, which the declared schedule never calls |
//! | `HNN/LatticeDeposit.{carried_remainder_bounded, remainder_numerator_bounded, remainder_rat_bits_bounded}` | [`Constitution::carried_remainders`], [`CarrierBits::remainders`] |
//! | `HNN/LatticeDeposit.{release_bounded, release_bounded_since_founding, within_one_unit_since_founding, remainder_below_grain}` | [`DepositReading::released`] |
//! | `HNN/LatticeDeposit.{carried_gram_posDef, carried_gram_posDef_rule}` | [`NormalLaw::gram`] (the carried Gram) |
//! | `HNN/LatticeDeposit.{lattice_bits_bounded, lattice_rat_bits_bounded}` | [`Constitution::carrier_bits`] |
//! | `HNN/LatticeDeposit.lattice_deposit_descends` | [`Constitution::deposited`] with `hnn::retention::collapse` |
//! | `HNN/Ring.gain_backtrack_midpoint` | [`GainBacktrack`], [`DepositReading::backtracks`] |

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;

use crate::compression::landmark::context::{Landmarks, Letter};
use crate::hnn::HnnError;
use crate::hnn::contact::{
    certify_boost, contact_conductances, signed_form_certifies, signed_stiffness,
};
use crate::hnn::field::{ConstitutionRead, Field, lattice_exponent};
use crate::hnn::moment::PairPort;
use crate::hnn::port::Deposit;
use crate::hnn::propagation::gram;
use crate::hnn::realization::{indexed, outer_integral};
use crate::hnn::receiving::{ReceivingStep, landmark_declaration, receiving_population};
use crate::hnn::ring::{
    Floquet, FloquetBound, FloquetReading, ResonatorMaterial, ResonatorOperands, attain_metric,
};
use crate::holon::deposition::{
    CertifiedStep, CommittedEnergyBound, JointReading, root_ceiling, schur_norms, significant,
    span_factors, spectral_norm, sqrt_ceiling,
};
use crate::ratio::linear::inertia::inertia;
use crate::ratio::linear::vector::{
    Chart, IntegralMatrix, integer_dot, integral, lcm, matrix_form,
};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::{Rat, rat};
use crate::receiver::population::PortPopulation;

/// The declared constitution budget of campaign 1: `B_Θ = 2^33` exact bits.
pub const CAMPAIGN_ONE_BUDGET: u64 = 1 << 33;

/// [definition; agent-inferred, September 30] **The founding modulus** on the lattice
/// `2^(−lattice)ℤ` (Lean `HNN/IndexedOpen.IsFounding`; [`Constitution::founding_transport`]): the
/// greatest `ρ₀ = k 2^(−lattice)` with `ρ₀^period ≤ 2^(−chart)`, `k` the integer `period`-th root
/// of `2^(lattice·period − chart)`, read exactly. `None` where the lattice cannot carry it
/// (`lattice·period < chart`, or `k = 0`).
pub fn founding_modulus(lattice: u32, period: u64, chart: u32) -> Option<Rat> {
    let power = (u64::from(lattice) * period).checked_sub(u64::from(chart))?;
    let root = (num_bigint::BigUint::one() << usize::try_from(power).ok()?)
        .nth_root(u32::try_from(period).ok()?);
    let modulus = Rat::new(BigInt::from(root), BigInt::one() << lattice as usize);
    modulus.is_positive().then_some(modulus)
}

// -------------------------------------------------------------------------------------------
// the carrier lattice

/// [definition; agent-inferred] **A declared carrier lattice** `2^(−L)ℤ` (Lean
/// `HNN/LatticeDeposit`): the Ratio's division with remainder at a dyadic unit. See the module
/// header for the law and its source.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lattice {
    exponent: u32,
}

impl Lattice {
    pub const fn new(exponent: u32) -> Self {
        Self { exponent }
    }

    /// `L`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// `2^L`.
    fn scale(&self) -> BigInt {
        BigInt::one() << self.exponent as usize
    }

    /// The unit `2^(−L)`.
    pub fn unit(&self) -> Rat {
        Rat::new(BigInt::one(), self.scale())
    }

    /// Whether `value` lies on the lattice (Lean `OnLattice`).
    pub fn contains(&self, value: &Rat) -> bool {
        (self.scale() % value.denom()).is_zero()
    }

    /// **Division with remainder at the nearest lattice point, ties upward** (Lean
    /// `HNN/LatticeDeposit.{quot, rem, div_rem_spec, rem_bounds}`): `value = q·2^(−L) + r` with
    /// `q = ⌊value·2^L + ½⌋`, so `−2^(−L−1) ≤ r < 2^(−L−1)`, and a remainder alone divides to
    /// `q = 0` (`quot_eq_zero_of_bounds`). It is the budgeted carry's **fine split** (Lean `fine`,
    /// `release`), at the fine lattice `2^(−L−k_m)ℤ`. Read in the value's own chart: for
    /// `value = a/b` in lowest terms, `q = ⌊(2a·2^L + b)/2b⌋`, and the remainder's numerator
    /// `a·2^L − bq` shares only powers of two with its denominator `b·2^L` (`gcd(a, b) = 1`), so it
    /// is reduced by a shift: one integer division and no `gcd` of the value's size.
    pub fn div_rem(&self, value: &Rat) -> (BigInt, Rat) {
        let (numerator, denominator) = (value.numer(), value.denom());
        let scaled = numerator << self.exponent as usize;
        let top: BigInt = (&scaled << 1usize) + denominator;
        let bottom: BigInt = denominator << 1usize;
        let (mut quotient, residue) = (&top / &bottom, &top % &bottom);
        if residue.is_negative() {
            quotient -= 1;
        }
        let remainder = scaled - denominator * &quotient;
        if remainder.is_zero() {
            return (quotient, Rat::zero());
        }
        let whole = denominator << self.exponent as usize;
        let shift = remainder
            .trailing_zeros()
            .unwrap_or(0)
            .min(whole.trailing_zeros().unwrap_or(0));
        (quotient, Rat::new_raw(remainder >> shift, whole >> shift))
    }

    /// **The same division of a point given by its coordinate on a finer lattice** `2^(−L−k)ℤ`
    /// (Lean `quot`, `rem` at a point of `OnLattice (L + k)`): `P·2^(−L−k) = q·2^(−L) + ρ·2^(−L−k)`
    /// with `q = ⌊(P + 2^(k−1)) / 2^k⌋` (ties upward) and `ρ = P − q·2^k ∈ [−2^(k−1), 2^(k−1))`. It is
    /// the budgeted carry's **coarse split** of the fine point; at `k = 0` the point is on the
    /// lattice and `ρ = 0`.
    pub fn div_rem_coordinate(&self, point: &BigInt, finer: u32) -> (BigInt, BigInt) {
        if finer == 0 {
            return (point.clone(), BigInt::zero());
        }
        let quotient = (point + (BigInt::one() << (finer - 1) as usize)) >> finer as usize;
        let remainder = point - (&quotient << finer as usize);
        (quotient, remainder)
    }
}

/// [definition; agent-inferred] **The precision of the budgeted carry at deposit clock `m`**: the
/// Elias-gamma length `k_m = 2⌊log₂ m⌋ + 1` of `m` (Lean `HNN/LatticeDeposit.gammaLength`, `k_0 = 1`),
/// the field's own natural code (`field.rs`, `describe`). Its weights `2^(−k_m)` sum to less than one
/// over every clock (`gamma_kraft_lt_one`).
pub fn gamma_length(clock: u64) -> u32 {
    2 * clock.max(1).ilog2() + 1
}

/// [definition; agent-inferred] **One deposit's budgeted carry at one locus** (Lean
/// `HNN/LatticeDeposit.{step, carry, release}`; the module header states the law): the locus's
/// lattice `2^(−L)ℤ`, the clock `m` the deposit advances it to (its precision `k_m` names the fine
/// lattice `2^(−L−k_m)ℤ`), and what the deposit does there, staged by carrier and entry until it
/// publishes: each entry's released residual `e` (exact) and its applied coordinate `q`, and whether
/// any update at the locus was nonzero (only then does the clock advance).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BudgetedCarry {
    lattice: Lattice,
    clock: u64,
    staged: BTreeMap<(Carrier, usize), (Rat, BigInt)>,
    moved: bool,
    backtracks: Vec<GainBacktrack>,
}

/// [definition; agent-inferred] **A loaded resonator gain's backtrack** (the loaded resonator's repair; the
/// rule of [`Constitution::deposited`]): a candidate step that would carry gain family `family` of
/// ring `ring` from `from > 0` to `candidate ≤ 0` carries it to `to` instead, the midpoint `from/2`
/// of the admissible side `(0, from]` split at the locus's lattice by the carry's own nearest point,
/// ties upward (toward `from`): `to = ⌈q/2⌉·2^(−L)` for `from = q·2^(−L)`, exactly `from/2` when `q`
/// is even, and `from` itself at the lattice's first point `q = 1`. The substitute step `to − from`
/// lies on the lattice, so the carry moves the gain by exactly that step and its remainder stays in
/// its cell (Lean `HNN/Ring.gain_backtrack_midpoint`: the coordinate `⌊(q + 1)/2⌋ ∈ [1, q]`).
/// Deposition never releases a family: a zero amplitude would zero its covector for every later
/// word, and release belongs to campaign 3's collapse law with its receipt. Every substitution is
/// named in the deposit's reading ([`DepositReading::backtracks`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GainBacktrack {
    pub ring: usize,
    pub family: usize,
    pub from: Rat,
    pub candidate: Rat,
    pub to: Rat,
}

impl BudgetedCarry {
    /// At a locus's lattice, for the deposit that advances its clock to `clock` (`m ≥ 1`).
    pub fn new(lattice: Lattice, clock: u64) -> Self {
        Self {
            lattice,
            clock,
            staged: BTreeMap::new(),
            moved: false,
            backtracks: Vec::new(),
        }
    }

    /// The gain backtracks this deposit took at the locus ([`GainBacktrack`]).
    pub fn backtracks(&self) -> &[GainBacktrack] {
        &self.backtracks
    }

    /// `m`, the clock the deposit advances the locus to.
    pub fn clock(&self) -> u64 {
        self.clock
    }

    /// `k_m`.
    pub fn precision(&self) -> u32 {
        gamma_length(self.clock)
    }

    /// Whether any update at the locus was nonzero, so the clock advances (Lean `carry_zero`
    /// otherwise).
    pub fn moved(&self) -> bool {
        self.moved
    }

    /// **The released residuals** `e ≠ 0`, exact, by carrier and entry (Lean `release`): each at most
    /// `½·2^(−L−k_m)` (`release_bounded`).
    pub fn released(&self) -> Vec<(Carrier, usize, Rat)> {
        self.staged
            .iter()
            .filter(|(_, (residual, _))| !residual.is_zero())
            .map(|((carrier, entry), (residual, _))| (*carrier, *entry, residual.clone()))
            .collect()
    }

    /// The number of entries whose applied lattice coordinate `q` is nonzero (review R5).
    pub fn stepped(&self) -> u64 {
        self.staged
            .values()
            .filter(|(_, quotient)| !quotient.is_zero())
            .count() as u64
    }

    /// Whether any entry of a family's carriers took a nonzero applied coordinate `q`
    /// ([`Family::carries`]).
    fn family_moved(&self, family: Family) -> bool {
        self.staged
            .iter()
            .any(|((carrier, _), (_, quotient))| family.carries(carrier) && !quotient.is_zero())
    }

    /// The locus's lattice `2^(−L)ℤ`, the one this deposit carries on.
    pub fn lattice(&self) -> Lattice {
        self.lattice
    }

    /// [definition; agent-inferred] **The re-base onto the finer lattice** `2^(−L−j)ℤ` (Lean
    /// `HNN/LatticeDeposit/Rebase.Carried.rebase`), of every array the locus carries, before the
    /// deposit stages anything. Each carried remainder `r` is divided at the finer unit
    /// `u′ = 2^(−L−j)`, `r = q′u′ + r′` with `r′ ∈ [−u′/2, u′/2)` ([`Lattice::div_rem`]); the entry
    /// takes `q′u′` and `r′` is carried. The clock is kept, so the precision schedule `k_m`
    /// continues, and nothing is released.
    ///
    /// [proved-derived; formal-checked] Per entry, `entry′ + r′ = entry + r`
    /// (`rebase_value_add_rem`), a lattice entry lands on the finer lattice (`rebase_onLattice`),
    /// and over any history of deposits and re-bases the releases since the founding stay below
    /// half the founding unit (`history_release_lt`), the entry within `u₀/2 + u/2` of the exact
    /// accumulation (`history_within_founding_unit`). The bound is in the founding unit `u₀`, not
    /// the current `u`.
    ///
    /// [definition; agent-inferred] The declared schedule keeps one lattice per locus and never
    /// calls this; a refining grain (`HNN/Ratio/Resolution.grainRead_of_refined`, dyadic
    /// `2^⌈log₂ L(N)⌉`) re-bases by the levels its exponent grew. Refused once the deposit has
    /// staged an entry (its applied coordinates are in the coarser unit), past a `u32` exponent,
    /// and for a remainder whose entry the array does not have.
    pub(crate) fn rebase(
        &mut self,
        levels: u32,
        arrays: &mut [(&mut Carry, &mut [Rat])],
    ) -> Result<(), HnnError> {
        let refused = HnnError::Rebase {
            exponent: self.lattice.exponent,
            levels,
            staged: self.staged.len(),
        };
        let exponent = self.lattice.exponent.checked_add(levels);
        let (Some(exponent), true) = (exponent, self.staged.is_empty()) else {
            return Err(refused);
        };
        for (carry, entries) in arrays.iter() {
            if let Some(&index) = carry.0.keys().next_back()
                && index >= entries.len()
            {
                return Err(HnnError::Shape {
                    what: "re-based carrier",
                    expected: entries.len(),
                    found: index + 1,
                });
            }
        }
        let finer = Lattice::new(exponent);
        for (carry, entries) in arrays.iter_mut() {
            let remainders = std::mem::take(&mut carry.0);
            for (index, remainder) in remainders {
                let (quotient, rest) = finer.div_rem(&remainder);
                if !quotient.is_zero() {
                    entries[index] = &entries[index] + Rat::new(quotient, finer.scale());
                }
                if !rest.is_zero() {
                    carry.0.insert(index, rest);
                }
            }
        }
        self.lattice = finer;
        Ok(())
    }
}

/// [definition] **The carried remainders of one lattice-valued array** (Lean `Carried.rem`), by
/// flat entry index; a zero remainder is not stored, so two carriers with one content compare equal.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Carry(BTreeMap<usize, Rat>);

impl Carry {
    /// **One entry's budgeted deposit** (Lean `carry`, `carry_accounting`): `y = Δ + r_prev` split at
    /// the fine lattice `2^(−L−k_m)ℤ` into `y_f + e` and `y_f` at the lattice into `q·2^(−L) + r`; the
    /// entry moves by `q·2^(−L)`, `r` is carried and `e` is staged for release. A zero update moves
    /// nothing and releases nothing (`carry_entry_zero`). A residual staged by an earlier step of the
    /// same deposit at this entry is taken back into `y`, so the deposit releases once per entry.
    fn deposit(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        index: usize,
        entry: &mut Rat,
        update: &Rat,
    ) {
        if update.is_zero() {
            return;
        }
        at.moved = true;
        let staged = at.staged.remove(&(carrier, index));
        let previous = self.0.remove(&index);
        let carried = carried_entry(&at.lattice, at.precision(), entry, update, staged, previous);
        self.adopt(at, carrier, index, entry, carried)
    }

    /// Carry a whole flat array's update, entry by entry.
    ///
    /// [definition; agent-inferred] Each entry's step reads only its own update, staged residual
    /// and carried remainder, and writes only its own: the entries run together
    /// (`hnn::realization`), and their results are taken into the carry and the budgeted
    /// carry afterwards, in entry order.
    pub(crate) fn deposit_all(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        entries: &mut [Rat],
        updates: &[Rat],
    ) {
        let moving: Vec<(usize, Option<Staged>, Option<Rat>)> =
            (0..entries.len().min(updates.len()))
                .filter(|&index| !updates[index].is_zero())
                .map(|index| {
                    (
                        index,
                        at.staged.remove(&(carrier, index)),
                        self.0.remove(&index),
                    )
                })
                .collect();
        if moving.is_empty() {
            return;
        }
        at.moved = true;
        let (lattice, precision) = (at.lattice, at.precision());
        let current: &[Rat] = entries;
        let carried: Vec<(usize, CarriedEntry)> = moving
            .into_par_iter()
            .map(|(index, staged, previous)| {
                (
                    index,
                    carried_entry(
                        &lattice,
                        precision,
                        &current[index],
                        &updates[index],
                        staged,
                        previous,
                    ),
                )
            })
            .collect();
        for (index, step) in carried {
            self.adopt(at, carrier, index, &mut entries[index], step);
        }
    }

    /// Take one entry's carried step into the array, the carry and the budgeted carry.
    fn adopt(
        &mut self,
        at: &mut BudgetedCarry,
        carrier: Carrier,
        index: usize,
        entry: &mut Rat,
        step: CarriedEntry,
    ) {
        *entry = step.entry;
        if !step.remainder.is_zero() {
            self.0.insert(index, step.remainder);
        }
        if let Some(staged) = step.staged {
            at.staged.insert((carrier, index), staged);
        }
    }

    /// The remainder at an entry.
    pub(crate) fn at(&self, index: usize) -> Rat {
        self.0.get(&index).cloned().unwrap_or_else(Rat::zero)
    }

    fn bits(&self) -> u64 {
        self.0.values().map(bits).sum()
    }
}

/// An entry's staged residual `e` and applied coordinate `q` within one deposit.
type Staged = (Rat, BigInt);

/// **One entry's carried step**, read alone: the entry moved by `q·2^(−L)`, the remainder `r` to
/// carry, and the residual and coordinate to stage (none when both are zero).
struct CarriedEntry {
    entry: Rat,
    remainder: Rat,
    staged: Option<Staged>,
}

/// **One entry's budgeted deposit** of a nonzero update ([`Carry::deposit`], Lean `carry`,
/// `carry_accounting`) at the lattice and precision of its locus's deposit, from the entry, the
/// residual and coordinate an earlier step of the same deposit staged there, and the remainder the
/// entry carries.
fn carried_entry(
    lattice: &Lattice,
    precision: u32,
    entry: &Rat,
    update: &Rat,
    staged: Option<Staged>,
    previous: Option<Rat>,
) -> CarriedEntry {
    let (staged, applied) = staged.unwrap_or_else(|| (Rat::zero(), BigInt::zero()));
    let previous = previous.unwrap_or_else(Rat::zero);
    let exponent = lattice.exponent + precision;
    // y = Δ + staged + r_prev. The carried remainder lies on the fine lattice of an earlier
    // clock, so it moves the fine point by its own coordinate and adds nothing to `e`.
    let mut moving = if staged.is_zero() {
        update.clone()
    } else {
        update + &staged
    };
    let carried = match dyadic_coordinate(&previous, exponent) {
        Some(coordinate) => coordinate,
        None => {
            moving += &previous;
            BigInt::zero()
        }
    };
    let (point, residual) = Lattice::new(exponent).div_rem(&moving);
    let point = point + carried;
    // y_f = P·2^(−L−k): its coordinate at the lattice, nearest, ties upward.
    let (quotient, coordinate) = lattice.div_rem_coordinate(&point, precision);
    let remainder = Rat::new(coordinate, BigInt::one() << exponent as usize);
    let entry = entry + Rat::new(quotient.clone(), lattice.scale());
    let applied = applied + quotient;
    let staged = (!residual.is_zero() || !applied.is_zero()).then_some((residual, applied));
    CarriedEntry {
        entry,
        remainder,
        staged,
    }
}

/// The coordinate of `value` on `2^(−S)ℤ`, when it lies there (`None` otherwise).
fn dyadic_coordinate(value: &Rat, exponent: u32) -> Option<BigInt> {
    let denominator = value.denom();
    let twos = denominator.trailing_zeros().unwrap_or(0);
    (denominator.bits() == twos + 1 && twos <= u64::from(exponent))
        .then(|| value.numer() << (u64::from(exponent) - twos) as usize)
}

/// Carry a matrix update onto a lattice-valued matrix, refusing a mismatched shape.
fn carried_matrix(
    carry: &mut Carry,
    at: &mut BudgetedCarry,
    carrier: Carrier,
    matrix: &ExactRatMatrix,
    update: &ExactRatMatrix,
    what: &'static str,
) -> Result<ExactRatMatrix, HnnError> {
    if (update.rows(), update.columns()) != (matrix.rows(), matrix.columns()) {
        return Err(HnnError::Shape {
            what,
            expected: matrix.rows() * matrix.columns(),
            found: update.rows() * update.columns(),
        });
    }
    let mut entries = matrix.entries().to_vec();
    carry.deposit_all(at, carrier, &mut entries, update.entries());
    flat_matrix(matrix.rows(), matrix.columns(), entries)
}

fn flat_matrix(rows: usize, columns: usize, entries: Vec<Rat>) -> Result<ExactRatMatrix, HnnError> {
    let rows_vec: Vec<Vec<Rat>> = if columns == 0 {
        vec![Vec::new(); rows]
    } else {
        entries.chunks(columns).map(<[Rat]>::to_vec).collect()
    };
    Ok(ExactRatMatrix::shaped(rows, columns, rows_vec)?)
}

/// [definition] **The constitution's bits by carrier** (the budget's parts): the lattice entries
/// (maps, factors, statistics), their carried remainders, and the solved charts `X̂ ≈ H⁻¹` of the
/// carried Grams at their lattices, with their certificates; each value counted by its numerator's
/// and denominator's bits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CarrierBits {
    pub entries: u64,
    pub remainders: u64,
    pub solved: u64,
}

impl CarrierBits {
    pub fn total(&self) -> u64 {
        self.entries + self.remainders + self.solved
    }

    fn add(&mut self, other: CarrierBits) {
        self.entries += other.entries;
        self.remainders += other.remainders;
        self.solved += other.solved;
    }
}

// -------------------------------------------------------------------------------------------
// loci

/// [definition] **A locus of the constitution**, as the collapse and the budget name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Locus {
    /// Ring `g`'s element: `W_s`, the slices, `W_c` (edge `g → g`).
    Element(usize),
    /// Ring `g`'s junction: `Y_g` (edges `g → g`, `g → h`), declared.
    Junction(usize),
    /// Contact `a`'s channel: `c_a`, `b_a`, `F_a` and its matchings.
    Channel(usize),
    /// Contact `a`'s conductance `G_a`: `Y_a`, `β_a` and the pair geometry, declared.
    Conductance(usize),
    /// Ring `g`'s source ports `E_g`, `E_g^(δ)`, `I_g`.
    SourcePort(usize),
    /// Ring `g`'s standing `q_g`.
    Standing(usize),
    /// Ring `g`'s loaded resonator's four squared gain coordinates `(C,K,D,pump)`.
    Resonator(usize),
    /// Ring `g`'s receiving map `R`.
    ReceivingMap(usize),
}

impl Locus {
    /// **The design's operator-entry count** of a locus: an element's `n_g²`, a channel's `3k_a²`
    /// (its `C`, `K`, `D`), four scalar resonator gains, and zero for the other loci (design (a),
    /// retention item 3, the count the retired `release.py` reported:
    /// [`d4596102`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release.py)).
    pub fn entries(&self, field: &Field) -> usize {
        match *self {
            Locus::Element(ring) => field.ring(ring).width().pow(2),
            Locus::Resonator(_) => 4,
            Locus::Channel(contact) => 3 * field.contact(contact).width().pow(2),
            _ => 0,
        }
    }
}

// -------------------------------------------------------------------------------------------
// steps

// -------------------------------------------------------------------------------------------
// the solved chart

/// `⌈log₂ x⌉` for `x ≥ 1` (`0` at `x ≤ 1`).
fn ceil_log2(x: u128) -> u32 {
    if x <= 1 {
        0
    } else {
        128 - (x - 1).leading_zeros()
    }
}

/// The widest shift a residual's coordinates take: `2^(L_s + e_H)` with its sign and one more bit
/// of headroom stays inside the `i128` carrier.
const RESIDUAL_SHIFT: u32 = 125;

/// [definition; agent-inferred] **The chart rule of a normal law's locus** (the lattice word; Lean
/// `HNN/LatticeWord.{prox_chart_certificate, rounded_refinement_certificate_left,
/// roundedIter_certificate}`), declared from the locus's carrier lattice `L_ℓ` and the finest
/// admitted receiver grain `L_R`, as `L_ℓ` is from `L_R` and `X_ℓ`:
///
/// ```text
/// target     δ_ℓ = 2^(−D_ℓ) ,   D_ℓ = 2L_ℓ + 1 − ⌊log₂ L_R⌋        (so δ_ℓ ≤ L_R·2^(−2L_ℓ−1))
/// lattice    L_s = D_ℓ + ⌈log₂ n⌉ + ⌈log₂ ‖H'‖∞⌉ + 2                (n the Gram's width)
/// ```
///
/// **Why the target.** At an executed chart `X̂` of the carried successor Gram `H'`, the map step
/// `ΔW = γ Σ w g fᵀX̂` leaves the prox identity `(W + ΔW)H' = WH' + γG` (`G = Σ w g fᵀ`) with the
/// released residual `ρ = γG(1 − X̂H')` (`prox_chart_residual`, summed over the window's returns),
/// `‖ρ‖∞ ≤ ‖γG‖∞ δ` (`prox_chart_certificate`). The map differs from the exact prox step's by
/// `−ρH'⁻¹`, so a read at an operand `x` moves by `|ρ_i H'⁻¹ x| ≤ ‖ρ_i‖₂‖x‖₂/λ_min(H') ≤
/// ‖ρ‖∞‖x‖₁/c`, with `c = 1 − 1/(2L_R)` the carried Gram's margin (`carried_gram_posDef_rule`).
/// One return of a unit-scale covector (`‖wηg‖∞ ≤ 1`, the lattice rule's assumption, which the
/// certified step enforces) and a feature
/// `‖f‖₁ ≤ X_ℓ` read at an operand `‖x‖₁ ≤ X_ℓ` therefore moves by at most `X_ℓ²δ/c`; the lattice
/// rule's `2L_R X_ℓ ≤ 2^(L_ℓ)` makes that at most `2^(2L_ℓ)δ/(2L_R(2L_R − 1)) ≤ 1/(4L_R)` at
/// `δ ≤ δ_ℓ`: the chart's release moves a read by no more than a carried remainder does
/// (`remainder_below_grain`), below the receiver's grain. Each deposit reports the bound its own
/// returns reach ([`ChartReading::read`]), so the unit-scale assumption is measured, as the lattice
/// rule's is.
///
/// **Why the lattice.** A rounded refinement adds to the certificate the chart's rounding
/// `‖ΔH'‖∞ ≤ n·2^(−L_s)/2·‖H'‖∞` (`rounded_refinement_certificate_left`) and the residual's rounding at
/// the chart's lattice, `‖(R̃ − R)X̂H'‖∞ ≤ n·2^(−L_s)/2·(1 + δ)`; together at most
/// `2n·2^(−L_s)‖H'‖∞ ≤ δ_ℓ/2`, so from any certificate at most `δ_ℓ` every rounded refinement stays
/// at most `δ_ℓ` (`roundedIter_certificate` at `c = δ_ℓ ≤ 1/2`), and from above it the certificates
/// fall to the fixed point near `δ_ℓ/2`. The Gram's own norm is read at each deposit, as the clock's
/// Elias-gamma length is: the lattice refines as the Gram grows, and never coarsens (a coarser chart
/// is a finer one's lattice point). Brandon may override the rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartRule {
    lattice: Lattice,
    grain: u128,
}

impl ChartRule {
    /// At a locus's carrier lattice and the finest admitted receiver grain `L_R ≥ 1`.
    pub fn new(lattice: Lattice, grain: u128) -> Self {
        Self {
            lattice,
            grain: grain.max(1),
        }
    }

    /// `L_ℓ`'s lattice.
    pub fn lattice(&self) -> Lattice {
        self.lattice
    }

    /// `L_R`.
    pub fn grain(&self) -> u128 {
        self.grain
    }

    /// `D_ℓ = 2L_ℓ + 1 − ⌊log₂ L_R⌋` (at least 1).
    pub fn target_exponent(&self) -> u32 {
        (2 * self.lattice.exponent() + 1)
            .saturating_sub(self.grain.ilog2())
            .max(1)
    }

    /// `δ_ℓ = 2^(−D_ℓ)`.
    pub fn target(&self) -> Rat {
        Lattice::new(self.target_exponent()).unit()
    }

    /// `L_s = D_ℓ + ⌈log₂ n⌉ + ⌈log₂ ‖H'‖∞⌉ + 2` for a Gram of width `n` whose norm has
    /// `⌈log₂ ‖H'‖∞⌉ = norm`.
    pub fn exponent(&self, width: usize, norm: u32) -> u32 {
        self.target_exponent() + ceil_log2(width as u128) + norm + 2
    }

    /// **The most a released prox residual of norm `‖ρ‖∞ ≤ released` moves a read** at an operand
    /// of ℓ1 norm `X_ℓ ≤ 2^(L_ℓ)/(2L_R)`: `released · X_ℓ/c ≤ released · 2^(L_ℓ)/(2L_R − 1)`.
    pub fn read(&self, released: &Rat) -> Rat {
        released * Rat::new(self.lattice.scale(), BigInt::from(2 * self.grain - 1))
    }

    /// **The refinements one phase may take**: from the scaled identity `2^(−a)I`,
    /// `a = ⌈log₂ ‖H'‖∞⌉`, the residual `1 − 2^(−a)H'` has spectrum in `[0, 1 − 2^(−a)c]`, and
    /// `k` refinements raise it to the `2^k`-th power (`newton_schulz_iter_left`); its row
    /// certificate is at most `√n` times its spectral radius, so
    /// `a + ⌈log₂(D_ℓ + ⌈log₂ n⌉ + 2)⌉ + 4` refinements reach `δ_ℓ` with the rounding's margin.
    fn refinements(&self, width: usize, norm: u32) -> u32 {
        let depth = u128::from(self.target_exponent() + ceil_log2(width as u128) + 2);
        norm + ceil_log2(depth) + 4
    }
}

/// [definition; agent-inferred] **The solved chart** `X̂ ≈ H⁻¹` of a normal law's carried Gram
/// (the lattice word; Lean `HNN/LatticeWord`): a symmetric lattice matrix on `2^(−L_s)ℤ` with its certified
/// left residual `δ = ‖1 − X̂H‖∞`, computed exactly. The Gram is the identity off its **support**
/// (the rows where a deposit moved it: `H = I + Σ w f fᵀ` moves only rows some feature reached), and
/// so is the chart; the chart is carried on the support as integer coordinates (`i128`, with the
/// carrier refused past it), and every product it takes is an integer product. The founding chart is
/// exact: `H_0 = I`, `X̂ = I`, `δ = 0`.
///
/// A deposit ([`SolvedChart::deposited`]) moves the Gram to `H' = H + Σ w f fᵀ` (carried) and the
/// chart in three stages, each on the successor's lattice:
///
/// ```text
/// warm start   X₀ = X̂ − X̂F(Ω⁻¹ + FᵀX̂F)⁻¹FᵀX̂      the window's returns F, Ω = diag(w), one rank-one step each, rounded
///              1 − X₀(H + FΩFᵀ) = (1 − X̂FS⁻¹Fᵀ)(1 − X̂H)                                              (exact identity)
/// certificate  δ = ‖1 − X₀H'‖∞                      exact, from integer products
/// refinement   X ← round((2 − XH')X) = round(X + R X) ,  R = 1 − XH'     until δ ≤ δ_ℓ ;  1 − X'H' = R² − (rounding)H'
/// ```
///
/// [agent-inferred] The previous chart alone is not a warm start: after a deposit it has residual
/// `(1 − X̂H) − X̂ΔH` (`warm_start_residual`), whose certificate `δ + ‖ΔH‖∞‖X̂‖∞`
/// (`warm_start_certificate`) passes 1 whenever a return's feature is large (`‖f fᵀ‖∞` up to
/// `X_ℓ²`), and the exact residual `−H⁻¹ΔH` then has spectral radius above 1, where Newton–Schulz
/// diverges. The window's rank-one steps (Sherman–Morrison, read at the chart's lattice) carry the
/// residual instead: with `S = Ω⁻¹ + FᵀX̂F` the identity above holds in any ring (it expands to
/// `X̂F[Ω − S⁻¹(Ω⁻¹ + FᵀX̂F)Ω]Fᵀ = 0`), so an exact chart stays exact and a certified one keeps its
/// residual up to `1 − X̂FS⁻¹Fᵀ` (near `H'⁻¹H`). The Lean statement of that identity is owed in #62
/// ("Step 4 (#73) owed"); nothing rests on it, since the certificate is computed exactly afterwards.
/// When the warm start's certificate is not below 1, or a refinement does not lower it, the chart
/// restarts from the scaled identity `2^(−a)I`, whose residual is contracting (spectrum in `[0, 1)`).
/// A refinement that does not reach `δ_ℓ` within the rule's count is refused. Sherman–Morrison and the
/// exact inversion are retired as solves: the rank-one steps are only the warm start.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolvedChart {
    /// `L_s`: every entry lies on `2^(−L_s)ℤ`.
    exponent: u32,
    /// The Gram's support `S`, ascending; off it the chart is the identity.
    support: Vec<usize>,
    /// The chart on `S × S` as integer coordinates at `2^(−L_s)`, row-major and symmetric.
    block: Vec<i128>,
    /// `δ = ‖1 − X̂H‖∞`, exact.
    certificate: Rat,
}

/// What one deposit's refinement of a chart read: the warm start's certificate (`None` when it left
/// the `i128` carrier), the refinements taken, whether it restarted from the scaled identity, and the
/// bits of the certified residual `1 − X̂H'` (its nonzero entries, reduced).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Refinement {
    warm: Option<Rat>,
    refinements: u32,
    cold: bool,
    residual_bits: u64,
}

/// A carried Gram read on its support: the support, the finest dyadic exponent `e_H` of its entries
/// there, their integer coordinates at `2^(−e_H)` (row-major), and `⌈log₂ ‖H‖∞⌉` (0 at most 1).
struct GramBlock {
    support: Vec<usize>,
    exponent: u32,
    coordinates: Vec<i128>,
    norm: u32,
}

impl GramBlock {
    /// Read a carried Gram (every entry on a dyadic lattice), refusing a coordinate past `i128` and an
    /// entry off every dyadic lattice (a Gram that is not carried has no chart).
    fn of(gram: &[Vec<Rat>]) -> Result<Self, HnnError> {
        let support: Vec<usize> = (0..gram.len())
            .filter(|&i| {
                gram[i].iter().enumerate().any(
                    |(j, x)| {
                        if i == j { !x.is_one() } else { !x.is_zero() }
                    },
                )
            })
            .collect();
        let s = support.len();
        let mut exponent = 0u32;
        for &i in &support {
            for &j in &support {
                let denominator = gram[i][j].denom();
                let twos = denominator.trailing_zeros().unwrap_or(0);
                if denominator.bits() != twos + 1 {
                    return Err(ExactLinearError::InverseCertificateFailure.into());
                }
                exponent = exponent.max(twos as u32);
            }
        }
        let overflow = || HnnError::from(ExactLinearError::ExtentOverflow);
        let mut coordinates = Vec::with_capacity(s * s);
        let mut widest = 1u128 << exponent;
        for &i in &support {
            let mut row = 0u128;
            for &j in &support {
                let value = &gram[i][j];
                let twos = value.denom().trailing_zeros().unwrap_or(0) as u32;
                let coordinate = (value.numer() << (exponent - twos) as usize)
                    .to_i128()
                    .ok_or_else(overflow)?;
                row = row
                    .checked_add(coordinate.unsigned_abs())
                    .ok_or_else(overflow)?;
                coordinates.push(coordinate);
            }
            widest = widest.max(row);
        }
        let norm = ceil_log2(widest).saturating_sub(exponent);
        Ok(Self {
            support,
            exponent,
            coordinates,
            norm,
        })
    }
}

/// One row of an integer product, exact: in the `i128` carrier while every partial sum fits it,
/// otherwise in bounded-bit integers (the row's bits are at most the operands' plus `⌈log₂ s⌉`).
enum ProductRow {
    Narrow(Vec<i128>),
    Wide(Vec<BigInt>),
}

impl ProductRow {
    /// Row `row · B` of an `s × s` row-major `B`.
    fn of(row: &[i128], matrix: &[i128], s: usize) -> Self {
        let mut sums = vec![0i128; s];
        let narrow = 'narrow: {
            for (k, &left) in row.iter().enumerate() {
                if left == 0 {
                    continue;
                }
                for (sum, &right) in sums.iter_mut().zip(&matrix[k * s..(k + 1) * s]) {
                    match left
                        .checked_mul(right)
                        .and_then(|term| sum.checked_add(term))
                    {
                        Some(value) => *sum = value,
                        None => break 'narrow false,
                    }
                }
            }
            true
        };
        if narrow {
            return ProductRow::Narrow(sums);
        }
        let mut sums = vec![BigInt::zero(); s];
        for (k, &left) in row.iter().enumerate() {
            if left == 0 {
                continue;
            }
            let left = BigInt::from(left);
            for (sum, &right) in sums.iter_mut().zip(&matrix[k * s..(k + 1) * s]) {
                if right != 0 {
                    *sum += &left * right;
                }
            }
        }
        ProductRow::Wide(sums)
    }

    /// Entry `j` with `offset − entry` taken, in the `i128` carrier or `None`.
    fn subtracted_from(&self, j: usize, offset: i128) -> Option<i128> {
        match self {
            ProductRow::Narrow(sums) => offset.checked_sub(sums[j]),
            ProductRow::Wide(sums) => (BigInt::from(offset) - &sums[j]).to_i128(),
        }
    }

    /// Entry `j` at the nearest point of `2^(−k)` coarser, ties upward, in the `i128` carrier or
    /// `None`.
    fn nearest(&self, j: usize, k: u32) -> Option<i128> {
        match self {
            ProductRow::Narrow(sums) => nearest_shift(sums[j], k),
            ProductRow::Wide(sums) => nearest_shift_wide(&sums[j], k).to_i128(),
        }
    }
}

/// `x·2^(−k)` at its nearest integer, ties upward (Lean `quot` at a coordinate).
fn nearest_shift(x: i128, k: u32) -> Option<i128> {
    if k == 0 {
        return Some(x);
    }
    x.checked_add(1i128 << (k - 1)).map(|y| y >> k)
}

/// `x·2^(−k)` at its nearest integer, ties upward, in bounded-bit integers.
fn nearest_shift_wide(x: &BigInt, k: u32) -> BigInt {
    if k == 0 {
        return x.clone();
    }
    (x + (BigInt::one() << (k - 1) as usize)) >> k as usize
}

/// `numerator / denominator` at its nearest integer, ties upward (`denominator > 0`).
fn nearest_quotient(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let top: BigInt = (numerator << 1usize) + denominator;
    let bottom: BigInt = denominator << 1usize;
    let (mut quotient, residue) = (&top / &bottom, &top % &bottom);
    if residue.is_negative() {
        quotient -= 1;
    }
    quotient
}

/// A symmetric `s × s` block from its upper-triangle rows (row `i` holds columns `i..s`).
fn mirrored(s: usize, upper: Vec<Vec<i128>>) -> Vec<i128> {
    let mut block = vec![0i128; s * s];
    for (i, row) in upper.into_iter().enumerate() {
        for (offset, value) in row.into_iter().enumerate() {
            let j = i + offset;
            block[i * s + j] = value;
            block[j * s + i] = value;
        }
    }
    block
}

/// **The certified residual** of a chart block `X` (at `2^(−L_s)`) against a Gram block `H` (at
/// `2^(−e_H)`): `P = 2^(L_s + e_H)(1 − XH)` exactly, with `δ = max_i Σ_j |P_ij| · 2^(−L_s − e_H)`
/// (Lean `rowNorm`). Each row reads only the shared blocks and writes only its own: the rows run
/// together. `None` when an entry leaves the `i128` carrier.
fn certified(block: &[i128], gram: &[i128], s: usize, shift: u32) -> Option<(Vec<i128>, Rat)> {
    let one = 1i128 << shift;
    let rows: Vec<Option<(Vec<i128>, u128)>> = (0..s)
        .into_par_iter()
        .map(|i| {
            let product = ProductRow::of(&block[i * s..(i + 1) * s], gram, s);
            let mut row = Vec::with_capacity(s);
            let mut sum = 0u128;
            for j in 0..s {
                let value = product.subtracted_from(j, if i == j { one } else { 0 })?;
                sum = sum.checked_add(value.unsigned_abs())?;
                row.push(value);
            }
            Some((row, sum))
        })
        .collect();
    let mut residual = Vec::with_capacity(s * s);
    let mut widest = 0u128;
    for row in rows {
        let (row, sum) = row?;
        widest = widest.max(sum);
        residual.extend(row);
    }
    Some((
        residual,
        Rat::new(BigInt::from(widest), BigInt::one() << shift as usize),
    ))
}

/// **One rounded Newton–Schulz refinement, left form** (Lean `nsStep`, `newton_schulz_left`,
/// `rounded_refinement_certificate_left`): `X' = round(X + R̃X)` on `2^(−L_s)ℤ`, with `R̃` the certified
/// residual `P·2^(−L_s−e_H)` read at the chart's lattice. `X + RX = (2 − XH)X` is symmetric for a
/// symmetric `X` and `H`, so the upper triangle is formed and mirrored. The rows run together. `None`
/// when an entry leaves the `i128` carrier.
fn refined(
    block: &[i128],
    residual: &[i128],
    s: usize,
    gram_exponent: u32,
    exponent: u32,
) -> Option<Vec<i128>> {
    let rounded: Vec<i128> = residual
        .iter()
        .map(|&p| nearest_shift(p, gram_exponent))
        .collect::<Option<_>>()?;
    let upper: Vec<Option<Vec<i128>>> = (0..s)
        .into_par_iter()
        .map(|i| {
            let product = ProductRow::of(&rounded[i * s..(i + 1) * s], block, s);
            (i..s)
                .map(|j| block[i * s + j].checked_add(product.nearest(j, exponent)?))
                .collect()
        })
        .collect();
    Some(mirrored(s, upper.into_iter().collect::<Option<_>>()?))
}

/// **The warm start's rank-one steps** at the chart's lattice (Sherman–Morrison): for each return
/// `(w, f)`, with `f̃` the feature at `2^(−L_s)` and `v = X̂f̃` rounded there,
/// `X̂ ← X̂ − w v vᵀ/(1 + w f̃ᵀv)`, each entry at its nearest lattice point (upper triangle, mirrored).
/// A step whose denominator is not positive is skipped (the certificate then decides). The rows of
/// each step run together.
fn corrected(
    mut block: Vec<i128>,
    s: usize,
    exponent: u32,
    features: &[(&Rat, Vec<BigInt>)],
) -> Result<Vec<i128>, HnnError> {
    let overflow = || HnnError::from(ExactLinearError::ExtentOverflow);
    let shift = exponent as usize;
    for (weight, feature) in features {
        let reach: Vec<BigInt> = (0..s)
            .into_par_iter()
            .map(|i| {
                let mut sum = BigInt::zero();
                for (k, value) in feature.iter().enumerate() {
                    let c = block[i * s + k];
                    if c != 0 && !value.is_zero() {
                        sum += value * c;
                    }
                }
                nearest_shift_wide(&sum, exponent)
            })
            .collect();
        let energy: BigInt = feature.iter().zip(&reach).map(|(f, v)| f * v).sum();
        let denominator: BigInt = (weight.denom() << (2 * shift)) + weight.numer() * &energy;
        if !denominator.is_positive() {
            continue;
        }
        let scaled: Vec<BigInt> = reach
            .iter()
            .map(|v| (weight.numer() * v) << shift)
            .collect();
        let current = &block;
        let upper: Vec<Result<Vec<i128>, HnnError>> = (0..s)
            .into_par_iter()
            .map(|i| {
                (i..s)
                    .map(|j| {
                        let step = nearest_quotient(&(&scaled[i] * &reach[j]), &denominator)
                            .to_i128()
                            .ok_or_else(overflow)?;
                        current[i * s + j].checked_sub(step).ok_or_else(overflow)
                    })
                    .collect()
            })
            .collect();
        block = mirrored(s, upper.into_iter().collect::<Result<_, _>>()?);
    }
    Ok(block)
}

/// The bits of a residual's nonzero entries `P·2^(−shift)`, each as a reduced ratio.
fn residual_bits(residual: &[i128], shift: u32) -> u64 {
    residual
        .iter()
        .filter(|p| **p != 0)
        .map(|&p| lattice_bits(p, shift))
        .sum()
}

/// The bits of the lattice value `c·2^(−L)` as a reduced ratio (numerator and denominator), as
/// [`bits`] counts it.
fn lattice_bits(c: i128, exponent: u32) -> u64 {
    if c == 0 {
        return 1;
    }
    let twos = c.trailing_zeros().min(exponent);
    let magnitude = c.unsigned_abs() >> twos;
    u64::from(128 - magnitude.leading_zeros()) + u64::from(exponent - twos + 1)
}

impl SolvedChart {
    /// **The founding chart**: `H_0 = I`, so `X̂ = I` exactly, `δ = 0`.
    pub fn identity() -> Self {
        Self {
            exponent: 0,
            support: Vec::new(),
            block: Vec::new(),
            certificate: Rat::zero(),
        }
    }

    /// `L_s`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// `δ = ‖1 − X̂H‖∞`, exact.
    pub fn certificate(&self) -> &Rat {
        &self.certificate
    }

    /// The Gram's support the chart is carried on.
    pub fn support(&self) -> &[usize] {
        &self.support
    }

    /// The chart as rows of width `n`.
    pub fn dense(&self, n: usize) -> Vec<Vec<Rat>> {
        let mut rows: Vec<Vec<Rat>> = (0..n).map(|i| unit(n, i)).collect();
        let (s, scale) = (self.support.len(), BigInt::one() << self.exponent as usize);
        for (a, &i) in self.support.iter().enumerate() {
            for (b, &j) in self.support.iter().enumerate() {
                rows[i][j] = Rat::new(BigInt::from(self.block[a * s + b]), scale.clone());
            }
        }
        rows
    }

    /// Its bits at its lattice as a matrix of width `n`, each entry a reduced ratio as [`bits`]
    /// counts the other carriers (off the support: `1` on the diagonal, `0` elsewhere), with the
    /// certificate's.
    fn bits(&self, n: usize) -> u64 {
        let s = self.support.len();
        let outside = (n * n - s * s) as u64 + (n - s) as u64;
        let block: u64 = self
            .block
            .iter()
            .map(|&c| lattice_bits(c, self.exponent))
            .sum();
        outside + block + bits(&self.certificate)
    }

    /// **The reach `X̂f`** of a feature in the integral chart (`F / d`), in the integral chart
    /// (`over d·2^(L_s)`): the identity off the support.
    fn reach(&self, (values, denominator): &Chart) -> Chart {
        let shift = self.exponent as usize;
        let mut reach: Vec<BigInt> = values.iter().map(|value| value << shift).collect();
        let s = self.support.len();
        for (a, &i) in self.support.iter().enumerate() {
            let mut sum = BigInt::zero();
            for (b, &k) in self.support.iter().enumerate() {
                let c = self.block[a * s + b];
                if c != 0 && !values[k].is_zero() {
                    sum += &values[k] * c;
                }
            }
            reach[i] = sum;
        }
        (reach, denominator << shift)
    }

    /// The chart carried onto another support at a lattice at least as fine: an entry both
    /// supports hold moves by `2^(L − L_s)` exactly, and an index the chart did not hold enters as the
    /// identity's.
    fn carried_to(&self, support: &[usize], exponent: u32) -> Result<Vec<i128>, HnnError> {
        let s = support.len();
        // Every chart and the rule's lattice lie within the residual's shift, so the move fits.
        let shift = exponent - self.exponent;
        if exponent > RESIDUAL_SHIFT {
            return Err(ExactLinearError::ExtentOverflow.into());
        }
        let scale = 1i128 << shift;
        let held: BTreeMap<usize, usize> = self
            .support
            .iter()
            .enumerate()
            .map(|(a, &i)| (i, a))
            .collect();
        let width = self.support.len();
        let mut block = vec![0i128; s * s];
        for (a, i) in support.iter().enumerate() {
            for (b, j) in support.iter().enumerate() {
                let value = match (held.get(i), held.get(j)) {
                    (Some(&p), Some(&q)) => self.block[p * width + q],
                    _ if a == b => 1i128 << self.exponent,
                    _ => 0,
                };
                block[a * s + b] = value
                    .checked_mul(scale)
                    .ok_or(ExactLinearError::ExtentOverflow)?;
            }
        }
        Ok(block)
    }

    /// **The successor's chart** (the type's header): the Gram `gram` is the carried successor, and
    /// `features` the window's returns `(w, f)` in the integral chart. Refused past the `i128` carrier
    /// or when the refinement does not reach `δ_ℓ` within the rule's count.
    fn deposited(
        &self,
        gram: &[Vec<Rat>],
        features: &[(&Rat, &Chart)],
        rule: &ChartRule,
    ) -> Result<(Self, Refinement), HnnError> {
        let n = gram.len();
        let carried = GramBlock::of(gram)?;
        let s = carried.support.len();
        let exponent = rule.exponent(n, carried.norm).max(self.exponent);
        let shift = exponent + carried.exponent;
        if shift > RESIDUAL_SHIFT {
            return Err(ExactLinearError::ExtentOverflow.into());
        }
        if s == 0 {
            let chart = Self {
                exponent,
                ..Self::identity()
            };
            let refinement = Refinement {
                warm: Some(Rat::zero()),
                refinements: 0,
                cold: false,
                residual_bits: 0,
            };
            return Ok((chart, refinement));
        }
        // The returns on the support at the chart's lattice.
        let features: Vec<(&Rat, Vec<BigInt>)> = features
            .iter()
            .map(|(weight, (values, denominator))| {
                let feature = carried
                    .support
                    .iter()
                    .map(|&k| {
                        let value = &values[k] << exponent as usize;
                        if denominator.is_one() {
                            value
                        } else {
                            nearest_quotient(&value, denominator)
                        }
                    })
                    .collect();
                (*weight, feature)
            })
            .collect();
        let target = rule.target();
        let warm = corrected(
            self.carried_to(&carried.support, exponent)?,
            s,
            exponent,
            &features,
        )?;
        let mut residual = certified(&warm, &carried.coordinates, s, shift);
        let certificate = residual.as_ref().map(|(_, delta)| delta.clone());
        let mut block = warm;
        let limit = rule.refinements(n, carried.norm);
        let (mut refinements, mut phase, mut cold, mut stalled) = (0u32, 0u32, false, false);
        loop {
            if let Some((_, delta)) = &residual
                && *delta <= target
            {
                break;
            }
            let contracting = residual
                .as_ref()
                .is_some_and(|(_, delta)| *delta < Rat::one());
            if !cold && (!contracting || stalled || phase >= limit) {
                // The scaled identity 2^(−a)I: its residual 1 − 2^(−a)H' is contracting.
                cold = true;
                phase = 0;
                block = vec![0i128; s * s];
                for a in 0..s {
                    block[a * s + a] = 1i128 << (exponent - carried.norm);
                }
                residual = certified(&block, &carried.coordinates, s, shift);
                continue;
            }
            let failure = || HnnError::from(ExactLinearError::InverseCertificateFailure);
            if phase >= limit {
                return Err(failure());
            }
            let (p, delta) = residual.as_ref().ok_or_else(failure)?;
            let Some(next) = refined(&block, p, s, carried.exponent, exponent) else {
                // A warm refinement that leaves the carrier restarts; a cold one is refused.
                if cold {
                    return Err(failure());
                }
                stalled = true;
                continue;
            };
            let next_residual = certified(&next, &carried.coordinates, s, shift);
            stalled = next_residual
                .as_ref()
                .is_none_or(|(_, next_delta)| next_delta >= delta);
            block = next;
            residual = next_residual;
            refinements += 1;
            phase += 1;
        }
        let (p, delta) = residual.expect("certified above");
        let chart = Self {
            exponent,
            support: carried.support,
            block,
            certificate: delta,
        };
        let refinement = Refinement {
            warm: certificate,
            refinements,
            cold,
            residual_bits: residual_bits(&p, shift),
        };
        Ok((chart, refinement))
    }
}

/// **One rounded refinement of a dense chart** (a test fixture's reading of the certified residual
/// and the refinement): a symmetric chart on `2^(−exponent)ℤ` against a carried Gram, returning the
/// refined chart with the certificates before and after. `None` when the chart is off its lattice or
/// an entry leaves the `i128` carrier.
#[cfg(test)]
pub(crate) fn refined_once(
    chart: &[Vec<Rat>],
    exponent: u32,
    gram: &[Vec<Rat>],
) -> Option<(Vec<Vec<Rat>>, Rat, Rat)> {
    let carried = GramBlock::of(gram).ok()?;
    let s = carried.support.len();
    let scale = Rat::from_integer(BigInt::one() << exponent as usize);
    let mut block = Vec::with_capacity(s * s);
    for &i in &carried.support {
        for &j in &carried.support {
            let coordinate = &chart[i][j] * &scale;
            if !coordinate.is_integer() {
                return None;
            }
            block.push(coordinate.to_integer().to_i128()?);
        }
    }
    let shift = exponent + carried.exponent;
    let (residual, before) = certified(&block, &carried.coordinates, s, shift)?;
    let next = refined(&block, &residual, s, carried.exponent, exponent)?;
    let (_, after) = certified(&next, &carried.coordinates, s, shift)?;
    let chart = SolvedChart {
        exponent,
        support: carried.support,
        block: next,
        certificate: after.clone(),
    };
    Some((chart.dense(gram.len()), before, after))
}

/// [definition] **One normal law's solved chart at a deposit** (the lattice word; Lean
/// `HNN/LatticeWord.prox_chart_certificate`): the chart's lattice `L_s`, the declared target `δ_ℓ`,
/// the warm start's certificate (`None` when it left the `i128` carrier), the executed chart's
/// certificate `δ = ‖1 − X̂H'‖∞` (exact), the refinements taken and whether the chart restarted from
/// the scaled identity; the **released prox residual** `ρ = γ G (1 − X̂H')` by its certificate
/// `‖ρ‖∞ ≤ Σ_t |wγ| ‖g_t‖∞ ‖f_t‖₁ · δ` (exact; `prox_chart_certificate` per return, summed) and the most
/// it moves a read ([`ChartRule::read`]); and the bits of its factor `1 − X̂H'` (nonzero entries,
/// reduced), the part of `ρ` the deposit's own covectors do not already carry. The release is
/// reported, never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReading {
    pub exponent: u32,
    pub target: Rat,
    pub warm: Option<Rat>,
    pub certificate: Rat,
    pub refinements: u32,
    pub cold: bool,
    pub released: Rat,
    pub read: Rat,
    pub residual_bits: u64,
}

// -------------------------------------------------------------------------------------------
// the normal law

/// [definition] **One observed return at a linear locus**: its weight `w`, its feature `f_t` and
/// its descent covector `g_t` (Lean `HNN/Normal.Sample`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sample {
    pub weight: Rat,
    pub feature: Vec<Rat>,
    pub covector: Vec<Rat>,
}

/// [definition] **One locus's deposition owner** (design (c), `NormalLaw`): the map `W` (`m × n`)
/// and its Gram `H` (`n × n`, the locus's own width), each on the locus's lattice with its carried
/// remainders, and the solved chart `X̂ ≈ H⁻¹` of the carried Gram on its own lattice with its
/// certified residual ([`SolvedChart`], the lattice word). `B = W H` is not carried (module header). Its
/// law is the prox step at the carried Gram through the executed chart (Lean
/// `HNN/Normal.normal_prox_step`, `HNN/LatticeWord.prox_chart_residual`: `W' = W + γ G X̂`, the prox
/// identity holding up to the released residual `γG(1 − X̂H')`) with the carried Gram within one unit
/// of the exact statistic since the locus's founding
/// (`HNN/LatticeDeposit.within_one_unit_since_founding`): `W` is the prox iterate, not the minimizer
/// of the accumulated objective `tr(WHWᵀ) − 2tr(WBᵀ) + C`, which `normalStatistic_standing` states for
/// an exact `(H, B)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalLaw {
    map: ExactRatMatrix,
    gram: Vec<Vec<Rat>>,
    chart: SolvedChart,
    map_carry: Carry,
    gram_carry: Carry,
}

impl NormalLaw {
    /// **The unit prior at a map**: `H_0 = I` (so `B_0 = W_0`), no remainder, and the founding chart
    /// `X̂ = I` exact (`δ = 0`).
    pub fn with_prior(map: ExactRatMatrix) -> Self {
        let n = map.columns();
        let identity: Vec<Vec<Rat>> = (0..n).map(|i| unit(n, i)).collect();
        Self {
            gram: identity,
            chart: SolvedChart::identity(),
            map,
            map_carry: Carry::default(),
            gram_carry: Carry::default(),
        }
    }

    /// `W`.
    pub fn map(&self) -> &ExactRatMatrix {
        &self.map
    }

    /// `H`, the carried Gram.
    pub fn gram(&self) -> ExactRatMatrix {
        rows_matrix(&self.gram)
    }

    /// `X̂ ≈ H⁻¹`, the solved chart of the carried Gram, dense: within `δ` of the inverse in its
    /// left residual, `‖1 − X̂H‖∞ = δ` ([`NormalLaw::chart`]).
    pub fn solved(&self) -> ExactRatMatrix {
        rows_matrix(&self.chart.dense(self.gram.len()))
    }

    /// The solved chart, with its lattice and certificate.
    pub fn chart(&self) -> &SolvedChart {
        &self.chart
    }

    /// `W`'s carried remainders, dense.
    pub fn map_remainder(&self) -> ExactRatMatrix {
        let (m, n) = (self.map.rows(), self.map.columns());
        rows_matrix(
            &(0..m)
                .map(|i| (0..n).map(|j| self.map_carry.at(i * n + j)).collect())
                .collect::<Vec<Vec<Rat>>>(),
        )
    }

    /// `H`'s carried remainders, dense.
    pub fn gram_remainder(&self) -> ExactRatMatrix {
        let n = self.gram.len();
        rows_matrix(
            &(0..n)
                .map(|i| (0..n).map(|j| self.gram_carry.at(i * n + j)).collect())
                .collect::<Vec<Vec<Rat>>>(),
        )
    }

    /// **The carried prox step through the solved chart, prepared at its unit step** (Lean
    /// `HNN/Normal.normal_prox_step`, `HNN/LatticeDeposit.carry`, `HNN/LatticeWord.prox_chart_residual`;
    /// module header, "The certified step"): `ΔH = Σ w f fᵀ` carried onto `H` gives `H'`; the chart of
    /// `H'` follows from the previous chart ([`SolvedChart`]: the warm start, its exact certificate
    /// and the rounded refinements to `δ ≤ δ_ℓ` of the locus's [`ChartRule`]); then the **unit step**
    /// `D = Σ w g (X̂f)ᵀ` is formed in the integral chart with the readings its certificate needs: the
    /// alignment `a = Σ_t w ⟨g_t, D f_t⟩` (checked, never assumed), the feature moves
    /// `b = Σ_t w |D f_t|²`, the lattice's covector scale `c = max_t |w g_t|_∞`, and the Schur norms of
    /// `W` and `D`. The step `η` is certified by the constitution (it reads every locus's gains) and
    /// applied by [`PreparedStep::stepped`]: `ΔW = η D`, so `(W + ΔW)H' = WH' + ηG − ηG(1 − X̂H')`
    /// exactly, with `G = Σ w g fᵀ`. The Gram's carry is at the budgeted carry `at` of the locus's
    /// deposit (its residuals staged there). `None` when the window reached nothing (no nonzero
    /// weighted feature), which moves nothing.
    ///
    /// [definition; agent-inferred] **The sums are read in the integral chart**: each sample's
    /// feature and covector is charted once as integers over its least common denominator
    /// (`ratio::linear::vector::integral`), each reach `X̂f` is an integer product over the feature's
    /// denominator times `2^(L_s)`, each sum of rank-one terms is formed over integers and each entry
    /// normalized once (`D` by row blocks, the symmetric `ΔH` on its upper triangle and mirrored). A
    /// reduced ratio is canonical, so every value equals the termwise rational sum's.
    pub(crate) fn prepare(
        &self,
        samples: &[Sample],
        rule: &ChartRule,
        at: &mut BudgetedCarry,
    ) -> Result<Option<PreparedStep>, HnnError> {
        let (m, n) = (self.map.rows(), self.map.columns());
        for sample in samples {
            if sample.feature.len() != n || sample.covector.len() != m {
                return Err(HnnError::Shape {
                    what: "a normal sample (feature, covector)",
                    expected: n + m,
                    found: sample.feature.len() + sample.covector.len(),
                });
            }
        }
        let active: Vec<(&Sample, Chart)> = samples
            .iter()
            .filter(|sample| !sample.weight.is_zero())
            .filter(|sample| sample.feature.iter().any(|x| !x.is_zero()))
            .map(|sample| (sample, integral(&sample.feature)))
            .collect();
        if active.is_empty() {
            return Ok(None);
        }
        let mut law = self.clone();
        // ΔH = Σ w f fᵀ, carried onto H.
        let gram_update = gram_sum(
            n,
            active
                .iter()
                .map(|(sample, feature)| (&sample.weight, feature)),
        );
        let mut gram: Vec<Rat> = self.gram.iter().flatten().cloned().collect();
        law.gram_carry
            .deposit_all(at, Carrier::Gram, &mut gram, &gram_update);
        law.gram = gram.chunks(n).map(<[Rat]>::to_vec).collect();
        // The chart of H', from the previous chart.
        let features: Vec<(&Rat, &Chart)> = active
            .iter()
            .map(|(sample, feature)| (&sample.weight, feature))
            .collect();
        let (chart, refinement) = self.chart.deposited(&law.gram, &features, rule)?;
        law.chart = chart;
        // The unit step D = Σ w g (X̂f)ᵀ at the successor's chart. Each sample's term reads only its
        // own covector and reach: the samples run together. Each term's `|w| ‖g‖∞ ‖f‖₁` bounds its
        // share of the released prox residual at the unit step, and its `|w| ‖g‖∞` the lattice's
        // covector scale.
        let chart = &law.chart;
        let terms: Vec<(Rat, Chart, Chart, Rat, Rat)> = indexed(active.len(), |t| {
            let (sample, feature) = &active[t];
            let covector = integral(&sample.covector);
            let widest = covector
                .0
                .iter()
                .map(|x| x.magnitude())
                .max()
                .cloned()
                .unwrap_or_default();
            let mass: BigInt = feature
                .0
                .iter()
                .map(|x| BigInt::from(x.magnitude().clone()))
                .sum();
            let scale = sample.weight.abs() * Rat::new(BigInt::from(widest), covector.1.clone());
            let share = &scale * Rat::new(mass, feature.1.clone());
            Ok((
                sample.weight.clone(),
                covector,
                chart.reach(feature),
                share,
                scale,
            ))
        })?;
        let unit = outer_integral(
            m,
            n,
            &terms
                .iter()
                .map(|(weight, covector, reach, ..)| (weight, covector, reach))
                .collect::<Vec<_>>(),
        );
        // a = Σ w ⟨g, D f⟩ and b = Σ w |D f|², each sample's D f read once in the integral chart.
        let reads: Vec<(Rat, Rat)> = indexed(active.len(), |t| {
            let (sample, feature) = &active[t];
            let (moved, denominator) = unit.apply(feature);
            let (covector, covector_denominator) = &terms[t].1;
            let alignment = Rat::new(
                integer_dot(covector, &moved),
                covector_denominator * &denominator,
            );
            let squares: BigInt = moved.iter().map(|x| x * x).sum();
            let moves = Rat::new(squares, &denominator * &denominator);
            Ok((&sample.weight * alignment, &sample.weight * moves))
        })?;
        let (mut alignment, mut moves) = (Rat::zero(), Rat::zero());
        for (a, b) in reads {
            alignment += a;
            moves += b;
        }
        let covector = terms
            .iter()
            .map(|(.., scale)| scale.clone())
            .max()
            .unwrap_or_else(Rat::zero);
        let shares = terms.iter().map(|(_, _, _, share, _)| share).sum::<Rat>();
        Ok(Some(PreparedStep {
            unit_norms: unit.schur_norms(),
            law,
            unit,
            alignment,
            moves,
            covector,
            shares,
            refinement,
            target: rule.target(),
            rule: *rule,
        }))
    }

    /// **The carried prox step at a given step `η`** ([`NormalLaw::prepare`] then
    /// [`PreparedStep::stepped`]): the law's own step (Lean `HNN/Normal.normal_prox_step` at
    /// `γ = η`), which a deposit takes at its certified step and a test at any step. Returns the
    /// successor with its chart's reading, `None` when the window reached nothing.
    pub fn deposited(
        &self,
        samples: &[Sample],
        step: &Rat,
        rule: &ChartRule,
        at: &mut BudgetedCarry,
    ) -> Result<(Self, Option<ChartReading>), HnnError> {
        match self.prepare(samples, rule, at)? {
            None => Ok((self.clone(), None)),
            Some(prepared) => {
                let (next, reading) = prepared.stepped(step, at)?;
                Ok((next, Some(reading)))
            }
        }
    }

    /// Its bits by carrier.
    fn carrier_bits(&self) -> CarrierBits {
        CarrierBits {
            entries: self
                .map
                .entries()
                .iter()
                .chain(self.gram.iter().flatten())
                .map(bits)
                .sum(),
            remainders: self.map_carry.bits() + self.gram_carry.bits(),
            solved: self.chart.bits(self.gram.len()),
        }
    }

    /// Whether every entry of `W` and `H` lies on the lattice.
    fn on_lattice(&self, lattice: &Lattice) -> bool {
        self.map
            .entries()
            .iter()
            .chain(self.gram.iter().flatten())
            .all(|value| lattice.contains(value))
    }
}

/// [definition; agent-inferred] **A normal law's step prepared at its unit step**
/// ([`NormalLaw::prepare`]): the law with its Gram and chart carried (its map not yet moved), the
/// unit step `D` in the integral chart, its alignment `a`, its feature moves `b`, the lattice's
/// covector scale `c`, the Schur norms of `D`, the released residual's factor at the unit step, and
/// the chart's refinement.
pub(crate) struct PreparedStep {
    law: NormalLaw,
    unit: IntegralMatrix,
    alignment: Rat,
    moves: Rat,
    covector: Rat,
    shares: Rat,
    unit_norms: (Rat, Rat),
    refinement: Refinement,
    target: Rat,
    rule: ChartRule,
}

impl PreparedStep {
    /// **The step taken at `η`** (module header, "The certified step"): `ΔW = η D` carried onto `W`
    /// at the locus's budgeted carry, with the chart's reading: its certificate and the released prox
    /// residual `ρ = ηG(1 − X̂H')` by `‖ρ‖∞ ≤ η Σ_t |w| ‖g_t‖∞ ‖f_t‖₁ · δ`.
    pub(crate) fn stepped(
        self,
        step: &Rat,
        at: &mut BudgetedCarry,
    ) -> Result<(NormalLaw, ChartReading), HnnError> {
        let (m, n) = (self.law.map.rows(), self.law.map.columns());
        let mut next = self.law;
        let update: Vec<Rat> = self.unit.scaled_rows(step).into_iter().flatten().collect();
        let mut map = next.map.entries().to_vec();
        next.map_carry
            .deposit_all(at, Carrier::Map, &mut map, &update);
        next.map = flat_matrix(m, n, map)?;
        let released = next.chart.certificate() * step * &self.shares;
        let reading = ChartReading {
            exponent: next.chart.exponent(),
            target: self.target,
            warm: self.refinement.warm,
            certificate: next.chart.certificate().clone(),
            refinements: self.refinement.refinements,
            cold: self.refinement.cold,
            read: self.rule.read(&released),
            released,
            residual_bits: self.refinement.residual_bits,
        };
        Ok((next, reading))
    }
}

/// **`Σ_t w_t f_t f_tᵀ` in the integral chart**: each feature charted once, the numerators summed
/// over integers on the terms' common denominator, and each entry of the upper triangle normalized
/// once; the form is symmetric, so the lower triangle is its mirror. Each row of the upper triangle
/// reads only the shared features and writes only its own entries: the rows run together
/// (`hnn::realization`).
fn gram_sum<'a>(n: usize, terms: impl IntoIterator<Item = (&'a Rat, &'a Chart)>) -> Vec<Rat> {
    let terms: Vec<(&Rat, &Chart, BigInt)> = terms
        .into_iter()
        .map(|(weight, feature)| (weight, feature, weight.denom() * &feature.1 * &feature.1))
        .collect();
    let denominator = terms
        .iter()
        .fold(BigInt::one(), |common, (.., scale)| lcm(&common, scale));
    let factors: Vec<BigInt> = terms
        .iter()
        .map(|(weight, _, scale)| weight.numer() * (&denominator / scale))
        .collect();
    let rows: Vec<Vec<Rat>> = (0..n)
        .into_par_iter()
        .map(|i| {
            let mut numerators = vec![BigInt::zero(); n - i];
            for ((_, (values, _), _), factor) in terms.iter().zip(&factors) {
                if values[i].is_zero() {
                    continue;
                }
                let left = &values[i] * factor;
                for j in i..n {
                    if !values[j].is_zero() {
                        numerators[j - i] += &left * &values[j];
                    }
                }
            }
            numerators
                .into_iter()
                .map(|numerator| {
                    if numerator.is_zero() {
                        Rat::zero()
                    } else {
                        Rat::new(numerator, denominator.clone())
                    }
                })
                .collect()
        })
        .collect();
    let mut entries = vec![Rat::zero(); n * n];
    for (i, row) in rows.into_iter().enumerate() {
        for (offset, value) in row.into_iter().enumerate() {
            let j = i + offset;
            if value.is_zero() {
                continue;
            }
            entries[j * n + i] = value.clone();
            entries[i * n + j] = value;
        }
    }
    entries
}

/// **The factor step's update `rate · g`**, the canonical product of two reduced ratios:
/// `(a/b)(c/d) = (a/g₁ · c/g₂) / (b/g₂ · d/g₁)` with `g₁ = gcd(a, d)`, `g₂ = gcd(c, b)`, the same
/// reduced value as `Ratio`'s product.
///
/// [definition; agent-inferred] The rate `η_x / h_x` is a small lattice ratio and the gradient
/// entry a large one (thousands of bits, from the pullback), so each cross `gcd` pairs a small
/// operand with a large one. It is read by Euclid's remainder first (`crate::ratio::gcd`), which
/// costs the large operand's size once; the binary `gcd` behind `Ratio`'s product halves the large
/// operand a bit at a time, paying its full size on every step. The value is `Ratio`'s (receipt:
/// the equality run of the notebook's `hnn_lattice_growth`, retired at `2d34b819`, which
/// recomputed every factor update as `Ratio`'s product, [`NormalLaw::deposited`]).
fn rate_times(rate: &Rat, value: &Rat) -> Rat {
    if rate.is_zero() || value.is_zero() {
        return Rat::zero();
    }
    let first = crate::ratio::gcd(rate.numer(), value.denom());
    let second = crate::ratio::gcd(value.numer(), rate.denom());
    Rat::new_raw(
        (rate.numer() / &first) * (value.numer() / &second),
        (rate.denom() / &second) * (value.denom() / &first),
    )
}

/// `rate · G` entry by entry ([`rate_times`]).
fn rate_matrix(rate: &Rat, matrix: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    let entries: Vec<Rat> = matrix
        .entries()
        .iter()
        .map(|x| rate_times(rate, x))
        .collect();
    flat_matrix(matrix.rows(), matrix.columns(), entries)
}

fn rows_matrix(rows: &[Vec<Rat>]) -> ExactRatMatrix {
    let columns = rows.first().map_or(0, Vec::len);
    ExactRatMatrix::shaped(rows.len(), columns, rows.to_vec()).expect("rows of one width")
}

fn bits(value: &Rat) -> u64 {
    value.numer().bits() + value.denom().bits()
}

// -------------------------------------------------------------------------------------------
// the material

#[derive(Clone, Debug, PartialEq, Eq)]
struct RingMaterial {
    standing: Vec<Rat>,
    standing_scale: Rat,
    passive: ExactRatMatrix,
    passive_scale: Rat,
    contrast: NormalLaw,
    slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    slice_scale: Rat,
    source: Option<NormalLaw>,
    pairs: Vec<(usize, PairPort)>,
    pair_scale: Rat,
    receiving: Option<NormalLaw>,
    /// The receiving parametron's landmark tree (`compression::landmark::context`), on a receiving ring.
    tree: Option<Landmarks>,
    /// The receiver's population over the tree's face and the combined face (ruling A; THE_REBUILD
    /// U1, `hnn::receiving::receiving_population`), on a receiving ring: their likelihoods.
    population: Option<PortPopulation>,
    /// The ring's loaded resonator: immutable base forms with learned scalar amplitudes.
    resonator: Option<ResonatorMaterial>,
    /// The four factor-family statistics for its squared gain coordinates.
    resonator_scales: [Rat; 4],
    /// The hop at which every candidate resonator material is certified.
    resonator_step: Option<Rat>,
    /// [definition; agent-inferred, September 30] **The source navigator's transport modulus**
    /// `ρ_g ∈ (0, 1]` a tick (`hnn::moment`, "One passage, its transported weights"): a crossing
    /// `a` ticks old is carried to the reading frame at `ρ^a`. One (a rotation, nothing lost) at the
    /// founding; part of the source port's locus, on its lattice.
    transport: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ContactMaterial {
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    scales: [Rat; 3],
    /// A declared boost (campaign 2, `hnn::contact`): the stiffness factor's column signs and the
    /// certification context its every solve is checked in.
    boost: Option<Boost>,
    /// The declared surface-storage density `γ` of the contact's break law (#31).
    surface: Option<Rat>,
}

/// [definition] **A declared boost**: the signature `σ` of the stiffness factor's columns
/// (`K = b diag(σ) bᵀ`), the conductances the contact can take (`None` when a screw's pitch makes the
/// family infinite; then the signed form must certify every conductance at once) and the hop.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Boost {
    signature: Vec<bool>,
    conductances: Option<Vec<Rat>>,
    step: Rat,
}

impl Boost {
    /// **Certify a boost's material** (Lean `HNN/Contact.contact_boost_solve_or_singular_direction`):
    /// the signed form certifies every conductance at once, or else each admitted conductance's
    /// operator is nonsingular; a refusal carries the singular direction.
    fn certify(&self, contact: usize, material: &ContactMaterial) -> Result<(), HnnError> {
        let storage = gram(&material.storage)?;
        let stiffness = signed_stiffness(&material.stiffness, Some(&self.signature))?;
        let dissipation = gram(&material.dissipation)?;
        if signed_form_certifies(&storage, &stiffness, &dissipation, &self.step)? {
            return Ok(());
        }
        let Some(conductances) = &self.conductances else {
            return Err(HnnError::UncertifiedBoost { contact });
        };
        for conductance in conductances {
            certify_boost(
                contact,
                [&storage, &stiffness, &dissipation],
                conductance,
                &self.step,
            )?;
        }
        Ok(())
    }
}

/// A gradient on a signed factor: `∂⟨K̄, b diag(σ) bᵀ⟩/∂b = (K̄ + K̄ᵀ) b diag(σ)`, the Gram factor's
/// gradient with each column multiplied by its sign.
fn signed_columns(
    gradient: &ExactRatMatrix,
    signature: &[bool],
) -> Result<ExactRatMatrix, HnnError> {
    if signature.len() != gradient.columns() {
        return Err(HnnError::Shape {
            what: "a stiffness signature (one sign per factor column)",
            expected: gradient.columns(),
            found: signature.len(),
        });
    }
    Ok(ExactRatMatrix::shaped(
        gradient.rows(),
        gradient.columns(),
        (0..gradient.rows())
            .map(|i| {
                (0..gradient.columns())
                    .map(|j| {
                        let entry = gradient.get(i, j).expect("in range").clone();
                        if signature[j] { entry } else { -entry }
                    })
                    .collect()
            })
            .collect(),
    )?)
}

/// [definition] **A carried array of a locus**: an array whose entries live on the locus's
/// lattice with their carried remainders. `Map` and `Gram` are a normal law's `W` and `H` (the
/// contrast port's on an element, `E`'s on a source port, `R`'s on a receiving map); the others are
/// the factor families' entries and statistics `h_x`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Carrier {
    Map,
    Gram,
    Passive,
    PassiveScale,
    Slices,
    SliceScale,
    Standing,
    StandingScale,
    Resonator(usize),
    ResonatorScale(usize),
    /// Family 0, 1, 2: the outputs `e`, the current reads `a`, the earlier reads `b`.
    Pair {
        offset: usize,
        family: usize,
    },
    PairScale,
    /// 0, 1, 2: the storage `c`, the stiffness `b`, the dissipation `F`.
    Factor(usize),
    FactorScale(usize),
}

type Carries = BTreeMap<(Locus, Carrier), Carry>;

/// `h_x' = h_x + Σ w|f|²`, carried on the family's lattice: the family's metric, whose unit step is
/// `G_x / h_x'`. Refused when the carried statistic is not positive.
fn advance(
    carries: &mut Carries,
    at: &mut BudgetedCarry,
    key: (Locus, Carrier),
    scale: &mut Rat,
    energy: &Rat,
) -> Result<Rat, HnnError> {
    carries
        .entry(key)
        .or_default()
        .deposit(at, key.1, 0, scale, energy);
    if !scale.is_positive() {
        return Err(HnnError::FactorStatistic {
            locus: key.0,
            statistic: scale.clone(),
        });
    }
    Ok(scale.clone())
}

/// Carry `rate · delta` onto a family of vectors, flat in row order.
fn carried_rows(
    carry: &mut Carry,
    at: &mut BudgetedCarry,
    carrier: Carrier,
    base: &[Vec<Rat>],
    delta: &[Vec<Rat>],
    rate: &Rat,
) -> Vec<Vec<Rat>> {
    let mut index = 0;
    base.iter()
        .zip(delta)
        .map(|(row, drow)| {
            let width = row.len();
            let mut row = row.clone();
            for (i, (x, dx)) in row.iter_mut().zip(drow).enumerate() {
                carry.deposit(at, carrier, index + i, x, &rate_times(rate, dx));
            }
            index += width;
            row
        })
        .collect()
}

/// [definition] **A linear locus** that a deposit's normal law updates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LinearLocus {
    /// `E_g`: feature the phase-binned counts `M_g[c]`, covector `P^(c−τ)` of the open's covector.
    SourcePort(usize),
    /// `W_c,g`: feature the contrast `c_t`, covector the element adjoint's `u_t`.
    Contrast(usize),
    /// `R` on ring `g`: feature the rotated anchor, covector the logit covector.
    Receiving(usize),
}

impl LinearLocus {
    pub fn locus(&self) -> Locus {
        match *self {
            LinearLocus::SourcePort(g) => Locus::SourcePort(g),
            LinearLocus::Contrast(g) => Locus::Element(g),
            LinearLocus::Receiving(g) => Locus::ReceivingMap(g),
        }
    }
}

/// [definition] **One linear locus's window**: its samples inside the causal diamond.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearStep {
    pub locus: LinearLocus,
    pub samples: Vec<Sample>,
}

/// [definition] **One reached comparison's deposit into the receiving parametron's landmark tree**
/// (the landmark tree): its receiving ring, the causal address its phase read the tree at
/// (`hnn::receiving::ActiveAddress::phase`) and its target class. The deposit applies a window's
/// steps in cell order, each on the paths its address opens (Lean
/// `Compression/Landmark/Context/Tree.landmark_step`), at the receiving locus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkStep {
    pub ring: usize,
    pub address: Vec<Letter>,
    pub class: usize,
}

/// [definition] **A factor family's descent direction `G_x`** (the negative gradient of the ratio's
/// log), shaped as the family's factors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactorGradient {
    /// The passive factor `f_g` (`W_s = −f fᵀ`).
    Passive {
        ring: usize,
        gradient: ExactRatMatrix,
    },
    /// The slices' `(u_ρ, v_ρ)`.
    Slices {
        ring: usize,
        gradient: Vec<(Vec<Rat>, Vec<Rat>)>,
    },
    /// The standing `q_g`, through the declared lock chart (the class covector carried by the
    /// transpose of the contrast map `q ↦ Δ`), with its chart's **reach**: every ring whose contrast
    /// a move of `q_g` moves (`g` and the other ends of its contacts), each with its element
    /// window's energy `Σ_t |x̄_t|²`, which the certified step's curvature reads (module header,
    /// "The factor families' certified step").
    Standing {
        ring: usize,
        gradient: Vec<Rat>,
        reach: Vec<(usize, Rat)>,
    },
    /// One squared scalar amplitude of a declared resonator base form: `C`, `K`, `D`, or pump.
    Resonator {
        ring: usize,
        family: usize,
        gradient: Rat,
    },
    /// The pair port's outputs `e_ρ`, current reads `a_ρ` and earlier reads `b_ρ`.
    PairPort {
        ring: usize,
        offset: usize,
        outputs: Vec<Vec<Rat>>,
        current: Vec<Vec<Rat>>,
        earlier: Vec<Vec<Rat>>,
    },
    /// `c_a` (`C_a = c cᵀ`).
    Storage {
        contact: usize,
        gradient: ExactRatMatrix,
    },
    /// `b_a` (`K_a = b bᵀ`).
    Stiffness {
        contact: usize,
        gradient: ExactRatMatrix,
    },
    /// `F_a` (`D_a = F Fᵀ`).
    Dissipation {
        contact: usize,
        gradient: ExactRatMatrix,
    },
}

impl FactorGradient {
    /// Every entry of the descent direction, in the family's carry order.
    pub fn entries(&self) -> Box<dyn Iterator<Item = &Rat> + '_> {
        match self {
            FactorGradient::Passive { gradient, .. }
            | FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. } => Box::new(gradient.entries().iter()),
            FactorGradient::Slices { gradient, .. } => {
                Box::new(gradient.iter().flat_map(|(u, v)| u.iter().chain(v)))
            }
            FactorGradient::Standing { gradient, .. } => Box::new(gradient.iter()),
            FactorGradient::Resonator { gradient, .. } => Box::new(std::iter::once(gradient)),
            FactorGradient::PairPort {
                outputs,
                current,
                earlier,
                ..
            } => Box::new(outputs.iter().chain(current).chain(earlier).flatten()),
        }
    }

    pub fn locus(&self) -> Locus {
        match *self {
            FactorGradient::Passive { ring, .. } | FactorGradient::Slices { ring, .. } => {
                Locus::Element(ring)
            }
            FactorGradient::Standing { ring, .. } => Locus::Standing(ring),
            FactorGradient::Resonator { ring, .. } => Locus::Resonator(ring),
            FactorGradient::PairPort { ring, .. } => Locus::SourcePort(ring),
            FactorGradient::Storage { contact, .. }
            | FactorGradient::Stiffness { contact, .. }
            | FactorGradient::Dissipation { contact, .. } => Locus::Channel(contact),
        }
    }

    /// The family the step moves at its locus.
    pub fn family(&self) -> Family {
        match *self {
            FactorGradient::Passive { .. } => Family::Passive,
            FactorGradient::Slices { .. } => Family::Slices,
            FactorGradient::Standing { .. } => Family::Standing,
            FactorGradient::Resonator { family, .. } => Family::Resonator(family),
            FactorGradient::PairPort { offset, .. } => Family::Pair(offset),
            FactorGradient::Storage { .. } => Family::Factor(0),
            FactorGradient::Stiffness { .. } => Family::Factor(1),
            FactorGradient::Dissipation { .. } => Family::Factor(2),
        }
    }
}

/// [definition] **The family a certified step moves at its locus**: a normal law's map (`E_g`, `R`,
/// `W_c`), or one factor family (module header, "The factor families' certified step").
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// A normal law's map `W`.
    Map,
    /// The element's passive factor `f` (`W_s = −f fᵀ`).
    Passive,
    /// The element's skew slices `(u_ρ, v_ρ)`.
    Slices,
    /// The standing `q`, through its lock chart.
    Standing,
    /// A loaded resonator's gain: `C`, `K`, `D` or pump.
    Resonator(usize),
    /// The pair port at its declared offset.
    Pair(usize),
    /// A channel's storage `c`, stiffness `b` or dissipation `F` (0, 1, 2).
    Factor(usize),
}

impl Family {
    /// Whether a carrier holds this family's moved entries (its values, not its scale or Gram).
    fn carries(self, carrier: &Carrier) -> bool {
        match (self, carrier) {
            (Family::Map, Carrier::Map)
            | (Family::Passive, Carrier::Passive)
            | (Family::Slices, Carrier::Slices)
            | (Family::Standing, Carrier::Standing) => true,
            (Family::Resonator(f), Carrier::Resonator(c)) | (Family::Factor(f), Carrier::Factor(c)) => {
                f == *c
            }
            (Family::Pair(o), Carrier::Pair { offset, .. }) => o == *offset,
            _ => false,
        }
    }
}

/// [definition] **One factor step**: the family's descent direction `G_x`, the feature energy
/// `e = Σ_t w|f_t|²` its window adds to the family's statistic `h_x`, and the **covector scale**
/// `c = max_t |g_t|_∞`, the largest entry of the covector one return carries at the family's output
/// (the element's adjoint `u_t` for the element's families and the standing, the transit's solved
/// `r̄_t` for a channel's and a resonator's, the turned opening at a phase for a pair port), which
/// the certified step reads as the linear loci read theirs (module header, "The factor families'
/// certified step").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorStep {
    pub gradient: FactorGradient,
    pub energy: Rat,
    pub covector: Rat,
}

/// [definition; agent-inferred] **A deposit's reach** (module header, "The certified step"): what
/// its covectors summed before they reached the loci. The receiving ring its stations read; each
/// station's read tick (the full ticks its change had run when the station read the ring's anchor);
/// each tick at which the source moment entered the change; and the most phases one source moment
/// occupied (the phase-binned counts one injection sums). A word read at its receiving epochs
/// declares one station at each epoch and one entry at `0` (the retired linear readout's refinement
/// of `K` words of `w` ticks read at `m` stations declared `m` stations at `K·w` and entries at
/// `0, w, …, (K−1)w`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reach {
    pub receiver: usize,
    pub stations: Vec<u64>,
    pub entries: Vec<u64>,
    pub phases: u64,
}

impl Reach {
    /// `Σ_j (Σ_(n: T_n ≤ T_j) g^(T_j − T_n))² · F(T_j − min_n T_n)`: the re-entries' amplitude gains
    /// summed at every station, for a per-tick amplitude growth `g`, each station's multiplied by
    /// the pumped medium's span factor at its longest span (module header, "The pumped medium's
    /// reach"; Lean `Holon/Deposition.entry_span_gain`). No factor reads the passive medium's.
    pub(crate) fn entry_gain(&self, growth: &Rat, factor: Option<&[Rat]>) -> Rat {
        let powers = Self::powers(growth, self.stations.iter().max().map_or(0, |t| t + 1));
        self.stations
            .iter()
            .map(|&station| {
                let sum: Rat = self
                    .entries
                    .iter()
                    .filter(|&&entry| entry <= station)
                    .map(|&entry| powers[(station - entry) as usize].clone())
                    .sum();
                let square = &sum * &sum;
                let first = self.entries.iter().filter(|&&entry| entry <= station).min();
                match (factor, first) {
                    (Some(factor), Some(&first)) => square * &factor[(station - first) as usize],
                    _ => square,
                }
            })
            .sum()
    }

    /// `Σ_j Σ_(τ < T_j) g^(2(T_j − τ − 1)) F(T_j − τ)`: every tick's energy gain to every station,
    /// each span's multiplied by the pumped medium's span factor (module header, "The pumped
    /// medium's reach"; Lean `Holon/Deposition.station_tick_gain`). No factor reads the passive
    /// medium's.
    pub(crate) fn tick_gain(&self, growth: &Rat, factor: Option<&[Rat]>) -> Rat {
        let top = self.stations.iter().max().copied().unwrap_or(0);
        let powers = Self::powers(&(growth * growth), top);
        // `sums[t] = Σ_(k < t) g^(2k) F(k + 1)`.
        let mut sums = Vec::with_capacity(top as usize + 1);
        sums.push(Rat::zero());
        for (k, power) in powers.iter().enumerate() {
            let next = match factor {
                Some(factor) => sums.last().expect("seeded") + power * &factor[k + 1],
                None => sums.last().expect("seeded") + power,
            };
            sums.push(next);
        }
        self.stations
            .iter()
            .map(|&station| sums[station as usize].clone())
            .sum()
    }

    /// `[1, x, x², …, x^(count − 1)]`, each from the one before.
    fn powers(x: &Rat, count: u64) -> Vec<Rat> {
        let mut powers = Vec::with_capacity(count as usize);
        let mut current = Rat::one();
        for _ in 0..count {
            powers.push(current.clone());
            current *= x;
        }
        powers
    }
}

/// [definition; agent-inferred] **One family's certified step at a deposit** (module header, "The
/// certified step", "The factor families' certified step", "The tightened certificate"): the family
/// it moves, the step with its alignment `a`, its own curvature `C = ½·κ²·b` and covector scale `c`;
/// the gain `κ²` read at the rays' ends, and its parts: the output's moves `b` along the whole ray,
/// the bound `m ≥ √(κ² b)` on its logit move that the joint certificate reads, the readout's
/// certified spectral bound `‖R‖₂²` and the per-tick amplitude growth `1 + ω`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StepReading {
    pub family: Family,
    pub step: CertifiedStep,
    pub gain: Rat,
    pub moves: Rat,
    pub bound: Rat,
    pub readout: Rat,
    pub amplitude: Rat,
}

/// [definition; agent-inferred, September 30] **A carried source step's reading**
/// ([`Constitution::stepped_source`]): the step `η`, the unit step's alignment `a` with its returns
/// and its largest absolute column sum, the entries whose lattice coordinate moved, the residuals
/// the carry released (exact), the chart's reading, the certified storage growth, the successor's
/// largest absolute entry of the source port, and its exact bits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceStep {
    pub step: Rat,
    pub alignment: Rat,
    pub unit: Rat,
    pub stepped: u64,
    pub released: Vec<Rat>,
    pub chart: ChartReading,
    pub storage_growth: Rat,
    pub largest: Rat,
    pub bits: u64,
}

/// [definition] **What a deposit's publication reads** (module header, "The committed energy bound,
/// enforced at the commit"): the certified storage growth `ε_k` of the storage forms the deposit
/// changes (`Q_(k+1) ⪯ (1 + ε_k) Q_k`; a deposit with none certified is refused) and the product
/// `∏(1 + ε_k)` since the founding; each family's certified step, by locus ([`StepReading`], its
/// family named in it); the
/// successor's per-tick amplitude growth `1 + ω` (the contrast ports' certified bound; `None` when a
/// pumped resonator leaves it uncertified); the commit reached, the successor's exact bits against
/// the budget, the loci reached, and the budgeted carry's report: every residual the deposit
/// released (exact and sparse, with its locus, carrier and entry; Lean
/// `HNN/LatticeDeposit.release`), their bits, and the number of entries whose lattice coordinate
/// moved (`q ≠ 0`, review R5); and each normal law's solved chart with the prox residual its chart
/// released ([`ChartReading`], the lattice word); and the cells its reached comparisons deposited
/// into the receiving parametrons' landmark trees (the landmark tree). The release is reported,
/// never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepositReading {
    pub storage_growth: Rat,
    pub storage_product: Rat,
    pub steps: Vec<(Locus, StepReading)>,
    /// The joint certificate the steps hold together, `s (Σ η m)² ≤ Σ η a` (`None` when no family
    /// stepped).
    pub joint: Option<JointReading>,
    pub amplitude: Option<Rat>,
    pub commit: u64,
    pub bits: u64,
    pub budget: u64,
    pub loci: Vec<Locus>,
    pub released: Vec<(Locus, Carrier, usize, Rat)>,
    pub released_bits: u64,
    pub stepped: u64,
    /// [definition; agent-inferred, October 2; the
    /// [contact loop record](../../../../research/records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)]
    /// **The rounding refusals**: every family certified at a step `η > 0` none of whose entries
    /// took a nonzero lattice coordinate, so its constitution did not change at this deposit. Its
    /// move is released below the fine lattice or carried as a remainder below the coarse one
    /// ([`Constitution::carried_remainders`] says which); it is not necessarily lost. A reached
    /// family either moves or is named here.
    pub vanished: Vec<(Locus, Family)>,
    pub charts: Vec<(Locus, ChartReading)>,
    pub landmarks: u64,
    /// Every loaded resonator gain step the deposit backtracked instead of carrying a gain to
    /// `g ≤ 0` ([`GainBacktrack`]); deposition never releases a family.
    pub backtracks: Vec<GainBacktrack>,
    /// The lobe law's reading: the crossings the standings' lock chart offered, and the families
    /// it held in their lobes (`None` when every standing step kept its lobes; module header,
    /// "Within a lobe").
    pub lobe: Option<LobeReading>,
    /// The lock's proposal, when the chart's steps turn a sheet the held successor keeps
    /// ([`Constitution::locked`]; module header, "At a node: the lock's half-turn").
    pub lock: Option<LockProposal>,
    /// The pumped medium's reach the certified steps read: each ring not certified passive with
    /// its Floquet decision and bound, the span factor at the longest span, and the families held
    /// (`None` when every resonator is certified passive; module header, "The pumped medium's
    /// reach").
    pub pumped: Option<PumpedReading>,
}

impl DepositReading {
    /// **A normal law's certified step** at its locus (zero where its alignment certified none).
    pub fn linear_step(&self, locus: Locus) -> Rat {
        self.family_step(locus, Family::Map)
    }

    /// **A family's certified step** at its locus (zero where its alignment certified none).
    pub fn family_step(&self, locus: Locus, family: Family) -> Rat {
        self.steps
            .iter()
            .find(|(at, reading)| *at == locus && reading.family == family)
            .map_or_else(Rat::zero, |(_, reading)| reading.step.step.clone())
    }
}

/// [definition; agent-inferred, September 29] **One ring's reach** (module header, "The pumped
/// medium's reach"): a ring whose resonator is not certified passive, its Floquet monodromy decided
/// exactly at its lattice's grain (passive, the edge or growing; `hnn::ring::Floquet::decide`); the
/// bounds its certified growths give (`hnn::ring::FloquetBound`: `ρ` a period, the largest tick
/// factor `σ²`, `γ_lo`, `γ_hi`), the decided growth's first and each on the ladder above it; and
/// its reach over the spans `0..=S`, each span's the least of the bounds' (each certified, so their
/// least is), at its ceiling on the certificate's face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingReach {
    pub ring: usize,
    pub reading: FloquetReading,
    pub bounds: Vec<FloquetBound>,
    pub reach: Vec<Rat>,
}

/// [definition; agent-inferred, September 29] **The medium's reach** ([`Constitution::medium_reach`];
/// module header, "The pumped medium's reach"): the contrast ports' per-tick amplitude growth
/// `1 + ω`, each ring not certified passive with its reach, and the span factors
/// `F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)` over the spans `0..=S` (every factor one when every
/// resonator is passive). A span of `s` ticks moves the energy by at most `(1 + ω)^(2s) F(s)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MediumReach {
    pub amplitude: Rat,
    pub rings: Vec<RingReach>,
    pub factors: Vec<Rat>,
}

impl MediumReach {
    /// `F(s)` for a span within the declared ones (`None` past them: no factor is certified there).
    pub fn factor(&self, span: u64) -> Option<&Rat> {
        self.factors.get(span as usize)
    }
}

/// [definition; agent-inferred, September 29] **What a deposit through a pumped medium read**
/// ([`DepositReading::pumped`]; module header, "The pumped medium's reach"): each ring's reach, the
/// longest span its stations read and the span factor there, and the families held: a ring's own
/// gain families whose rays move its monodromy, so no certified reach covers them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpedReading {
    pub rings: Vec<RingReach>,
    pub span: u64,
    pub factor: Rat,
    pub held: Vec<(Locus, Family)>,
}

// -------------------------------------------------------------------------------------------
// the constitution

/// [definition] **The constitution `Θ`**, the one owner. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constitution {
    rings: Vec<RingMaterial>,
    contacts: Vec<ContactMaterial>,
    budget: u64,
    commit: u64,
    released: BTreeSet<Locus>,
    /// `∏(1 + ε_k)` since the founding: the committed energy bound's product of certified storage
    /// growths (module header, "The committed energy bound, enforced at the commit").
    storage_product: Rat,
    /// Each ring's declared storage admittance `Y_g` (the field's), which the certified step's gains
    /// read.
    admittances: Vec<Rat>,
    /// Each contact's conductance bound at every lift (the field's): `Y_a` when `β_a ≥ 0`, since
    /// `G_a = 2^(−β_a Q_a / 2) Y_a` with `Q_a ≥ 0`; `None` when `β_a < 0`, where no bound holds and a
    /// channel family's certified step is refused (module header, "The factor families' certified
    /// step").
    conductances: Vec<Option<Rat>>,
    /// The field's hop `h`, which the channels' and resonators' outputs and powers read.
    hop: Rat,
    /// The declared lattice of every learned locus (the field's).
    lattices: BTreeMap<Locus, Lattice>,
    /// The factor families' carried remainders (the normal laws carry their own).
    carries: Carries,
    /// Each locus's deposit clock: the deposits that reached it with a nonzero update since its
    /// founding.
    clocks: BTreeMap<Locus, u64>,
    /// `L_R`, the finest admitted receiver grain (the field's), which the chart rule reads.
    grain: u128,
    /// The standing's lock chart `Δ = M q` (the field's contrast map), which the lobes read
    /// (module header, "The standing's fold").
    lock: LockChart,
    /// The field's fixed nodes: the slices of the chart's singular components, founded on their
    /// node (module header, "The founding").
    fixed: Vec<(usize, usize)>,
}

/// SplitMix64's finalizer after one golden-gamma step.
fn splitmix(state: u64) -> u64 {
    let mut z = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// **The declared sign sequence** (design (d), campaign 1's declared values): entry `(i, j)` of
/// locus `ℓ` is `+1` when the low bit of `SplitMix64` over `(0, ℓ, i, j)` is set, `−1` otherwise,
/// the tuple folded as `z ← splitmix(z ⊕ x)` from `z = splitmix(0)`.
pub fn declared_sign(locus: u64, i: u64, j: u64) -> Rat {
    let mut z = splitmix(0);
    for x in [locus, i, j] {
        z = splitmix(z ^ x);
    }
    if z & 1 == 1 { Rat::one() } else { -Rat::one() }
}

/// The locus codes of the sign sequence: `kind · 2^40 + index · 2^20 + part`.
fn locus_code(kind: u64, index: usize, part: usize) -> u64 {
    (kind << 40) + ((index as u64) << 20) + part as u64
}

fn scaled_identity(n: usize, value: Rat) -> ExactRatMatrix {
    ExactRatMatrix::identity(n)
        .expect("a positive extent")
        .scaled(&value)
}

fn unit(n: usize, i: usize) -> Vec<Rat> {
    (0..n)
        .map(|j| if i == j { Rat::one() } else { Rat::zero() })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the standing's fold: its nodes, lobes, amplitudes and the lock's half-turn

/// [definition; agent-inferred, September 29] **The standing's lock chart** `Δ = M q` (module
/// header, "The standing's fold"): the contrast map of [`Field::contrast`], read once from the
/// field's connection incidence at the founding, so that the constitution reads its standings'
/// nodes and lobes without the field. Row `(r, ρ)` holds the terms `(g, j, w)` of
/// `Δ_r[ρ] = Σ w q_g[j]`: `−1` at `(r, ρ)`, each contact block `T_a` read forward at its `from` end
/// and transposed at its `to` end, exactly as [`Field::contrast`] reads them.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LockChart {
    rows: Vec<Vec<Vec<(usize, usize, Rat)>>>,
}

impl LockChart {
    /// The chart read from the field's connection incidence.
    fn of(field: &Field) -> Result<Self, HnnError> {
        let connection = field.connection();
        let (sources, targets) = (connection.sources(), connection.targets());
        let mut rows = Vec::with_capacity(field.rings().len());
        for (r, ring) in field.rings().iter().enumerate() {
            let width = ring.width();
            let mut terms: Vec<BTreeMap<(usize, usize), Rat>> = (0..width)
                .map(|rho| BTreeMap::from([((r, rho), -Rat::one())]))
                .collect();
            for &a in field.incident(r) {
                let block = connection.transport(a).ok_or(HnnError::Shape {
                    what: "a contact's block of the connection incidence",
                    expected: field.contacts().len(),
                    found: a,
                })?;
                // `Δ_r += T_a q_(t a)` at the `from` end, `Δ_r += T_aᵀ q_(s a)` at the `to` end.
                let (forward, other) = if sources[a] == r {
                    (true, targets[a])
                } else {
                    (false, sources[a])
                };
                let (extent, reach) = if forward {
                    (block.rows(), block.columns())
                } else {
                    (block.columns(), block.rows())
                };
                if extent != width {
                    return Err(HnnError::Shape {
                        what: "a contact block's side at its ring (the ring's realified width)",
                        expected: width,
                        found: extent,
                    });
                }
                for (rho, row) in terms.iter_mut().enumerate() {
                    for j in 0..reach {
                        let w = if forward {
                            block.get(rho, j)?
                        } else {
                            block.get(j, rho)?
                        };
                        if !w.is_zero() {
                            *row.entry((other, j)).or_insert_with(Rat::zero) += w;
                        }
                    }
                }
            }
            rows.push(
                terms
                    .into_iter()
                    .map(|row| {
                        row.into_iter()
                            .filter(|(_, w)| !w.is_zero())
                            .map(|((g, j), w)| (g, j, w))
                            .collect()
                    })
                    .collect(),
            );
        }
        Ok(Self { rows })
    }

    /// `Δ_r` of every ring at the standings `q`.
    fn contrast(&self, standings: &[&[Rat]]) -> Vec<Vec<Rat>> {
        self.rows
            .iter()
            .map(|ring| {
                ring.iter()
                    .map(|terms| {
                        terms
                            .iter()
                            .map(|(g, j, w)| w * &standings[*g][*j])
                            .sum()
                    })
                    .collect()
            })
            .collect()
    }

    /// Whether row `(r, ρ)` reads ring `g`'s standing at a coordinate in `moved`.
    fn reads(&self, r: usize, rho: usize, g: usize, moved: &BTreeSet<usize>) -> bool {
        self.rows[r][rho]
            .iter()
            .any(|(ring, j, _)| *ring == g && moved.contains(j))
    }

    /// [definition; agent-inferred, September 29] **The standing founded as a standing wave with
    /// declared lobes** (module header, "The founding"). The chart is block diagonal over the
    /// connected components of its coordinates; on each component `C` the founding solves
    /// `M_C q_C = k u_C 𝟙` exactly: every slice's amplitude at the component's first lattice unit
    /// `k u_C` in the `+1` lobe, `u_C` the coarsest standing unit among the component's rings and `k`
    /// the least positive integer with `k M_C⁻¹ 𝟙` integral (so `q_C` lies on every ring's lattice).
    /// A component whose chart is singular cannot place its declared lobes off the node (its kernel
    /// fixes a combination of its contrasts: a single channel's two ends read `Δ` and `−Δ`); it stays
    /// founded on its node, and its slices are returned as the field's **fixed nodes**.
    fn founding(&self, units: &[Rat]) -> Result<Founding, HnnError> {
        let widths: Vec<usize> = self.rows.iter().map(Vec::len).collect();
        let mut base = Vec::with_capacity(widths.len());
        let mut total = 0usize;
        for width in &widths {
            base.push(total);
            total += width;
        }
        let mut parent: Vec<usize> = (0..total).collect();
        fn root(parent: &mut [usize], mut v: usize) -> usize {
            while parent[v] != v {
                parent[v] = parent[parent[v]];
                v = parent[v];
            }
            v
        }
        for (r, ring) in self.rows.iter().enumerate() {
            for (rho, terms) in ring.iter().enumerate() {
                for (g, j, _) in terms {
                    let (x, y) = (root(&mut parent, base[r] + rho), root(&mut parent, base[*g] + j));
                    if x != y {
                        parent[x.max(y)] = x.min(y);
                    }
                }
            }
        }
        let mut components: BTreeMap<usize, Vec<(usize, usize)>> = BTreeMap::new();
        for (r, width) in widths.iter().enumerate() {
            for rho in 0..*width {
                let top = root(&mut parent, base[r] + rho);
                components.entry(top).or_default().push((r, rho));
            }
        }
        let mut standings: Vec<Vec<Rat>> = widths.iter().map(|w| vec![Rat::zero(); *w]).collect();
        let mut fixed = Vec::new();
        for members in components.values() {
            let local: BTreeMap<(usize, usize), usize> = members
                .iter()
                .enumerate()
                .map(|(index, member)| (*member, index))
                .collect();
            let chart: Vec<Vec<Rat>> = members
                .iter()
                .map(|&(r, rho)| {
                    let mut row = vec![Rat::zero(); members.len()];
                    for (g, j, w) in &self.rows[r][rho] {
                        row[local[&(*g, *j)]] += w;
                    }
                    row
                })
                .collect();
            let inverse = match ExactRatMatrix::new(chart)?.inverse() {
                Ok(inverse) => inverse,
                Err(ExactLinearError::SingularMatrix) => {
                    fixed.extend(members.iter().copied());
                    continue;
                }
                Err(refusal) => return Err(refusal.into()),
            };
            let wave = inverse.apply(&vec![Rat::one(); members.len()])?;
            let k = wave
                .iter()
                .fold(BigInt::one(), |common, y| lcm(&common, y.denom()));
            let unit = members
                .iter()
                .map(|&(r, _)| units[r].clone())
                .max()
                .unwrap_or_else(Rat::zero);
            let amplitude = &unit * Rat::from_integer(k);
            for (&(r, rho), y) in members.iter().zip(&wave) {
                standings[r][rho] = &amplitude * y;
            }
        }
        Ok(Founding { standings, fixed })
    }
}

/// The founding's standings and the field's fixed nodes ([`LockChart::founding`]).
struct Founding {
    standings: Vec<Vec<Rat>>,
    fixed: Vec<(usize, usize)>,
}

/// [definition; agent-inferred, September 29] **The slices a standing move takes out of their
/// lobes** (module header, "Within a lobe"): every `(r, ρ)` whose sheet class changes (the
/// half-open lobes `Δ ≥ 0` and `Δ < 0`), or whose contrast the move carries onto its node from off
/// it. A move with none keeps every class, so the element reads it not at all (Lean
/// `HNN/Normal.{lobe_step_keeps_element, lobe_move_is_null}`).
fn crossings(before: &[Vec<Rat>], after: &[Vec<Rat>]) -> Vec<(usize, usize)> {
    let mut crossed = Vec::new();
    for (r, (ring_before, ring_after)) in before.iter().zip(after).enumerate() {
        for (rho, (x, y)) in ring_before.iter().zip(ring_after).enumerate() {
            if x.is_negative() != y.is_negative() || (!x.is_zero() && y.is_zero()) {
                crossed.push((r, rho));
            }
        }
    }
    crossed
}

/// [definition; agent-inferred, September 29] **The lobe's reading at a deposit** (module header,
/// "Within a lobe"): the slices the lock chart's certified step would have carried across their
/// nodes (the crossings it offered the lock), and each standing family the lobe held, with the step
/// it took (`Some(k)`, the step `2^k`, halved from its chart's) or none (dropped: its move could not
/// stay in its lobes above its fine lattice's resolution).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LobeReading {
    pub offered: Vec<(usize, usize)>,
    pub held: Vec<(usize, Option<i64>)>,
}

/// One standing the lock's proposal moves: its entries, carried remainders, clock and released
/// residuals at the lock chart's certified step.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ProposedStanding {
    ring: usize,
    standing: Vec<Rat>,
    carry: Carry,
    clock: u64,
    released: Vec<(Carrier, usize, Rat)>,
}

/// [definition; agent-inferred, September 29] **The lock's proposal at a deposit** (module header,
/// "At a node: the lock's half-turn"): the standings the lock chart's certified step reaches when
/// it carries some slices across their nodes, and those crossings. It is taken only by
/// [`Constitution::locked`] on the successor it was proposed at, when the lock's exact comparison
/// of the comparison's code at both sheets ([`crate::holon::deposition::strictly_better`]) says the
/// crossed sheets are strictly better.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockProposal {
    commit: u64,
    standings: Vec<ProposedStanding>,
    crossings: Vec<(usize, usize)>,
}

impl LockProposal {
    /// The successor's commit the proposal was made at.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// The slices `(r, ρ)` whose sheet the proposal turns by a half-turn (or carries onto its node).
    pub fn crossings(&self) -> &[(usize, usize)] {
        &self.crossings
    }
}

/// [definition] **The lock's reading** ([`Constitution::locked`]): the crossings taken, the commit
/// reached, the successor's exact bits, and the residuals the proposal's carry released.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockReading {
    pub crossings: Vec<(usize, usize)>,
    pub commit: u64,
    pub bits: u64,
    pub released: Vec<(Locus, Carrier, usize, Rat)>,
}

impl Constitution {
    /// **Campaign 1's initial constitution and its priors** (design (d), R3 D2):
    ///
    /// | Locus | Initial value | Update |
    /// |---|---|---|
    /// | `E_g` on a source ring | the sign sequence times ½ | normal law, `H_0 = I`, `B_0 = E_0` |
    /// | `E_g^(δ)`, rank `2d_g` | `e_ρ = 0`; `a_ρ`, `b_ρ` from the sign sequence | factor steps |
    /// | `R` on a receiving ring | 0 | normal law, `H_0 = I`, `B_0 = 0` |
    /// | the landmark tree on a receiving ring, declared from its first receiver | empty: every node unfounded, every face uniform (`α = ½` at first arrival) | the landmark deposit (the landmark tree) |
    /// | `W_c,g` | 0 | normal law, `H_0 = I`, `B_0 = 0` |
    /// | `W_s,g = −f fᵀ` | `f = ½I` | factor step |
    /// | slices | `u_ρ = e_ρ`, `v_ρ = e_(ρ+1)`: the skew cyclic shift | factor steps |
    /// | `q_g` | the standing wave `M_C q_C = k u_C 𝟙`, every slice at its component's first unit in the `+1` lobe; a singular component on its node (module header, "The founding") | the lock chart's preconditioned step, held in its lobes; the lock's half-turn |
    /// | `c_a`, `b_a`, `F_a` | `I`, `½I`, `½I` | factor steps |
    ///
    /// The sign sequence's locus codes: `E` of ring `g` is kind 0; the pair port's current and
    /// earlier reads of ring `g` at the `o`-th declared offset are kind 2 and 3 with part `o` (kind
    /// 1 was `R`'s while it opened at the sign sequence, the region table).
    ///
    /// [definition; agent-inferred] **`R_0 = 0`, `E_0` the sign sequence times ½.** The receiving
    /// map opens at zero, so the combined face opens exactly at the tree's and the wave earns every
    /// bit it moves: the located failure read the old prior's reading `R_0 z` alone at `10 + 9/16 +
    /// ε` bits a cell, a share in `[51/56, 3713/4077]` of the held-out logits' energy. With `E_0 = 0`
    /// and `e_ρ = 0` as well, the source moment `m̃`, the open, every wave and every feature
    /// `f = P_R^(τ_R) v_R` would be zero, so `R`'s step `G = Σ γ g fᵀ` and every upstream covector
    /// `Rᵀ g` would vanish at every commit: the chain of maps needs one nonzero member to carry a
    /// covector. `E_0` takes the sign sequence's pattern at the value `R_0` had. Its normal law keeps
    /// the prior's reading (`B_0 = E_0`), a fixed feature map that `R` reads, not a term of the
    /// face: at `R = 0` it moves no logit. `R` moves at the first deposit, and the upstream loci
    /// receive a covector from the second compare on (the tests
    /// `the_wave_is_inert_when_every_map_opens_at_zero` and
    /// `r_opens_at_zero_and_learns_from_the_first_deposit`).
    ///
    /// Every initial value (0, ±½, 1, the unit vectors) lies on every lattice `L ≥ 1`, and each
    /// locus takes the field's declared lattice ([`Field::lattice`]). No step is declared: every
    /// locus's step is certified at its deposit (module header).
    pub fn initial(field: &Field, budget: u64) -> Result<Self, HnnError> {
        let lattices = field.lattices().clone();
        // L_R = ⌈1/ε_bits⌉, the finest admitted receiver's (`FieldDeclaration::lattice_by_rule`).
        let grain = field
            .receivers()
            .iter()
            .filter(|receiver| receiver.tolerance.is_positive())
            .filter_map(|receiver| {
                (Rat::one() / &receiver.tolerance)
                    .ceil()
                    .to_integer()
                    .to_u128()
            })
            .max()
            .unwrap_or(1);
        let a = field.alphabet();
        let receivers: BTreeSet<usize> = field.receivers().iter().map(|r| r.ring).collect();
        // Each receiving ring's tree, declared from its first declared receiver.
        let tree = |g: usize| -> Result<Option<Landmarks>, HnnError> {
            field
                .receivers()
                .iter()
                .find(|receiver| receiver.ring == g)
                .map(|receiver| Ok(Landmarks::new(landmark_declaration(field, receiver)?)?))
                .transpose()
        };
        // The standing founded as a standing wave with declared lobes (module header, "The
        // founding"): every slice at its component's first lattice unit in the `+1` lobe.
        let lock = LockChart::of(field)?;
        let units: Vec<Rat> = (0..field.rings().len())
            .map(|g| {
                lattices
                    .get(&Locus::Standing(g))
                    .map(Lattice::unit)
                    .ok_or(HnnError::Lattice {
                        locus: Locus::Standing(g),
                    })
            })
            .collect::<Result<_, HnnError>>()?;
        let Founding {
            standings: mut founded,
            fixed,
        } = lock.founding(&units)?;
        let rings = field
            .rings()
            .iter()
            .enumerate()
            .map(|(g, ring)| {
                let n = ring.width();
                // `E_0`: the declared sign sequence times ½ on every field. [historical] The founded
                // injection of a passage-founded port chart (each cell's column at one node's real
                // quadrature) was retired on September 29 with the founded charts: many codes shared
                // one node, aliasing cells, and on the prediction field it alone made the
                // refinement's exact cost grow past its bound (the lessons record, §4; `96d8940b`).
                let source = field
                    .is_source(g)
                    .then(|| {
                        let map = ExactRatMatrix::shaped(
                            n,
                            a,
                            (0..n)
                                .map(|i| {
                                    (0..a)
                                        .map(|j| {
                                            declared_sign(locus_code(0, g, 0), i as u64, j as u64)
                                                * rat(1, 2)
                                        })
                                        .collect()
                                })
                                .collect(),
                        )?;
                        Ok::<_, HnnError>(NormalLaw::with_prior(map))
                    })
                    .transpose()?;
                let pairs = if field.is_source(g) {
                    field
                        .offsets()
                        .iter()
                        .enumerate()
                        .map(|(o, &offset)| {
                            let reads = |kind: u64| -> Vec<Vec<Rat>> {
                                (0..n)
                                    .map(|rho| {
                                        (0..a)
                                            .map(|x| {
                                                declared_sign(
                                                    locus_code(kind, g, o),
                                                    rho as u64,
                                                    x as u64,
                                                )
                                            })
                                            .collect()
                                    })
                                    .collect()
                            };
                            Ok((
                                offset,
                                PairPort::new(vec![vec![Rat::zero(); n]; n], reads(2), reads(3))?,
                            ))
                        })
                        .collect::<Result<Vec<_>, HnnError>>()?
                } else {
                    Vec::new()
                };
                let receiving = receivers
                    .contains(&g)
                    .then(|| ExactRatMatrix::zero(2 * a, n).map(NormalLaw::with_prior))
                    .transpose()?;
                Ok(RingMaterial {
                    standing: std::mem::take(&mut founded[g]),
                    standing_scale: Rat::one(),
                    passive: scaled_identity(n, rat(1, 2)),
                    passive_scale: Rat::one(),
                    contrast: NormalLaw::with_prior(ExactRatMatrix::zero(n, n)?),
                    slices: (0..n)
                        .map(|rho| (unit(n, rho), unit(n, (rho + 1) % n)))
                        .collect(),
                    slice_scale: Rat::one(),
                    source,
                    pairs,
                    pair_scale: Rat::one(),
                    receiving,
                    population: receivers.contains(&g).then(receiving_population),
                    tree: tree(g)?,
                    resonator: None,
                    resonator_scales: std::array::from_fn(|_| Rat::one()),
                    resonator_step: None,
                    transport: Rat::one(),
                })
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let contacts = field
            .contacts()
            .iter()
            .map(|contact| {
                let k = contact.width();
                ContactMaterial {
                    storage: scaled_identity(k, Rat::one()),
                    stiffness: scaled_identity(k, rat(1, 2)),
                    dissipation: scaled_identity(k, rat(1, 2)),
                    scales: [Rat::one(), Rat::one(), Rat::one()],
                    boost: None,
                    surface: None,
                }
            })
            .collect();
        Ok(Self {
            rings,
            contacts,
            budget,
            commit: 0,
            released: BTreeSet::new(),
            storage_product: Rat::one(),
            admittances: field
                .rings()
                .iter()
                .map(|ring| ring.admittance().clone())
                .collect(),
            conductances: field
                .contacts()
                .iter()
                .map(|contact| {
                    (!contact.exponent().is_negative()).then(|| contact.admittance().clone())
                })
                .collect(),
            hop: field.step().clone(),
            lattices,
            carries: Carries::new(),
            clocks: BTreeMap::new(),
            grain,
            lock,
            fixed,
        })
    }

    /// The commit counter.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// `B_Θ`.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    /// The loci the collapse has released.
    pub fn released(&self) -> &BTreeSet<Locus> {
        &self.released
    }

    /// **A locus's deposit clock** `m` (Lean `Carried.clock`): the count of epochs at the locus's
    /// section, the deposits that reached it with a nonzero update since its founding; not reset at
    /// an aeon boundary, and ended when the collapse releases the locus whole. It is the flux of the
    /// constitution's aeon since the founding through the locus's section
    /// ([`crate::aeon::Epochs::flux`]; Lean `Aeon/Clock/Epoch.reading_eq_crossings`), a count
    /// because deposits only advance (module header); the ticks are not retained.
    pub fn clock(&self, locus: Locus) -> u64 {
        self.clocks.get(&locus).copied().unwrap_or(0)
    }

    /// Ring `g`'s source-port normal law `E_g`.
    pub fn source_law(&self, ring: usize) -> Option<&NormalLaw> {
        self.rings[ring].source.as_ref()
    }

    /// Ring `g`'s contrast-port normal law `W_c,g`.
    pub fn contrast_law(&self, ring: usize) -> &NormalLaw {
        &self.rings[ring].contrast
    }

    /// Ring `g`'s receiving-map normal law `R`.
    pub fn receiving_law(&self, ring: usize) -> Option<&NormalLaw> {
        self.rings[ring].receiving.as_ref()
    }

    /// The factor families' statistics `h_x` of ring `g`: standing, passive, slices, pair port.
    #[cfg(test)]
    pub(crate) fn ring_scales(&self, ring: usize) -> [&Rat; 4] {
        let material = &self.rings[ring];
        [
            &material.standing_scale,
            &material.passive_scale,
            &material.slice_scale,
            &material.pair_scale,
        ]
    }

    /// Contact `a`'s factor statistics `h_x`: storage, stiffness, dissipation.
    pub fn contact_scales(&self, contact: usize) -> &[Rat; 3] {
        &self.contacts[contact].scales
    }

    /// **Replace one ring's element material** (a test and control chart, never a law): the
    /// arbitrary-value witness of the collapse and the declared material of a control field. A
    /// chart may place any exact value, on or off the lattice (a directional-derivative probe
    /// needs off-lattice perturbations); a deposit then moves it by lattice steps. The replaced
    /// arrays' carried remainders are dropped with them.
    ///
    /// **A complex-bilinear block is refused at declaration** (design (d), "Reaction"): a reaction
    /// slice is declared only through its factor pair `(u_ρ, v_ρ)`, so `A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ` is
    /// skew and workless, the real-bilinear reaction (`Holon/Reaction.skewReaction_workless`). A full block `c ⊗ s` has no declaration, since no
    /// such block is power-neutral for both `c` and `i c` unless it is zero
    /// (`Holon/Reaction.bilinear_reaction_workless_iff_zero`). The guarantee is structural, the
    /// parameter's type; the doctest fails with a type mismatch (`E0308`):
    ///
    /// ```compile_fail,E0308
    /// use holonics::hnn::Constitution;
    /// use holonics::ratio::linear::ExactRatMatrix;
    /// // A full block is not a declarable slice: slices are factor pairs (u, v).
    /// fn block(theta: Constitution, n: ExactRatMatrix) -> Constitution {
    ///     theta.with_element(0, n.clone(), n.clone(), vec![n]).unwrap()
    /// }
    /// ```
    pub fn with_element(
        mut self,
        ring: usize,
        passive: ExactRatMatrix,
        contrast: ExactRatMatrix,
        slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    ) -> Result<Self, HnnError> {
        let material = &mut self.rings[ring];
        let n = material.standing.len();
        if passive.rows() != n
            || contrast.rows() != n
            || contrast.columns() != n
            || slices.len() != n
            || slices.iter().any(|(u, v)| u.len() != n || v.len() != n)
        {
            return Err(HnnError::Shape {
                what: "ring element material",
                expected: n,
                found: passive.rows(),
            });
        }
        material.passive = passive;
        material.contrast = NormalLaw::with_prior(contrast);
        material.slices = slices;
        for part in [Carrier::Passive, Carrier::Slices] {
            self.carries.remove(&(Locus::Element(ring), part));
        }
        Ok(self)
    }

    /// **Replace one contact's channel factors** (a test and control chart, never a law).
    pub fn with_channel(
        mut self,
        contact: usize,
        storage: ExactRatMatrix,
        stiffness: ExactRatMatrix,
        dissipation: ExactRatMatrix,
    ) -> Result<Self, HnnError> {
        let material = &mut self.contacts[contact];
        let k = material.storage.rows();
        for factor in [&storage, &stiffness, &dissipation] {
            if factor.rows() != k {
                return Err(HnnError::Shape {
                    what: "contact factor rows (the channel width)",
                    expected: k,
                    found: factor.rows(),
                });
            }
        }
        material.storage = storage;
        material.stiffness = stiffness;
        material.dissipation = dissipation;
        for family in 0..3 {
            self.carries
                .remove(&(Locus::Channel(contact), Carrier::Factor(family)));
        }
        Ok(self)
    }

    /// **Declare a contact's boost** (campaign 2, `hnn::contact`): the signs of its stiffness
    /// factor's columns, `K_a = b_a diag(σ) b_aᵀ`, certified before it is admitted (the signed form
    /// `2C + hD + (h²/2)K ⪰ 0`, or a nonsingular operator at every conductance the contact can take
    /// on the field), and refused with the singular direction otherwise. Every later deposit is
    /// certified again, and a deposit that would make a solve singular is refused.
    pub fn with_contact_signature(
        mut self,
        field: &Field,
        contact: usize,
        signature: Vec<bool>,
    ) -> Result<Self, HnnError> {
        let columns = self.contacts[contact].stiffness.columns();
        if signature.len() != columns {
            return Err(HnnError::Shape {
                what: "a stiffness signature (one sign per factor column)",
                expected: columns,
                found: signature.len(),
            });
        }
        let boost = Boost {
            signature,
            conductances: contact_conductances(field, contact)?,
            step: field.step().clone(),
        };
        boost.certify(contact, &self.contacts[contact])?;
        self.contacts[contact].boost = Some(boost);
        Ok(self)
    }

    /// **Declare a contact's break law** (#31, `hnn::contact::BreakReceipt`): its surface-storage
    /// density `γ ≥ 0`, the gluing work of each parted node.
    pub fn with_surface_storage(mut self, contact: usize, density: Rat) -> Result<Self, HnnError> {
        if density.is_negative() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        self.contacts[contact].surface = Some(density);
        Ok(self)
    }

    /// **Declare a ring's resonator** (campaign 2, `hnn::ring`), certified at every pump phase at the
    /// field's hop on the ring's realified width.
    ///
    /// [definition; agent-inferred] **Its gains' lattice is the lattice rule's**
    /// ([`crate::hnn::field::lattice_exponent`], the lattice deposit): `L = ⌈log₂(2 L_R X)⌉` with the
    /// fan-in `X = n`, the resonator's realified width. Each gain scales a base form whose rows
    /// read `n` unit-scale coordinates of the ring's state (`C₀w`, `K₀u`, `D₀ω`, the pumped `K`'s
    /// rows), and the rule bounds a factor entry by the fan-in of the read it enters, as for the
    /// element's factors (`W_s = −ffᵀ`, the slices), whose fan-in is the same ring width. The gain
    /// enters its forms squared, so its read's bound through `g²` and the base form's coefficients
    /// is the factor loci's word-level certificate owed in #62. For a field whose element lattice
    /// is the rule's, the two lattices agree (campaign 1's ring 0: `n = 10`,
    /// `L = ⌈log₂ 320⌉ = 9`).
    pub fn with_ring_resonator(
        mut self,
        field: &Field,
        ring: usize,
        material: ResonatorMaterial,
    ) -> Result<Self, HnnError> {
        if self.released.contains(&Locus::Resonator(ring)) {
            return Err(HnnError::ReleasedLocus {
                locus: Locus::Resonator(ring),
            });
        }
        if material.width() != field.ring(ring).width() {
            return Err(HnnError::Shape {
                what: "a resonator (the ring's realified width)",
                expected: field.ring(ring).width(),
                found: material.width(),
            });
        }
        material.certify(ring, field.step())?;
        let lattice = Lattice::new(lattice_exponent(self.grain, material.width() as u128));
        self.rings[ring].resonator = Some(material);
        self.rings[ring].resonator_step = Some(field.step().clone());
        self.lattices.insert(Locus::Resonator(ring), lattice);
        Ok(self)
    }

    /// **The campaign-2 material declaration code** in the field's exact self-delimiting chart:
    /// ring indices, immutable resonator base forms, the base pump, its initial gain coordinates,
    /// and contact boosts/surface densities. This code is charged with `Field::describe` and
    /// includes the immutable operands omitted from the learned-lattice carrier census.
    pub fn describe_physics(&self) -> Vec<bool> {
        use crate::hnn::field::{natural, rational};

        fn matrix(code: &mut Vec<bool>, matrix: &ExactRatMatrix) {
            natural(code, matrix.rows() as u64);
            natural(code, matrix.columns() as u64);
            for value in matrix.entries() {
                rational(code, value);
            }
        }

        let mut code = Vec::new();
        let resonators: Vec<_> = self
            .rings
            .iter()
            .enumerate()
            .filter_map(|(ring, material)| material.resonator.as_ref().map(|m| (ring, m)))
            .collect();
        natural(&mut code, resonators.len() as u64);
        for (ring, material) in resonators {
            natural(&mut code, ring as u64);
            let (capacity, stiffness, dissipation, _) = material.gain_bases();
            for form in [capacity, stiffness, dissipation] {
                matrix(&mut code, form);
            }
            match material.base_pump() {
                None => natural(&mut code, 0),
                Some(pump) => {
                    natural(&mut code, 1);
                    rational(&mut code, pump.strength());
                    rational(&mut code, pump.axis().cos());
                    rational(&mut code, pump.axis().sin());
                    natural(
                        &mut code,
                        match pump.step() {
                            crate::hnn::ring::PumpStep::Stand => 0,
                            crate::hnn::ring::PumpStep::Quarter => 1,
                            crate::hnn::ring::PumpStep::Half => 2,
                            crate::hnn::ring::PumpStep::ThreeQuarters => 3,
                        },
                    );
                }
            }
            natural(&mut code, 4);
            for gain in material.gains() {
                rational(&mut code, gain);
            }
        }

        let contacts: Vec<_> = self
            .contacts
            .iter()
            .enumerate()
            .filter(|(_, material)| material.boost.is_some() || material.surface.is_some())
            .collect();
        natural(&mut code, contacts.len() as u64);
        for (contact, material) in contacts {
            natural(&mut code, contact as u64);
            match &material.boost {
                None => natural(&mut code, 0),
                Some(boost) => {
                    natural(&mut code, 1);
                    natural(&mut code, boost.signature.len() as u64);
                    code.extend(boost.signature.iter().copied());
                    match &boost.conductances {
                        None => natural(&mut code, 0),
                        Some(values) => {
                            natural(&mut code, 1);
                            natural(&mut code, values.len() as u64);
                            for value in values {
                                rational(&mut code, value);
                            }
                        }
                    }
                    rational(&mut code, &boost.step);
                }
            }
            match &material.surface {
                None => natural(&mut code, 0),
                Some(density) => {
                    natural(&mut code, 1);
                    rational(&mut code, density);
                }
            }
        }
        code
    }

    /// The current scalar gain amplitudes for every declared resonator, in ring order. Their
    /// material forms scale by these amplitudes squared. This is a compact constitutive reading,
    /// not an event log.
    pub fn resonator_gains(&self) -> Vec<(usize, [Rat; 4])> {
        self.rings
            .iter()
            .enumerate()
            .filter_map(|(ring, material)| {
                material
                    .resonator
                    .as_ref()
                    .map(|resonator| (ring, resonator.gains().clone()))
            })
            .collect()
    }

    /// The carried remainders of every declared resonator's four gain amplitudes, in ring order:
    /// what reached a family below its lattice's unit and has not moved its amplitude (zero where
    /// nothing is carried).
    pub fn resonator_gain_remainders(&self) -> Vec<(usize, [Rat; 4])> {
        self.rings
            .iter()
            .enumerate()
            .filter(|(_, material)| material.resonator.is_some())
            .map(|(ring, _)| {
                let remainders = std::array::from_fn(|family| {
                    self.carries
                        .get(&(Locus::Resonator(ring), Carrier::Resonator(family)))
                        .map_or_else(Rat::zero, |carry| carry.at(0))
                });
                (ring, remainders)
            })
            .collect()
    }

    /// The carried feature-energy scales for a ring's four scalar gain families, if it declares a
    /// loaded resonator.
    pub fn resonator_scales(&self, ring: usize) -> Option<&[Rat; 4]> {
        self.rings.get(ring).and_then(|material| {
            material
                .resonator
                .as_ref()
                .map(|_| &material.resonator_scales)
        })
    }

    /// The loaded resonator on ring `g`, if that ring declares one.
    pub fn resonator(&self, ring: usize) -> Option<&ResonatorMaterial> {
        self.rings[ring].resonator.as_ref()
    }

    /// [definition; agent-inferred, September 30] **The source port carried by a declared
    /// comparison's returns at a step `η`** (`hnn::executed`, "The committed move"): the source
    /// port's normal law prepared on the returns ([`NormalLaw::prepare`]: `ΔH = Σ w f fᵀ` carried,
    /// the chart of `H′` refined, the unit step `D = Σ w g (X̂f)ᵀ`, its alignment `a = Σ w⟨g, Df⟩`)
    /// and stepped by `ηD` through the locus's budgeted carry ([`PreparedStep::stepped`]), the
    /// locus's clock advanced when an entry moved, the commit counted, and the successor refused
    /// past the budget or when its committed storage growth is uncertified (the guards of
    /// [`Constitution::deposited`]). `None` when the returns reach nothing. It publishes nothing:
    /// the executed comparison's move adopts the successor only when every commit guard holds on it
    /// (`hnn::executed::executed_move`), so it is visible to the crate alone.
    pub(crate) fn stepped_source(
        &self,
        ring: usize,
        samples: &[Sample],
        step: &Rat,
    ) -> Result<Option<(Self, SourceStep)>, HnnError> {
        let locus = Locus::SourcePort(ring);
        if self.released.contains(&locus) {
            return Err(HnnError::ReleasedLocus { locus });
        }
        let law = self.rings[ring]
            .source
            .as_ref()
            .ok_or(HnnError::MissingSourcePort { ring })?;
        let rule = self.chart_rule(locus)?;
        let mut at = BudgetedCarry::new(self.lattice(locus)?, self.clock(locus) + 1);
        let Some(prepared) = law.prepare(samples, &rule, &mut at)? else {
            return Ok(None);
        };
        let alignment = prepared.alignment.clone();
        let (unit, _) = prepared.unit_norms.clone();
        let (stepped, chart) = prepared.stepped(step, &mut at)?;
        let mut next = self.clone();
        next.rings[ring].source = Some(stepped);
        next.commit += 1;
        if at.moved() {
            next.clocks.insert(locus, at.clock());
        }
        let storage_growth =
            certify_storage_growth(&self.storage_forms()?, &next.storage_forms()?)?
                .ok_or(HnnError::UncertifiedStorage)?;
        next.storage_product = &self.storage_product * (Rat::one() + &storage_growth);
        let bits = next.exact_bits();
        if bits > self.budget {
            return Err(HnnError::ConstitutionBudget {
                bits,
                budget: self.budget,
                commit: self.commit,
                loci: vec![locus],
            });
        }
        let largest = next.rings[ring]
            .source
            .as_ref()
            .map(|law| {
                law.map()
                    .entries()
                    .iter()
                    .map(|x| x.abs())
                    .max()
                    .unwrap_or_else(Rat::zero)
            })
            .unwrap_or_else(Rat::zero);
        let reading = SourceStep {
            step: step.clone(),
            alignment,
            unit,
            stepped: at.stepped(),
            released: at.released().into_iter().map(|(.., e)| e).collect(),
            chart,
            storage_growth,
            largest,
            bits,
        };
        Ok(Some((next, reading)))
    }

    /// **Replace one ring's standing, source port or receiving map** (a test and control chart).
    pub fn with_ports(
        mut self,
        ring: usize,
        standing: Option<Vec<Rat>>,
        source: Option<ExactRatMatrix>,
        receiving: Option<ExactRatMatrix>,
    ) -> Result<Self, HnnError> {
        let material = &mut self.rings[ring];
        if let Some(standing) = standing {
            if standing.len() != material.standing.len() {
                return Err(HnnError::Shape {
                    what: "standing q_g",
                    expected: material.standing.len(),
                    found: standing.len(),
                });
            }
            material.standing = standing;
            self.carries
                .remove(&(Locus::Standing(ring), Carrier::Standing));
        }
        if let Some(source) = source {
            material.source = Some(NormalLaw::with_prior(source));
        }
        if let Some(receiving) = receiving {
            material.receiving = Some(NormalLaw::with_prior(receiving));
        }
        Ok(self)
    }

    /// [definition; agent-inferred, September 30; the
    /// [modulus's record](../../../../research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md)]
    /// **The transport's founding off the lossless boundary** (`hnn::moment`, "The founding off
    /// the lossless boundary"; Lean `HNN/IndexedOpen.{founded_modulus_alias, founded_modulus_lt_one,
    /// founded_modulus_greatest}`): the largest modulus `ρ₀` on the source port's lattice
    /// `2^(−L_s)` whose one-turn transport carries a datum to one unit of the weights' chart,
    /// `ρ₀^d ≤ 2^(−L_ν)` (`d` the ring's period, `L_ν` the population chart's exponent,
    /// `PopulationChart::of`): `ρ₀ = ⌊2^((L_s d − L_ν)/d)⌋ 2^(−L_s)`, the integer `d`-th root read
    /// exactly. The phase record identifies a datum's age only within one turn, so its one-turn
    /// alias weighs `ρ^d` of it (`framed_weight_ratio`); `ρ₀` is the least dissipative transport
    /// whose alias is at most one chart unit, the record sufficient at the chart's grain. Refused
    /// off a source ring, or where the lattice cannot carry a modulus that small (`ρ₀ = 0`).
    pub fn founding_transport(&self, field: &Field, ring: usize) -> Result<Rat, HnnError> {
        if self
            .rings
            .get(ring)
            .is_none_or(|material| material.source.is_none())
        {
            return Err(HnnError::MissingSourcePort { ring });
        }
        let lattice = self.lattice(Locus::SourcePort(ring))?;
        let period = field.ring(ring).period();
        let chart = crate::hnn::moment::PopulationChart::of(field).exponent();
        founding_modulus(lattice.exponent(), period, chart).ok_or(HnnError::Transport {
            ring,
            modulus: Rat::zero(),
        })
    }

    /// **The constitution with its transport founded off the lossless boundary**
    /// ([`Constitution::founding_transport`]) on a source ring: the executed comparison's declared
    /// opening (`hnn::executed`, "The committed move"). The card, the bank's face path, the
    /// readout's one anchor and a passage over more than one turn do not read a modulus below one
    /// (each refuses it, typed); they keep the lossless founding until their forms are built.
    pub fn founded_transport(self, field: &Field, ring: usize) -> Result<Self, HnnError> {
        let modulus = self.founding_transport(field, ring)?;
        self.with_transport(ring, modulus)
    }

    /// [definition; agent-inferred, September 30] **The source navigator's transport modulus set**
    /// (`hnn::moment`, "One passage, its transported weights"): `0 < ρ ≤ 1` (the transport is
    /// passive: its energy a tick `ρ² ≤ 1`, its dissipation `1 − ρ² ≥ 0`), on the source port's
    /// lattice. Refused off a source ring, outside `(0, 1]`, or off the lattice. The executed
    /// comparison's move adopts it only when every commit guard holds (`hnn::executed`).
    pub fn with_transport(mut self, ring: usize, modulus: Rat) -> Result<Self, HnnError> {
        let material = self
            .rings
            .get_mut(ring)
            .filter(|material| material.source.is_some())
            .ok_or(HnnError::MissingSourcePort { ring })?;
        if !modulus.is_positive() || modulus > Rat::one() {
            return Err(HnnError::Transport { ring, modulus });
        }
        let unit = self
            .lattices
            .get(&Locus::SourcePort(ring))
            .copied()
            .ok_or(HnnError::Lattice {
                locus: Locus::SourcePort(ring),
            })?
            .unit();
        if !(&modulus / &unit).is_integer() {
            return Err(HnnError::Transport { ring, modulus });
        }
        material.transport = modulus;
        Ok(self)
    }

    /// **Replace a receiving ring's landmark tree** (a test and control chart): refused off a
    /// receiving ring, or for a tree of another declaration than the ring's.
    pub fn with_tree(mut self, ring: usize, tree: Landmarks) -> Result<Self, HnnError> {
        let slot = self
            .rings
            .get_mut(ring)
            .and_then(|material| material.tree.as_mut())
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        if slot.declaration() != tree.declaration() {
            return Err(HnnError::Shape {
                what: "a landmark tree against the receiving ring's declared tree (its depth)",
                expected: slot.declaration().depth,
                found: tree.declaration().depth,
            });
        }
        *slot = tree;
        Ok(self)
    }

    /// **Replace one source ring's pair port at a declared offset** (a test and control chart).
    pub fn with_pair(
        mut self,
        ring: usize,
        offset: usize,
        pair: PairPort,
    ) -> Result<Self, HnnError> {
        let slot = self.rings[ring]
            .pairs
            .iter_mut()
            .find(|(declared, _)| *declared == offset)
            .ok_or(HnnError::Offset { offset })?;
        if pair.rank() != slot.1.rank()
            || pair.outputs().first().map(Vec::len) != slot.1.outputs().first().map(Vec::len)
            || pair.current_reads().first().map(Vec::len)
                != slot.1.current_reads().first().map(Vec::len)
        {
            return Err(HnnError::Shape {
                what: "pair port shape",
                expected: slot.1.rank(),
                found: pair.rank(),
            });
        }
        slot.1 = pair;
        for family in 0..3 {
            self.carries
                .remove(&(Locus::SourcePort(ring), Carrier::Pair { offset, family }));
        }
        Ok(self)
    }

    /// **The constitution's exact bits by carrier** per retained locus: every numerator and
    /// denominator of its lattice entries (values and statistics), of their carried remainders and
    /// of its solved charts at their lattices. Immutable material bases are charged by
    /// `describe_physics`; derived resonator forms are regenerated from those bases and gains.
    /// This is a logical carrier census, not an allocation or total resident-memory measurement.
    pub fn carrier_bits_by_locus(&self) -> Vec<(Locus, CarrierBits)> {
        let values = |values: &mut dyn Iterator<Item = &Rat>| -> u64 { values.map(bits).sum() };
        let mut loci: Vec<(Locus, CarrierBits)> = Vec::new();
        for (g, material) in self.rings.iter().enumerate() {
            let mut element = material.contrast.carrier_bits();
            element.entries += values(
                &mut material
                    .passive
                    .entries()
                    .iter()
                    .chain(material.slices.iter().flat_map(|(u, v)| u.iter().chain(v)))
                    .chain([&material.passive_scale, &material.slice_scale]),
            );
            loci.push((Locus::Element(g), element));
            loci.push((
                Locus::Standing(g),
                CarrierBits {
                    entries: values(
                        &mut material.standing.iter().chain([&material.standing_scale]),
                    ),
                    ..CarrierBits::default()
                },
            ));
            if material.source.is_some() || !material.pairs.is_empty() {
                let mut source = material
                    .source
                    .as_ref()
                    .map(NormalLaw::carrier_bits)
                    .unwrap_or_default();
                source.entries += values(
                    &mut material
                        .pairs
                        .iter()
                        .flat_map(|(_, pair)| {
                            pair.outputs()
                                .iter()
                                .chain(pair.current_reads())
                                .chain(pair.earlier_reads())
                                .flatten()
                        })
                        .chain([&material.pair_scale]),
                );
                loci.push((Locus::SourcePort(g), source));
            }
            if let Some(receiving) = &material.receiving {
                let mut parts = receiving.carrier_bits();
                parts.entries += material.tree.as_ref().map_or(0, Landmarks::bits);
                parts.entries += material.population.as_ref().map_or(0, PortPopulation::bits);
                loci.push((Locus::ReceivingMap(g), parts));
            }
            if let Some(resonator) = &material.resonator {
                loci.push((
                    Locus::Resonator(g),
                    CarrierBits {
                        entries: values(
                            &mut resonator.gains().iter().chain(&material.resonator_scales),
                        ),
                        ..CarrierBits::default()
                    },
                ));
            }
        }
        for (a, material) in self.contacts.iter().enumerate() {
            loci.push((
                Locus::Channel(a),
                CarrierBits {
                    entries: values(
                        &mut material
                            .storage
                            .entries()
                            .iter()
                            .chain(material.stiffness.entries())
                            .chain(material.dissipation.entries())
                            .chain(&material.scales),
                    ),
                    ..CarrierBits::default()
                },
            ));
        }
        for ((locus, _), carry) in &self.carries {
            if let Some((_, parts)) = loci.iter_mut().find(|(l, _)| l == locus) {
                parts.remainders += carry.bits();
            }
        }
        loci.retain(|(locus, _)| !self.released.contains(locus));
        loci
    }

    /// **The constitution's exact bits** per retained locus: the sum of its carriers.
    pub fn bits_by_locus(&self) -> Vec<(Locus, u64)> {
        self.carrier_bits_by_locus()
            .into_iter()
            .map(|(locus, parts)| (locus, parts.total()))
            .collect()
    }

    /// The constitution's bits by carrier, over its retained loci.
    pub fn carrier_bits(&self) -> CarrierBits {
        let mut total = CarrierBits::default();
        for (_, parts) in self.carrier_bits_by_locus() {
            total.add(parts);
        }
        total
    }

    /// The constitution's exact bits: the sum over its retained loci.
    pub fn exact_bits(&self) -> u64 {
        self.carrier_bits().total()
    }

    /// **Every carried remainder**, exact, with its locus, its array and its entry (a reading of
    /// the lattice law: each lies in `[−2^(−L_ℓ−1), 2^(−L_ℓ−1))`, Lean `carried_remainder_bounded`).
    pub fn carried_remainders(&self) -> Vec<(Locus, Carrier, usize, Rat)> {
        let mut carried: Vec<(Locus, Carrier, usize, Rat)> = self
            .carries
            .iter()
            .flat_map(|((locus, array), carry)| {
                carry
                    .0
                    .iter()
                    .map(|(entry, r)| (*locus, *array, *entry, r.clone()))
            })
            .collect();
        for (g, material) in self.rings.iter().enumerate() {
            for (locus, law) in [
                (Locus::Element(g), Some(&material.contrast)),
                (Locus::SourcePort(g), material.source.as_ref()),
                (Locus::ReceivingMap(g), material.receiving.as_ref()),
            ] {
                if let Some(law) = law {
                    for (array, carry) in [
                        (Carrier::Map, &law.map_carry),
                        (Carrier::Gram, &law.gram_carry),
                    ] {
                        carried.extend(
                            carry
                                .0
                                .iter()
                                .map(|(entry, r)| (locus, array, *entry, r.clone())),
                        );
                    }
                }
            }
        }
        carried
    }

    /// **The carried trajectory** `Θ + r`: every carried remainder added back onto its entry (a
    /// reading chart, never published: it is off the lattice, and carries no remainder). Reading it
    /// against `Θ` measures what the carried remainders move at a receiver; with the released
    /// residuals it is the exact accumulation of what reached each locus.
    #[cfg(test)]
    pub(crate) fn with_remainders(&self) -> Result<Self, HnnError> {
        let mut exact = self.clone();
        for (locus, array, entry, r) in self.carried_remainders() {
            let ring = match locus {
                Locus::Element(g)
                | Locus::Standing(g)
                | Locus::SourcePort(g)
                | Locus::ReceivingMap(g)
                | Locus::Resonator(g)
                | Locus::Junction(g) => g,
                Locus::Channel(a) | Locus::Conductance(a) => a,
            };
            let add = |values: &mut [Rat]| -> Result<(), HnnError> {
                let expected = values.len();
                let slot = values.get_mut(entry).ok_or(HnnError::Shape {
                    what: "a carried remainder's entry",
                    expected,
                    found: entry,
                })?;
                *slot += &r;
                Ok(())
            };
            let add_matrix = |matrix: &mut ExactRatMatrix| -> Result<(), HnnError> {
                let mut values = matrix.entries().to_vec();
                add(&mut values)?;
                *matrix = flat_matrix(matrix.rows(), matrix.columns(), values)?;
                Ok(())
            };
            match (locus, array) {
                (Locus::Channel(_), Carrier::Factor(index)) => {
                    let material = &mut exact.contacts[ring];
                    add_matrix(match index {
                        0 => &mut material.storage,
                        1 => &mut material.stiffness,
                        _ => &mut material.dissipation,
                    })?;
                }
                (Locus::Channel(_), Carrier::FactorScale(index)) => {
                    add(std::slice::from_mut(
                        &mut exact.contacts[ring].scales[index],
                    ))?;
                }
                (_, Carrier::Passive) => add_matrix(&mut exact.rings[ring].passive)?,
                (_, Carrier::PassiveScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].passive_scale))?
                }
                (_, Carrier::SliceScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].slice_scale))?
                }
                (_, Carrier::StandingScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].standing_scale))?
                }
                (_, Carrier::PairScale) => {
                    add(std::slice::from_mut(&mut exact.rings[ring].pair_scale))?
                }
                (_, Carrier::Standing) => add(&mut exact.rings[ring].standing)?,
                (_, Carrier::Slices) => {
                    let material = &mut exact.rings[ring];
                    let n = material.standing.len();
                    let (rho, side, i) = (entry / (2 * n), (entry / n) % 2, entry % n);
                    let (u, v) = &mut material.slices[rho];
                    let slot = if side == 0 { &mut u[i] } else { &mut v[i] };
                    *slot += &r;
                }
                (_, Carrier::Pair { offset, family }) => {
                    let material = &mut exact.rings[ring];
                    let slot = material
                        .pairs
                        .iter_mut()
                        .find(|(declared, _)| *declared == offset)
                        .ok_or(HnnError::Offset { offset })?;
                    let mut families = [
                        slot.1.outputs().to_vec(),
                        slot.1.current_reads().to_vec(),
                        slot.1.earlier_reads().to_vec(),
                    ];
                    let width = families[family].first().map_or(1, Vec::len).max(1);
                    families[family][entry / width][entry % width] += &r;
                    let [outputs, current, earlier] = families;
                    slot.1 = PairPort::new(outputs, current, earlier)?;
                }
                (_, Carrier::Map | Carrier::Gram) => {
                    let material = &mut exact.rings[ring];
                    let law = match locus {
                        Locus::SourcePort(_) => material.source.as_mut(),
                        Locus::ReceivingMap(_) => material.receiving.as_mut(),
                        _ => Some(&mut material.contrast),
                    }
                    .ok_or(HnnError::MissingSourcePort { ring })?;
                    if array == Carrier::Map {
                        add_matrix(&mut law.map)?;
                    } else {
                        let n = law.gram.len();
                        law.gram[entry / n][entry % n] += &r;
                    }
                }
                (Locus::Resonator(_), Carrier::Resonator(family)) => {
                    let material = exact.rings[ring]
                        .resonator
                        .as_ref()
                        .ok_or(HnnError::Lattice { locus })?;
                    let mut gains = material.gains().clone();
                    let gain = gains.get_mut(family).ok_or(HnnError::Resonator {
                        ring,
                        what: "a resonator gain family is one of C, K, D, or pump",
                    })?;
                    *gain += &r;
                    let candidate = material.with_gains(gains)?;
                    exact.rings[ring].resonator = Some(candidate);
                }
                (Locus::Resonator(_), Carrier::ResonatorScale(family)) => {
                    let scale = exact.rings[ring].resonator_scales.get_mut(family).ok_or(
                        HnnError::Resonator {
                            ring,
                            what: "a resonator gain family is one of C, K, D, or pump",
                        },
                    )?;
                    *scale += &r;
                }
                (_, Carrier::Resonator(_) | Carrier::ResonatorScale(_)) => {
                    return Err(HnnError::Lattice { locus });
                }
                (_, Carrier::Factor(_) | Carrier::FactorScale(_)) => {}
            }
        }
        exact.carries.clear();
        for material in &mut exact.rings {
            for law in [
                Some(&mut material.contrast),
                material.source.as_mut(),
                material.receiving.as_mut(),
            ]
            .into_iter()
            .flatten()
            {
                law.map_carry = Carry::default();
                law.gram_carry = Carry::default();
            }
        }
        Ok(exact)
    }

    /// `L_R`, the finest admitted receiver grain the chart rule reads.
    pub fn grain(&self) -> u128 {
        self.grain
    }

    /// **The chart rule of a normal law's locus** ([`ChartRule`]): its lattice and `L_R`.
    pub fn chart_rule(&self, locus: Locus) -> Result<ChartRule, HnnError> {
        Ok(ChartRule::new(self.lattice(locus)?, self.grain))
    }

    /// The declared lattice of a learned locus.
    pub fn lattice(&self, locus: Locus) -> Result<Lattice, HnnError> {
        self.lattices
            .get(&locus)
            .copied()
            .ok_or(HnnError::Lattice { locus })
    }

    /// [definition; agent-inferred] **A contact's channel re-based onto the finer lattice**
    /// `2^(−L−j)ℤ` (Lean `HNN/LatticeDeposit/Rebase.Carried.rebase`; [`BudgetedCarry::rebase`] is
    /// the law): the storage, stiffness and dissipation factors and their three scales move with
    /// their carried remainders, the locus's lattice becomes the finer one and its clock is kept.
    /// Every entry plus its remainder is unchanged and nothing is released; the releases since the
    /// founding stay below half the founding unit over any history (`history_release_lt`). The
    /// declared schedule never calls it; a refining grain re-bases by the levels its exponent grew.
    ///
    /// A channel's lattice is read only by its deposits, so its re-base is this move alone. The ring
    /// loci also read their lattice outside the deposit (the solved charts' rule, the founding
    /// modulus, the standing's fine half unit, the resonator's Floquet grain), and their re-base is
    /// refused ([`HnnError::RebaseLocus`]); a released channel is refused
    /// ([`HnnError::ReleasedLocus`]).
    ///
    /// [definition; agent-inferred] A re-base by `j > 0` levels is published as a commit, since an
    /// entry that takes `q′u′` changes the applied factors and the lattice changes the next deposit's
    /// split: a boost's solve is certified again, the storage growth `C_a`, `K_a` is certified by
    /// inertia into [`Constitution::storage_product`] (module header, "The committed energy bound,
    /// enforced at the commit"), the exact bits stay within `B_Θ`, and the commit counter advances,
    /// so a deposit staged against the predecessor is refused ([`HnnError::StaleDeposit`]). A re-base
    /// by zero levels is the identity.
    pub fn rebased(&self, locus: Locus, levels: u32) -> Result<Self, HnnError> {
        let Locus::Channel(contact) = locus else {
            return Err(HnnError::RebaseLocus { locus });
        };
        if self.released.contains(&locus) {
            return Err(HnnError::ReleasedLocus { locus });
        }
        if levels == 0 {
            return Ok(self.clone());
        }
        let mut next = self.clone();
        let mut at = BudgetedCarry::new(next.lattice(locus)?, next.clock(locus) + 1);
        let material = next
            .contacts
            .get_mut(contact)
            .ok_or(HnnError::Lattice { locus })?;
        let mut carries: [Carry; 6] = std::array::from_fn(|k| {
            let carrier = if k < 3 {
                Carrier::Factor(k)
            } else {
                Carrier::FactorScale(k - 3)
            };
            next.carries.remove(&(locus, carrier)).unwrap_or_default()
        });
        let mut factors = [
            material.storage.entries().to_vec(),
            material.stiffness.entries().to_vec(),
            material.dissipation.entries().to_vec(),
        ];
        {
            let [c0, c1, c2, s0, s1, s2] = &mut carries;
            let [f0, f1, f2] = &mut factors;
            let [x0, x1, x2] = &mut material.scales;
            at.rebase(
                levels,
                &mut [
                    (c0, f0.as_mut_slice()),
                    (c1, f1.as_mut_slice()),
                    (c2, f2.as_mut_slice()),
                    (s0, std::slice::from_mut(x0)),
                    (s1, std::slice::from_mut(x1)),
                    (s2, std::slice::from_mut(x2)),
                ],
            )?;
        }
        let [f0, f1, f2] = factors;
        material.storage = flat_matrix(material.storage.rows(), material.storage.columns(), f0)?;
        material.stiffness =
            flat_matrix(material.stiffness.rows(), material.stiffness.columns(), f1)?;
        material.dissipation = flat_matrix(
            material.dissipation.rows(),
            material.dissipation.columns(),
            f2,
        )?;
        for (k, carry) in carries.into_iter().enumerate() {
            let carrier = if k < 3 {
                Carrier::Factor(k)
            } else {
                Carrier::FactorScale(k - 3)
            };
            if !carry.0.is_empty() {
                next.carries.insert((locus, carrier), carry);
            }
        }
        next.lattices.insert(locus, at.lattice());
        if let Some(boost) = &next.contacts[contact].boost {
            boost.certify(contact, &next.contacts[contact])?;
        }
        let storage_growth =
            certify_storage_growth(&self.storage_forms()?, &next.storage_forms()?)?
                .ok_or(HnnError::UncertifiedStorage)?;
        next.storage_product = &self.storage_product * (Rat::one() + &storage_growth);
        let bits = next.exact_bits();
        if bits > self.budget {
            return Err(HnnError::ConstitutionBudget {
                bits,
                budget: self.budget,
                commit: self.commit,
                loci: vec![locus],
            });
        }
        next.commit += 1;
        Ok(next)
    }

    /// **Whether every retained entry lies on its locus's lattice** (Lean `run_onLattice`): the
    /// maps, factors and statistics; the solved charts live on their own lattices `2^(−L_s)ℤ` by
    /// construction (integer coordinates), and the remainders are the carried residuals.
    pub fn on_lattice(&self) -> bool {
        let retained = |locus: Locus| !self.released.contains(&locus);
        let all = |lattice: Option<&Lattice>, values: &mut dyn Iterator<Item = &Rat>| {
            let Some(lattice) = lattice else {
                return false;
            };
            for value in values {
                if !lattice.contains(value) {
                    return false;
                }
            }
            true
        };
        let rings = self.rings.iter().enumerate().all(|(g, material)| {
            let element = self.lattices.get(&Locus::Element(g));
            let standing = self.lattices.get(&Locus::Standing(g));
            let source = self.lattices.get(&Locus::SourcePort(g));
            let receiving = self.lattices.get(&Locus::ReceivingMap(g));
            let resonator = self.lattices.get(&Locus::Resonator(g));
            (!retained(Locus::Element(g))
                || (all(
                    element,
                    &mut material
                        .passive
                        .entries()
                        .iter()
                        .chain(material.slices.iter().flat_map(|(u, v)| u.iter().chain(v)))
                        .chain([&material.passive_scale, &material.slice_scale]),
                ) && element.is_some_and(|l| material.contrast.on_lattice(l))))
                && (!retained(Locus::Standing(g))
                    || all(
                        standing,
                        &mut material.standing.iter().chain([&material.standing_scale]),
                    ))
                && (!retained(Locus::SourcePort(g))
                    || material.source.is_none() && material.pairs.is_empty()
                    || (all(
                        source,
                        &mut material
                            .pairs
                            .iter()
                            .flat_map(|(_, pair)| {
                                pair.outputs()
                                    .iter()
                                    .chain(pair.current_reads())
                                    .chain(pair.earlier_reads())
                                    .flatten()
                            })
                            .chain([&material.pair_scale]),
                    ) && material
                        .source
                        .as_ref()
                        .is_none_or(|law| source.is_some_and(|l| law.on_lattice(l)))))
                && material
                    .receiving
                    .as_ref()
                    .is_none_or(|law| receiving.is_some_and(|l| law.on_lattice(l)))
                && material.resonator.as_ref().is_none_or(|law| {
                    resonator.is_some_and(|l| {
                        law.gains()
                            .iter()
                            .chain(&material.resonator_scales)
                            .all(|x| l.contains(x))
                    })
                })
        });
        let contacts = self.contacts.iter().enumerate().all(|(a, material)| {
            !retained(Locus::Channel(a))
                || all(
                    self.lattices.get(&Locus::Channel(a)),
                    &mut material
                        .storage
                        .entries()
                        .iter()
                        .chain(material.stiffness.entries())
                        .chain(material.dissipation.entries())
                        .chain(&material.scales),
                )
        });
        rings && contacts
    }

    /// **The storage forms a deposit can change** (module header, "The committed energy bound,
    /// enforced at the commit"): each contact's `C_a = c cᵀ` and `K_a = b bᵀ`, and each unpumped
    /// resonator's `C` and `K` (squared gains times their declared bases). A pumped resonator's
    /// stiffness may be indefinite; its growth is its Floquet reach, and its own gains are held
    /// (module header, "The pumped medium's reach"), so no deposit changes its storage.
    fn storage_forms(&self) -> Result<Vec<ExactRatMatrix>, HnnError> {
        let mut forms = Vec::new();
        for material in &self.contacts {
            forms.push(gram(&material.storage)?);
            forms.push(gram(&material.stiffness)?);
        }
        for material in &self.rings {
            if let Some(resonator) = &material.resonator
                && !pumped(resonator)
            {
                let (capacity, stiffness, _) = resonator.forms();
                forms.push(capacity.clone());
                forms.push(stiffness.clone());
            }
        }
        Ok(forms)
    }

    /// `∏(1 + ε_k)` since the founding: the committed energy bound's product of certified storage
    /// growths.
    pub fn storage_product(&self) -> &Rat {
        &self.storage_product
    }

    /// **The per-tick amplitude growth `1 + ω`** of the word at this constitution (module header,
    /// "The certified step"): `ω` the largest certified bound of a ring's contrast port
    /// (`holon::deposition::{schur_norms, sqrt_ceiling}` at the ring's element lattice), so a tick
    /// multiplies the power by at most `(1 + ω)²` (`holon::deposition::active_growth`). `None` when a
    /// resonator is not certified passive: its growth is the medium's reach, read with the span
    /// factor ([`Constitution::medium_reach`]; module header, "The pumped medium's reach").
    pub fn amplitude(&self) -> Result<Option<Rat>, HnnError> {
        for material in &self.rings {
            if let Some(resonator) = &material.resonator
                && !certified_passive(resonator)?
            {
                return Ok(None);
            }
        }
        Ok(Some(self.contrast_amplitude()?))
    }

    /// `1 + ω`, the contrast ports' certified per-tick amplitude growth, whatever the resonators.
    pub fn contrast_amplitude(&self) -> Result<Rat, HnnError> {
        let mut bound = Rat::zero();
        for (g, material) in self.rings.iter().enumerate() {
            let (column, row) = schur_norms(material.contrast.map());
            let omega = sqrt_ceiling(&(column * row), self.lattice(Locus::Element(g))?.exponent());
            if omega > bound {
                bound = omega;
            }
        }
        Ok(Rat::one() + bound)
    }

    /// [definition; agent-inferred, September 29] **Each ring's reach over the spans `0..=span`**
    /// (module header, "The pumped medium's reach"): every ring whose resonator is not certified
    /// passive, its Floquet monodromy over its pump's period on the exact law
    /// (`hnn::ring::Floquet::of` at the ring's admittance and hop), decided at its resonator
    /// lattice's grain `2^(−g)` (its growth `ρ₀`), and its growth's ladder `ρ₀(1 + 2^k)`,
    /// `|k| ≤ g`, each metric attained by the exact Stein solve and certified by inertia
    /// (`hnn::ring::{attain_metric, Floquet::certify, Floquet::bound}`). A metric near `ρ₀` is
    /// ill-conditioned (`γ_hi/γ_lo` large); a growth far above it grows every period: the ladder
    /// climbs from `k = 0` toward the rung whose reach at the longest span is least and stops where
    /// it no longer falls, and each span's reach is the least of the certified bounds' (each a bound,
    /// so their least is). When no rung certifies, the decided certificate's bound is read. A
    /// refused decision is the refusal [`HnnError::UncertifiedGain`], with its reason: no step is
    /// certified through that ring.
    fn ring_reaches(&self, span: u64) -> Result<Vec<RingReach>, HnnError> {
        let mut rings = Vec::new();
        for (ring, material) in self.rings.iter().enumerate() {
            let Some(resonator) = &material.resonator else {
                continue;
            };
            if certified_passive(resonator)? {
                continue;
            }
            let locus = Locus::Resonator(ring);
            let hop = material
                .resonator_step
                .as_ref()
                .ok_or(HnnError::Lattice { locus })?;
            let grain = self.lattice(locus)?.exponent();
            let refused = |error: HnnError| match error {
                HnnError::UncertifiedFloquet { ring, refusal } => {
                    HnnError::UncertifiedGain { ring, refusal }
                }
                other => other,
            };
            let operands =
                ResonatorOperands::at_cut(ring, resonator, &self.admittances[ring], hop, None)?;
            let floquet = Floquet::of(&operands)?;
            let reading = floquet.decide(grain).map_err(refused)?;
            let decided = reading.certificate().growth().clone();
            let longest = span as usize;
            // One rung: the growth `ρ₀(1 + 2^k)`, its metric attained by the exact Stein solve and
            // certified by inertia; a growth the solve cannot attain (`ρ² = μ_iμ_j`) or the
            // certificate refuses gives no bound.
            let rung = |k: i64| -> Result<Option<(FloquetBound, Vec<Rat>)>, HnnError> {
                let margin = if k < 0 {
                    Rat::new(BigInt::one(), BigInt::one() << (-k) as usize)
                } else {
                    Rat::from_integer(BigInt::one() << k as usize)
                };
                let growth = &decided * (Rat::one() + margin);
                let Ok(metric) = attain_metric(ring, floquet.monodromy(), &growth) else {
                    return Ok(None);
                };
                let Ok(certificate) = floquet.certify(&metric, &growth) else {
                    return Ok(None);
                };
                let bound = floquet.bound(&certificate, grain)?;
                let table = (0..=span).map(|s| ceiling(&bound.reach(s))).collect();
                Ok(Some((bound, table)))
            };
            // The ladder climbs from `k = 0` toward the rung whose reach at the longest span is
            // least, one dyadic rung at a time within `|k| ≤ g`, and stops where it no longer falls.
            let bound_k = i64::from(grain);
            let mut read: Vec<(i64, FloquetBound, Vec<Rat>)> = Vec::new();
            if let Some((bound, table)) = rung(0)? {
                read.push((0, bound, table));
            }
            if let Some((_, _, at_zero)) = read.first().cloned() {
                for direction in [-1i64, 1] {
                    let mut best = at_zero[longest].clone();
                    let mut k = direction;
                    while k.abs() <= bound_k {
                        let Some((bound, table)) = rung(k)? else {
                            break;
                        };
                        let falls = table[longest] < best;
                        if falls {
                            best = table[longest].clone();
                        }
                        read.push((k, bound, table));
                        if !falls {
                            break;
                        }
                        k += direction;
                    }
                }
            }
            // No rung certified: the decided certificate's own bound.
            if read.is_empty() {
                let bound = floquet
                    .bound(reading.certificate(), grain)
                    .map_err(refused)?;
                let table = (0..=span).map(|s| ceiling(&bound.reach(s))).collect();
                read.push((i64::MIN, bound, table));
            }
            read.sort_by_key(|(k, ..)| *k);
            let mut reach = read[0].2.clone();
            for (_, _, table) in &read[1..] {
                for (kept, value) in reach.iter_mut().zip(table) {
                    if value < kept {
                        *kept = value.clone();
                    }
                }
            }
            let bounds = read.into_iter().map(|(_, bound, _)| bound).collect();
            rings.push(RingReach {
                ring,
                reading,
                bounds,
                reach,
            });
        }
        Ok(rings)
    }

    /// The span factors `F(0..=span)` of the rings' reaches, each at its ceiling on the
    /// certificate's face (`holon::deposition::span_factors`).
    fn factors_of(rings: &[RingReach], span: u64) -> Vec<Rat> {
        let tables: Vec<Vec<Rat>> = rings.iter().map(|ring| ring.reach.clone()).collect();
        span_factors(&tables, span as usize)
            .iter()
            .map(ceiling)
            .collect()
    }

    /// [definition; agent-inferred, September 29] **The medium's reach over the spans `0..=span`**
    /// (module header, "The pumped medium's reach"): the contrast ports' `1 + ω`, each ring not
    /// certified passive with its reach, and the span factors. A consumer's energy bound over a
    /// refinement of `T` ticks reads `F(T)` beside `1 + ω` (Lean `Holon/Deposition.pumped_span_factor`:
    /// every span within `T` is carried by `F(T)` at most). Refused where a ring's certificate is.
    pub fn medium_reach(&self, span: u64) -> Result<MediumReach, HnnError> {
        let rings = self.ring_reaches(span)?;
        let factors = Self::factors_of(&rings, span);
        Ok(MediumReach {
            amplitude: self.contrast_amplitude()?,
            rings,
            factors,
        })
    }

    /// **A linear locus's gain `κ²`** at a readout bound `‖R‖₂²` and an amplitude growth `1 + ω`
    /// (module header, "The certified step").
    fn gain(&self, locus: LinearLocus, reach: &Reach, readout: &Rat, sums: &(Rat, Rat)) -> Rat {
        match locus {
            LinearLocus::Receiving(_) => Rat::one(),
            LinearLocus::SourcePort(g) => self.source_gain(g, reach, readout, &sums.1),
            LinearLocus::Contrast(r) => self.element_gain(r, reach, readout, &sums.0),
        }
    }

    /// **The gain from an injection at source ring `g`**, `d ‖R‖² (Y_g/Y_R) Σ_j (Σ_n (1+ω)^(T_j−T_n))²`
    /// at the reach's entry gain (module header, "The certified step").
    fn source_gain(&self, g: usize, reach: &Reach, readout: &Rat, entry: &Rat) -> Rat {
        Rat::from_integer(BigInt::from(reach.phases))
            * readout
            * (&self.admittances[g] / &self.admittances[reach.receiver])
            * entry
    }

    /// **The gain from an element output at ring `r`**, `‖R‖² (Y_r/Y_R) Σ_j Σ_(τ<T_j) (1+ω)^(2(T_j−τ−1))`
    /// at the reach's tick gain (module header, "The certified step").
    fn element_gain(&self, r: usize, reach: &Reach, readout: &Rat, tick: &Rat) -> Rat {
        readout * (&self.admittances[r] / &self.admittances[reach.receiver]) * tick
    }

    /// **The gain from a solve's right-hand side whose difference carries at most `P|δζ|²`** (a
    /// channel's transit or a loaded resonator's solve), `‖R‖² (4/(h Y_R)) P Σ_j Σ_(τ<T_j) (1+ω)^(2(T_j−τ−1))`
    /// (module header, "The factor families' certified step"; Lean
    /// `Holon/Deposition.{contracting_resolvent, transit_difference_power}`).
    fn power_gain(&self, power: &Rat, reach: &Reach, readout: &Rat, tick: &Rat) -> Rat {
        readout * Rat::from_integer(BigInt::from(4)) * power
            / (&self.hop * &self.admittances[reach.receiver])
            * tick
    }

    /// **A solve's difference power coefficient** `P = G/(2h) + ½(G/h)²‖C‖ + ⅛G²‖K‖` at a conductance
    /// `G` and storage norms `‖C‖`, `‖K‖` (Lean `Holon/Deposition.transit_difference_power`; a loaded
    /// resonator is the case `G = 2Y`).
    fn difference_power(&self, conductance: &Rat, storage: &Rat, stiffness: &Rat) -> Rat {
        let ratio = conductance / &self.hop;
        &ratio / Rat::from_integer(BigInt::from(2))
            + &ratio * &ratio * storage / Rat::from_integer(BigInt::from(2))
            + conductance * conductance * stiffness / Rat::from_integer(BigInt::from(8))
    }

    /// **The certified steps of a deposit's families** (module header, "The certified step", "The
    /// factor families' certified step", "The tightened certificate"): each prepared unit step whose
    /// alignment is positive, a normal law's or a factor family's, is certified (a negative alignment
    /// is refused). Each family's own curvature `C = s κ² b` is read with the gains and the moves at
    /// the end of every family's ray, and the families' joint moves by the triangle on the joint ray,
    /// `s (Σ η m)² ≤ Σ η a` with `m = √(κ² b)` at its dyadic ceiling
    /// ([`crate::holon::deposition::JointReading`]). Each family starts at the largest dyadic its own
    /// certificate admits (`ηC ≤ a`, `ηc ≤ 1`); a step whose own certificate the readings at the rays'
    /// ends do not admit is halved, and while the joint certificate fails the family whose halving
    /// gains it most, `½ η (s m (2 Σ η m − ½ η m) − a)`, is halved, until both hold. Refused without a
    /// reach, through a declared boost, through a ring whose Floquet decision is refused, and for a
    /// channel family through a contact whose conductance has no bound. Every gain but the
    /// receiving map's reads the pumped medium's span factor, and a reach-read ring's own gain
    /// families are held (module header, "The pumped medium's reach").
    fn certify_steps(
        &self,
        reach: Option<&Reach>,
        linear: &[(Locus, LinearLocus, &PreparedStep)],
        factors: &[(Locus, &FactorPrepared)],
    ) -> Result<CertifiedSteps, HnnError> {
        /// A normal law's readings at the certificate's faces: its alignment at its floor, its
        /// covector scale, feature moves and unit step's Schur norms at their ceilings, and (the
        /// receiving map's only) its unit step's certified spectral norm.
        struct LinearFace {
            kind: LinearLocus,
            alignment: Rat,
            covector: Rat,
            moves: Rat,
            unit: (Rat, Rat),
            norm: Rat,
        }
        /// A family stepping in the deposit.
        enum Part<'p> {
            Linear(LinearFace),
            Factor(&'p FactorPrepared),
        }
        /// The prepared factor family at a key, when it steps.
        fn factor_at<'p>(
            parts: &'p [(Locus, Family, Part<'p>)],
            place: &BTreeMap<(Locus, Family), usize>,
            key: (Locus, Family),
        ) -> Option<&'p FactorPrepared> {
            place.get(&key).and_then(|&index| match &parts[index].2 {
                Part::Factor(prepared) => Some(*prepared),
                Part::Linear(..) => None,
            })
        }
        let mut parts: Vec<(Locus, Family, Part<'_>)> = Vec::new();
        for (locus, kind, prepared) in linear {
            let alignment = floor(&prepared.alignment);
            let covector = ceiling(&prepared.covector);
            if CertifiedStep::certify(&alignment, &Rat::zero(), &covector)?.is_none() {
                continue;
            }
            // The receiving map's unit step moves the readout every other family's gain reads: its
            // certified spectral norm (the other maps' rays read their Schur norms).
            let norm = match kind {
                LinearLocus::Receiving(_) => {
                    let rows = prepared.unit.to_rows();
                    let columns = rows.first().map_or(0, Vec::len);
                    let entries: Vec<Rat> = rows.into_iter().flatten().collect();
                    ceiling(&spectral_norm(
                        entries.len() / columns.max(1),
                        columns,
                        &entries,
                    ))
                }
                _ => Rat::zero(),
            };
            if alignment.is_zero() {
                continue;
            }
            let face = LinearFace {
                kind: *kind,
                alignment,
                covector,
                moves: ceiling(&prepared.moves),
                unit: ceilings(&prepared.unit_norms),
                norm,
            };
            parts.push((*locus, Family::Map, Part::Linear(face)));
        }
        for (locus, prepared) in factors {
            if CertifiedStep::certify(&prepared.alignment, &Rat::zero(), &prepared.covector)?
                .is_some()
            {
                parts.push((*locus, prepared.family, Part::Factor(prepared)));
            }
        }
        if parts.is_empty() {
            return Ok((BTreeMap::new(), None, None));
        }
        let reach = reach.ok_or(HnnError::MissingReach)?;
        if let Some(contact) = self
            .contacts
            .iter()
            .position(|material| material.boost.is_some())
        {
            return Err(HnnError::ActiveContact { contact });
        }
        for (locus, ..) in &parts {
            if let Locus::Channel(contact) = *locus
                && self.conductances[contact].is_none()
            {
                return Err(HnnError::UncertifiedConductance { contact });
            }
        }
        // `s`, the station score's curvature in its realified logits (module header).
        let score = rat(1, 2);
        let receiving = self
            .rings
            .get(reach.receiver)
            .and_then(|material| material.receiving.as_ref())
            .ok_or(HnnError::MissingReceivingMap {
                ring: reach.receiver,
            })?;
        // The readout's certified spectral norm `‖R‖₂` (module header, "The tightened certificate").
        let map = receiving.map();
        let readout_base = ceiling(&spectral_norm(map.rows(), map.columns(), map.entries()));
        // The pumped medium's reach (module header, "The pumped medium's reach"): each ring not
        // certified passive read by its Floquet bound (refused where its certificate is), the span
        // factors over the stations' spans, and the ring's own gain families held where their rays
        // would read a reach no certificate covers: always for a pumped ring (its pumped stiffness
        // also has no certified storage growth at the commit), and for a signed stiffness unless
        // the readout is zero along the whole joint ray (then every gain is zero, whatever the
        // reach).
        let span = reach.stations.iter().max().copied().unwrap_or(0);
        let rings = self.ring_reaches(span)?;
        let factors = (!rings.is_empty()).then(|| Self::factors_of(&rings, span));
        let mut held = Vec::new();
        if !rings.is_empty() {
            let silent = readout_base.is_zero()
                && !parts.iter().any(|(locus, family, _)| {
                    *locus == Locus::ReceivingMap(reach.receiver) && *family == Family::Map
                });
            let holds = |locus: &Locus| match *locus {
                Locus::Resonator(ring) => {
                    rings.iter().any(|reached| reached.ring == ring)
                        && (!silent || self.rings[ring].resonator.as_ref().is_some_and(pumped))
                }
                _ => false,
            };
            held = parts
                .iter()
                .filter(|(locus, ..)| holds(locus))
                .map(|(locus, family, _)| (*locus, *family))
                .collect();
            parts.retain(|(locus, ..)| !holds(locus));
        }
        let pumped_reading = factors.as_ref().map(|factors| PumpedReading {
            rings: rings.clone(),
            span,
            factor: factors.last().cloned().unwrap_or_else(Rat::one),
            held: held.clone(),
        });
        if parts.is_empty() {
            return Ok((BTreeMap::new(), None, pumped_reading));
        }
        let place: BTreeMap<(Locus, Family), usize> = parts
            .iter()
            .enumerate()
            .map(|(index, (locus, family, _))| ((*locus, *family), index))
            .collect();
        let contrast_base: Vec<(Rat, Rat)> = self
            .rings
            .iter()
            .map(|material| ceilings(&schur_norms(material.contrast.map())))
            .collect();
        let grains: Vec<u32> = (0..self.rings.len())
            .map(|g| Ok(self.lattice(Locus::Element(g))?.exponent()))
            .collect::<Result<_, HnnError>>()?;
        // The slices' Schur norms by ring (their rows the slices `ρ`), which the standing's lock
        // chart reads at every ring it reaches.
        let slice_base: Vec<((Rat, Rat), (Rat, Rat))> = self
            .rings
            .iter()
            .map(|material| {
                let (u, v) = slice_norms(&material.slices);
                (ceilings(&u), ceilings(&v))
            })
            .collect();
        // Each channel's storage and stiffness factors' Schur norms, at their ceilings.
        let channel_base: Vec<((Rat, Rat), (Rat, Rat))> = self
            .contacts
            .iter()
            .map(|material| {
                (
                    ceilings(&schur_norms(&material.storage)),
                    ceilings(&schur_norms(&material.stiffness)),
                )
            })
            .collect();
        // Each loaded resonator's gains and its storage bases' Schur products.
        let resonator_base: Vec<Option<([Rat; 4], Rat, Rat)>> = self
            .rings
            .iter()
            .map(|material| {
                material.resonator.as_ref().map(|resonator| {
                    let (capacity, stiffness, ..) = resonator.gain_bases();
                    let product = |form: &ExactRatMatrix| {
                        let (column, row) = ceilings(&schur_norms(form));
                        column * row
                    };
                    (
                        resonator.gains().clone(),
                        product(capacity),
                        product(stiffness),
                    )
                })
            })
            .collect();
        // The step a family takes (zero when it does not step).
        let taken = |steps: &[Option<CertifiedStep>], key: (Locus, Family)| -> Rat {
            place
                .get(&key)
                .and_then(|&index| steps[index].as_ref())
                .map_or_else(Rat::zero, |step| step.step.clone())
        };
        // The Schur bound at the end of a ray: `(‖W‖₁ + η‖D‖₁)(‖W‖_∞ + η‖D‖_∞)`.
        let ray = |base: &(Rat, Rat), moved: Option<(&Rat, &(Rat, Rat))>| -> Rat {
            match moved {
                Some((step, unit)) => ray_product(base, unit, step),
                None => &base.0 * &base.1,
            }
        };
        let gains = |steps: &[Option<CertifiedStep>]| -> (Rat, Rat) {
            let moved = |key: (Locus, Family)| {
                place.get(&key).and_then(|&index| match &parts[index].2 {
                    Part::Linear(face) => {
                        steps[index].as_ref().map(|step| (&step.step, &face.unit))
                    }
                    Part::Factor(_) => None,
                })
            };
            // `(‖R‖₂ + η‖D‖₂)²` at the end of the receiving map's ray (the triangle on the
            // certified spectral norms).
            let key = (Locus::ReceivingMap(reach.receiver), Family::Map);
            let reached = place
                .get(&key)
                .and_then(|&index| match (&parts[index].2, steps[index].as_ref()) {
                    (Part::Linear(face), Some(step)) => Some(&step.step * &face.norm),
                    _ => None,
                })
                .map_or_else(|| readout_base.clone(), |moved| &readout_base + moved);
            let readout = &reached * &reached;
            let omega = (0..self.rings.len())
                .map(|r| {
                    sqrt_ceiling(
                        &ray(&contrast_base[r], moved((Locus::Element(r), Family::Map))),
                        grains[r],
                    )
                })
                .max()
                .unwrap_or_else(Rat::zero);
            (readout, Rat::one() + omega)
        };
        // A factor family's square carrier at the end of its ray, `S(x + ηD)` (its current value
        // when it does not step).
        let square_ray =
            |steps: &[Option<CertifiedStep>], key: (Locus, Family), base: &(Rat, Rat)| {
                match factor_at(&parts, &place, key).map(|prepared| &prepared.moves) {
                    Some(Moves::Square { unit, factor, .. }) => {
                        ray_product(factor, unit, &taken(steps, key))
                    }
                    _ => &base.0 * &base.1,
                }
            };
        // Each family's gain `κ²` and moves `b` at the end of every ray.
        let curvature = |index: usize,
                         steps: &[Option<CertifiedStep>],
                         readout: &Rat,
                         sums: &(Rat, Rat)|
         -> Result<(Rat, Rat), HnnError> {
            let (locus, family, part) = &parts[index];
            let prepared = match part {
                Part::Linear(face) => {
                    return Ok((
                        self.gain(face.kind, reach, readout, sums),
                        face.moves.clone(),
                    ));
                }
                Part::Factor(prepared) => *prepared,
            };
            let own = &taken(steps, (*locus, *family));
            let tick = || sums.0.clone();
            match (*locus, &prepared.moves) {
                (Locus::Standing(_), Moves::Standing { unit, reach: rings }) => {
                    let tick = tick();
                    let (mut moves, mut widest, mut terms) = (Rat::zero(), Rat::zero(), 0u64);
                    for (r, energy) in rings {
                        if energy.is_zero() {
                            continue;
                        }
                        let (u, v) = &slice_base[*r];
                        let (s_u, s_v) =
                            match factor_at(&parts, &place, (Locus::Element(*r), Family::Slices))
                                .map(|prepared| &prepared.moves)
                            {
                                Some(Moves::Slices { du, dv, .. }) => {
                                    let step = taken(steps, (Locus::Element(*r), Family::Slices));
                                    (ray_product(u, du, &step), ray_product(v, dv, &step))
                                }
                                _ => (&u.0 * &u.1, &v.0 * &v.1),
                            };
                        let term =
                            Rat::from_integer(BigInt::from(4)) * unit * unit * s_u * s_v * energy;
                        if term.is_zero() {
                            continue;
                        }
                        let gain = self.element_gain(*r, reach, readout, &tick);
                        if gain > widest {
                            widest = gain;
                        }
                        moves += term;
                        terms += 1;
                    }
                    Ok((Rat::from_integer(BigInt::from(terms)) * widest, moves))
                }
                (Locus::Element(r), moves) => Ok((
                    self.element_gain(r, reach, readout, &tick()),
                    moves.own(&prepared.energy, own)?,
                )),
                (Locus::SourcePort(g), moves) => Ok((
                    self.source_gain(g, reach, readout, &sums.1),
                    moves.own(&prepared.energy, own)?,
                )),
                (Locus::Channel(a), moves) => {
                    let conductance = self.conductances[a]
                        .as_ref()
                        .ok_or(HnnError::UncertifiedConductance { contact: a })?;
                    let (storage, stiffness) = &channel_base[a];
                    let storage = square_ray(steps, (*locus, Family::Factor(0)), storage);
                    let stiffness = square_ray(steps, (*locus, Family::Factor(1)), stiffness);
                    let power = self.difference_power(conductance, &storage, &stiffness);
                    Ok((
                        self.power_gain(&power, reach, readout, &tick()),
                        moves.own(&prepared.energy, own)?,
                    ))
                }
                (Locus::Resonator(g), moves) => {
                    let (gains, capacity, stiffness) = resonator_base[g]
                        .as_ref()
                        .ok_or(HnnError::Lattice { locus: *locus })?;
                    // `g_i + η|D_i|` at the end of each gain's ray.
                    let reached = |family: usize| -> Rat {
                        let key = (*locus, Family::Resonator(family));
                        match factor_at(&parts, &place, key).map(|prepared| &prepared.moves) {
                            Some(Moves::Resonator { unit, gain }) => {
                                gain + taken(steps, key) * unit
                            }
                            _ => gains[family].abs(),
                        }
                    };
                    let (c, k) = (reached(0), reached(1));
                    let power = self.difference_power(
                        &(Rat::from_integer(BigInt::from(2)) * &self.admittances[g]),
                        &(&c * &c * capacity),
                        &(&k * &k * stiffness),
                    );
                    Ok((
                        self.power_gain(&power, reach, readout, &tick()),
                        moves.own(&prepared.energy, own)?,
                    ))
                }
                _ => Err(HnnError::Lattice { locus: *locus }),
            }
        };
        // The reach's tick and entry sums at an amplitude growth, at their ceilings, read once a
        // pass.
        let sums = |amplitude: &Rat| {
            (
                ceiling(&reach.tick_gain(amplitude, factors.as_deref())),
                ceiling(&reach.entry_gain(amplitude, factors.as_deref())),
            )
        };
        let reading = |steps: &[Option<CertifiedStep>]| -> Result<Vec<(Rat, Rat)>, HnnError> {
            let (readout, amplitude) = gains(steps);
            let sums = sums(&amplitude);
            (0..parts.len())
                .map(|index| curvature(index, steps, &readout, &sums))
                .collect()
        };
        let alignment = |part: &Part<'_>| -> (Rat, Rat) {
            match part {
                Part::Linear(face) => (face.alignment.clone(), face.covector.clone()),
                Part::Factor(prepared) => (prepared.alignment.clone(), prepared.covector.clone()),
            }
        };
        // The first steps: each family's own certificate at the current constitution (its curvature
        // `C = s κ² b`, the largest dyadic with `ηC ≤ a` and `ηc ≤ 1`).
        let none = vec![None; parts.len()];
        let first = reading(&none)?;
        let mut steps: Vec<Option<CertifiedStep>> = parts
            .iter()
            .zip(&first)
            .map(|((.., part), (gain, moves))| {
                let (a, c) = alignment(part);
                CertifiedStep::certify(&a, &(&score * gain * moves), &c)
            })
            .collect::<Result<_, _>>()?;
        loop {
            let read = reading(&steps)?;
            // Each family's own certificate at the rays' ends: a step it no longer admits is halved.
            let mut changed = false;
            for (step, (gain, moves)) in steps.iter_mut().zip(&read) {
                let certified = step
                    .as_mut()
                    .expect("a positive alignment certifies a step");
                let curvature = &score * gain * moves;
                if certified.admits(&curvature) {
                    certified.curvature = curvature;
                } else {
                    *certified = certified.halved();
                    changed = true;
                }
            }
            if changed {
                continue;
            }
            // The joint moves by the triangle: `m = √(κ² b)` at its dyadic ceiling.
            let bounds: Vec<Rat> = read
                .iter()
                .map(|(gain, moves)| root_ceiling(&ceiling(&(gain * moves))))
                .collect();
            let certified: Vec<&CertifiedStep> = steps
                .iter()
                .map(|step| {
                    step.as_ref()
                        .expect("a positive alignment certifies a step")
                })
                .collect();
            // The joint certificate reads the realized score's moves: a standing's step stays in
            // its lobes (module header, "Within a lobe"), where the element reads it not at all, so
            // its realized move and decrease are both zero and it leaves the joint certificate
            // (Lean `HNN/Normal.lobe_move_is_null`); its own lock-chart certificate still rates it.
            let realized: Vec<bool> = parts
                .iter()
                .map(|(_, family, _)| *family != Family::Standing)
                .collect();
            let joint = JointReading::read(
                &score,
                certified
                    .iter()
                    .zip(&bounds)
                    .zip(&realized)
                    .filter(|(_, realized)| **realized)
                    .map(|((step, bound), _)| (&step.step, &step.alignment, bound)),
            );
            if !joint.holds() {
                // The family whose halving gains the joint certificate most,
                // `½ η (s m (2 Σ η m − ½ η m) − a)`; the first in the deposit's order at a tie.
                let total: Rat = certified
                    .iter()
                    .zip(&bounds)
                    .zip(&realized)
                    .filter(|(_, realized)| **realized)
                    .map(|((step, bound), _)| &step.step * bound)
                    .sum();
                let two = rat(2, 1);
                let mut worst: Option<(usize, Rat)> = None;
                for (index, (step, bound)) in certified.iter().zip(&bounds).enumerate() {
                    if !realized[index] {
                        continue;
                    }
                    let moved = &step.step * bound;
                    let gained = &step.step
                        * (&score * bound * (&two * &total - &moved / &two) - &step.alignment)
                        / &two;
                    if worst.as_ref().is_none_or(|(_, kept)| gained > *kept) {
                        worst = Some((index, gained));
                    }
                }
                let (index, _) = worst.expect("a stepping family");
                let step = steps[index].as_mut().expect("a stepping family");
                *step = step.halved();
                continue;
            }
            let (readout, amplitude) = gains(&steps);
            let readings: BTreeMap<(Locus, Family), StepReading> = parts
                .iter()
                .zip(&steps)
                .zip(read)
                .zip(bounds)
                .map(|((((locus, family, _), step), (gain, moves)), bound)| {
                    (
                        (*locus, *family),
                        StepReading {
                            family: *family,
                            step: step.clone().expect("a positive alignment certifies a step"),
                            gain,
                            moves,
                            bound,
                            readout: readout.clone(),
                            amplitude: amplitude.clone(),
                        },
                    )
                })
                .collect();
            return Ok((readings, Some(joint), pumped_reading));
        }
    }

    /// **The successor of a staged deposit** (design (c), `deposit`): each linear locus's step
    /// prepared at its unit step (its Gram carried and its chart refined) and each factor family's
    /// (its statistic carried, its unit step `G_x / h_x′` read), all certified together against every
    /// family's gains and moves (module header, "The certified step", "The factor families' certified
    /// step") and carried; the commit advanced; the storage growth certified (a deposit with none
    /// certified is refused); and the budget checked on the successor's exact bits before anything
    /// is published. Refused with [`HnnError::ConstitutionBudget`] past `B_Θ`, with
    /// [`HnnError::StaleDeposit`] when the deposit was computed at another commit, with
    /// [`HnnError::ReleasedLocus`] when it names a released locus, with
    /// [`HnnError::RepeatedFactorStep`] when it steps one family twice, and with the certified step's
    /// refusals. A loaded resonator's gain step whose carried gain would be `≤ 0` backtracks to the
    /// midpoint of the admissible side and is named in the reading ([`GainBacktrack`]): deposition
    /// never releases a family.
    pub fn deposited(&self, deposit: &Deposit) -> Result<(Self, DepositReading), HnnError> {
        if deposit.commit() != self.commit {
            return Err(HnnError::StaleDeposit {
                staged: deposit.commit(),
                published: self.commit,
            });
        }
        let mut next = self.clone();
        // The deposit's steps by locus, each with its place in the deposit's order (its linear
        // steps, then its factor steps, then its class-mass steps).
        let mut groups: BTreeMap<Locus, Vec<(usize, LocusStep<'_>)>> = BTreeMap::new();
        for (index, step) in deposit.linear().iter().enumerate() {
            groups
                .entry(step.locus.locus())
                .or_default()
                .push((index, LocusStep::Linear(step)));
        }
        for (locus, steps) in &groups {
            if steps.len() > 1 {
                return Err(HnnError::RepeatedLinearStep { locus: *locus });
            }
        }
        let linear = deposit.linear().len();
        let mut families: BTreeSet<(Locus, Family)> = BTreeSet::new();
        for (index, step) in deposit.factors().iter().enumerate() {
            let locus = step.gradient.locus();
            if !families.insert((locus, step.gradient.family())) {
                return Err(HnnError::RepeatedFactorStep {
                    locus,
                    family: step.gradient.family(),
                });
            }
            groups
                .entry(locus)
                .or_default()
                .push((linear + index, LocusStep::Factor(step)));
        }
        let factors = linear + deposit.factors().len();
        for (index, step) in deposit.landmarks().iter().enumerate() {
            groups
                .entry(Locus::ReceivingMap(step.ring))
                .or_default()
                .push((factors + index, LocusStep::Landmark(step)));
        }
        let landmarks = factors + deposit.landmarks().len();
        for (index, step) in deposit.receiving().iter().enumerate() {
            groups
                .entry(Locus::ReceivingMap(step.ring))
                .or_default()
                .push((landmarks + index, LocusStep::Receiving(step)));
        }
        let resonators_to_certify: Vec<usize> = groups
            .keys()
            .filter_map(|locus| match locus {
                Locus::Resonator(ring) => Some(*ring),
                _ => None,
            })
            .collect();
        // Each locus's material and carried remainders, taken apart: a locus's steps read and
        // write only its own, so the loci run together (`hnn::realization`), each in its
        // steps' order with its own budgeted carry, at the clock it would advance it to.
        let mut local: BTreeMap<Locus, Carries> = groups
            .keys()
            .map(|locus| (*locus, Carries::new()))
            .collect();
        let mut rest = Carries::new();
        for (key, carry) in std::mem::take(&mut next.carries) {
            match local.get_mut(&key.0) {
                Some(map) => {
                    map.insert(key, carry);
                }
                None => {
                    rest.insert(key, carry);
                }
            }
        }
        let mut materials = LocusMaterial::split(&mut next.rings, &mut next.contacts, &groups);
        let mut regions: Vec<_> = groups
            .iter()
            .zip(local)
            .map(|((locus, steps), (_, carries))| (*locus, steps, materials.remove(locus), carries))
            .collect();
        drop(materials);
        // Pass 1: each locus's linear step and factor families prepared at their unit steps, the
        // loci together.
        let prepared: Vec<Result<Prepared, (usize, HnnError)>> = regions
            .par_iter_mut()
            .map(|(locus, steps, material, carries)| {
                self.prepare_at(*locus, steps, material.as_mut(), carries)
            })
            .collect();
        let mut first: Option<(usize, HnnError)> = None;
        let mut ready = Vec::with_capacity(prepared.len());
        for region in prepared {
            match region {
                Ok(region) => ready.push(region),
                Err(refusal) => {
                    if first.as_ref().is_none_or(|(index, _)| refusal.0 < *index) {
                        first = Some(refusal);
                    }
                }
            }
        }
        if let Some((_, refusal)) = first {
            return Err(refusal);
        }
        // The certificate reads every prepared step at once.
        let (certified, joint, pumped) = {
            let linear: Vec<(Locus, LinearLocus, &PreparedStep)> = regions
                .iter()
                .zip(&ready)
                .filter_map(|((locus, ..), region)| {
                    region
                        .linear
                        .as_ref()
                        .and_then(|(_, locus_kind, prepared)| {
                            prepared
                                .as_ref()
                                .map(|prepared| (*locus, *locus_kind, prepared))
                        })
                })
                .collect();
            let factors: Vec<(Locus, &FactorPrepared)> = regions
                .iter()
                .zip(&ready)
                .flat_map(|((locus, ..), region)| {
                    region
                        .factors
                        .iter()
                        .map(move |prepared| (*locus, prepared))
                })
                .collect();
            self.certify_steps(deposit.reach(), &linear, &factors)?
        };
        let mut certified = certified;
        // The standing's fold (module header, "Within a lobe", "At a node"): each standing
        // family's step held inside its lobes, and the crossings its lock chart offered proposed
        // to the lock.
        let (lobe, lock) = {
            let stepping: Vec<(usize, &[Rat], Rat)> = regions
                .iter()
                .zip(&ready)
                .filter_map(|((locus, steps, ..), region)| {
                    let Locus::Standing(g) = *locus else {
                        return None;
                    };
                    let gradient = steps.iter().find_map(|(_, step)| match step {
                        LocusStep::Factor(FactorStep {
                            gradient: FactorGradient::Standing { gradient, .. },
                            ..
                        }) => Some(gradient.as_slice()),
                        _ => None,
                    })?;
                    let scale = region
                        .factors
                        .iter()
                        .find(|prepared| prepared.family == Family::Standing)?
                        .scale
                        .clone();
                    Some((g, gradient, scale))
                })
                .collect();
            self.lobe(&stepping, &mut certified)?
        };
        // Pass 2: every locus's steps in the deposit's order, each family at its certified step,
        // the loci together.
        let done: Vec<LocusDeposit> = regions
            .into_par_iter()
            .zip(ready)
            .map(|((locus, steps, mut material, mut carries), region)| {
                self.deposit_at(
                    locus,
                    steps,
                    material.as_mut(),
                    &mut carries,
                    region,
                    &certified,
                )
                .map(|at| (locus, carries, at))
            })
            .collect();
        // The refusal is the first in the deposit's order: the one the steps taken in that order
        // meet first.
        let (mut deposited, mut refusals) = (Vec::with_capacity(done.len()), Vec::new());
        for region in done {
            match region {
                Ok(region) => deposited.push(region),
                Err(refusal) => refusals.push(refusal),
            }
        }
        if let Some((_, refusal)) = refusals.into_iter().min_by_key(|(index, _)| *index) {
            return Err(refusal);
        }
        let mut strokes: BTreeMap<Locus, BudgetedCarry> = BTreeMap::new();
        let mut charts: Vec<(Locus, ChartReading)> = Vec::new();
        next.carries = rest;
        for (locus, carries, (at, read)) in deposited {
            next.carries.extend(carries);
            strokes.insert(locus, at);
            charts.extend(read.into_iter().map(|reading| (locus, reading)));
        }
        next.carries.retain(|_, carry| !carry.0.is_empty());
        // A deposit that would make a boost's solve singular is refused, with its direction.
        for (contact, material) in next.contacts.iter().enumerate() {
            if let Some(boost) = &material.boost {
                boost.certify(contact, material)?;
            }
        }
        // The resonator's four gain families may share one comparison. Certify their complete
        // successor once, at every pump phase, before this cloned constitution can be published.
        for ring in resonators_to_certify {
            let material = &next.rings[ring];
            let resonator = material.resonator.as_ref().ok_or(HnnError::Lattice {
                locus: Locus::Resonator(ring),
            })?;
            let hop = material.resonator_step.as_ref().ok_or(HnnError::Lattice {
                locus: Locus::Resonator(ring),
            })?;
            resonator.certify(ring, hop)?;
        }
        next.commit += 1;
        // The clocks of the loci whose update was nonzero advance; the released residuals and the
        // stepped entries are read off the budgeted carries.
        let (mut released, mut stepped) = (Vec::new(), 0u64);
        for (locus, at) in &strokes {
            if at.moved() {
                next.clocks.insert(*locus, at.clock());
            }
            stepped += at.stepped();
            released.extend(
                at.released()
                    .into_iter()
                    .map(|(carrier, entry, residual)| (*locus, carrier, entry, residual)),
            );
        }
        let released_bits = released.iter().map(|(.., residual)| bits(residual)).sum();
        let vanished: Vec<(Locus, Family)> = certified
            .iter()
            .filter(|(_, reading)| reading.step.step.is_positive())
            .filter(|((locus, family), _)| {
                strokes.get(locus).is_none_or(|at| !at.family_moved(*family))
            })
            .map(|(key, _)| *key)
            .collect();
        let backtracks: Vec<GainBacktrack> = strokes
            .values()
            .flat_map(|at| at.backtracks().iter().cloned())
            .collect();
        // The committed energy bound at the commit: the storage growth certified by inertia, or the
        // deposit refused (module header, "The committed energy bound, enforced at the commit").
        let storage_growth =
            certify_storage_growth(&self.storage_forms()?, &next.storage_forms()?)?
                .ok_or(HnnError::UncertifiedStorage)?;
        next.storage_product = &self.storage_product * (Rat::one() + &storage_growth);
        let bits = next.exact_bits();
        if bits > self.budget {
            let predecessor = self.bits_by_locus();
            let mut grown: Vec<(Locus, i128)> = next
                .bits_by_locus()
                .into_iter()
                .map(|(locus, after)| {
                    let before = predecessor
                        .iter()
                        .find(|(l, _)| *l == locus)
                        .map_or(0, |(_, bits)| *bits);
                    (locus, i128::from(after) - i128::from(before))
                })
                .collect();
            grown.sort_by(|a, b| b.1.cmp(&a.1));
            return Err(HnnError::ConstitutionBudget {
                bits,
                budget: self.budget,
                commit: self.commit,
                loci: grown.into_iter().take(4).map(|(locus, _)| locus).collect(),
            });
        }
        let reading = DepositReading {
            storage_growth,
            storage_product: next.storage_product.clone(),
            steps: certified
                .into_iter()
                .map(|((locus, _), reading)| (locus, reading))
                .collect(),
            joint,
            amplitude: next.amplitude()?,
            commit: next.commit,
            bits,
            budget: self.budget,
            loci: deposit.loci(),
            released,
            released_bits,
            stepped,
            vanished,
            charts,
            landmarks: deposit.landmarks().len() as u64,
            backtracks,
            lobe,
            lock,
            pumped,
        };
        Ok((next, reading))
    }

    /// [definition; agent-inferred, September 29] **The lobe law at a deposit** (module header,
    /// "Within a lobe", "At a node: the lock's half-turn"). Each stepping standing family's move is
    /// read on its carried lattice successor, exactly as pass 2 carries it; the contrasts `Δ = M q`
    /// of every ring are read before and after. When the lock chart's certified steps keep every
    /// slice in its lobe (no class changes, no slice carried onto its node from off it), nothing
    /// changes. Otherwise the crossings are offered to the lock: the standings the chart's steps
    /// reach are the lock's proposal, and the families whose moves reach a crossed slice are halved
    /// together (the joint ray scaled), until no slice leaves its lobe; a family whose step falls
    /// below half its fine lattice's unit on its widest entry moves nothing there and is dropped
    /// (its statistic moved in pass 1, its entries do not). The halving ends: a dropped family moves
    /// no coordinate, so a crossing that remains is read by a family still stepping.
    fn lobe(
        &self,
        stepping: &[(usize, &[Rat], Rat)],
        certified: &mut BTreeMap<(Locus, Family), StepReading>,
    ) -> Result<(Option<LobeReading>, Option<LockProposal>), HnnError> {
        struct Trial {
            standing: Vec<Rat>,
            carry: Carry,
            clock: u64,
            released: Vec<(Carrier, usize, Rat)>,
        }
        // The families that step, with their gradient, metric, chart step and fine half-unit.
        let mut families: Vec<(usize, &[Rat], Rat, CertifiedStep, Rat)> = Vec::new();
        for (g, gradient, scale) in stepping {
            let Some(reading) = certified.get(&(Locus::Standing(*g), Family::Standing)) else {
                continue;
            };
            let locus = Locus::Standing(*g);
            let precision = gamma_length(self.clock(locus) + 1);
            let exponent = self.lattice(locus)?.exponent() + precision + 1;
            let half_fine = Rat::new(BigInt::one(), BigInt::one() << exponent as usize);
            families.push((*g, gradient, scale.clone(), reading.step.clone(), half_fine));
        }
        if families.is_empty() {
            return Ok((None, None));
        }
        let trial = |g: usize, gradient: &[Rat], scale: &Rat, step: &Rat| -> Result<Trial, HnnError> {
            let locus = Locus::Standing(g);
            let mut carry = self
                .carries
                .get(&(locus, Carrier::Standing))
                .cloned()
                .unwrap_or_default();
            let mut at = BudgetedCarry::new(self.lattice(locus)?, self.clock(locus) + 1);
            let mut standing = self.rings[g].standing.clone();
            let rate = step / scale;
            for (i, (x, dx)) in standing.iter_mut().zip(gradient).enumerate() {
                carry.deposit(&mut at, Carrier::Standing, i, x, &rate_times(&rate, dx));
            }
            Ok(Trial {
                standing,
                carry,
                clock: at.clock(),
                released: at.released(),
            })
        };
        let before_standings: Vec<&[Rat]> = self
            .rings
            .iter()
            .map(|material| material.standing.as_slice())
            .collect();
        let before = self.lock.contrast(&before_standings);
        // The successor's contrasts at the families' steps (`None`: the family does not step).
        let successor = |steps: &[Option<Rat>]| -> Result<(Vec<Option<Trial>>, Vec<Vec<Rat>>), HnnError> {
            let trials: Vec<Option<Trial>> = families
                .iter()
                .zip(steps)
                .map(|((g, gradient, scale, ..), step)| {
                    step.as_ref()
                        .map(|step| trial(*g, gradient, scale, step))
                        .transpose()
                })
                .collect::<Result<_, HnnError>>()?;
            let mut standings = before_standings.clone();
            for ((g, ..), moved) in families.iter().zip(&trials) {
                if let Some(moved) = moved {
                    standings[*g] = moved.standing.as_slice();
                }
            }
            let after = self.lock.contrast(&standings);
            Ok((trials, after))
        };
        let chart_steps: Vec<Option<Rat>> = families
            .iter()
            .map(|(.., step, _)| Some(step.step.clone()))
            .collect();
        let (proposed, proposed_after) = successor(&chart_steps)?;
        let offered = crossings(&before, &proposed_after);
        if offered.is_empty() {
            return Ok((None, None));
        }
        let mut steps = chart_steps;
        let mut halvings = vec![0i64; families.len()];
        let held_after = loop {
            let (trials, after) = successor(&steps)?;
            let crossed = crossings(&before, &after);
            if crossed.is_empty() {
                break after;
            }
            let mut halved = false;
            for (index, (g, gradient, scale, _, half_fine)) in families.iter().enumerate() {
                let (Some(step), Some(moved)) = (&steps[index], &trials[index]) else {
                    continue;
                };
                let coordinates: BTreeSet<usize> = moved
                    .standing
                    .iter()
                    .zip(before_standings[*g])
                    .enumerate()
                    .filter(|(_, (x, y))| x != y)
                    .map(|(j, _)| j)
                    .collect();
                if !crossed
                    .iter()
                    .any(|&(r, rho)| self.lock.reads(r, rho, *g, &coordinates))
                {
                    continue;
                }
                let next = step * rat(1, 2);
                halvings[index] += 1;
                halved = true;
                steps[index] = (&next * widest(gradient) / scale >= *half_fine).then_some(next);
            }
            if !halved {
                return Err(HnnError::Carrier {
                    what: "a standing's crossing that no stepping family's move reads",
                });
            }
        };
        // The lock's proposal: the chart's standings where the lobe held a family, and the classes
        // they turn against the held successor.
        let proposal_crossings: Vec<(usize, usize)> = held_after
            .iter()
            .zip(&proposed_after)
            .enumerate()
            .flat_map(|(r, (held, proposed))| {
                held.iter()
                    .zip(proposed)
                    .enumerate()
                    .filter(|(_, (x, y))| x.is_negative() != y.is_negative())
                    .map(move |(rho, _)| (r, rho))
            })
            .collect();
        let mut standings = Vec::new();
        let mut lobe_held = Vec::new();
        for (index, ((g, ..), proposed)) in families.iter().zip(proposed).enumerate() {
            if halvings[index] == 0 {
                continue;
            }
            let key = (Locus::Standing(*g), Family::Standing);
            match &steps[index] {
                Some(_) => {
                    let reading = certified.get_mut(&key).expect("a stepping standing family");
                    for _ in 0..halvings[index] {
                        reading.step = reading.step.halved();
                    }
                    lobe_held.push((*g, Some(reading.step.exponent)));
                }
                None => {
                    certified.remove(&key);
                    lobe_held.push((*g, None));
                }
            }
            if let Some(proposed) = proposed {
                standings.push(ProposedStanding {
                    ring: *g,
                    standing: proposed.standing,
                    carry: proposed.carry,
                    clock: proposed.clock,
                    released: proposed.released,
                });
            }
        }
        let lock =(!proposal_crossings.is_empty()).then(|| LockProposal {
            commit: self.commit + 1,
            standings,
            crossings: proposal_crossings,
        });
        Ok((
            Some(LobeReading {
                offered,
                held: lobe_held,
            }),
            lock,
        ))
    }

    /// [definition; agent-inferred, September 29] **The lock's half-turn** (module header, "At a
    /// node: the lock's half-turn"): the successor with the lock's proposal taken, its standings
    /// moved to the chart's certified step so every proposed slice's sheet turns by `e^{iπ}`, as a
    /// commit of its own. The caller takes it only where the lock's exact comparison of the
    /// comparison's code at both sheets says the turned sheets are strictly better
    /// ([`crate::holon::deposition::strictly_better`]); the constitution certifies only that the
    /// proposal was made at this commit, on retained standings, within the budget. Refused with
    /// [`HnnError::StaleDeposit`] at another commit, [`HnnError::ReleasedLocus`] on a released
    /// standing and [`HnnError::ConstitutionBudget`] past `B_Θ`.
    pub fn locked(&self, proposal: &LockProposal) -> Result<(Self, LockReading), HnnError> {
        if proposal.commit != self.commit {
            return Err(HnnError::StaleDeposit {
                staged: proposal.commit,
                published: self.commit,
            });
        }
        let mut next = self.clone();
        let mut released = Vec::new();
        for proposed in &proposal.standings {
            let locus = Locus::Standing(proposed.ring);
            if self.released.contains(&locus) {
                return Err(HnnError::ReleasedLocus { locus });
            }
            next.rings[proposed.ring].standing = proposed.standing.clone();
            if proposed.carry.0.is_empty() {
                next.carries.remove(&(locus, Carrier::Standing));
            } else {
                next.carries
                    .insert((locus, Carrier::Standing), proposed.carry.clone());
            }
            next.clocks.insert(locus, proposed.clock);
            released.extend(
                proposed
                    .released
                    .iter()
                    .map(|(carrier, entry, residual)| (locus, *carrier, *entry, residual.clone())),
            );
        }
        next.commit += 1;
        let bits = next.exact_bits();
        if bits > self.budget {
            return Err(HnnError::ConstitutionBudget {
                bits,
                budget: self.budget,
                commit: self.commit,
                loci: proposal
                    .standings
                    .iter()
                    .map(|proposed| Locus::Standing(proposed.ring))
                    .collect(),
            });
        }
        Ok((
            next,
            LockReading {
                crossings: proposal.crossings.clone(),
                commit: self.commit + 1,
                bits,
                released,
            },
        ))
    }

    /// **The field's fixed nodes** (module header, "The founding"): the slices `(r, ρ)` of the lock
    /// chart's singular components, founded on their node, where a combination of the contrasts is
    /// fixed by the chart's kernel whatever the standings.
    #[cfg(test)]
    pub(crate) fn fixed_nodes(&self) -> &[(usize, usize)] {
        &self.fixed
    }

    /// **The standing contrasts** `Δ_r = (M q)_r` of every ring, read through the lock chart.
    #[cfg(test)]
    pub(crate) fn standing_contrasts(&self) -> Vec<Vec<Rat>> {
        let standings: Vec<&[Rat]> = self
            .rings
            .iter()
            .map(|material| material.standing.as_slice())
            .collect();
        self.lock.contrast(&standings)
    }

    /// **One locus's steps prepared** (pass 1 of [`Constitution::deposited`]): the locus's budgeted
    /// carry opened at the clock the deposit would advance it to; its normal law's Gram carried, chart
    /// refined and unit step formed ([`NormalLaw::prepare`]); and each factor family's statistic
    /// carried and unit step read ([`factor_prepared`]). A locus with neither opens nothing here.
    fn prepare_at(
        &self,
        locus: Locus,
        steps: &[(usize, LocusStep<'_>)],
        mut material: Option<&mut LocusMaterial<'_>>,
        carries: &mut Carries,
    ) -> Result<Prepared, (usize, HnnError)> {
        let mut prepared = Prepared {
            stroke: None,
            linear: None,
            factors: Vec::new(),
        };
        for (index, step) in steps {
            let refused = |refusal: HnnError| (*index, refusal);
            match step {
                LocusStep::Linear(step) => {
                    if self.released.contains(&locus) {
                        return Err(refused(HnnError::ReleasedLocus { locus }));
                    }
                    let law = material
                        .as_deref_mut()
                        .and_then(|material| material.law(step.locus))
                        .ok_or(HnnError::MissingSourcePort {
                            ring: match step.locus {
                                LinearLocus::SourcePort(g)
                                | LinearLocus::Contrast(g)
                                | LinearLocus::Receiving(g) => g,
                            },
                        })
                        .map_err(refused)?;
                    let at = self.stroke(locus, &mut prepared.stroke).map_err(refused)?;
                    let rule = self.chart_rule(locus).map_err(refused)?;
                    // The receiving map's step in its class Fisher metric (the contact loop record
                    // §19): the normal law's own step (its `1/n` feature metric unchanged) with its
                    // covectors' magnitudes taken through the inverse of the readings' mean class
                    // Fisher, and certified in the readings' own Fisher form, at most the unit step.
                    let metric = match step.locus {
                        LinearLocus::Receiving(_) => receiving_class_metric(&step.samples),
                        _ => None,
                    };
                    let scaled: Vec<Sample>;
                    let samples = match &metric {
                        Some(scale) => {
                            scaled = step
                                .samples
                                .iter()
                                .map(|sample| Sample {
                                    weight: sample.weight.clone(),
                                    feature: sample.feature.clone(),
                                    covector: sample
                                        .covector
                                        .iter()
                                        .enumerate()
                                        .map(|(i, c)| if i % 2 == 0 { c * scale } else { c.clone() })
                                        .collect(),
                                })
                                .collect();
                            &scaled[..]
                        }
                        None => &step.samples[..],
                    };
                    let mut step_prepared = law.prepare(samples, &rule, at).map_err(refused)?;
                    if let (Some(_), Some(prepared_step)) = (&metric, step_prepared.as_mut()) {
                        if let Some((moves, oscillation)) =
                            receiving_fisher_face(&step.samples, &prepared_step.unit.to_rows())
                        {
                            prepared_step.moves = moves;
                            // At most the unit step: `η · max(osc, 1) ≤ 1`.
                            prepared_step.covector = oscillation.max(Rat::one());
                        }
                    }
                    prepared.linear = Some((*index, step.locus, step_prepared));
                }
                LocusStep::Factor(step) => {
                    if self.released.contains(&locus) {
                        return Err(refused(HnnError::ReleasedLocus { locus }));
                    }
                    let at = self.stroke(locus, &mut prepared.stroke).map_err(refused)?;
                    let material = material
                        .as_deref_mut()
                        .ok_or(HnnError::Lattice { locus })
                        .map_err(refused)?;
                    let factor =
                        factor_prepared(material, carries, step, at, &self.hop).map_err(refused)?;
                    prepared.factors.push(FactorPrepared {
                        index: *index,
                        ..factor
                    });
                }
                LocusStep::Landmark(_) | LocusStep::Receiving(_) => {}
            }
        }
        Ok(prepared)
    }

    /// The locus's budgeted carry for this deposit, opened at the clock the deposit would advance it
    /// to when no step has opened it yet.
    fn stroke<'s>(
        &self,
        locus: Locus,
        stroke: &'s mut Option<BudgetedCarry>,
    ) -> Result<&'s mut BudgetedCarry, HnnError> {
        if stroke.is_none() {
            *stroke = Some(BudgetedCarry::new(
                self.lattice(locus)?,
                self.clock(locus) + 1,
            ));
        }
        Ok(stroke.as_mut().expect("opened above"))
    }

    /// **One locus's steps of a deposit** (pass 2 of [`Constitution::deposited`]), in the deposit's
    /// order, on the locus's material and carried remainders alone, with the locus's budgeted carry
    /// (opened by its preparation, or here at the clock the deposit would advance it to): its linear
    /// step taken at its certified step with its normal law's chart reading, and each factor family
    /// moved by its certified step along its unit step, `Δx = η G_x / h_x′` (zero where its alignment
    /// certified none: the statistic moved in pass 1, the family does not). A refusal returns with
    /// the place of the step that met it in the deposit's order.
    fn deposit_at(
        &self,
        locus: Locus,
        steps: &[(usize, LocusStep<'_>)],
        mut material: Option<&mut LocusMaterial<'_>>,
        carries: &mut Carries,
        prepared: Prepared,
        certified: &BTreeMap<(Locus, Family), StepReading>,
    ) -> Result<(BudgetedCarry, Vec<ChartReading>), (usize, HnnError)> {
        let Prepared {
            mut stroke,
            mut linear,
            factors,
        } = prepared;
        let mut charts = Vec::new();
        let step_of = |family: Family| {
            certified
                .get(&(locus, family))
                .map_or_else(Rat::zero, |reading| reading.step.step.clone())
        };
        for (index, step) in steps {
            let refused = |refusal: HnnError| (*index, refusal);
            if self.released.contains(&locus) {
                return Err(refused(HnnError::ReleasedLocus { locus }));
            }
            match step {
                LocusStep::Linear(step) => {
                    let law = material
                        .as_deref_mut()
                        .and_then(|material| material.law(step.locus))
                        .ok_or(HnnError::MissingSourcePort {
                            ring: match step.locus {
                                LinearLocus::SourcePort(g)
                                | LinearLocus::Contrast(g)
                                | LinearLocus::Receiving(g) => g,
                            },
                        })
                        .map_err(refused)?;
                    let at = self.stroke(locus, &mut stroke).map_err(refused)?;
                    // The step prepared in pass 1 (none when its window reached nothing), at its
                    // certified step (zero when its alignment was zero: the Gram and chart move,
                    // the map does not).
                    if let Some((_, _, Some(prepared))) = linear.take() {
                        let (next, reading) = prepared
                            .stepped(&step_of(Family::Map), at)
                            .map_err(refused)?;
                        *law = next;
                        charts.push(reading);
                    }
                }
                LocusStep::Factor(step) => {
                    let at = self.stroke(locus, &mut stroke).map_err(refused)?;
                    let material = material
                        .as_deref_mut()
                        .ok_or(HnnError::Lattice { locus })
                        .map_err(refused)?;
                    let prepared = factors
                        .iter()
                        .find(|prepared| prepared.index == *index)
                        .ok_or(HnnError::Lattice { locus })
                        .map_err(refused)?;
                    let rate = step_of(prepared.family) / &prepared.scale;
                    factor_step(material, carries, step, &rate, at).map_err(refused)?;
                }
                LocusStep::Landmark(step) => {
                    // The tree carries no lattice remainder, so the stroke is opened for the locus's
                    // reading and nothing moves its clock.
                    self.stroke(locus, &mut stroke).map_err(refused)?;
                    let tree = material
                        .as_deref_mut()
                        .and_then(LocusMaterial::tree)
                        .ok_or(HnnError::MissingReceivingMap { ring: step.ring })
                        .map_err(refused)?;
                    tree.deposit(&step.address, step.class)
                        .map_err(|refusal| refused(refusal.into()))?;
                }
                LocusStep::Receiving(step) => {
                    // The population carries its likelihoods' bounds, so it moves no lattice clock.
                    self.stroke(locus, &mut stroke).map_err(refused)?;
                    let population = material
                        .as_deref_mut()
                        .and_then(LocusMaterial::population)
                        .ok_or(HnnError::MissingReceivingMap { ring: step.ring })
                        .map_err(refused)?;
                    population
                        .receive(&step.faces())
                        .map_err(crate::hnn::receiving::population_refusal)
                        .map_err(refused)?;
                }
            }
        }
        stroke
            .map(|at| (at, charts))
            .ok_or(HnnError::Lattice { locus })
            .map_err(|refusal| (0, refusal))
    }

    /// **Release loci** (the collapse's only mutator, `hnn::retention`): each released locus's
    /// learned material becomes the zero map and its statistics are dropped; it counts no bits and
    /// no reading reads it.
    pub(crate) fn release(&mut self, loci: &BTreeSet<Locus>) -> Result<(), HnnError> {
        for locus in loci {
            match *locus {
                Locus::Element(g) => {
                    let material = &mut self.rings[g];
                    let n = material.standing.len();
                    material.passive = ExactRatMatrix::zero(n, material.passive.columns())?;
                    material.contrast = NormalLaw::with_prior(ExactRatMatrix::zero(n, n)?);
                    material.slices = vec![(vec![Rat::zero(); n], vec![Rat::zero(); n]); n];
                }
                Locus::Standing(g) => {
                    let material = &mut self.rings[g];
                    material.standing = vec![Rat::zero(); material.standing.len()];
                }
                Locus::Resonator(g) => {
                    let material = &mut self.rings[g];
                    material.resonator = None;
                    material.resonator_scales = std::array::from_fn(|_| Rat::zero());
                    material.resonator_step = None;
                }
                Locus::SourcePort(g) => {
                    let material = &mut self.rings[g];
                    if let Some(source) = &material.source {
                        let (m, n) = (source.map.rows(), source.map.columns());
                        material.source = Some(NormalLaw::with_prior(ExactRatMatrix::zero(m, n)?));
                    }
                    for (_, pair) in &mut material.pairs {
                        let zero = |family: &[Vec<Rat>]| -> Vec<Vec<Rat>> {
                            family.iter().map(|x| vec![Rat::zero(); x.len()]).collect()
                        };
                        *pair = PairPort::new(
                            zero(pair.outputs()),
                            zero(pair.current_reads()),
                            zero(pair.earlier_reads()),
                        )?;
                    }
                }
                Locus::Channel(a) => {
                    let material = &mut self.contacts[a];
                    let k = material.storage.rows();
                    material.storage = ExactRatMatrix::zero(k, material.storage.columns())?;
                    material.stiffness = ExactRatMatrix::zero(k, material.stiffness.columns())?;
                    material.dissipation = ExactRatMatrix::zero(k, material.dissipation.columns())?;
                }
                // The receiving map is never released; junctions and conductances are declared.
                Locus::ReceivingMap(_) | Locus::Junction(_) | Locus::Conductance(_) => {}
            }
            self.released.insert(*locus);
        }
        // A released locus leaves whole, with its carried remainders and its clock (Lean
        // `carriedRel`); the retained loci keep theirs.
        let kept = |locus: &Locus| !loci.contains(locus) || matches!(locus, Locus::ReceivingMap(_));
        self.carries.retain(|(locus, _), _| kept(locus));
        self.clocks.retain(|locus, _| kept(locus));
        Ok(())
    }
}

/// [definition; agent-inferred, October 2; the
/// [contact loop record](../../../../research/records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)
/// §18] **The receiving map's step in its own Fisher form.** A receiving read's code in bits is
/// `f(v) = −v_t + log₂ Σ_c 2^(v_c)`, whose Hessian in the exponents is `ln 2 (diag p − p pᵀ)`, so
/// `δᵀ ∇²f δ = ln 2 · Var_p(δ)`. A logit change `Δ` multiplies every class's mass by at most
/// `2^(osc Δ)`, `osc Δ = max Δ − min Δ`, so along the whole ray `[0, η]` with `η · osc ≤ 1` the
/// second derivative is at most `2 ln 2 · Var_p(Δ)` (the bound `f(v + Δ) ≤ f + gᵀΔ +
/// (e^(osc)/2) Var_p(Δ)` in nats, carried to bits). The covector's masses are the odometer chart
/// `p̃` (`p̃ − q`, the HNN adjoint's), and `p_c/p̃_c ≤ 17/16` (`2^x/(1 + x)` lies in `[0.94, 1]` on
/// `[0, 1)`), so `Var_p(Δ) ≤ E_p[(Δ − E_p̃ Δ)²] ≤ (17/16) Var_p̃(Δ)`. The phase part's curvature is
/// at most `¼` (module header, "The certified step"). With `ln 2 ≤ 7/10`, each read's curvature
/// along the unit step `Δ_t = D f_t` is at most `(119/80) Var_p̃(Δ_t^Re) + ¼ |Δ_t^Im|²`. The
/// certificate's `C = s κ² b` with `s = ½`, `κ² = 1` then takes `b = 2 Σ_t (…)`, and its covector
/// scale is the largest magnitude oscillation `max_t osc(Δ_t^Re)` (`ηc ≤ 1` is `η · osc ≤ 1`).
/// `None`, leaving the worst-case readings, when a covector is not a face's `q − p̃`.
/// [definition; agent-inferred, October 2; the contact loop record §19] **The receiving readings'
/// class metric**: the inverse of their mean class Fisher eigenvalue on the zero-sum classes,
/// `λ̄ = mean_t (1 − Σ_c p̃_(t,c)²)/(|A| − 1)` (the trace of `diag p̃ − p̃ p̃ᵀ` over its rank), held at
/// the power of two at or below `1/λ̄`: about `|A|` at a uniform reading, so the step's magnitude
/// part is the normal law's own scaled into the receiver's own curvature. `None` when a covector is
/// not a face's `q − p̃`, or the readings carry no curvature.
pub(crate) fn receiving_class_metric(samples: &[Sample]) -> Option<Rat> {
    let (mut trace, mut count, mut classes) = (Rat::zero(), 0u64, 0usize);
    for sample in samples.iter().filter(|s| !s.weight.is_zero()) {
        let mut masses: Vec<Rat> = sample.covector.iter().step_by(2).map(|c| -c).collect();
        if let Some(target) = (0..masses.len()).find(|&c| masses[c].is_negative()) {
            masses[target] += Rat::one();
        }
        if masses.iter().any(Signed::is_negative) || masses.iter().sum::<Rat>() != Rat::one() {
            return None;
        }
        classes = masses.len();
        trace += Rat::one() - masses.iter().map(|p| p * p).sum::<Rat>();
        count += 1;
    }
    if count == 0 || classes < 2 || !trace.is_positive() {
        return None;
    }
    let mean = trace / Rat::from_integer(BigInt::from(count * (classes as u64 - 1)));
    let exponent = crate::ratio::disk::floor_log2(&mean.recip());
    Some(if exponent >= 0 {
        Rat::from_integer(BigInt::from(1) << exponent as usize)
    } else {
        Rat::new(BigInt::from(1), BigInt::from(1) << (-exponent) as usize)
    })
}

fn receiving_fisher_face(samples: &[Sample], unit: &[Vec<Rat>]) -> Option<(Rat, Rat)> {
    let (mut curvature, mut oscillation) = (Rat::zero(), Rat::zero());
    for sample in samples.iter().filter(|s| !s.weight.is_zero()) {
        let delta: Vec<Rat> = unit
            .iter()
            .map(|row| row.iter().zip(&sample.feature).map(|(d, f)| d * f).sum())
            .collect();
        let real: Vec<&Rat> = delta.iter().step_by(2).collect();
        let imaginary: Vec<&Rat> = delta.iter().skip(1).step_by(2).collect();
        // The covector is the descent `q − p̃`; the masses are `p̃ = q − covector`.
        let mut masses: Vec<Rat> = sample.covector.iter().step_by(2).map(|c| -c).collect();
        if let Some(target) = (0..masses.len()).find(|&c| masses[c].is_negative()) {
            masses[target] += Rat::one();
        }
        if masses.iter().any(Signed::is_negative) || masses.iter().sum::<Rat>() != Rat::one() {
            return None;
        }
        let mean: Rat = masses.iter().zip(&real).map(|(p, d)| p * *d).sum();
        let second: Rat = masses.iter().zip(&real).map(|(p, d)| p * *d * *d).sum();
        let variance = second - &mean * &mean;
        let phase: Rat = imaginary.iter().map(|d| *d * *d).sum();
        curvature += sample.weight.abs()
            * (Rat::new(BigInt::from(119), BigInt::from(80)) * variance
                + phase / Rat::from_integer(BigInt::from(4)));
        if let (Some(high), Some(low)) = (real.iter().max(), real.iter().min()) {
            oscillation = oscillation.max(*high - *low);
        }
    }
    Some((Rat::from_integer(BigInt::from(2)) * curvature, oscillation))
}

/// One locus's deposited carried remainders, budgeted carry and chart readings, or the refusal its
/// steps met with the place of the refusing step in the deposit's order.
type LocusDeposit = Result<(Locus, Carries, (BudgetedCarry, Vec<ChartReading>)), (usize, HnnError)>;

/// A deposit's certified steps by family, the joint certificate they hold together (`None` when
/// no family stepped), and the pumped medium's reach they read (`None` when every resonator is
/// certified passive).
type CertifiedSteps = (
    BTreeMap<(Locus, Family), StepReading>,
    Option<JointReading>,
    Option<PumpedReading>,
);

/// One locus's pass-1 preparation: its budgeted carry (opened by its first step), its linear step's
/// place, kind and prepared unit step (none when its window reached nothing), and its factor
/// families' prepared unit steps.
struct Prepared {
    stroke: Option<BudgetedCarry>,
    linear: Option<(usize, LinearLocus, Option<PreparedStep>)>,
    factors: Vec<FactorPrepared>,
}

/// [definition; agent-inferred] **A factor family's step prepared at its unit step** (module
/// header, "The factor families' certified step"): its place in the deposit's order, its family, its
/// carried statistic `h_x′` (the metric of the unit step `D = G_x / h_x′`), the unit step's alignment
/// `a = |G_x|² / h_x′`, the covector scale `c`, the feature energy `e`, and the norms its output's
/// moves read.
pub(crate) struct FactorPrepared {
    index: usize,
    family: Family,
    scale: Rat,
    alignment: Rat,
    covector: Rat,
    energy: Rat,
    moves: Moves,
}

/// **The norms a factor family's output moves read** (module header's table), each Schur pair
/// `(‖X‖₁, ‖X‖_∞)` exact.
enum Moves {
    /// A square carrier `w x xᵀ` read at its feature: `weight = 4w²`, the unit step's and the
    /// factor's Schur norms; `b(η) = weight S(D) S(x + ηD) e`.
    Square {
        weight: Rat,
        unit: (Rat, Rat),
        factor: (Rat, Rat),
    },
    /// The slices, their rows the slices `ρ`: the unit step's `dU`, `dV` and the factors' `U`, `V`;
    /// `b(η) = 8 (S(dU) S(V + η dV) + S(U + η dU) S(dV)) e`.
    Slices {
        du: (Rat, Rat),
        dv: (Rat, Rat),
        u: (Rat, Rat),
        v: (Rat, Rat),
    },
    /// The standing: `|D|_∞` and its lock chart's reach (each ring with its element window's
    /// energy); its moves read the reached rings' slices (the certificate).
    Standing { unit: Rat, reach: Vec<(usize, Rat)> },
    /// A resonator gain: `|D|` and `|g_i| > 0`; `b(η) = |D|² e ((|g_i| + η|D|) / |g_i|)²`.
    Resonator { unit: Rat, gain: Rat },
    /// A pair port, per rank `(|De_ρ|², |Da_ρ|², |Db_ρ|², |e_ρ|², |a_ρ|², |b_ρ|²)`;
    /// `b(η) = 3 k e Σ_ρ (|De_ρ|² A_ρ B_ρ + E_ρ |Da_ρ|² B_ρ + E_ρ A_ρ |Db_ρ|²)`,
    /// `X_ρ = 2|x_ρ|² + 2η²|Dx_ρ|²`.
    Pair { ranks: Vec<[Rat; 6]> },
}

impl Moves {
    /// `b(η)` at the family's own ray (the standing's reads its chart's rings, in the certificate).
    fn own(&self, energy: &Rat, step: &Rat) -> Result<Rat, HnnError> {
        let integer = |n: i64| Rat::from_integer(BigInt::from(n));
        Ok(match self {
            Moves::Square {
                weight,
                unit,
                factor,
            } => weight * &unit.0 * &unit.1 * ray_product(factor, unit, step) * energy,
            Moves::Slices { du, dv, u, v } => {
                integer(8)
                    * (&du.0 * &du.1 * ray_product(v, dv, step)
                        + ray_product(u, du, step) * &dv.0 * &dv.1)
                    * energy
            }
            Moves::Resonator { unit, gain } => {
                if !gain.is_positive() {
                    return Err(HnnError::Carrier {
                        what: "a resonator gain's certified step at a gain that is not positive",
                    });
                }
                let reached = (gain + step * unit) / gain;
                unit * unit * energy * &reached * &reached
            }
            Moves::Pair { ranks } => {
                let square = step * step;
                let bound = |x: &Rat, dx: &Rat| integer(2) * x + integer(2) * &square * dx;
                let sum: Rat = ranks
                    .iter()
                    .map(|[de, da, db, e, a, b]| {
                        let (big_e, big_a, big_b) = (bound(e, de), bound(a, da), bound(b, db));
                        de * &big_a * &big_b + &big_e * da * &big_b + &big_e * &big_a * db
                    })
                    .sum();
                integer(3) * integer(ranks.len() as i64) * energy * sum
            }
            Moves::Standing { .. } => {
                return Err(HnnError::Carrier {
                    what: "the standing's moves read its lock chart's rings, in the certificate",
                });
            }
        })
    }
}

/// [definition; agent-inferred] **The certificate's faces**: every reading a certified step
/// compares is carried at [`FACE`] significant bits, its decrease `a` at its floor and every factor
/// of its curvature `C`, its covector scale `c` and the gains' norms at their ceilings
/// (`holon::deposition::significant`), so `ηC⁺ ≤ a⁻` and `ηc⁺ ≤ 1` imply the exact certificate while
/// its products stay a few hundred bits wide, whatever the exact readings' own (thousands of bits
/// from the pullback). The step is exact; only the certificate's comparison reads the faces.
const FACE: u32 = 64;

/// A reading's floor at the certificate's face.
fn floor(x: &Rat) -> Rat {
    significant(x, FACE, false)
}

/// A reading's ceiling at the certificate's face.
fn ceiling(x: &Rat) -> Rat {
    significant(x, FACE, true)
}

/// A Schur pair's ceilings at the certificate's face.
fn ceilings(pair: &(Rat, Rat)) -> (Rat, Rat) {
    (ceiling(&pair.0), ceiling(&pair.1))
}

/// `(‖X‖₁ + η‖D‖₁)(‖X‖_∞ + η‖D‖_∞)`: the Schur bound at the end of a ray `X + tD`, `t ∈ [0, η]`.
fn ray_product(base: &(Rat, Rat), unit: &(Rat, Rat), step: &Rat) -> Rat {
    (&base.0 + step * &unit.0) * (&base.1 + step * &unit.1)
}

/// **The Schur norms `(‖X‖₁, ‖X‖_∞)` of a flat row-major array** of `columns` columns, read in the
/// integral chart (one normalization per norm).
fn schur_flat(entries: &[Rat], columns: usize) -> (Rat, Rat) {
    if entries.is_empty() || columns == 0 {
        return (Rat::zero(), Rat::zero());
    }
    let (values, denominator) = integral(entries);
    let mut column_sums = vec![BigInt::zero(); columns];
    let mut row_widest = BigInt::zero();
    for row in values.chunks(columns) {
        let mut sum = BigInt::zero();
        for (total, value) in column_sums.iter_mut().zip(row) {
            let magnitude = value.abs();
            sum += &magnitude;
            *total += magnitude;
        }
        if sum > row_widest {
            row_widest = sum;
        }
    }
    let column_widest = column_sums.into_iter().max().unwrap_or_default();
    (
        Rat::new(column_widest, denominator.clone()),
        Rat::new(row_widest, denominator),
    )
}

/// `Σ x²` of an array, read in the integral chart.
fn squared(entries: &[Rat]) -> Rat {
    if entries.is_empty() {
        return Rat::zero();
    }
    let (values, denominator) = integral(entries);
    Rat::new(
        values.iter().map(|x| x * x).sum(),
        &denominator * &denominator,
    )
}

/// `max |x|` of an array.
fn widest(entries: &[Rat]) -> Rat {
    entries
        .iter()
        .map(Signed::abs)
        .max()
        .unwrap_or_else(Rat::zero)
}

/// The Schur norms of the slices' two factor matrices `U`, `V`, their rows the slices `ρ`.
fn slice_norms(slices: &[(Vec<Rat>, Vec<Rat>)]) -> ((Rat, Rat), (Rat, Rat)) {
    let width = slices.first().map_or(0, |(u, _)| u.len());
    let u: Vec<Rat> = slices.iter().flat_map(|(u, _)| u.iter().cloned()).collect();
    let v: Vec<Rat> = slices.iter().flat_map(|(_, v)| v.iter().cloned()).collect();
    (schur_flat(&u, width), schur_flat(&v, width))
}

/// **One factor family's statistic carried and its unit step read** (pass 1 of
/// [`Constitution::deposited`]; module header, "The factor families' certified step"): `h_x` carried
/// to `h_x′ = h_x + e`, and the unit step `D = G_x / h_x′` read by its alignment `a = |G_x|²/h_x′`
/// and the norms its output's moves read, on the family's locus's material and carried remainders.
/// The family's entries do not move here ([`factor_step`] moves them at the certified step).
fn factor_prepared(
    material: &mut LocusMaterial<'_>,
    carries: &mut Carries,
    step: &FactorStep,
    at: &mut BudgetedCarry,
    hop: &Rat,
) -> Result<FactorPrepared, HnnError> {
    let locus = step.gradient.locus();
    let energy = &step.energy;
    let integer = |n: i64| Rat::from_integer(BigInt::from(n));
    let (scale, alignment, moves) = match (&step.gradient, material) {
        (
            FactorGradient::Passive { gradient, .. },
            LocusMaterial::Element {
                passive,
                passive_scale,
                ..
            },
        ) => {
            let scale = advance(
                carries,
                at,
                (locus, Carrier::PassiveScale),
                passive_scale,
                energy,
            )?;
            let (column, row) = schur_flat(gradient.entries(), gradient.columns());
            let moves = Moves::Square {
                weight: integer(4),
                unit: ceilings(&(column / &scale, row / &scale)),
                factor: ceilings(&schur_norms(passive)),
            };
            (scale.clone(), squared(gradient.entries()) / &scale, moves)
        }
        (
            FactorGradient::Slices { gradient, .. },
            LocusMaterial::Element {
                slices,
                slice_scale,
                ..
            },
        ) => {
            let scale = advance(
                carries,
                at,
                (locus, Carrier::SliceScale),
                slice_scale,
                energy,
            )?;
            let width = gradient.first().map_or(0, |(du, _)| du.len());
            let du: Vec<Rat> = gradient
                .iter()
                .flat_map(|(du, _)| du.iter().cloned())
                .collect();
            let dv: Vec<Rat> = gradient
                .iter()
                .flat_map(|(_, dv)| dv.iter().cloned())
                .collect();
            let per = |(column, row): (Rat, Rat)| ceilings(&(column / &scale, row / &scale));
            let (u, v) = slice_norms(slices);
            let moves = Moves::Slices {
                du: per(schur_flat(&du, width)),
                dv: per(schur_flat(&dv, width)),
                u: ceilings(&u),
                v: ceilings(&v),
            };
            (scale.clone(), (squared(&du) + squared(&dv)) / &scale, moves)
        }
        (
            FactorGradient::Standing {
                gradient, reach, ..
            },
            LocusMaterial::Standing { scale, .. },
        ) => {
            let scale = advance(carries, at, (locus, Carrier::StandingScale), scale, energy)?;
            let moves = Moves::Standing {
                unit: ceiling(&(widest(gradient) / &scale)),
                reach: reach
                    .iter()
                    .map(|(ring, energy)| (*ring, ceiling(energy)))
                    .collect(),
            };
            (scale.clone(), squared(gradient) / &scale, moves)
        }
        (
            FactorGradient::Resonator {
                ring,
                family,
                gradient,
            },
            LocusMaterial::Resonator {
                ring: material_ring,
                material,
                scales,
                ..
            },
        ) if ring == material_ring => {
            if *family >= 4 {
                return Err(HnnError::Resonator {
                    ring: *ring,
                    what: "a resonator gain family is one of C, K, D, or pump",
                });
            }
            let current = material.as_ref().ok_or(HnnError::Lattice { locus })?;
            let gain = current.gains()[*family].abs();
            let scale = advance(
                carries,
                at,
                (locus, Carrier::ResonatorScale(*family)),
                &mut scales[*family],
                energy,
            )?;
            let moves = Moves::Resonator {
                unit: ceiling(&(gradient.abs() / &scale)),
                gain: floor(&gain),
            };
            (scale.clone(), gradient * gradient / &scale, moves)
        }
        (
            FactorGradient::PairPort {
                offset,
                outputs,
                current,
                earlier,
                ..
            },
            LocusMaterial::SourcePort { pairs, scale, .. },
        ) => {
            let scale = advance(carries, at, (locus, Carrier::PairScale), scale, energy)?;
            let slot = pairs
                .iter()
                .find(|(declared, _)| declared == offset)
                .ok_or(HnnError::Offset { offset: *offset })?;
            let square_scale = &scale * &scale;
            let ranks: Vec<[Rat; 6]> = (0..slot.1.rank())
                .map(|rho| {
                    [
                        squared(&outputs[rho]) / &square_scale,
                        squared(&current[rho]) / &square_scale,
                        squared(&earlier[rho]) / &square_scale,
                        squared(&slot.1.outputs()[rho]),
                        squared(&slot.1.current_reads()[rho]),
                        squared(&slot.1.earlier_reads()[rho]),
                    ]
                    .map(|x| ceiling(&x))
                })
                .collect();
            let total: Rat = [outputs, current, earlier]
                .into_iter()
                .flatten()
                .map(|row| squared(row))
                .sum();
            (scale.clone(), total / &scale, Moves::Pair { ranks })
        }
        (
            FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. },
            LocusMaterial::Channel(material),
        ) => {
            let index = match &step.gradient {
                FactorGradient::Storage { .. } => 0,
                FactorGradient::Stiffness { .. } => 1,
                _ => 2,
            };
            let scale = advance(
                carries,
                at,
                (locus, Carrier::FactorScale(index)),
                &mut material.scales[index],
                energy,
            )?;
            // The transit reads `2C(w − ω)`, `hK(u + ½hω)` and `hDω`: the output's weight `w` enters
            // the moves as `4w²` (16, `4h²`, `4h²`). A boost's signature flips columns only, so the
            // unit step's norms are the gradient's.
            let weight = match index {
                0 => integer(16),
                _ => integer(4) * hop * hop,
            };
            let factor = match index {
                0 => &material.storage,
                1 => &material.stiffness,
                _ => &material.dissipation,
            };
            let (column, row) = schur_flat(gradient.entries(), gradient.columns());
            let moves = Moves::Square {
                weight,
                unit: ceilings(&(column / &scale, row / &scale)),
                factor: ceilings(&schur_norms(factor)),
            };
            (scale.clone(), squared(gradient.entries()) / &scale, moves)
        }
        // A factor step's locus is its gradient's, so its material is this locus's.
        _ => return Err(HnnError::Lattice { locus }),
    };
    Ok(FactorPrepared {
        index: 0,
        family: step.gradient.family(),
        scale,
        alignment: floor(&alignment),
        covector: ceiling(&step.covector),
        energy: ceiling(energy),
        moves,
    })
}

/// Whether a resonator is pumped (its declared pump at a nonzero strength).
fn pumped(resonator: &ResonatorMaterial) -> bool {
    resonator
        .pump()
        .is_some_and(|pump| !pump.strength().is_zero())
}

/// [definition; agent-inferred, September 29] **A resonator certified passive** (module header, "The
/// pumped medium's reach"): unpumped with its stiffness `K ⪰ 0` by exact inertia (its `C, D ⪰ 0` by
/// declaration), so its tick keeps or dissipates its storage `diag(K, C)` (Lean
/// `HNN/Floquet.storage_form_certifies_passive`). Otherwise (a pump, or a signed stiffness) its
/// growth is its Floquet reach.
fn certified_passive(resonator: &ResonatorMaterial) -> Result<bool, HnnError> {
    if pumped(resonator) {
        return Ok(false);
    }
    let (_, stiffness, _) = resonator.forms();
    Ok(inertia(&crate::hnn::contact::symmetric(stiffness)?).negative == 0)
}

/// One step of a deposit at its locus.
#[derive(Clone, Copy)]
enum LocusStep<'d> {
    Linear(&'d LinearStep),
    Factor(&'d FactorStep),
    Landmark(&'d LandmarkStep),
    Receiving(&'d ReceivingStep),
}

/// [definition; agent-inferred] **One locus's material, borrowed apart from the rest** of the
/// successor a deposit builds (the module header's loci): the element's passive factor, contrast
/// port and slices with their statistics (and the ring's width, which the slices' carry indexes
/// by); the standing and its statistic; the source port with the pair ports and their statistic;
/// the receiving map with the receiving parametron's landmark tree; a contact's channel factors. No
/// two loci share a part, so their steps run together.
enum LocusMaterial<'a> {
    Element {
        passive: &'a mut ExactRatMatrix,
        passive_scale: &'a mut Rat,
        contrast: &'a mut NormalLaw,
        slices: &'a mut Vec<(Vec<Rat>, Vec<Rat>)>,
        slice_scale: &'a mut Rat,
        width: usize,
    },
    Standing {
        standing: &'a mut Vec<Rat>,
        scale: &'a mut Rat,
    },
    SourcePort {
        source: &'a mut Option<NormalLaw>,
        pairs: &'a mut Vec<(usize, PairPort)>,
        scale: &'a mut Rat,
    },
    ReceivingMap {
        receiving: &'a mut Option<NormalLaw>,
        tree: &'a mut Option<Landmarks>,
        population: &'a mut Option<PortPopulation>,
    },
    Resonator {
        ring: usize,
        material: &'a mut Option<ResonatorMaterial>,
        scales: &'a mut [Rat; 4],
        step: &'a mut Option<Rat>,
    },
    Channel(&'a mut ContactMaterial),
}

impl<'a> LocusMaterial<'a> {
    /// Each locus the steps name, its material borrowed apart.
    fn split<S>(
        rings: &'a mut [RingMaterial],
        contacts: &'a mut [ContactMaterial],
        named: &BTreeMap<Locus, S>,
    ) -> BTreeMap<Locus, Self> {
        let mut materials = BTreeMap::new();
        for (g, material) in rings.iter_mut().enumerate() {
            let RingMaterial {
                standing,
                standing_scale,
                passive,
                passive_scale,
                contrast,
                slices,
                slice_scale,
                source,
                pairs,
                pair_scale,
                receiving,
                tree,
                population,
                resonator,
                resonator_scales,
                resonator_step,
                transport: _,
            } = material;
            let width = standing.len();
            if named.contains_key(&Locus::Element(g)) {
                materials.insert(
                    Locus::Element(g),
                    LocusMaterial::Element {
                        passive,
                        passive_scale,
                        contrast,
                        slices,
                        slice_scale,
                        width,
                    },
                );
            }
            if named.contains_key(&Locus::Standing(g)) {
                materials.insert(
                    Locus::Standing(g),
                    LocusMaterial::Standing {
                        standing,
                        scale: standing_scale,
                    },
                );
            }
            if named.contains_key(&Locus::SourcePort(g)) {
                materials.insert(
                    Locus::SourcePort(g),
                    LocusMaterial::SourcePort {
                        source,
                        pairs,
                        scale: pair_scale,
                    },
                );
            }
            if named.contains_key(&Locus::ReceivingMap(g)) {
                materials.insert(
                    Locus::ReceivingMap(g),
                    LocusMaterial::ReceivingMap {
                        receiving,
                        tree,
                        population,
                    },
                );
            }
            if named.contains_key(&Locus::Resonator(g)) {
                if resonator.is_some() {
                    materials.insert(
                        Locus::Resonator(g),
                        LocusMaterial::Resonator {
                            ring: g,
                            material: resonator,
                            scales: resonator_scales,
                            step: resonator_step,
                        },
                    );
                }
            }
        }
        for (a, material) in contacts.iter_mut().enumerate() {
            if named.contains_key(&Locus::Channel(a)) {
                materials.insert(Locus::Channel(a), LocusMaterial::Channel(material));
            }
        }
        materials
    }

    /// The normal law a linear step deposits on, when this locus carries it.
    fn law(&mut self, locus: LinearLocus) -> Option<&mut NormalLaw> {
        match (locus, self) {
            (LinearLocus::SourcePort(_), LocusMaterial::SourcePort { source, .. }) => {
                source.as_mut()
            }
            (LinearLocus::Contrast(_), LocusMaterial::Element { contrast, .. }) => Some(contrast),
            (LinearLocus::Receiving(_), LocusMaterial::ReceivingMap { receiving, .. }) => {
                receiving.as_mut()
            }
            _ => None,
        }
    }

    /// The receiver's population, when this locus carries it.
    fn population(&mut self) -> Option<&mut PortPopulation> {
        match self {
            LocusMaterial::ReceivingMap { population, .. } => population.as_mut(),
            _ => None,
        }
    }

    /// The receiving parametron's landmark tree, when this locus carries it.
    fn tree(&mut self) -> Option<&mut Landmarks> {
        match self {
            LocusMaterial::ReceivingMap { tree, .. } => tree.as_mut(),
            _ => None,
        }
    }
}

/// **One factor family's carried step** (pass 2 of [`Constitution::deposited`]; module header, "The
/// factor families' certified step"): `Δx = rate · G_x` carried onto the family's entries at
/// `rate = η / h_x′`, `η` the family's certified step and `h_x′` the statistic carried in pass 1
/// ([`factor_prepared`]), on the family's locus's material and carried remainders.
fn factor_step(
    material: &mut LocusMaterial<'_>,
    carries: &mut Carries,
    step: &FactorStep,
    rate: &Rat,
    at: &mut BudgetedCarry,
) -> Result<(), HnnError> {
    let locus = step.gradient.locus();
    match (&step.gradient, material) {
        (FactorGradient::Passive { gradient, .. }, LocusMaterial::Element { passive, .. }) => {
            **passive = carried_matrix(
                carries.entry((locus, Carrier::Passive)).or_default(),
                at,
                Carrier::Passive,
                passive,
                &rate_matrix(rate, gradient)?,
                "a passive factor gradient",
            )?;
        }
        (FactorGradient::Slices { gradient, .. }, LocusMaterial::Element { slices, width, .. }) => {
            let n = *width;
            let carry = carries.entry((locus, Carrier::Slices)).or_default();
            for (rho, ((u, v), (du, dv))) in slices.iter_mut().zip(gradient).enumerate() {
                for (side, (x, dx)) in [(u, du), (v, dv)].into_iter().enumerate() {
                    for (i, (x, dx)) in x.iter_mut().zip(dx).enumerate() {
                        carry.deposit(
                            at,
                            Carrier::Slices,
                            (2 * rho + side) * n + i,
                            x,
                            &rate_times(rate, dx),
                        );
                    }
                }
            }
        }
        (FactorGradient::Standing { gradient, .. }, LocusMaterial::Standing { standing, .. }) => {
            let carry = carries.entry((locus, Carrier::Standing)).or_default();
            for (i, (x, dx)) in standing.iter_mut().zip(gradient).enumerate() {
                carry.deposit(at, Carrier::Standing, i, x, &rate_times(rate, dx));
            }
        }
        (
            FactorGradient::Resonator {
                ring,
                family,
                gradient,
            },
            LocusMaterial::Resonator {
                ring: material_ring,
                material,
                step: hop,
                ..
            },
        ) if ring == material_ring => {
            if *family >= 4 {
                return Err(HnnError::Resonator {
                    ring: *ring,
                    what: "a resonator gain family is one of C, K, D, or pump",
                });
            }
            let current = material.as_ref().ok_or(HnnError::Lattice { locus })?;
            // The candidate step, carried on copies of the entry's carry; kept when the carried
            // gain stays positive, backtracked otherwise ([`GainBacktrack`]).
            let carrier = Carrier::Resonator(*family);
            let from = current.gains()[*family].clone();
            let delta = rate_times(rate, gradient);
            let carry = carries.entry((locus, carrier)).or_default();
            let (mut trial, mut stroke, mut gain) = (carry.clone(), at.clone(), from.clone());
            trial.deposit(&mut stroke, carrier, 0, &mut gain, &delta);
            if gain.is_positive() {
                *carry = trial;
                *at = stroke;
            } else {
                let candidate = gain;
                let (quotient, _) = at.lattice.div_rem(&(&from * rat(1, 2)));
                let midpoint = Rat::from_integer(quotient) * at.lattice.unit();
                gain = from.clone();
                carry.deposit(at, carrier, 0, &mut gain, &(&midpoint - &from));
                if !gain.is_positive() {
                    return Err(HnnError::Resonator {
                        ring: *ring,
                        what: "a backtracked gain stays positive on its lattice",
                    });
                }
                at.backtracks.push(GainBacktrack {
                    ring: *ring,
                    family: *family,
                    from,
                    candidate,
                    to: gain.clone(),
                });
            }
            let mut gains = current.gains().clone();
            gains[*family] = gain;
            let candidate = current.with_gains(gains)?;
            let _hop = hop.as_ref().ok_or(HnnError::Lattice { locus })?;
            **material = Some(candidate);
        }
        (
            FactorGradient::PairPort {
                offset,
                outputs,
                current,
                earlier,
                ..
            },
            LocusMaterial::SourcePort { pairs, .. },
        ) => {
            let slot = pairs
                .iter_mut()
                .find(|(declared, _)| declared == offset)
                .ok_or(HnnError::Offset { offset: *offset })?;
            let mut family = |index: usize, base: &[Vec<Rat>], delta: &[Vec<Rat>]| {
                let carrier = Carrier::Pair {
                    offset: *offset,
                    family: index,
                };
                carried_rows(
                    carries.entry((locus, carrier)).or_default(),
                    at,
                    carrier,
                    base,
                    delta,
                    rate,
                )
            };
            let outputs = family(0, slot.1.outputs(), outputs);
            let current = family(1, slot.1.current_reads(), current);
            let earlier = family(2, slot.1.earlier_reads(), earlier);
            slot.1 = PairPort::new(outputs, current, earlier)?;
        }
        (
            FactorGradient::Storage { gradient, .. }
            | FactorGradient::Stiffness { gradient, .. }
            | FactorGradient::Dissipation { gradient, .. },
            LocusMaterial::Channel(material),
        ) => {
            let index = match &step.gradient {
                FactorGradient::Storage { .. } => 0,
                FactorGradient::Stiffness { .. } => 1,
                _ => 2,
            };
            // A boost's stiffness factor carries its signature: its gradient's columns take their
            // signs (`signed_columns`).
            let gradient = match (index, &material.boost) {
                (1, Some(boost)) => signed_columns(gradient, &boost.signature)?,
                _ => gradient.clone(),
            };
            let factor = match index {
                0 => &mut material.storage,
                1 => &mut material.stiffness,
                _ => &mut material.dissipation,
            };
            *factor = carried_matrix(
                carries.entry((locus, Carrier::Factor(index))).or_default(),
                at,
                Carrier::Factor(index),
                factor,
                &rate_matrix(rate, &gradient)?,
                "a channel factor gradient",
            )?;
        }
        // A factor step's locus is its gradient's, so its material is this locus's.
        _ => return Err(HnnError::Lattice { locus }),
    }
    Ok(())
}

/// The least `ε ∈ {0} ∪ {2^k : −20 ≤ k ≤ 40}` certifying `Q_(k+1) ⪯ (1 + ε) Q_k` on every storage
/// form a deposit can change ([`Constitution::storage_forms`]), or `None` when no candidate
/// certifies them, which refuses the deposit.
///
/// [definition; agent-inferred] Read form by form: the joint form is block-diagonal, so it is
/// certified at `ε` exactly when every block is (its negative inertia is the blocks' sum), and the
/// least joint `ε` is the largest of the blocks' least. Each block's `Q_k` is positive semidefinite
/// (a Gram `c cᵀ`, `b bᵀ`, or a squared gain times a declared base), so `(1 + ε) Q_k − Q_(k+1)`
/// only gains the PSD term `(ε′ − ε) Q_k` as `ε` grows to `ε′`: a block's certified candidates are
/// upward closed, and its least is found by bisection over the ordered candidates. An unchanged
/// block certifies at `0`.
fn certify_storage_growth(
    before: &[ExactRatMatrix],
    after: &[ExactRatMatrix],
) -> Result<Option<Rat>, HnnError> {
    let candidates: Vec<Rat> = std::iter::once(Rat::zero())
        .chain((-20i32..=40).map(|k| {
            if k < 0 {
                Rat::new(BigInt::one(), BigInt::one() << (-k) as usize)
            } else {
                Rat::from_integer(BigInt::one() << k as usize)
            }
        }))
        .collect();
    let last = candidates.len() - 1;
    let mut least = 0usize;
    for (old, new) in before.iter().zip(after) {
        if old == new {
            continue;
        }
        let form = |m: &ExactRatMatrix| matrix_form(m).map_err(crate::holon::HolonError::from);
        let (old, new) = (form(old)?, form(new)?);
        let certifies = |index: usize| {
            CommittedEnergyBound::certify_deposit(&old, &new, &candidates[index]).is_ok()
        };
        if certifies(least) {
            continue;
        }
        if !certifies(last) {
            return Ok(None);
        }
        // `lo` fails and `hi` certifies.
        let (mut lo, mut hi) = (least, last);
        while hi - lo > 1 {
            let middle = lo + (hi - lo) / 2;
            if certifies(middle) {
                hi = middle;
            } else {
                lo = middle;
            }
        }
        least = hi;
    }
    Ok(Some(candidates[least].clone()))
}

// -------------------------------------------------------------------------------------------
// the continuing state

/// [definition; agent-inferred, September 30; step 1b's pin §13.6] **The complete continuing state
/// of a source ring's port**: what the executed comparison's move changes and the next epoch reads,
/// the source port's normal law whole (the map `E`, the carried Gram `H`, the solved chart `X̂` with
/// its lattice, support and certificate, and the carried remainders of `W` and `H`), the source
/// navigator's transport modulus `ρ`, the locus's deposit clock `m` (its budgeted carry's precision
/// reads it), the commit counter and the committed storage growth's product. Nothing else of the
/// constitution moves under that move, and the state is refused, typed, where anything else has
/// moved (another locus's clock, a released locus, a factor family's remainder), so a restored
/// state is never partial silently.
///
/// Its consumer: [`Constitution::continued`] restores it onto the declared opening, and one move
/// from the restored constitution equals the same move continued without a checkpoint, exactly
/// (the owner's test over successive receptions). A remount of `E` and `ρ` alone
/// ([`Constitution::with_ports`] and [`Constitution::with_transport`]) rebuilds the normal law from
/// its prior, losing the Gram, the chart, the remainders and the clock: it is partial, and every
/// reader of one says so.
///
/// The text ([`ContinuingState::to_text`]) opens with the port's rows and its modulus in the form
/// the harness's partial remount reads (`E rows cols`, the rows, `rho ρ`), so a checkpoint is also a
/// partial remount's input; the rest follows it line by line, every value exact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContinuingState {
    ring: usize,
    law: NormalLaw,
    transport: Rat,
    clock: u64,
    commit: u64,
    storage_product: Rat,
}

impl Constitution {
    /// **The complete continuing state of ring `g`'s source port** ([`ContinuingState`]): refused off
    /// a source ring, and where a locus other than the source port has a clock, a locus is released,
    /// or a factor family carries a remainder (the state would not be complete).
    pub fn continuing_state(&self, ring: usize) -> Result<ContinuingState, HnnError> {
        let law = self
            .rings
            .get(ring)
            .and_then(|material| material.source.clone())
            .ok_or(HnnError::MissingSourcePort { ring })?;
        let locus = Locus::SourcePort(ring);
        if self.clocks.keys().any(|other| *other != locus) {
            return Err(HnnError::ContinuingState {
                what: "a locus other than the source port has moved",
            });
        }
        if !self.released.is_empty() {
            return Err(HnnError::ContinuingState {
                what: "a locus is released",
            });
        }
        if self.carries.values().any(|carry| !carry.0.is_empty()) {
            return Err(HnnError::ContinuingState {
                what: "a factor family carries a remainder",
            });
        }
        Ok(ContinuingState {
            ring,
            law,
            transport: self.rings[ring].transport.clone(),
            clock: self.clock(locus),
            commit: self.commit,
            storage_product: self.storage_product.clone(),
        })
    }

    /// **The constitution continued from a checkpoint** ([`ContinuingState`]): the state's source
    /// port, modulus, clock, commit and storage product placed on this constitution, which must be
    /// the declared opening the state continued from (no locus moved, none released, no factor
    /// remainder: refused, typed, otherwise), with the state's port of the declared shape.
    pub fn continued(mut self, state: &ContinuingState) -> Result<Self, HnnError> {
        let ring = state.ring;
        let shape = self
            .rings
            .get(ring)
            .and_then(|material| material.source.as_ref())
            .map(|law| (law.map.rows(), law.map.columns()))
            .ok_or(HnnError::MissingSourcePort { ring })?;
        if shape != (state.law.map.rows(), state.law.map.columns()) {
            return Err(HnnError::Shape {
                what: "a continuing state's source port against the declared port",
                expected: shape.0 * shape.1,
                found: state.law.map.rows() * state.law.map.columns(),
            });
        }
        if !self.clocks.is_empty()
            || !self.released.is_empty()
            || self.carries.values().any(|carry| !carry.0.is_empty())
        {
            return Err(HnnError::ContinuingState {
                what: "the constitution it is restored onto is not the declared opening",
            });
        }
        let lattice = self.lattice(Locus::SourcePort(ring))?;
        if !state.law.on_lattice(&lattice) {
            return Err(HnnError::ContinuingState {
                what: "the state's port or Gram lies off the source port's lattice",
            });
        }
        self.rings[ring].source = Some(state.law.clone());
        self = self.with_transport(ring, state.transport.clone())?;
        if state.clock > 0 {
            self.clocks.insert(Locus::SourcePort(ring), state.clock);
        }
        self.commit = state.commit;
        self.storage_product = state.storage_product.clone();
        Ok(self)
    }
}

impl ContinuingState {
    /// The source ring.
    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `E`.
    pub fn port(&self) -> &ExactRatMatrix {
        &self.law.map
    }

    /// `ρ`.
    pub fn transport(&self) -> &Rat {
        &self.transport
    }

    /// The source port's deposit clock.
    pub fn clock(&self) -> u64 {
        self.clock
    }

    /// **The state as text**, every value exact (the type's header): `E rows cols`, the rows,
    /// `rho ρ`, then `state g`, `gram n` with its rows, `chart L_s δ`, `support k` with the support,
    /// `block` with the chart's integer coordinates, `map-carry k` and `gram-carry k` each with
    /// `index value` lines, `clock m`, `commit c`, `storage-product p`, `end`.
    pub fn to_text(&self) -> String {
        let join = |values: &mut dyn Iterator<Item = String>| values.collect::<Vec<_>>().join(" ");
        let map = &self.law.map;
        let mut s = format!("E {} {}\n", map.rows(), map.columns());
        for i in 0..map.rows() {
            s += &join(&mut (0..map.columns()).map(|j| map.get(i, j).expect("in range").to_string()));
            s.push('\n');
        }
        s += &format!("rho {}\n", self.transport);
        s += &format!("state {}\n", self.ring);
        s += &format!("gram {}\n", self.law.gram.len());
        for row in &self.law.gram {
            s += &join(&mut row.iter().map(ToString::to_string));
            s.push('\n');
        }
        let chart = &self.law.chart;
        s += &format!("chart {} {}\n", chart.exponent, chart.certificate);
        s += &format!("support {}\n", chart.support.len());
        s += &join(&mut chart.support.iter().map(ToString::to_string));
        s.push('\n');
        s += "block\n";
        s += &join(&mut chart.block.iter().map(ToString::to_string));
        s.push('\n');
        for (name, carry) in [("map-carry", &self.law.map_carry), ("gram-carry", &self.law.gram_carry)] {
            s += &format!("{name} {}\n", carry.0.len());
            for (index, value) in &carry.0 {
                s += &format!("{index} {value}\n");
            }
        }
        s += &format!("clock {}\n", self.clock);
        s += &format!("commit {}\n", self.commit);
        s += &format!("storage-product {}\n", self.storage_product);
        s += "end\n";
        s
    }

    /// **The state read back from its text** ([`ContinuingState::to_text`]); refused, typed, on any
    /// line out of its form (a remount of `E` and `ρ` alone has no `state` line and is refused here:
    /// it is partial).
    pub fn from_text(text: &str) -> Result<Self, HnnError> {
        fn refuse<T>(what: &'static str) -> Result<T, HnnError> {
            Err(HnnError::ContinuingState { what })
        }
        let mut lines = text.lines();
        let mut next = |what: &'static str| lines.next().ok_or(HnnError::ContinuingState { what });
        let rats = |line: &str, what: &'static str| -> Result<Vec<Rat>, HnnError> {
            line.split_whitespace()
                .map(|x| x.parse::<Rat>().map_err(|_| HnnError::ContinuingState { what }))
                .collect()
        };
        let head = |line: &str, key: &str, what: &'static str| -> Result<Vec<String>, HnnError> {
            let mut words = line.split_whitespace();
            if words.next() != Some(key) {
                return refuse(what);
            }
            Ok(words.map(str::to_string).collect())
        };
        let number = |word: Option<&String>, what: &'static str| -> Result<usize, HnnError> {
            word.and_then(|w| w.parse().ok())
                .ok_or(HnnError::ContinuingState { what })
        };
        let shape = head(next("the port's head")?, "E", "the port's head")?;
        let (rows, columns) = (
            number(shape.first(), "the port's rows")?,
            number(shape.get(1), "the port's columns")?,
        );
        let mut map_rows = Vec::with_capacity(rows);
        for _ in 0..rows {
            let row = rats(next("a port row")?, "a port row")?;
            if row.len() != columns {
                return refuse("a port row's width");
            }
            map_rows.push(row);
        }
        let map = ExactRatMatrix::shaped(rows, columns, map_rows)?;
        let rho = head(next("the modulus")?, "rho", "the modulus")?;
        let transport = rho
            .first()
            .and_then(|x| x.parse::<Rat>().ok())
            .ok_or(HnnError::ContinuingState { what: "the modulus" })?;
        let ring = number(
            head(next("the state line (a partial remount has none)")?, "state", "the state line")?
                .first(),
            "the state's ring",
        )?;
        let n = number(head(next("the Gram's head")?, "gram", "the Gram's head")?.first(), "the Gram's width")?;
        let mut gram = Vec::with_capacity(n);
        for _ in 0..n {
            let row = rats(next("a Gram row")?, "a Gram row")?;
            if row.len() != n {
                return refuse("a Gram row's width");
            }
            gram.push(row);
        }
        let chart_head = head(next("the chart's head")?, "chart", "the chart's head")?;
        let exponent = number(chart_head.first(), "the chart's exponent")? as u32;
        let certificate = chart_head
            .get(1)
            .and_then(|x| x.parse::<Rat>().ok())
            .ok_or(HnnError::ContinuingState { what: "the chart's certificate" })?;
        let k = number(head(next("the support's head")?, "support", "the support's head")?.first(), "the support's size")?;
        let support: Vec<usize> = next("the support")?
            .split_whitespace()
            .map(|x| x.parse().map_err(|_| HnnError::ContinuingState { what: "the support" }))
            .collect::<Result<_, _>>()?;
        if support.len() != k {
            return refuse("the support's size");
        }
        head(next("the block's head")?, "block", "the block's head")?;
        let block: Vec<i128> = next("the block")?
            .split_whitespace()
            .map(|x| x.parse().map_err(|_| HnnError::ContinuingState { what: "the block" }))
            .collect::<Result<_, _>>()?;
        if block.len() != k * k {
            return refuse("the block's size");
        }
        let mut carries = Vec::with_capacity(2);
        for key in ["map-carry", "gram-carry"] {
            let count = number(head(next("a carry's head")?, key, "a carry's head")?.first(), "a carry's count")?;
            let mut carry = BTreeMap::new();
            for _ in 0..count {
                let line = next("a carried remainder")?;
                let mut words = line.split_whitespace();
                let index: usize = words
                    .next()
                    .and_then(|w| w.parse().ok())
                    .ok_or(HnnError::ContinuingState { what: "a remainder's index" })?;
                let value: Rat = words
                    .next()
                    .and_then(|w| w.parse().ok())
                    .ok_or(HnnError::ContinuingState { what: "a remainder's value" })?;
                if value.is_zero() {
                    return refuse("a zero remainder (never stored)");
                }
                carry.insert(index, value);
            }
            carries.push(Carry(carry));
        }
        let mut scalar = |key: &str, what: &'static str| -> Result<String, HnnError> {
            head(next(what)?, key, what)?
                .into_iter()
                .next()
                .ok_or(HnnError::ContinuingState { what })
        };
        let clock: u64 = scalar("clock", "the clock")?
            .parse()
            .map_err(|_| HnnError::ContinuingState { what: "the clock" })?;
        let commit: u64 = scalar("commit", "the commit")?
            .parse()
            .map_err(|_| HnnError::ContinuingState { what: "the commit" })?;
        let storage_product: Rat = scalar("storage-product", "the storage product")?
            .parse()
            .map_err(|_| HnnError::ContinuingState { what: "the storage product" })?;
        if next("the end")?.trim() != "end" {
            return refuse("the end");
        }
        let gram_carry = carries.pop().expect("two carries");
        let map_carry = carries.pop().expect("two carries");
        Ok(Self {
            ring,
            law: NormalLaw {
                map,
                gram,
                chart: SolvedChart {
                    exponent,
                    support,
                    block,
                    certificate,
                },
                map_carry,
                gram_carry,
            },
            transport,
            clock,
            commit,
            storage_product,
        })
    }
}

impl ConstitutionRead for Constitution {
    fn standing(&self, ring: usize) -> &[Rat] {
        &self.rings[ring].standing
    }
    fn contact_stiffness_signature(&self, contact: usize) -> Option<&[bool]> {
        self.contacts[contact]
            .boost
            .as_ref()
            .map(|boost| boost.signature.as_slice())
    }
    fn contact_surface_storage(&self, contact: usize) -> Option<&Rat> {
        self.contacts[contact].surface.as_ref()
    }
    fn ring_resonator(&self, ring: usize) -> Option<&ResonatorMaterial> {
        self.rings[ring].resonator.as_ref()
    }
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix {
        &self.rings[ring].passive
    }
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix {
        self.rings[ring].contrast.map()
    }
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        &self.rings[ring].slices
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.rings[ring].source.as_ref().map(NormalLaw::map)
    }
    fn transport(&self, ring: usize) -> Rat {
        self.rings[ring].transport.clone()
    }
    fn pair_port(&self, ring: usize, offset: usize) -> Option<&PairPort> {
        self.rings[ring]
            .pairs
            .iter()
            .find(|(declared, _)| *declared == offset)
            .map(|(_, pair)| pair)
    }
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix {
        &self.contacts[contact].storage
    }
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix {
        &self.contacts[contact].stiffness
    }
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix {
        &self.contacts[contact].dissipation
    }
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.rings[ring].receiving.as_ref().map(NormalLaw::map)
    }
    fn landmarks(&self, ring: usize) -> Option<&Landmarks> {
        self.rings[ring].tree.as_ref()
    }
    fn population(&self, ring: usize) -> Option<&PortPopulation> {
        self.rings[ring].population.as_ref()
    }
}
