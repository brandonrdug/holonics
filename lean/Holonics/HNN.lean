import Holonics.HNN.Propagation
import Holonics.HNN.Word
import Holonics.HNN.Moment
import Holonics.HNN.Normal
import Holonics.HNN.LatticeDeposit
import Holonics.HNN.LatticeWord
import Holonics.HNN.Ratio
import Holonics.HNN.Ratio.Resolution
import Holonics.HNN.TargetFace
import Holonics.HNN.StandingRead
import Holonics.HNN.IndexedOpen
import Holonics.HNN.Encoding
import Holonics.HNN.RegionCounts
import Holonics.HNN.Retention
import Holonics.HNN.Keys
import Holonics.HNN.Ring
import Holonics.HNN.Floquet
import Holonics.HNN.FloquetPassage
import Holonics.HNN.BankFace
import Holonics.HNN.ExecutedComparison
import Holonics.HNN.Contact
import Holonics.HNN.ContactBreak
import Holonics.HNN.BornFace
import Holonics.HNN.ModeQuotient
import Holonics.HNN.Prediction

/-!
# The HNN law

[definition] Rebuild step 4 (#73), campaign 1: the laws of `docs/plans/THE_REBUILD.md`, "Step 4
design: the HNN law", table (b) rows 1–8, stated before their Rust owners in `holonics::hnn`.

| Module | Design item | Rust consumer |
|---|---|---|
| `HNN/Word` | 1. the ring's element and the tick's global power | `hnn::propagation` |
| `HNN/Propagation` | 2. the junction scattering, the transit, the causal cone and diamond | `hnn::{propagation, word}` |
| `HNN/Moment` | 3. selective stepping, the phase-binned moment, its adjoint and capacity | `hnn::moment` |
| `HNN/Normal` | 4. the normal constitution and deposition, per locus | `hnn::constitution` |
| `HNN/LatticeDeposit` | 4. deposition on a declared carrier lattice with a carried remainder | `hnn::constitution::{Lattice, NormalLaw}` |
| `HNN/LatticeWord` | Decision 24: transients and inverse charts on declared lattices, certified residuals | `hnn::{word, propagation, constitution}` |
| `HNN/Ratio` | 5. the Holon ratio at the receiver's face, and the carried power | `hnn::ratio` |
| `HNN/Ratio/Resolution` | the receiver's resolution (October 2, contact-loop record §11): shifting the face's exponents by `δ` (bits) moves the face by at most `(ln2/8)(max δ − min δ)²` bits of divergence, at most `(ln2/2)M²` for `\|δ\| ≤ M` (`klBits_face_shift_le`, finite Hoeffding); independent readings add (`klDivergence_joint`); any test errs with total probability at least `1 − √KL` (`test_error_ge`, `receiver_cannot_tell`); the first-order code bound `\|Δcode\| ≤ max δ − min δ` per reading (`codeLength_shift_abs_le`); the station score's curvature `ln 2/2`, magnitude and phase (`codeLength_quadratic_upper`, `station_score_quadratic_upper`), which makes `s` of `Holon/Deposition.gauss_newton_curvature` a theorem; the grain lemma, same-cell media carry less than `(ln 2/2)/L²` bits a reading, tight to second order, unconfirmable over `N` readings when `2L² ≥ N ln 2` (`grain_lemma`, `grain_lemma_tight`, `grain_unconfirmable`); the odometer covector pairs with the smooth gradient within the factor `K = 2^(1/L)·2/(e ln 2)`, so the certified decrease owes `1/K` (`odometer_pairing_ratio`, `odometer_certified_decrease`, `K < 8/7` at `L = 16`); the grain read from a reading count, `L(N) = ⌈√(N ln 2/2)⌉`, refines as `√N` and a finer integer refinement keeps every coarser read (`refiningGrain_spec`, `refiningGrain_growth`, `grainRead_of_refined`, `refiningGrain_unconfirmable`); campaign one's numbers: the aeon resolution lies in `(1/21, 1/20)` bit and the measured contact change sits between `2^10` and `2^11` below it (`resolution_aeon_bounds`, `measured_change_ratio`) | `hnn::ratio` (the measurement's reading, `hnn_exposure`); `hnn::constitution` (the certified step's `s`); `hnn::field` (the grain `L_R`) |
| `HNN/TargetFace` | Decision 26: the target's code face, the margin rule, the receiving locus's exogenous normal law | `hnn::{ratio, constitution}` |
| `HNN/StandingRead` | Decision 26: the face reads the receiving parametron's bound harmonic coordinate | `hnn::receiving` |
| `HNN/IndexedOpen` | Decision 26: the source opens on its normalized counts (its indexed pair read, ruling B, retired from the open by U6's encoding loop; its laws stay) | `hnn::moment` |
| `HNN/Encoding` | U6, law 12: Holonic Encoding's injection square, reduced recurrence (the source moment descends), separator and descent criterion; the open reads the whole offset moment, no window | `hnn::{encoding, moment}` |
| `HNN/RegionCounts` | Decision 27: the receiving face is the grain of the receiving parametron's region class masses, corrected by the wave | `hnn::receiving` (target owner); KT baseline `hnn::reference` |
| `HNN/Retention` | 6. retention as the collapse onto what the admitted future distinguishes | `hnn::{retention, pending}` |
| `HNN/Keys` | 7. keys by loop closure, and selective stepping | `hnn::keys` |
| `HNN/Ring` | campaign 2, item 8: the ring's mode tick keeps `Q = diag(K, C)`, its denominator, its executed balance with pump and port work, the two-port reference change, crossings as epoch ticks, the pump and the sheets | `hnn::ring` |
| `HNN/Floquet` | the parametron re-derived (September 29): the pumped ring's monodromy over one period and its growth certificate `M_Tᵀ G M_T ⪯ ρ² G` (energy grows by at most `ρ²` a period, passive at `ρ² ≤ 1`, one certificate per tick for a partial period, and the consumer's change of metric `E_Q(Mᵐx) ≤ (γ_hi/γ_lo) ρ^(2m) E_Q(x)`); the pump's in-phase and quadrature axes, the standing bifurcation where the stiffness is singular and the storage form's passivity below it; phase-sensitive amplification (growing and squeezed quadratures, the Cayley tick's multiplier on an eigen-axis); two pumps compose to the turn by their relative phase; no linear threshold reads a relative phase | `hnn::ring` (the Floquet certificate and the receiving bank) |
| `HNN/FloquetPassage` | the bank reads a superposed passage (September 29): a reflection absorbs a turn on either side, and two crossings separated by the ring's transport compose to the turn by their relative phase less the transport, `R_u Rot_v R_w = Rot(u v̄ w̄)`; one crossing more composes the passage's expansion in the pump, the second order pairing the new crossing with every earlier one, over the whole passage `Σ_(t<n) Σ_(s<t) Rot(v^(n−t) v̄^(t−s) v^s u_t ū_s)`; at a whole turn its trace is the passage's power spectrum, `2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ w|² − Σ|w|²` | `hnn::ring::ReceivingBank::read_turn`, `hnn::prediction::generate_by_bank` |
| `HNN/BankFace` | the bank's learning path (September 29): the station's face is the lock's exchange face over the candidates, `θ_x = A(x)/Σ A`, its covector on the log-readings `θ − q` (`bank_face_covector`); a member's power is quadratic along a ray and a unit-carrier resonance reads at most `d` times the passage's energy (`member_amplitude_ray`, `resonance_gain`); `log(1 + u) ≥ u − 2u²` for `u ≥ −1/2` gives the score's endpoint bound and its trust region (`log_one_add_ge`, `bank_score_endpoint`, `bank_score_trust`); a score beside the logits joins the joint certificate (`joint_descends_beside`); the executed law departs from the kicked chart: the node plane's reflection conjugates `R(c)` to `R(c̄)` and the kicked transport to `Rot(v̄)` (`flip_reflection`, `flip_rotation`), and a real pair kernel reads the resonance and its mirror equally (`sideband_pair_sum`) | none since September 30: its Rust consumers (`hnn::ring::{BankChart, Resonance}`, `hnn::prediction::{stage_bank, bank_reach}`, `hnn::constitution::BankReach`) were retired with the face path (batch H; at commit `f5fd8f3b`); `flip_reflection` is held by the Rust test `the_executed_turn_reads_a_passage_and_its_conjugate_alike` |
| `HNN/ExecutedComparison` | the release's own comparison (September 30): a tick with its variation is the first-order polynomial `C T + X·C ΔT`, the passage's constant coefficient the monodromy and its first-order coefficient composed forward `c₁′ = c₁T + c₀ΔT`, equal to the reverse sum `Σ_t T_(>t) ΔT_t T_(<t)` (`passage_coeff_zero`, `passage_coeff_one`, `product_deriv`); along a differentiable path of roots with `∂_λΦ ≠ 0` (a simple root), `μ′ = −∂_ηΦ/∂_λΦ` (`simple_root_deriv`), and `d log|μ| = Re(μ′/μ)` (`log_modulus_deriv`); a max descends where every active branch descends, and a sum of maxes where its active slopes sum below zero (`max_descends`, `sum_max_descends`, Danskin's bound summed); disjoint enclosures certify a strict decrease (`disjoint_enclosures_decrease`); class at every open station makes every lock correct (`predicates_release_the_section`) | `hnn::ring::{ReceivingBank::read_turn_covector, ReceivingBank::turn_variation, dominant_multiplier}`, `hnn::executed::{compare, executed_move}` |
| `HNN/Contact` | campaign 2, item 8: the contact's transfer and site kind by its stiffness's sign, the boost's certified solve or singular direction, the signed-storage balance, the lock address from the measured winding pair | `hnn::contact`, `hnn::propagation` |
| `HNN/ContactBreak` | campaign 2, item 8: the released storage `R = E_a + W_a − D_a − E_a′`, the advance `R ≥ J`, Griffith's closed-port case, the parted face's typed gluing defect | `hnn::contact`, `hnn::field` |
| `HNN/BornFace` | Decision 33: the wave read by the Born rule, a finitely correlated receiver on the receiving ring's register: the normalized digit split and dyadic cell face, the reception keeping a density, the density as the retained quotient, the absorbed unitary tick, the interference zero no nonnegative receiver makes, the exact covector and the Fisher-scored step | `hnn::born` (its Rust receiver `hnn::born` retired September 28) |
| `HNN/ModeQuotient` | Campaign 3, first construction: a loaded ring's modes descend to their future quotient: the pump's cycle factors through its period (`cycle_mul_add`), so the period lift reads exactly the admitted future (`periodic_lift_exact`); one chart for every phase releases at most the phase family's kernel, which lies in it (`shared_chart_le_phase_kernel`, `phase_kernel_le_lift`); the descended ring returns the same wave for every drive (`descended_run`, `descended_run_reads`); a pair silent at the loaded port on its state and its tick stores nothing (`released_pair_storage_null`); the learning covector factors through the chart (`descended_costate`, `descended_gain`, `gain_fibre_invariant`) exactly when each gain family's variation vanishes on the release (`solved_pairing_null_iff`), which capacity and dissipation always do and stiffness and pump do under a half-turn pump cycle (`half_turn_separates`) but not at a standing pump's threshold (`standing_pump_threshold_reads_release`), so a learning aeon admits the variations as receivers (`learning_chart_le_kernel`); and the descended block ticks with its descended storage form and the full ring's balance (`descended_form`, `descended_balance`) | retired at U2 (`hnn::modes`, at commit `1bdacc8f`) |
| `HNN/Prediction` | THE_REBUILD U6, native generation: the refinement is `K` words of one step (`refine_iterate`); the joint section is `Holon.ofEvolution` read at every station from the one refined field (`jointSection`, `jointSection_receive`); its image is not the product of its marginals (`joint_not_marginals`, `jointImage_ne_marginalProduct`); a reading through a face constant on the fibre releases at width zero and a parted one is held (`release_width_zero`, `plural_section_held`); the consumer equation is `ofEvolution_receive_eq_encoded` at `F^[K]` (`consumer_eq`) | `hnn::prediction` (the bank's release: `section_release`, `bank_release`; the linear readout that realized `refine_iterate` and `jointSection` was retired September 30, batch H, at commit `f5fd8f3b`) |

[definition] The receiving parametron's storage is the receiving tree, the shift navigator's
landmarks: its laws are `Compression/Landmark/Context` (its Rust owner
`compression::landmark::context`, which `hnn::receiving` reads). `HNN/RegionCounts` stays here: it
is the receiving face's region table, its grain read and the wave's combined face, and the tree
reads its KT count laws.
-/
