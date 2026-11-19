# A driven ring's energy is its growth plus its port's supply, a zero's tank is positive real only on the seam, and heat runs below a finite front and holds a gradient in a potential, in Lean

November 19, 13:39 UTC. The twenty-third formalization pass over #410, its twenty-fourth set, after [the
twenty-third](2026-11-19_A_RATIONAL_CAYLEY_TURN_CLOSES_ONLY_AT_THE_QUARTER_TURNS_THE_EARS_SCALE_DERIVATIVE_IS_A_MULTIPLIER_ON_THE_LINE_AND_THE_COMPARISON_PULLS_BACK_TO_THE_WHOLE_ANCHOR_IN_LEAN.md)
(#1035). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `HNN/DrivenRingSupply` | One tick of the pumped ring with its port loaded is `x′ = Mx + Be`, and its supply-rate certificate is `E_G(Mx + Be) ≤ σ²E_G(x) + s(x, e)` (`SupplyCertifies`); the form's Cauchy–Schwarz and Young split, from its positivity along a line, turn the owner's undriven certificate `MᵀGM ⪯ ρ²G` into one at `(1 + ε)ρ²` with supply `(1 + 1/ε)E_G(Be)` (`form_cauchy_schwarz`, `young_supply`, `young_certifies`); for a quadratic supply the certificate is the positivity of the dissipation block on `n ⊕ m`, whose `e = 0` face is the undriven certificate (`dissipationBlock_reading`, `supply_certifies_iff_block`, `block_undriven_face`); a span of certified ticks obeys the discrete Grönwall bound, read in a reference form and, with the drive off, as the owner's undriven reach (`discrete_gronwall`, `driven_span_bound`, `driven_span_metric_change`, `undriven_span_reach`); a bounded drive keeps a bounded energy below the bifurcation, grows linearly at it and geometrically past it (`driven_span_below`, `driven_span_below_uniform`, `driven_span_at`, `driven_span_past`); the field's return `e = Kx` with `s(x, Kx) ≤ μE_G(x)` certifies the closed loop at `σ² + μ`, so the span's factorization through the return reads the owner's reach (`return_certifies`, `return_quadratic`, `return_span_reach`); the damped quarter turn certified at `¼`, its Young supply, its bounded span and a return closing at `⅝` (`witness_certificate`, `witness_span_uniform`, `witness_return`, `witness_closed_loop_own`) | #410's box "The carried pumped loop's supply-rate certificate" (ticked); `Holon/Deposition`'s owed paragraph and the record of September 29, §6 item 1 | `hnn.driven-ring-supply` (new); `parametron.floquet-consumer`, `hnn.pumped-span-factor` (scope) |
| `Zeta/FosterReturn` | A parallel LC tank is a lossless one-port: along every solution of `C v̇ = i − i_L`, `L i̇_L = v` its storage `½Cv² + ½L i_L²` changes at the port's effort times flow, `v·i` (`tank_power_balance`); a Laplace mode solves the tank iff its amplitudes do, giving the response `V̂ = Z(w)Î` with `Z(w) = wL/(w²LC + 1)` and the absorbed power `Re Z·|Î|²` (`mode_solution_iff`, `mode_response`, `mode_power`); at the owner's `C = ½`, `L = −2/ρ′²` that impedance is the owner's tank in the seam's frame `w = z − ½`, and the owner's paired flux is a sum of half-weighted tank impedances there (`parallelImpedance_seam_frame`, `pair_eq_impedance`, `flux_frame`, `flux_eq_series_impedance`); with the port open the tank rings as `cos γt` at `γ = (LC)^(−1/2)` with period `2π/γ`, an undriven mode exists exactly at a pole, and the seam tank of `ρ′ = iγ` rings at the zero's height (`free_oscillation`, `free_period`, `free_mode_iff_pole`, `seam_clock`); a seam tank is positive real, and a finite reflection-closed comb is positive real iff every zero lies on the seam, iff every tank has positive real inductance, since a zero off the seam puts a pole in the open right half-plane where the real part runs to `−∞` (`re_tank_pos_of_seam`, `no_pole_right_of_positive`, `comb_positive_real_iff_seam`, `foster_finite`); a series port sums storage, balance and impedance, the element of `ρ′` with multiplicity `k` is the tank `C = 1/k`, `L = −k/ρ′²`, and the comb's flux is the impedance of the series interconnection of its elements, which a receiver driving the port reads (`series_power_balance`, `series_impedance`, `element_impedance_eq_half_tank`, `combFlux_eq_series`, `comb_receiver`, `seam_element_real`); two seam tanks reading `7/5` at `w = 1` and an off-seam tank with negative real part at `w = ⅛ + i` (`witness_seam_pair`, `witness_off_seam`) | #410's box "The Foster return" (ticked); `Zeta/FosterTanks` and the record of September 3 (FT0) | `rh.foster-return-one-port`, `rh.foster-finite-positive-real` (new); `rh.foster-paired-flux` (meaning) |
| `Physics/Thermal/RelativisticHeat` | A cell against a bath at a fixed temperature, at real heats and temperatures: the bath gains what the cell loses, the production `κ(T − T_b)²/(T T_b)` is nonnegative and zero only at the bath's temperature and is the rate of the total entropy in continuous time, the tick's gap is `(1 − hκ/C)` times the gap before, and under the tick condition `hκ/C ≤ 1` the tick's entropy `C log(U′/U) + q/T_b` is nonnegative through the owner's real enclosure, while past it a tick destroys entropy (`first_law`, `productionRate_eq_zero_iff`, `hasDerivAt_total_entropy`, `gap_after_tick`, `tick_entropy_enclosure`, `tick_entropy_nonneg`, `overshoot_destroys_entropy`); the owner's rational exchange is its `ℚ` face, and the bath is the owner's second cell with its capacity grown without bound (`productionRate_ratCast`, `exchange_heat_at_bath`, `tendsto_next₂_temperature`, `tendsto_bath_entropy`, `tendsto_exchange_entropy`); the Cattaneo–Vernotte law on modes holds exactly when `τs² + s + Dk² = 0`, the telegraph equation on the mode, whose roots `−1/(2τ) ± iΩ` decay and travel below `c_h = √(D/τ)`, reaching it at high wavenumber, while Fourier's root `−Dk²` has a rate per wavenumber without bound and is the limit of the slow root as `τ → 0⁺` (`mode_solves_iff`, `telegraph_mode_iff`, `dispersion_eq_zero_iff`, `re_neg_of_dispersion_eq_zero`, `phaseSpeed_lt_frontSpeed`, `tendsto_phaseSpeed_cocompact`, `fourier_rate_unbounded`, `tendsto_slowRoot`); the front is causal exactly when `D ≤ τc²` (`frontSpeed_le_iff`, `phaseSpeed_lt_of_causal`, `tendsto_frontSpeed`); in the static chart `g_tt = −e^(2Φ)` the static observer accelerates at `Φ′`, Eckart's rest-frame flux is `−κe^(−Φ)∂ₓ(Te^Φ)`, so heat stops flowing exactly when `Te^Φ` is constant and a potential holds a temperature gradient at equilibrium, `T(1 + Φ)` constant to first order (`static_observer_acceleration`, `eckartFlux_mul_exp`, `tolman_ehrenfest`, `equilibrium_gradient`, `tolman_weak_field`); a cell at `3/2`, a cell at `√2` whose heat is irrational, and a Cattaneo mode at `τ = 1`, `D = ½`, `k = 1` (`witness_cell_three_halves`, `witness_irrational_heat`, `witness_cattaneo_mode`) | #410's box "The relativistic heat law, and irrational heat into the bath" (ticked; its reading `agent-inferred`); `Physics/Spacetime`'s `[open]` paragraph, `Physics/Thermal/Exchange` and the record of July 17, Card B | `heat.cell-bath-real`, `heat.cattaneo-modes`, `heat.tolman-ehrenfest` (new); `heat.telegraph-relaxation` (scope) |

The boxes these answer, by their opening words: "The carried pumped loop's supply-rate certificate" (ticked); "The
Foster return" (ticked); and "The relativistic heat law, and irrational heat into the bath" (ticked).

## 2. What the pass corrected

1. The box names its consumer as `Field::{found, founding_cost}`, which retired with the October library at C8 of #603
   (`crates/holonics/src/hnn/field.rs@d5ed4adc1`); `founding_cost` there was a description increment in bits, not an
   energy reach, and the span reach the record's runs read was `hnn::ring::FloquetBound::reach` through
   `hnn::constitution`, retired with it. The module names those readers and restates nothing from them. The record's
   `supply(e, s′)` never defines `s′`; the module reads the supply on the state and the drive, which covers any `s′`
   read from that pair (a port output or the next state). The atlas rows `parametron.floquet-consumer` and
   `hnn.pumped-span-factor` and the paragraph of `Holon/Deposition` that held the loop owed under the closed #62 now
   name the module.
2. The owner's `flux_eq_tankSum` gives each member of a reflection pair half its pair's tank, `m_ρ (z − ½)/((z − ½)² −
   (ρ − ½)²)`, so the comb's flux is one tank per pair only when the pair's two members carry matched multiplicities;
   the atlas row `rh.foster-paired-flux` read "a sum of tank impedances", and its meaning now says one per pair, counted
   half from each member. As one-ports, the element of `ρ′` with multiplicity `k` is the tank `C = 1/k`, `L = −k/ρ′²`,
   which is the owner's `C = ½`, `L = −2/ρ′²` at `k = 2` (a pair's two members together), so the owner's normalization
   is the pair's and the module's is the member's. The hypothesis `0 ∉ Z` is needed only for the inductance reading
   (`foster_finite`); the seam's positivity (`comb_positive_real_iff_seam`) holds without it.
3. The box reads "(refused today)" with no further text; the module reads it as the owner's exchange being stated over
   `ℚ` with no bath, so that a heat or a temperature that is not rational is outside its statements, and marks the
   reading `agent-inferred`. A Fourier mode with real wavenumber has a real rate `s = −Dk²` and does not travel, so it
   has no phase speed to be unbounded; the module states its rate per wavenumber `|s|/|k| = D|k|`, unbounded in `k`, and
   the front speed `√(D/τ)` growing without bound as `τ → 0⁺`, while both underdamped Cattaneo roots have `|s|/|k| =
   √(D/τ)`. `Physics/Thermal/Exchange` called its first law "exact over `ℚ`", its production "an exact rational" and its
   enclosure "two exact Clausius readings", which the precision law bars; they now read "an identity over `ℚ`", "a
   rational" and "two rational Clausius readings" (with `Physics/Thermal`'s map), and its docstring and
   `Physics/Spacetime`'s `[open]` paragraph now name this module. The atlas row `heat.telegraph-relaxation` stays graded
   `proved-derived` on its guide owner, since the module reads modes and not the support of a solution; its scope now
   names `heat.cattaneo-modes`.

## 3. What each statement stands on, and what is left

- `HNN/DrivenRingSupply` states the driven ring's supply-rate certificate, its block form, its span, its three regimes
  and the small-gain discharge through the field's return. The reach along a ring's own gain ray (a tube of
  monodromies), a modulated pump's passage-dependent schedule, the executed chart's lattice word, the word-level
  composition of each span's gain, continuous-time dissipation and the frequency-domain side of the KYP lemma are not
  stated. The box is ticked.
- `Zeta/FosterReturn` states the tank as a lossless one-port, its impedance in the seam's frame, its free ring and
  clock, the finite Foster theorem for reflection-closed combs and the comb as the series interconnection a receiver
  reads. The infinite comb of `ξ` (the owner's Landau remainder, the zero factorization), the Riemann hypothesis itself,
  a dissipative tank, the Cauer and Foster canonical forms of a general reactance function and the Herglotz
  representation are not stated, and realness on the real axis is proved for one seam tank only. The box is ticked.
- `Physics/Thermal/RelativisticHeat` states a cell against a bath at real values with the owner's exchange as its
  rational face and its limit, the Cattaneo–Vernotte law on modes with its causality condition, and Tolman–Ehrenfest
  from Eckart's law in the static 1+1 chart. The Israel–Stewart second-order theory and the instability of Eckart's
  first-order theory, a viscous relativistic fluid, a bath of finite capacity with its own entropy curve, the telegraph
  equation as a PDE with a solution theory (the support of a solution), a general metric or three dimensions, and the
  join to `Physics/Spacetime/StressEnergy`'s heat flux `T⁰ⁱ` beyond naming it are not stated. The box is ticked.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the texts that named these statements as owed or unstated (`Holon/Deposition`'s paragraph on the driven ring's supply-rate certificate, `Physics/Spacetime`'s `[open]` paragraph on the finite-speed heat law, `Physics/Thermal`'s module map and `Physics/Thermal/Exchange`'s docstring, whose "exact" wording now reads "an identity", "a rational" and "rational"; the `Holonics` modules and their importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (8864 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10638 jobs)`, exit 0; `Holonics`, with `Holon/Deposition`, `Physics/Spacetime`, `Physics/Thermal` and `Physics/Thermal/Exchange` and their importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new or changed file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
