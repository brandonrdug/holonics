# A ring path's log-ratio is its lift's entropy reading and its mean carry is the current, an interconnection carries its step, its restriction and joint reception, and a retention counts its active Gram modes, in Lean

November 19, 06:38 UTC. The eleventh formalization pass over #410, its twelfth set, after [the
eleventh](2026-11-19_POLAR_FACTORS_CARRY_ONE_ROOT_AS_ITS_CONSTRAINT_A_CHASES_CAPTURE_AND_VIABILITY_STAND_BY_THE_TERRAINS_SIZE_AND_AN_INTERIOR_ELIMINATES_IN_STAGES_ALONG_A_TUBE_AND_A_TOWER_IN_LEAN.md)
(#1022). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #5, #145.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Thermal/ChainPathJoin` | A ring path on `Fin (M + 3)` that stays or moves one cell at every step lifts to `ℤ` and projects back (`lift`, `liftWord`, `liftAeon`, `cell_lift`, `lift_emod`); the lift's entropy reading is the path's affinity sum, `wordReading (entropyForm a) (lift word) = Σ_i affinity P (γ i) (γ (i+1))` with `a z = affinity P (z mod N) (z+1 mod N)`, for every ring path with no positivity (`wordReading_liftWord`), so for a positive path of an admissible nearest-neighbour ring `log(P_γ / P_(Rγ)) = (log π(γ₀) − log π(γₙ)) + (s(γₙ) − s(γ₀)) + A · (signed crossings at the carry section)` (`pathLogRatio_eq_entropy_reading`, `pathLogRatio_eq_carry_reading`); the lift's crossings of the carry section are the path's steps `N − 1 → 0` and `0 → N − 1`, their difference the lift's whole windings (`forwardCrossings_liftWord`, `backwardCrossings_liftWord`, `carryCount_eq_winding`); under a stationary law every step's pair has the flow law `π x P(x, y)` (`pair_marginal`, `mean_step_sum`), so the mean signed carry count over `n` steps is `n · J` (`mean_carryCount`, `mean_carryCount_eq_current`, `mean_liftCrossings_eq_current`, `mean_liftWinding_eq_current`), the helix's turn is the cycle affinity and the mean carry term is `n · J · A` (`turn_eq_cycleAffinity`, `mean_carryTerm_eq_production`); relabelling the cells by `Fin.rev` negates the mean (`carryCount_rev`, `mean_carryCount_reflect_eq_current`); the biased rotation of three cells carries `J = 1/9` and a mean signed crossing of `2/9` over two steps, its mean carry term over two steps `(2/3) log 2`, its production over two epochs (`rotation_current`, `rotation_mean_carryCount`, `rotation_mean_carryTerm`). | #410's box "The chain axes (from #5)"; `Physics/Thermal/ChainAxes`' open paragraph, `Aeon/Production/PathReversal`, `Aeon/Clock/Epoch`; the aeon record of September 24 | `heat.path-ratio-carry-current` (new), `heat.time-entropy-helix`, `heat.ring-current-affinity`, `aeon.production-state-heat` |
| `Holon/InterconnectionJoin` | A step of a port Holon is admitted in Dirac form when the assembled bond at the midpoint effort `Q x̄`, with the difference quotient as velocity, lies in its Dirac structure (`DiracStep`); then `E(x′) − E(x) = ⟨x′ − x, Q x̄⟩` and, for `h ≠ 0`, `E(x′) − E(x) = h(−⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩)` from power neutrality alone, with passivity for `R` positive semidefinite and `h > 0` (`storageEnergy_sub_midpoint`, `diracStep_balance`, `diracStep_passive`); a step of `A.interconnect B` restricts through one shared bond to steps of each side, their external powers summing to the composite's, and the joint balance is the sum of the two sides' (`diracStep_interconnect`, `diracStep_interconnect_balance`); a pair of morphisms that are the identity on the shared ports joins to a morphism of the interconnections, for Dirac structures and for port Holons (`interconnect_isMorphism`, `isMorphism_reindex`, `portHolon_interconnect_isMorphism`); two port Holons joined through an interface conductance at their midpoint efforts receive `−h⟨Δ̄, GΔ̄⟩ ≤ 0` over the step, so `ΔE_H + ΔE_R = −h(D_H + D_R + ⟨Δ̄, GΔ̄⟩) + h·(active supply)` (`joint_reception_step`, `joint_reception_passive`); a capacitor and a resistor, each the one-node Kirchhoff structure of its two ports, join to a circuit whose admitted points are the RC law, along which `x₀e^(−t/(RC))` is admitted at every `t` with `dE/dt = −R f_R²` and `E(t) = E(0)e^(−2t/(RC))`, and whose midpoint step `x(2RC − h)/(2RC + h)` loses `hR f̄²` (`capacitor_link`, `resistor_link`, `rcCircuit_admits_iff`, `rc_motion_admitted`, `rc_energy_rate`, `rc_energy_decay`, `rc_midpoint_step`, `rc_midpoint_witness`). | #410's box "Interconnection"; `Holon/{Element,Law,Dirac,Restriction/Morphism}`, `Holarchy/Join`, `Holarchy/Reception`; the record of September 22 on the Holon as an interconnected port object; Kotyczka and Lefèvre (2019) on the midpoint rule in Dirac form | `holon.dirac-form-step` (new), `holon.interconnect-morphism` (new), `holon.rc-interconnect-witness` (new), `holon.interconnect-port-holons`, `holon.pushforward-morphism`, `receipt.active-receiver-law` |
| `Compression/FaceMapPower` | A linear port Holon's unforced midpoint step `S` (a linear map with `S q − q = h(J − R)Q(½(q + S q))`, a hypothesis) is the face map's navigator and its port, the midpoint effort pulled back through the supply, `Bᵀē`, its receiver (`MidpointPort`, `faces`); the kernel is where the port reads zero after every number of steps (`mem_ker_faces_iff`). Under one supply sequence two forced motions differ by the free motion of their difference (`forced_sub`, `forcedEffort_sub`), so when that difference lies in the kernel the port efforts, the supplied energy `h⟨ē_k, B u_k⟩` and `ΔE + Σ h⟨ē_k, Rē_k⟩` agree at every step (`port_effort_descends`, `forced_ledger`, `supplied_energy_descends`): the supplied power is a face of the retained class. A released difference receives no port power, each free step changes its storage by `−h⟨ē, Rē⟩`, so its storage is nonincreasing for `R` positive semidefinite and constant for `R = 0` (`released_receives_no_port_power`, `free_step_balance`, `released_difference_dissipates`, `released_difference_conserved`), and constant for any `R` when the storage effort is also read (`effort_released_conserved`). The Gram `AᵀA` of a finite face map shares its kernel and rank, so the retention's dimension `dim X − dim(relevance kernel)` is the rank of the Gram and, over ℝ, the count of its nonzero eigenvalues (`gram_ker_rank`, `rank_eq_card_active_gram_modes`, `retention_dim_eq_gram_rank`, `retention_dim_eq_card_active_gram_modes`). On two square boundaries sharing one edge, `DᵀD = [[4, 1], [1, 4]]` is `TwoFaceConstitutive.faceMetric`, its modes `(1, 1)` and `(1, −1)` carry the values `5` and `3`, both active, the plus and minus coordinates are the pairings with them, and the compact law's denominators are `1 + τ · (mode value) · (material eigenvalue)` (`gram`, `gram_eq_faceMetric`, `gram_modes`, `both_modes_active`, `plus_minus_are_modes`, `compact_denominators`). | #410's box "The face map"; `Compression/Core/FaceMap`, `Holon/Element.midpoint_balance`, `Physics/TwoFaceConstitutive`; the clocked torus record of September 8 | `compression.port-supply-descends` (new), `compression.gram-mode-count` (new), `encoding.derived-grain`, `ph.two-face-constitutive` |

The boxes these answer, by their opening words: "The chain axes (from #5)"; "Interconnection"; "The face map".

## 2. What the pass corrected

1. **Neither target needs the neck, and the identification needs no positivity.** The box read "along an oriented chain
   through a neck", but `ChainAxes` keeps the neck (the least forward flow) apart from the carry section (a chart
   choice), and both statements hold at the carry section `N − 1 → 0` with no reference to the neck; the neck's only
   bound remains `production_le_neck`. The open paragraph asked for "a positive ring path"; the lift's reading equals
   the affinity sum on every ring path, since a held step reads `affinity P x x = 0` and `affinity` is antisymmetric,
   and positivity enters only through `pathLogRatio_split`. `ChainAxes`' open paragraph named the closed #62 and said a
   retired Rust owner "checks both exactly"; it now points to the new owner and keeps open only what is read on the
   witness alone.
2. **A Dirac-form balance needs a nonzero step, and the restriction facet's `π` names two things.** The brief asked for
   passivity at `h ≥ 0`; with the difference quotient as velocity, `h = 0` reads velocity `0` and leaves `x′` free, so
   the balance is stated for `h ≠ 0` and passivity for `h > 0`. The box writes the restriction facet as `π`, the Holon
   tuple's letter, while `Ports σ ρ π α` uses `π` for the external port kind; the module says "the restriction facet" in
   prose and keeps the code's letter for ports. Each element's structure is the one-node Kirchhoff structure of its two
   ports (Dirac by `kirchhoff_isDirac`), the link of `Holon/Dirac` living on `Bond τ × Bond τ`, and with these
   conventions the resistive flow is `f_R = +v`. Joint reception is stated as two Dirac-form balances and the interface
   law rather than one composite, since `PortHolon` holds resistance as `e = −R f` and a singular conductance has no
   such form.
3. **The box's balance is the midpoint step's, and "Gram modes 3 and 5" named values.** The box asked for "the
   `PortHolon` power balance" joined to the face map; `PortHolon` carries a Dirac structure and resistive ports with no
   `J` or `B`, and its own balance is pointwise and continuous, so the balance a face map's navigator can carry is
   `midpoint_balance` in the state form `(Q, J, R, B)`, and that is the join made; the step from a `PortHolon`'s Dirac
   structure to that form is left with the interconnection module's Dirac-form step. The brief's "a released difference
   only dissipates" needs no kernel for the monotonicity, which every free motion with `R` positive semidefinite has;
   what the kernel adds is that no supply reaches the motion through the port. The clocked torus record and
   `encoding.derived-grain` called 3 and 5 "the active Gram modes"; they are the modes' values, and the modes are `(1,
   −1)` and `(1, 1)`, as `ph.two-face-constitutive` already wrote ("5 on z₊, 3 on z₋"); the atlas row now says so.
   `TwoFaceConstitutive`'s title and summary called its reduction and its update "exact"; they now read "a two-face
   constitutive reduction" and "the compact update".

## 3. What each statement stands on, and what is left

- `Physics/Thermal/ChainPathJoin` stands on `ChainAxes` (`entropy_reading`, `ring_nets_eq`, `cycleAffinity`,
  `ringProduction`), on `PathReversal` (`pathLogRatio_split`, `sum_snoc`, `pathLaw_snoc`, the `Rotation` witness) and on
  `Epoch.signed_count_is_flux`. Its path sums are the path law's weighted sums, means in the sense of probability when
  `π` sums to one, which is not assumed; that the mean carry term is `PathReversal`'s production `σₙ = nσ` on every ring
  (a ring's epoch production read as its ring production) is read on the rotation witness alone; continuous-time and
  infinite chains are not treated.
- `Holon/InterconnectionJoin` stands on `PortHolon.power_balance`, `PortHolon.mem_interconnect`, `interconnect_power`,
  `storageEnergy_blocks`, `dissipation_blocks`, `active_receiver_law`, `kirchhoff_isDirac`,
  `PortHolon.energy_balance_const` and `Holarchy/Join`'s part identities. Existence and uniqueness of a Dirac-form step
  are `Holarchy/Reception`'s in the `(J − R)Q` form, and the uniqueness of the RC motion among solutions is not stated;
  a Dirac-form step of a nonlinear storage, a composite port Holon for the conductance, and morphisms that keep the four
  port kinds apart are not stated. The words "exact" in the docstrings of `Holon/Element` (the midpoint balance),
  `Holon/Dirac` (the interconnection's power balance) and `Holarchy/Reception` stay for a curation pass, since those
  modules sit under most of the library and a docstring change rebuilds it.
- `Compression/FaceMapPower` stands on `FaceMap` (`horizonFaceMap`, `rank_nullity_ledger`,
  `horizonBlind_finrank_pred_eq_ker`), on `midpoint_balance` and on Mathlib's Gram rank lemmas and Hermitian spectrum.
  The forced step's supply term is a hypothesis (solving for it needs `1 − (h/2)(J − R)Q` invertible,
  `Holarchy/Reception`); `rank [J D] = 6` on the four-torus's own branches is `Physics/FourTorusTwoFace`'s carrier and
  is not restated; a nonlinear face map and a Gram reading of the cokernel ledger are not stated.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed `ChainAxes`' open paragraph, added a pointer in `Compression/Core/FaceMap`, corrected the Gram-mode wording in `docs/HNN_FORMULA.md` and the atlas, retired "exact" from the titles of `Physics/TwoFaceConstitutive` and `Holon/Restriction` (and from `kron_exact`'s docstring, the name kept), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules and the four `Holonics` modules whose docstrings changed (`Compression/Core/FaceMap`, `Holon/Restriction`, `Physics/Thermal/ChainAxes`, `Physics/TwoFaceConstitutive`) read `Build completed successfully (3500 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10602 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0. The warnings printed are other modules' (unused simp arguments, unused section variables, universe notes), none in a changed file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
