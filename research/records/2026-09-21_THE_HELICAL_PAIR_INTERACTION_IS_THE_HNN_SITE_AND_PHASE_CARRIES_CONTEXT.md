# The helical pair interaction is the HNN site and phase carries context

**Date:** September 21, 2026. **Source under audit:** Holonics `73ff9950` and its
[situated-generator synthesis](2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md).
**Scope:** source audit of the HNN consumer against the elementary helical/interaction owners,
the design object Brandon confirmed for the next campaign, a formal-work audit with one new
checked Lean module, and plan/issue finalization. No native Rust behavior changed in this return.
The [Holon](../../docs/HOLON.md#the-helical-pair-interaction-unit) and
[helical guide](../../docs/HELICAL_GEOMETRY.md#the-pair-is-a-holonic-interaction-contact) own the
definitions; the [roadmap](../../docs/plans/THE_ROADMAP.md) owns order.

[historical] The later [design iteration](2026-09-21_THE_GENERATOR_MACHINE_RETAINS_ITS_SOURCE_AND_RECEIVING_LAWS.md) preserves this return and corrects its source-moment attribution, zero-power/lock and closure domains, harmonic-standing scope, spectral/functionality claim and cost contract. Use the live guides and native contract for the finalized implementation. The measurements and original source audit below retain their recorded scope.

## Direction

[project-postulate] Brandon's September 21 direction: the framework already supplies one
consistent computational object, the pairwise toroidal/helical Holonic Interaction. Robotics
and kinetics, the rotor machine and the Bombe are instances of it. The design must state that
object before implementation, and the HNN must consume it. The earlier synthesis correctly
recovered standing, release and the simulator interface. It left the action relation untyped
(`z`, `T_a`), listed helical geometry as one owner row among nine, and scheduled a join between
two HNA-internal paths. Brandon confirmed the unit and the phase-carried context below.

## What the source shows

[established-bounded; source-inspected] At `73ff9950`:

- `crates/holonics-hna/src/` imports none of `relational_geometry::screw`,
  `holonic_interaction`, `holonic_chain`, `standing`, `receiver_release` or
  `HelicalMomentReuse`. The word `winding` does not occur there. Only
  `examples/helical_field_generator.rs` uses a screw.
- No Rust file imports both `ScrewPair` and `HolonicInteraction`. `ContactFace` receives its
  slip map `J_f` as a supplied matrix; `PairQuadranceJet` already computes the pair's `Δ`, `Q`,
  `DQ`, `D²Q` and pullback. The helical guide states their relation in prose only.
- The Athena incident geometry is `examples/support/linked_torus_field.rs`: two
  `TorusLongitude` circles with the meridian fixed at `−1`, one shared junction and one mode.
  `linked_torus_incident_slot_junctions` assigns one junction to each source cell, in order
  around ring A, the overlap and ring B. The development run had 76,599 sites. Site count, resident
  state, the dense support statistic and checkpoint size therefore grow with source length.
- `IncidentEncoder` is a diagonal one-hot normal law with one learned column per exterior symbol.
  `IncidentTextReceiver` is a per-slot alphabet face plus a support face over aperture lengths.
- The participation kernel scores `β⟨q|Uq′⟩`, and the incident reaction already forms
  `Δ_i=U_i q_i−q_r`. By polarization that score is the pair quadrance with both advances zero.
  The field therefore already computes the circle×circle collapse of the pair receiver.
- The Lean default target `ElementaryHolonics.Framework` did not import
  `Transport/HolonicInteraction`, `Transport/HolonicChain`, `Transport/ContinuingTube`,
  `Foundation/Standing` or `Foundation/ReceiverRelease`.

[definition] The torus in that geometry is a tape: a position index drawn as a longitude angle.
It has one phase per ring, no second phase, no advance, no winding and no pair of moving sources.
This is the representation substitution the [Holonic Encoding record](2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md)
and the roadmap's symbol-basis correction already name. Routing compatibility families into it
does not repair it.

## The unit

[definition] A **helical pair interaction** is a `HolonicInteraction` whose media coordinates are
the parameters of a `ScrewPair` and whose contact slip map is that pair's relative velocity:

```text
Objects       a=(ξ_a, x_a(0)), b=(ξ_b, x_b(0))   SituatedScrew: generator and initial configuration
Parameters    (s,t), each a RationalPhase         own clock; chart phase and retained winding
Separation    Δ(s,t)=x_a(s)−x_b(t),  Q=⟨Δ|Δ⟩      PairQuadranceJet
Slip map      J=[v_a | −v_b],  Δ̇=J(ṡ,ṫ)           ContactFace.J_f, derived rather than supplied
First var.    DQ=2 J*Δ                            PairQuadranceJet::pullback is the adjoint
Second var.   D²Q=2 J*J + 2 diag(Δ·a_a, −Δ·a_b)   isotropic contact form plus geometric term
Contact       M_contact=Σ_f w_f J_f* D_f J_f,  P=⟨q̇,M_contact q̇⟩≥0,  P=0 ⇔ ṡ v_a=ṫ v_b
Medium        q̇=(Ω−M_contact)Gq+Bu               storage G, flux Ω, drive/action Bu, Clock
Reading       ρ_R at the Perspective               receiver; release through receiver_release
```

[proved-derived; formal-checked] `Transport/HelicalPairInteraction.lean` proves the slip-map
reading, its adjoint, pair contact power, the synchronized zero-power kernel on a dissipative
face, the two-jet decomposition above and the polarization identity
`⟨a|b⟩=(⟨a|a⟩+⟨b|b⟩−⟨a−b|a−b⟩)/2`. The kernel condition is the incidence/synchronization law
between `s` and `t` read from material. It does not identify the two parameters.

[definition] Each object degenerates independently through the helical guide's table: helix,
circle, line, axis line, point. A torus chart reads a phase modulo its closure. The helix is
the lift that retains the winding the torus forgets: `x(s)=(r e^{i(as+φ)}, bs)`. For a coaxial
pair the quadrance reads both parts, `|r_a e^{iα}−r_b e^{iβ}|²+(b_a s−b_b t+c)²`; a general pair
reads them through the same `Δ` with its axis offset and inclination. With `b=0` and `r=1` on
both objects it is `2−2cos(α−β)`, the existing unit-phase participation chart with connection φ.
The HNN's present score is this collapse; the unit restores radius, advance, winding, the
second variation and the contact material.

## The same object in the three references

[proved-derived; formal-checked] **Rotor machine.** Fixed material `P` carried by a phase shift
`S` is `phaseTransport S P d = S⁻ᵈ P Sᵈ`; stepping conjugates the carried material and leaves
the material unchanged (`phaseTransport_add`); a closing shift gives the toroidal chart
(`phaseTransport_add_period`). A forward passage `A` with reflection `F` returns through the
producing operands, `reflectedReturn A F = A⁻¹FA`, involutive and fixed-point-free when `F` is
(`reflectedReturn_involutive`, `reflectedReturn_no_fixed_point`). This is the paired adjoint of
`out=S_D(incoming,b)`. A stream of `n` occurrences composes to
`(P S⁻¹)ⁿ Sⁿ` (`steppedWord_eq_generator_power`): one act-and-advance generator, with the
stream length as an exponent and a retained winding. The machine does not grow with the stream.

[definition] The rotor key is material selection, frame offset, initial configuration and a
boundary involution: a generator **and an initial configuration** in a declared frame, which is
`SituatedScrew`. A rotor kept in its box retains material without an engaged phase, which is
standing. The alphabet and `n=26` are one boundary chart of this transport. The fixed-state
involution does not make the stepping machine an involution; the state evolution is retained.

[proved-derived; formal-checked] **Bombe.** A menu is an incidence graph of observed boundary
pairs at relative phase offsets. It is the incidence law stating which `(s,t)` interact. The
same unknown boundary map conjugates every stage, so a closed menu path closes at port `a`
exactly when the known stage word fixes `S a` (`menu_loop_closure`, with
`boundary_conj_list_prod` and `boundary_involution_reciprocal`). A hypothesised phase whose
word has no compatible fixed point is refuted without resolving `S`; a compatible phase leaves
the boundary family plural. Inference of an initial configuration from pairwise loop closure is
the training operation. Existing owners: `PairFiniteMotion::closes_after`,
`RationalPhase::lifted_winding`, the identity atlas kernel, `GeneratorInference`,
`TransportWord::descendingWord_is_optimal`. Sweeping candidate phases over co-present regions
is the hardware cover's partition law.

[definition] **Articulated body.** A serial chain is an ordered family of `SituatedScrew`s.
Its configuration is the ordered product of their finite motions applied to the initial
configuration. Joint space is the torus chart of the revolute phases with a line for each
prismatic parameter. A revolute joint is the zero-advance row, a prismatic joint the
zero-angular row, a screw joint the general row. Jacobian column `i` is
`ScrewGenerator::rechart` of `ξ_i` by the preceding motion. `reciprocal_pairing` is
wrench–twist power. A link–link or link–object contact is one helical pair interaction.
Actuation is the `Perturbation`/`Bu` drive on the medium; an observation is a receiver face of
phases, rates and contact readings; control cadence and held commands are `Clock` material.
The [simulator boundary](../../docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#robotics-and-simulation-boundary)
keeps Isaac Sim's descriptors as the exterior chart of this object. Knot and game navigation
use the same chain, contact kernel and transport-word laws with their own admitted moves.

## Field geometry: a fixed machine whose phases carry the source

[definition; agent-inferred] The HNN's sites are generators, not source cells. A declared finite
family of `SituatedScrew` sites with admitted pairs forms the machine. Its size is a model
choice and is independent of source and response length. `GeometricFieldSpec` is built from
that family: junctions are generator sites, arcs are admitted pairs, and each arc's
`ExactWavePhaseTransport` comes from the generators' rational phases. The inference from
Brandon's direction is the rotor identity above: context is the machine's phase state, and
material is reused at every phase.

[definition; agent-inferred] An ordered source passage enters through a boundary port. The
existing `IncidentEncoder` columns remain that port's chart from exterior symbol to port
current. Occurrence `k` is received at the generators' phases after `k` admitted steps, so site
`g` accumulates the phase-carried current

```text
m_g = Σ_k Ĝ_g(k)⁻¹ E(u_k),   with chart phase and winding of g retained,
M_gh(δ) = Σ_k ⟨Ĝ_g(k)E(u_k) | Ĝ_h(k+δ)E(u_{k+δ})⟩   pair relation at relative offset δ.
```

These are the helical moments of the source. `HelicalMomentReuse` and the quadratic moment
condensation already own their exact compression, ordered words and ambient fibre. Pair
moments at relative offsets are the source's menu; BPE's adjacent pair is offset one. Each
generator advances by its own declared or inferred rate, including zero, and several rates
supply several grains concurrently. The exterior codec unit does not define a native clock:
a Unicode position is the order of a passage through a port, and the rate at which that
passage advances a generator is material. Message parts, reply joins and recorded provenance
remain in `IncidentPreparation` and bind by phase offset instead of `slot_rows`.

[definition; agent-inferred] A response position is a receiving phase. The same receiver reads
the refined joint state transported to phase `j`, `y_j=ρ_R(Ĝ(j)q)`. `response_port_start` becomes
a phase offset with the same fixed-binding guarantee in generation, comparison and rest.
Response extent is a received termination face of the same field along the axial coordinate,
not a separate material whose rows scale with the aperture. Whole-section joint refinement,
one global `q/b`, the normal law, atomic publication and frozen producing cuts are unchanged;
they run over the machine's sites. The producing return traverses the same `Ĝ` operands in
reverse. Saved models with the ring layout keep their recorded binding.

[definition; agent-inferred] Learned material is the generators' rates and advances, initial
configurations and relative phases, contact material `D_f`, the reaction/reflection `M/D`, and
the boundary charts `E/R`. The normal law `H=H₀+Σw f f*`, `B=B₀+Σw t f*` is unchanged; its
features include the pair jet `(Δ,Q,DQ)` and its covector returns through
`PairQuadranceJet::pullback`. Discrete structure, such as which pairs are admitted and which
rational rates close, is inferred by closure tests over observed pairs. Compatible
configurations remain a plural family. The pre-reflection/terminal-observation distinction of
the earlier synthesis governs what each observation constrains.

[definition] A generator with no participation at the present phase retains its material,
initial configuration, phase and winding. `standing.rs` and `Foundation/Standing.lean` are its
law; re-engagement at a later phase is a present reconstruction, and `receiver_release` owns
the released boundary current. "Key-like" means the configuration and phase at which a retained
pair closes for the requested receiver.

## Retained and corrected from the earlier synthesis

[established-bounded; source-inspected] Retained: standing/memory and the dormant-direction
derivation; existential, robust and expected quantifiers; open-loop action versus feedback
policy; the pre-reflection formation port; the storage-rate law and its indefinite-`G` caveat;
permutation entropy versus heat; the simulator interface table; the Flash correction
(`Horizon.smith` exists); issue ownership of #16/#18/#61.

[definition] Corrected: the action relation is typed by the unit above. `z` is a family of
helical pair interactions with their media; `T_a` is their driven medium evolution composed
with phase stepping; `a` is a `Perturbation`/`Bu` word or a policy over receiver faces. The
statements that a finite permutation is "not a universal helix codec", that the rotor
conventions are "not generic helical periodicity laws" and that "key-like" names "no new
computational primitive" are replaced by the identifications above. No wrapper type is
introduced: the unit composes `ScrewPair`, `PairQuadranceJet`, `ContactFace`, `Medium` and
`HolonicInteraction`.

## Formal work: audit and return

[established-bounded; source-inspected] The Lean tree has 1,349 files and about 473,000 lines,
with no `sorry` or project axiom found by search. From the September 19 exact-algebra wave
(`5bb2cdbe`) through `73ff9950`, 141 native source files changed against 7 Lean files:
`ScrewGeometry`, the `AccumulatedNormalResponse` prior bound, three Computation modules
(adjoint normalization, constitutive circulation, cultivation charts) and two import files.
The existing `HolonicAdjointNormalization` does cover the
reverse-order adjoint, normalized face, order preservation and the joint held pullback used
by the incident field. The formal side had no statement joining the pair jet to the contact
face, no phase-carried transport or reflected-return law, and its default target omitted the
interaction and standing owners.

[proved-derived; formal-checked] This return adds
[`Transport/HelicalPairInteraction.lean`](../../formal/elementary-holonics/ElementaryHolonics/Transport/HelicalPairInteraction.lean)
with fifteen theorems, standard axioms only, and imports it with `HolonicInteraction`,
`HolonicChain` and `ContinuingTube` from `Framework/Dynamics`; `Framework/Core` now imports
`ReceiverRelease` and `Standing`. `bash tools/lean_check.sh ElementaryHolonics.Framework`
passes at 9,196 jobs.

[open] Formal obligations owed by this design, owned by #62:

1. Proper-rotation recharting and axis extraction of a screw. Rust has exact controls; Lean
   has translation covariance only.
2. The serial chain: ordered finite motions, Jacobian column as the recharted generator, and
   the revolute/prismatic rows.
3. `RationalPhase` chart/lifted winding and `closes_after`, joined to `phaseTransport`.
4. The stepped machine as a `TransportWord`/`ReceiverHistoryCompression` instance, so
   `E_next T=U E` covers phase-carried material with its retained winding.
5. The helical moment as the compressed source span: the accumulation law, its receiver
   decoder and ambient fibre, joined to `HolonicQuadraticMomentCondensation`.
6. Standing of a dormant generator: a `StandingLaw` instance whose future separator is a
   later phase.
7. The incident reaction `Φ(s,c)=s⊕c⊕(c⊗s)` with pair-jet features: its complex variation
   stated at the operands the native return uses.
8. Existing lifts #33, #34 and #54 keep their scopes.

Lean verifies the mathematics; native cultivation and inference remain outside it. Each native
packet below lands with its formal counterpart or names the obligation it leaves.

## Construction packets for the next campaign

[definition; agent-inferred] In dependency order, with disjoint owner paths:

| Packet | Owner paths | Return | Issue |
|---|---|---|---|
| 1. Pair contact | `holonic-engine/src/holonic_interaction.rs` and a `helical` submodule; `relational-geometry/src/screw.rs` unchanged | `ContactFace`/`MediumContact`/`HolonicInteraction` declared from a `ScrewPair` and its jet, with declared `D_f`, weight and `Clock`; exact tests mirror each Lean theorem | #28, #48 |
| 2. Serial chain | `holonic-engine/src/holonic_chain.rs` consumer of packet 1 | Ordered `SituatedScrew` chain: finite motion product, recharted Jacobian columns, per-pair contacts, revolute/prismatic rows, a planar closure control | #27 |
| 3. Machine geometry | `holonics-hna/src/native/field_geometry.rs`, `field_session/{incidence,incident_preparation,incident_application}.rs`; a new `examples/support/` machine spec | `GeometricFieldSpec` from a generator family; phase-carried source moments; receiving phases; pair-receiver participation with axial term and jet pullback; legacy ring layout preserved for saved models | #17 |
| 4. Material and closure inference | `body/field/{formation,incident}.rs`, `field_session/native_source.rs`, `identity_atlas`, `GeneratorInference` consumers | Pair-jet features in the existing normal law; closure inference of rates, configurations and admitted pairs; plural families retained | #17, #49 |
| 5. Standing and release | `holonics-hna` binding of `standing.rs` and `receiver_release.rs` | A dormant generator retained through an inactive interval and re-engaged at a later phase with its future separator | #17 |
| 6. Economy | `receiver_history_compression`, `hardware_cover`, `section_partition` | Moment accumulation as the compact source-span statistic; stepped words by generator power; resident state independent of source length; the actual launch realization reported | #18, #61 |
| 7. Episodes | `alpha/exposure.rs`, `examples/athena_exposure_field.rs` | The recorded Athena, mathematical and code episodes on the machine; a motor-chart control that infers chain phases for a requested receiving face, without a simulator | #16 |
| 8. Formal | `formal/elementary-holonics/ElementaryHolonics/{Geometry,Transport,Foundation}` | The obligations listed above | #62 |

[definition] The campaign's evidence is the same generating material consumed at a changed
phase, source and receiver; resident state and cost that do not scale with source length; a
dormant generator re-engaged; exact agreement of the jet pullback with rational differences;
and the inspected episode consequences with their complete residual. Character agreement on
one learned response remains a diagnostic.

[established-bounded; source-inspected] Verification for this return: the Lean receipts in
`docs/VERIFICATION_RECEIPTS.tsv`, link checks over the edited documents and `git diff --check`.
Native behavior keeps its existing receipts.
