# Sequence, fold and reaction current make the causal thought chain concrete

## Direct ruling and construction scope

[project-postulate] Brandon's later September 10 direction makes sequence-to-fold and biochemical kinetics keystone construction domains for HNN, with these chains considered as potential models of literal causal chains of thought. The preceding two-domain conformation example was a local component, not the boundary of that programme. This return adds actual sequence-conditioned folding and mechanochemical kinetics, and revises the existing Athena handoff. Native AC implementation remains paused.

[definition] The common operative chain is source occurrence → admitted incidence/current → constitutive reaction → emission and successor → next occurrence. A causal thought chain retains those actual joins and the organization that changes later conduct. A verbal trace is one possible receiver. Molecular and text/acoustic sources have their own codec and physical charts; the common relation does not route all language through a protein grid or make source ordinals latent identities.

## Sequence to a complete finite fold family

[definition] `sequence_folding.py` constructs an anchored six-site FCC chain. The first two positions are (0,0,0) and (1,1,0); the remaining four positions extend by one of the twelve signed/permuted (1,1,0) steps. All sites are distinct and adjacent squared distances are two. This is a declared three-dimensional lattice chart with triangular faces and held first bond, not an atomistic representation inferred from a letter name.

[definition] The two fixed inputs are HHPHPH and HPHHPH, both four hydrophobic and two polar sites. The exterior chemical chart assigns contact energy E_s(q)/ε=-C_s(q), where C counts nonbonded HH nearest-neighbor contacts. It does not use an expected fold, a ground-state label or a per-sequence lookup to choose the interaction. The H/P contact construction follows a classical physical-model precedent, while this source explicitly chooses its FCC geometry and anchoring. [Lau and Dill, 1989](https://pubs.acs.org/doi/10.1021/ma00200a030).

[established-bounded; implemented-exact] Exhaustive construction returns 12,711 anchored conformations and 79,476 directed legal local moves in one connected component. A local move relocates one of the four mobile sites by one FCC hop while preserving bonds and exclusion. These are discrete conformational passages; the render does not supply an unproved continuous swept-volume molecular trajectory.

[proved-derived; implemented-exact] For each sequence the energy minimum has five HH contacts and sixteen coordinate conformations. Their common degeneracy does not identify their geometry or dynamics. At b=exp(βε)=2, the exact partition functions are 33,391 and 35,911, so the minimum-energy family masses are 512/33391 and 512/35911. At b=16 they are 16777216/34477731 and 16777216/37404291. The environment parameter changes the returned distribution. These counts include the declared anchored receiver frame; they are not an unqualified count of distinct unframed protein folds.

[established-bounded; implemented-exact] The shortest legal paths from the held straight chain to the respective minimum-energy families have sixteen and twenty local moves. The displayed representatives are endpoints of these actual positive-weight paths. Path selection is an explicit receiver of the retained family, not a claim that the shortest path is the typical thermal history or an HNN inference algorithm.

## Actual kinetics, not an endpoint optimizer

[definition] There are 4×12=48 elementary fold proposals. For a legal move q→q′,

    P_s(q,q′) = (1/48) min(1, 2^(C_s(q′)-C_s(q))),
    P_s(q,q)  = 1 - Σ_(q′≠q) P_s(q,q′).

Rejected proposals remain in the source state. The thermal parameter is βε=log 2. This is a declared discrete kinetic chart using the Metropolis acceptance relation; it is not represented as calibrated continuous-time biochemical rates. [Original Metropolis et al. report](https://www.osti.gov/biblio/4390578).

[proved-derived; implemented-exact] Every row is nonnegative and sums to one. The geometric proposal is reversible, and the exact weight satisfies 2^C(q) P(q,q′)=2^C(q′) P(q′,q). Thus the normalized Gibbs weights are stationary. Complete populations are propagated deterministically with integer numerators over a common denominator power; no random sampling chooses the result. D=1536 is an encoding denominator derived from 48 proposals and the contact-energy range, not the physical clock or a native capacity.

[counterexample; computational-witness] Two actual states both have contact count one, but their complete next-bin rows, including self loops, are:

    state A: Pr(C′=1)=1;
    state B: Pr(C′=1)=47/48, Pr(C′=2)=1/48.

For the linear aggregation q onto contact bins, qδ_A=qδ_B but qPᵀδ_A≠qPᵀδ_B. Consequently no state-independent exact bin generator U can satisfy qPᵀ=Uq on the full admitted family. This does not make the energy receiver useless; it states precisely which continuation it cannot replace.

## Conformation and ligand occupancy change admissible moves

[definition] `sequence_kinetics.py` joins the fold population to a terminal ligand. A binding direction d is admitted exactly when r_5+d is an unoccupied FCC site. The chemical source keeps free states (q) and bound states (q,d). A bound fold proposal is admitted only when the carried ligand remains collision-free in the target conformation. Thus occupancy changes actual geometric admissibility, in addition to any sequence-dependent rate change.

[definition] Each joint clock chooses the fold or chemistry passage with equal weight. Within a free chemical passage, a binding attempt has weight one half and chooses uniformly among twelve directions. Within a bound chemical passage, unbinding and catalytic release each have weight one quarter, with the remaining half held. Hence joint-clock binding weight is 1/48 per open direction, while unbinding and catalysis each have weight 1/8. The complete integer transition denominator is 3072. These clock choices and substrate bath are declared source conditions.

[established-bounded; implemented-exact] In the displayed geometry, the otherwise legal hop of site index four by (1,1,0) ends at r_5+(0,1,-1). Its joint-clock weight is 1/96 when unoccupied and zero with that ligand bound. The rejected mass stays at the held bound state. This is a geometric consequence of the partner's occupancy; no “correct fold” score selects it.

[proved-derived; implemented-exact] The source tracks complete probability mass and joint first moments of catalytic product and net substrate drawn. At every state and step, drawn=product+bound mass, and total free plus bound mass is one. Product is an expected turnover count and can exceed one for a reusable enzyme. The fixed sequences return different expected product counts; at step 24,

    2^-26 < E[P_24 | HHPHPH] - E[P_24 | HPHHPH] < 2^-25.

The full exact fraction and intermediate source moments are retained. A small scalar output difference does not identify the joint kinetic states.

[counterexample; computational-witness] Actual binding current is Σ_q E_q O(q)/48, where O is the number of open directions. Replacing the joint free population by total free mass times the unconditional conformation-average accessibility gives E_total Σ_q p_q O(q)/48. The exact difference is nonzero in both returned runs. The reference code uses the same units on both sides; an extra factor twelve in an initial diagnostic was repaired before acceptance.

## Formal reaction and the joint-state separator

[proved-derived; formal-checked] `Physics/ReactionCurrent.lean` constructs the source of E+S⇄C→E+P from the stoichiometric columns and mass-action currents (k_on a(q) E S, k_off C, k_cat C). It derives conservation of E+C and S+C+P and nonnegative reaction currents under nonnegative concentrations and rates. The finite ligand model instantiates accessibility by the actual open-direction population; it is not left as a scored fold label.

[proved-derived; formal-checked] The same owner gives two joint fold/free-bound populations with equal fold marginals and equal free total. Their binding fluxes are a/2 and b/2, with exact difference (b-a)/2; they are unequal for a≠b. This is the elementary law behind the measured closure failure. The source fold/occupancy association must remain available to the next reaction.

[definition] The count ledger with a supplied substrate bath is the exterior counterpart of the closed stoichiometric source. A calibrated molecular realization additionally supplies its actual chemistry, units, solvent and barrier/rate law. Those are construction inputs and further realization work, not reasons to exclude sequence-to-fold or biochemical kinetics from HNN foundations.

[proved-derived; implemented-exact] The enzyme-state projection has stationary weights 12·2^C(q) for a free conformation and 2^C(q) for each admitted bound direction. Folding edges inherit detailed balance; binding at 1/48 and combined release at 1/4 give the same weighted flow. Yet the catalytic channel still emits product. The exact stationary product currents are 108911/1939800 and 116891/2084280 per joint clock. Stationary body occupancy therefore does not mean absent operation or absent emitted flux.

[proved-derived; formal-checked] `reactionSource_labeled_emission_distinguishes` shows that unbinding and catalytic release can have the same enzyme/complex source (+1,-1) and distinct substrate/product sources. 

[proved-derived; implemented-exact] The kinetic code retains this through a marked moment: μ′=Tμ and ν′=Tν+T_cat μ. Equivalently, a marked operator T(z)=T_noncat+zT_cat retains product history through its generating function; ν is its derivative at z=1. Keeping only the unmarked body transition would lose that receiver. HNN therefore returns emission as well as successor, not just a body-state endomorphism.

## The HNN handoff: actual owners and remaining binding

[established-bounded; source-inspected] The architecture, Athena, Soulkiller, interoperability and retraction/current-plan sources were recovered before revising the handoff. Current normal-wave source actuation borrows a section, retains before/after joined currents and predecessor/successor fibres, and changes held current under fixed material. `advance` carries the actual joined successor. `receive` is an actual next-current observation, while `develop_section` develops from supplied section pairs and preserves current occurrences. These effects remain distinct.

[definition] The common construction is sequence/source → situated organization → kinetic conduct → emitted result plus retained successor. For chemistry, the exterior chart can supply actual molecular constraints and reaction observations. For text/acoustics, source association and local condition come through their existing current charts. `SymbolCurrentChart` currently mounts one row per supplied symbol, but a source occurrence may have multiple views and parts; that implementation does not establish a universal position/row bijection. Equal spelling does not identify equal native occurrence.

[definition] The updated Athena blueprint carries three concrete obligations into its existing next packet:

1. Preserve the declared many-to-many exposure/codec association with actual source/current and producing-joint ownership; compose existing address/return owners before inventing a wrapper. A digest alone is not the relation.
2. Bind the returned comparison to the actual producing joint and material cut, then expose the later conduct changed by that return. An observation of an actual next current retains the existing `receive` contract; an addressed correction uses the separate producing-comparison passage still being constructed.
3. Admit kinetic or local-neighborhood composition only through explicit source, condition and output maps. Preserve occupancy, contact, clock and joint correlation required by the chosen future receiver. A histogram, mean fold or matched output scalar cannot silently supply those maps.

[conditional] Exact kinetic condensation owes qPᵀ=Uq for the admitted generators and receiver factorization; continuous-rate charts owe the corresponding qK=K̄q law. Failed closure retains the separating fibre or declared defect. Operator-word/factorized representations can preserve a full future family without archiving every raw state. The exhaustive reference population is exterior evidence, not the proposed consumer-hardware inference algorithm.

[project-postulate] A literal operative thought chain is the caused sequence of joins and changes in the body that makes the next operation possible. Its emitted verbal description is not the mechanism. Sequence-to-fold and reaction kinetics are constructive instances of that common problem. They inform the authorized AC work without inserting a universal protein simulator or restarting the paused implementation.

## Verification and artifacts

[definition] Final checked commands, diagrams and source-preservation receipts are recorded below after execution. This return does not change native cultivation/inference code.

[established-bounded; formal-checked; implemented-exact] Final verification returned:

- `sequence_folding.py`: exhaustive anchored conformations, legal graph, exact stochastic rows, detailed balance, population normalization, equilibrium families and positive-weight shortest histories.
- `sequence_kinetics.py`: both complete joint evolutions through 24 clocks with per-state catalyst/substrate/product moment identities. The source keeps geometric bound-state rejection and separates expected product count from probability.
- `verify_sequence.py`: all conformations and rows; genuine aggregated-bin non-lumpability; exact reaction moments, marginal-closure and stationary marked-current checks; the actual ligand-blocked hop; and eleven geometric/current source packets. All comparisons passed after review repairs to the energy sign, true bin aggregation and consistent kinetic-current units.
- `bash tools/lean_check.sh ElementaryHolonics.Framework.Physics`: passed with `ReactionCurrent` conservation, joint-marginal separator and labeled-emission results. No native operation or runtime proof assistant was introduced.
- Typst returned 28 numbered plates without overflow continuation. The new pages were rendered with Poppler and visually inspected, including the bound-site annotation, reaction source matrix and HNN producing-return diagram.
- `animate_sequence.py` returned three computed cuts of the selected legal history; decoded APNG frames match the source RGB renders exactly. No interpolated physical motion is inserted.

[definition] [Current paper](../papers/rendered/hnn-information-chemistry.pdf), [fold-history animation](../papers/rendered/receiver-engraving/sequence-fold-history.png), [new plates](../papers/source/papers/hnn-information-chemistry/sequence-plates.typ), and [revised Athena handoff](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md). Earlier woven, knot and architecture material is preserved. Native AC remains paused; this return is the authorized mathematical/physical construction and implementation-plan clarification.
