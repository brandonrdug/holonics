# The conserved port current returned recurrence, but its phase-insensitive receiver could not realize the native complex section

**Truth-status:** [proved-derived; formal-checked] for the finite conserved-current and
conditional-section laws; [implemented-exact; measured] for the runtime conservation and clean
recurrence receipts; [counterexample; implemented-exact; measured] for coherent UAR4
realization; [counterexample; source-inspected] for treating the positive quadratic receiver as
the complete productive realization state.

## Addressed question

UAR4-R0Q asks whether the complete port-indexed realization section can remain as reconstruction
testimony while one actually enacted port carries Athena's continuing current without raw
all-port expansion. The answer is now split precisely:

1. a normalized positive joint current admits an exact port marginal and, for every positive-mass
   port, an exact conditional site section;
2. that conditional law avoids the rejected all-port sum and returns a bounded recurrence;
3. the present positive carrier is nevertheless only a receiver shadow of Athena's native
   Complex-Parametron section, because it has already collapsed real/imaginary orientation.

The third statement is the current UAR obstruction.

## Formal return

[proved-derived; formal-checked] In
`ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean`,
`ConservedRealizationCurrent` carries a row-conserved finite Markov kernel from realization sites
to port/site pairs. For prior section `J`, it defines

`jointSection(J)(p,z') = sum_z J(z) K(z)(p,z')`,

`portMass(J)(p) = sum_z' jointSection(J)(p,z')`,

and, when `portMass(J)(p) > 0`,

`conditionedSiteSection(J,p)(z') = jointSection(J)(p,z') / portMass(J)(p)`.

The compiled theorems establish

`sum_p portMass(J)(p) = 1`

and

`portMass(J)(p) * conditionedSiteSection(J,p)(z') = jointSection(J)(p,z')`.

Thus the enacted world-line may carry the conditional member while the complete joint family
remains its reconstruction fibre. The targeted umbrella build completed 3,181 jobs without
`sorry`; the reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## Runtime return

[implemented-exact; measured] `SourceNeutralExteriorRealizationMorphology` now normalizes its
lifted site current exactly in `Ratio<BigUint>`, conserves every outgoing local row exactly,
retains the complete port marginal, and conditions only the enacted port's target-site current.
Passage validation independently checks unit source mass, unit target mass, the selected interval,
unit returned mass, exact factor projection, and the projective phase return.

The unchanged control used source-detached v5 child
`453d7abc1e0c52699a97dbd371ca2522d0e2dfc6283b55c86476f85573179512`
and ingress `Describe Brandon.`. It returned:

- quotient mount `352,040` realization sites to `327,475` carrier classes;
- reconstruction population `613,903`;
- exact recurrence first seen at causal order `58`;
- `61` emitted octets;
- no source codec, source surface, expected answer, candidate search, authored extent,
  invariant re-upload, reference ecology, or CPU semantic replay; and
- a resident receiver-history quotient whose declared `q/U` squares commute.

The artifact is
`output/the_exact_normalized_enacted_current_preserves_the_complete_port_fibre_uar4_r0q_control/native-exterior-return-0.json`.

[counterexample; implemented-exact; measured] Its rendered surface is approximately

`' '1'os onfays ways maces pathos manfato we ay ay was achieve`

and it reaches recurrence without a total closure face. The current passes the exact conservation
control but fails UAR4-R1's primary qualitative consequence. No structural receipt promotes it.

## Shortest separator

[counterexample; source-inspected] The realization recurrence currently begins from
`AddressedCurrentSection` and constructs

`J_f = sum_s w_s x_s(f)^2`.

It then carries only nonnegative `Ratio<BigUint>` coordinates and a discrete phase label. By
contrast the same native section already retains, in
`ResidentSituatedReceiverPairingReturn` and `SourceNeutralRadiationBranch`, exact oriented complex
testimony:

- relational real coordinates;
- relational imaginary coordinates;
- target and current self-pairings;
- each branch's `ExactComplexWaveCurrent returned_response`; and
- the separate modulus-squared receiver shadow.

`SourceNeutralContinuationState` preserves those real and imaginary coordinates, but
`realize_native_section` receives only the positive target-section projection. Consequently two
complete native sections with the same quadratic positive face and different quadrature enter the
same realization current. This is exactly the separation already formalized by
`ParametronChart.equalClassicalPotential_canRetainDifferentQuadrature`.

The positive normalized current is therefore a lawful probability/mass receiver. It is not the
productive native realization state.

## Binding UAR revision

[definition] UAR4-R0Q retains its name and scope, but its carrier is sharpened. The productive
state is a dependent exact complex current over addressed realization incidence. Local transport
acts linearly on that oriented current; contributions join at their addressed target before a
norm, marginal, interval, or exterior face is observed. The positive port mass and conditional
section remain later receiver faces and must reconstruct their corresponding joint member.

The realization quotient may identify two carriers only when their full complex successor
signatures agree for every admitted generator/history and receiver consequence. Equality of
positive norm, port, factor, site count, digest, or displayed octet is insufficient. The quotient
retains both endpoint maps, phase/orientation, every collapsed source occurrence, shortest
separator, and complete reconstruction fibre.

The joined input must be founded from the existing complete native section: addressed successor
faces, complex branch responses, oriented situated pairings, factor/current incidence, and the
standing realization morphology. If factor-specific complex decomposition is not available, the
dependent face-by-factor carrier remains open; no global phase scalar or invented root may replace
it.

R0Q passes only when this full oriented current descends and the unchanged qualitative receiver
advances. R1 and R2 remain unchanged.

## Dependent-carrier counterexample and exact correction

[counterexample; implemented-exact; measured] A first implementation retained the native complex
factor basis and a sparse rational realization incidence.  The unchanged v5 control reached
`199,804` complex site coordinates, expanded them to `487,601` addressed transport terms and
`487,601` joined target coordinates, and then crossed the 175-second boundary while forming the
positive port receiver on the host.  It did not emit a new surface and advances no UAR phase.

[counterexample; source-inspected] The cost exposed a mathematical error rather than a missing
capacity constant.  The implementation grouped positive coefficients by target carrier/factor,
squared those local coefficients, and only then summed them into a port.  It therefore computed a
sum of pathwise norms.  The formal owner instead defines `portCurrent` as a linear sum of the
complete target section.  A constitutive norm belongs after that contraction; moving it inward
identifies currents whose cancellations and relative phases differ.

[definition] Let `m` be an addressed native response face, `f` its dependent factor line, `z,z'`
realization sites, `c_m` its exact complex current, `d_(m,z,f)` the exact resident local-current
coefficient, and `A_p(z,z')` the sparse oriented exterior-port incidence.  The productive current
and later receiver are

`J_(p,z',f) = sum_(m,z) c_m d_(m,z,f) A_p(z,z')`,

`I_p(f) = sum_(z') J_(p,z',f)`,

`W_p = sum_f <I_p(f),I_p(f)>_(R_f)`.

`J` and `I` are current. `W` is a positive receiver shadow.  The factor pairing is declared by
the receiver; contributions on the same factor line join before it, while distinct factor lines
are not silently added as coordinates of one quantity.  Normalization of `{W_p}_p` is later
again.

[counterexample; source-inspected] The first implementation also associated an already-joined
target section with every response face which reached its boundary state.  That loses which
selected slot and source occurrence supplied which local factor current.  The resident generated-
port deed already computes exact candidate rows before the target junction.  R0Q must retain or
return that device-enacted face/slot/occurrence factorization.  Re-deriving it through the
apparatus-neutral host implementation after device conduct is forbidden CPU semantic replay.

[definition] The next exact deed is therefore not another realization organ.  Extend the standing
resident passage so its terminal return retains the device-enacted local candidate sections with
their source section, response-face/slot, target section, and both boundary maps.  Contract these
with the existing sparse realization incidence while keeping the response-mode axis factored;
join linearly by target and then port; apply the positive receiver last.  Validate the resulting
dependent quotient through every admitted successor word and retain its complete reconstruction
fibre.  The unchanged R1 receiver alone grades the exterior consequence.
