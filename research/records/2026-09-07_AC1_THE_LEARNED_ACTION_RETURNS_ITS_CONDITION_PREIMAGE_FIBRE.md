# AC1: the learned action returns its condition Preimage Fibre

[definition] Parent `6ef7bf9d`. The [conditional native action](2026-09-07_AC1_THE_MEASURED_CONDITION_FOUNDS_A_NATIVE_PHASE_ACTION.md)
now supplies a resident Preimage Fibre for conditions compatible with a fixed source and actual
later return. The inferred condition can enter a subsequent native operation. This is a local
construction within the declared learned relation, not recovery of an entire physical interior
or a new claim of useful conversation.

## The actual affine section

[definition] The existing source chart is `Phi(s,c) = s ⊕ c ⊕ (c ⊗ s)`. Let `R` be the represented
rational-linear relation in the realified source/receiving chart. The queried object is

```text
F(s,y;R) = { c | (Phi(s,c),y) belongs to R }.
```

`R` may be partial or have a vertical receiving fibre. No total function, selected condition,
or inverse of `R` is assumed. The source and observed return are already available exact current
views; the hidden condition is not an input to the query.

[proved-derived] Ordered echelon reduction defines a rational-linear map `P_R` whose kernel is
the row space `R`. Each elimination is `v -> v - (v_p/r_pp)*r_p`; composing these linear maps
leaves a unique remainder in the declared nonpivot coordinate complement. A vector has zero
remainder exactly when it belongs to `R`. The implementation's reduced numerator/denominator
representation changes neither that map nor its kernel.

[proved-derived] With `s,y` fixed, write

```text
v0 = (s,0,0,y),
L_s(c) = (0,c,c ⊗ s,0),
D_s(c) = P_R(L_s(c)),
b = -P_R(v0).
```

Then `F(s,y;R) = {c | D_s(c)=b}`. This follows from linearity and `ker(P_R)=R`. The construction
reduces through every original pivot, including vertical receiving directions. Omitting those
directions would impose conditions which the original receiver did not establish.

[definition] The kernel forms the graph of `D_s` from its condition-coordinate columns and
queries that graph at `b`, reusing the same native relation routines. A nonempty result is a
particular condition plus its complete free-direction span. A failure to inhabit the graph is
`OutsideRepresentedRelation`, with its exact residual. That names the boundary of this admitted
relation; it does not rule out different laws or unadmitted extensions of a partially known action.

## Native ownership and interface

[established-bounded; source-inspected] The existing owner exposes
`ResidentConstitutiveFibre::read_condition_preimage(source, observed)`. Its return,
`ResidentConditionPreimage`, owns the derived constraint graph, RHS and immutable condition
fibre. It neither copies nor changes the learned body. The original relation cut and source chart
remain explicit. `inspect_constraints` is a cold receiver of that derived evidence.

[definition] `ResidentConditionPreimage::current` supplies a uniquely supported condition to a
point-current consumer, whose hypothesis is checked on device. Plural conditions retain their
directions, and `read_differential_pairs` can expose a fixed receiver across that entire fibre.
The particular solution is a coordinate origin for the affine family, not a chosen actual cause.
No singleton condition or perfect inversion is required to return the fibre or a supported face.

[established-bounded; source-inspected] Source owners are
`constitutive_fibre/resident/preimage.rs`,
`resident_section/surface_passage.rs::record_condition_preimage`, and
`kernels/constitutive_condition_preimage.cuh::section_constitutive_condition_preimage`.
The kernel reuses `fibre_query`, `fibre_stage`, exact common denominators and normalization.
The original basis is read-only; all writable matrices are newly derived constraint evidence.
Pointness, positive denominators, shapes, same-surface placement and exact word/wide arithmetic
are checked. No host numerical value determines the inferred condition.

[definition] If the original relation has `W` real coordinates and the condition has `C`, the
derived graph uses `W+C` coordinates and the RHS has `W` coordinates plus a denominator.
Scratch is `W + 2*(W+C)` wide values; the mounted apparatus admits or refuses that representation.
The result uses the existing rational/fibre wire with target width `C`. This is a bounded dense
realization; it introduces no semantic width limit or claim of general scaling.

## Class receivers and source occurrences

[definition] Generic relation receivers now return `ConstitutiveDifferentialReading`, containing
the relation cut, status and an optional actual field source. A condition/class receiver has no
invented field occurrence. The field-specific conversion requires that source qualification;
the public text-codec consumer performs it explicitly. This completes the source/cut distinction
exposed by the earlier diagnostic failure without changing the numerical differential law.

## Actual native evidence

[established-bounded; measured] The updated public
[`native_conditioned_phase`](../../crates/holonic-engine/examples/native_conditioned_phase.rs)
example first develops the same local action from six native field observations. It then changes
the world's phase to `(-5+12i)/13` without providing that condition to the learner. Source `1-2i`
produces the actual native return `(19+22i)/13`. Those two currents alone enter the condition query.
The inferred fibre has particular `(-5/13,12/13)` and no free direction.

[established-bounded; measured] That resident condition enters a later operation on source `4+i`,
predicting `(-32+43i)/13` before the world produces its return. The actual native return agrees.
Condition inference performs one native deed with zero numerical section readout/egress and zero
ingress after the operands were mounted. The later action also performs zero numerical section
readout/egress, with four bytes of predecessor-edge metadata. The condition was not decoded and
remounted between those operations. The learned relation and its occurrence count are unchanged
by the Preimage Fibre query.

[established-bounded; measured] The portable
[return-preimage.json](2026-09-07_conditional_phase/return-preimage.json) retains the actual source,
return, inferred fibre, native constraint graph/RHS, model cut, subsequent prediction and complete
scoped census. Its whole-example clock reads 0.154 seconds. This includes the small teacher,
learner and cold diagnostics, and establishes no consumer text/audio throughput or power claim.
The report is research evidence, not a new independently executable model checkpoint.

[established-bounded; measured] Six native preimage controls cover:

- inference of an unprovided phase from an actual native field response, followed by new conduct;
- the fully free condition fibre at zero source/zero return and a distinct outside-relation case;
- original vertical receiving directions, and an earlier fibre preserved after further learning;
- two complex conditions with free directions but a fixed differential receiver;
- wrong source chart, foreign surface, nonpositive denominator and carrier overflow without
  modifying learned standing; and
- the represented domain of a partially known action, without inventing missing directions.

[established-bounded; process-audit] The final constitutive suite passed **100 tests**, zero
failures, in 19.72 seconds (`/tmp/athena-condition-preimage-final-tests.log`):

```sh
cargo test -p holonic-engine --lib native_ecology::constitutive_fibre -- --ignored --test-threads=1
```

The public whole-fibre text-codec control also passed after the receiver-metadata separation
(`/tmp/athena-condition-preimage-sdk-test.log`). The public phase example built and ran; its
numerical path was unchanged by that later metadata separation. No Lean source/build, retired
database, corpus replay or new conversation training run was involved.

## Remaining continuation

[definition] The compatible condition family is now inferred from an actual source/return,
rather than supplied as an answer label. The next composition carries such families as continuing
native standing and derives their supported forward consequences without choosing a member.
For fixed new source `s'`, the joint relation

```text
{ (c,y') | c in F and (Phi(s',c),y') in R }
```

is again affine. Its condition projection must retain any unsupported domain; its output
projection must preserve the joint Preimage Fibre. A fixed class face can conduct while the
condition remains plural. The unique-condition continuation and fixed differential are already
returned above; a general resident forward image of the whole family remains open.

[open] The actual conversation model still needs its situated conditions and action families
bound to real material. The preimage construction does not turn arbitrary codeword ratios into
English meaning, identify an external source implementation, or cure the earlier corpus-wide
linear relation by assertion. Athena-alpha remains unattained. Mac porting and acoustic generator
studies can consume this extension through the shared native owner and existing Metal elimination
helpers; no Apple execution is claimed here.
