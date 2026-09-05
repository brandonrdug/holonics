# HNP0: joined sections return local constitutive current with successor and rebase laws

**Date:** 2026-09-04. **Campaign:** HNP0 under the production-HNA plan.
**Starting revision:** `28a3051f`. **Scope:** first finite constitutive binding and numerical passage;
not a general production learner, completed locality compiler or useful-model result.

## The concrete binding

[definition] The first chart has a finite native site population, a constitutive cross-section
`M`, diagonal local admittance `a`, and a diagonal source duality `g`. The sections `x` and `y`
belong to actual occurrences joined through `AddressedPassage.Join`; they are not a prefix test
or a pair of observation identifiers. The local law is:

```text
pair current:       J(i,j) = M(i,j) x(j)
transported field:  t(i)   = sum_j J(i,j)
target difference:  r(i)   = y(i) - t(i)
returned current:   c(i)   = a(i) r(i)
source covector:    v(j)   = g(j) x(j)
local deposit:      dM(i,j)= c(i) v(j)
successor:         M'     = M + dM
```

[definition] This specializes the standing physical-crossing, duality and additive factorized
return laws; it is a new explicit composition, not a claim that a normalized secant learner was
already implemented. `a` and `g` are constitutive chart data carried by the admitted native
interaction. Their origin is not a count, a scalar reward, an expected answer or a shape match.
This finite diagonal chart is not offered as the only admissible reaction or update species.
There is no convergence, loss-monotonicity, generalization or physical-calibration theorem here.

## Returned formal consequences

[proved-derived; formal-checked] The existing owner
`formal/elementary-holonics/ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean`
now contains `ConstitutiveSectionReturn` and proves:

- `physicalCrossing_current`: this current is the existing `AddressedPhysicalCrossing` return;
  that crossing retains the actual joined occurrence and both exterior boundary maps.
- `recurrent_successor`: the concrete `present` and `advanceMorphology` instantiate
  `FiniteRecurrentOperation`; carrier, changed morphology and full chronology are its successor.
- `successor_eq_of_zero_factor`: an unaffected coefficient is unchanged.
- `successor_conduct`: for every later query `z`,
  `M'z = Mz + c * sum_j(v(j) z(j))`. This is operator execution, not replay of the exposure's y.
- `successor_conduct_eq_of_annihilates`: a later probe is unchanged when its complete coupling
  to the returned covector vanishes. A remote address or one zero output is not this hypothesis.
- `absent_relation_founded`: a zero coefficient becomes a nonzero relation when the actual
  returned factor product is nonzero.
- `next_difference_uses_successor`: the next return includes the prior deposited transport.
- `successor_rebase`, `recurrent_successor_rebase`, `recurrent_pairCurrent_rebase`: a site-chart
  equivalence transports current, emission, the complete successor and its chronology. The joining
  occurrence remains the same. This proved rebase family is finite site reindexing, not every
  possible nonlinear or physical coordinate change.
- `conduct_extend`, `successor_extend`: silent optional-site extension preserves old conduct and
  update. `new_site_contact_is_used` distinguishes actual acquisition from mere zero padding.
- `equal_scalar_distinct_deposits`: equal squared scalar readings can induce distinct oriented
  deposits. A scalar-loss-only replacement therefore loses a required distinction.

[definition] Coefficient support and one-query annihilation are not universal future-cone
soundness. HNP2 still owes the dependency/continuation hypotheses and their runtime realization.
The arbitrary linearized-route adjoint remains the standing `SituatedReturnedDifference` law;
this binding neither silently promotes a finite withdrawal to that theorem nor proves every
nonlinear reaction compatible with this particular diagonal chart.

## Numerical binding to the existing resident owner

[established-bounded; source-inspected] `operative_return.rs::enact_section_contact` composes
the already available resident laws. It is internal apparatus, not a new public learning mode:

| Mathematical passage | Resident realization |
|---|---|
| Transported source `Mx` | Already-produced native section supplied by the owning operation |
| `Mx - y` | `record_scale` by exact -1, then `record_re_entry` |
| Signed constitutive differential | `record_hadamard` with the admitted local admittance |
| Source covector | `record_hadamard` with the admitted source-duality section |
| Additive factors | Existing `deposit_from_material`, transposed seal and carried covector |
| Subsequent factor transport | Existing resident contractions through `U(Vx)` |

[definition] The existing deposit's explicit dyadic readout `eta = 2^-learning_shift` remains
reported: its effective formal admittance is `eta * a`. It is not claimed to be derived from
material, and it is not a new optimizer. Interval/factor sealing retains the existing numerical
projection boundary; the point-valued controls below do not establish exact real arithmetic for
arbitrary enclosures. No host array computes a differential or factor. The numeric helper checks
shapes and grains before allocation, but cannot certify the causal joining by those checks.

## HNP0 occurrence/application contract

[definition] The first admissible non-prefix occurrence is a pair of native carrier sections
whose source and target occurrences have a retained common boundary. Each section has its
declared chart and source occurrence; the owning interaction supplies the connection and native
constitutive admittance/duality. The session must construct and retain this joining from the
actual carrier owners before invoking the numeric helper. A JSON `joined: true`, equal identifier,
equal digest, same width, lexical match or caller-provided current is not admission.

[definition] Applications deliver material/causal interaction at supported ports. They may not
specify an internal target population from an expected answer, manufacture a new morphology edge,
or treat a process status as current. Source/target numerical sections must be produced through
their admitted carrier/codec laws. Unrelated, stale, differently charted or outside-domain material
returns the corresponding obstruction unless an actual transport/admission extension exists.

[definition] HNP1 must bind those owned occurrences to the live session, join the actual local
return into its successor, and exercise it on native model material. The internal helper added
here has no production caller yet. The old prefix interface and SKE's declared-family restrictions
are unchanged. This explicit limitation is why the two numerical tests are HNP0 apparatus evidence,
not a claim that HNP1 or the general public training interface has passed.

## Verification

[established-bounded; process-audit] The focused Lean owner checks and the live
`lake build ElementaryHolonics.Computation.HolonicQuantumTransport` build succeeded (3,775 jobs).
Printed new theorem dependencies contain only `propext`, `Classical.choice` and `Quot.sound`;
there is no new axiom or `sorry`. Existing unrelated dependency warnings remain.

[established-bounded; measured] On the standing CUDA apparatus:
`cargo test -p holonic-engine --lib joined_section_contact -- --ignored --nocapture`
passed both new tests, zero failures. The productive numerical control uses:

```text
x = [1,2,0], Mx = [3,4], y = [5,1]
a = [1/2,2], g = [1,1/2,3], eta = 1/2
dM = [[1/2,1/2,0],[-3,-3,0]]
later z = [2,1,99] -> dM z = [3/2,-9]
matched y = Mx -> zero later delta
```

The intermediate section-read counter is unchanged across the return; only the final test receiver
reads the later result. The refusal control changes an input grain and observes refusal before
new resident allocation or readout. These are bounded numerical/ownership controls, not an actual
world-interaction or qualitative model trial.

## Owners and continuation

- Formal: `ConstitutiveSectionReturn` in the existing oriented-site transport owner.
- Rust: `crates/holonic-engine/src/holonic_intelligence/operative_return.rs`,
  `SectionContactMaterial`, `enact_section_contact` and the two `joined_section_contact` tests.
- Resident primitives: `resident_section/{surface_shapes,surface_passage}.rs` and the existing
  `deposit_from_material`/`OverlayAtom` owners; no new CUDA kernel was needed.

[definition] HNP0 closes at this concrete finite binding and its explicit application contract.
Next is HNP1's live owned-occurrence admission and non-prefix local development, not another
proof-only fixture, another trainer, or a re-run of the unchanged HNA/SKE campaign.
