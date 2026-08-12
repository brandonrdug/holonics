# The contact face crosses the bond; conduct, not the codec, founds the section class

**Date:** 2026-08-12  
**Truth status:** `established-bounded`  
**Evidence:** `implemented-exact` in `soma/life/src/incidence_production.rs`,
`soma/life/src/material_incidence.rs`, `soma/life/src/causal_section.rs`, and the shared
`holonic_engine::cuda_refine` quotient; `computational-witness` in the passing host/device parity
tests and the compute-sanitizer-clean resident bounded grade form named in §3.  
**Provenance:** Brandon, 2026-08-12: *“allow this to now be the next item on the roadmap ... I
would like to proceed with construction and experimentation.”* The construction follows the
recurrent-section doctrine he had just ratified: material names remain codec and delivery lineage;
operation classes must be founded from exact consequences under interventions.  
**Band:** CONTACT FACE RETAINED / FACE DOES NOT GOVERN CLASS / SEVEN PRESENTATIONS / FOUR
CONDUCT BLOCKS / SAME OPERATION CROSSES THREE CODECS / SAME VALUE DIFFERENT LAW SEPARATES IN ONE
STEP / PORT REVERSAL SEPARATES IN ONE STEP / RECEIVER ABLATION ONLY COARSENS / SURFACE RENAMING
PRESERVES BLOCK SHAPE / COMPLETE FIBER RETURNED / NO REPRESENTATIVE SELECTED / EXTERIOR OPEN /
RESIDENT CUDA QUOTIENT / 34 DEVICE LAUNCHES / HOST SEMANTIC REPLAY FALSE / COMPUTE-SANITIZER ZERO
ERRORS / CORPUS CONDITIONING AND REMOUNT NOT YET RETURNED

---

## Present question

Can one bounded owner retain the different contact presentations of an information construction,
yet classify presentations only by their exact future conduct? The required result is stronger
than matching a value and weaker than discovering arithmetic from an unconditioned corpus. It must
show, on a declared finite ecology, that differently presented instances of one law share a stable
receiver/history class while a same-value instance of another law separates under a shortest
intervention.

## 1. The contact face now survives transport

`DeclaredContactFace` is the exterior lineage carried by a bond. Founding an incidence complex can
now receive one exact face for each admitted adjacent patch pair. Repeated contacts with equal
endpoints merge into one bond while retaining the union of their faces and the complete
multiplicity. Higher-grain bonds retain the union of the lower faces which caused their gluing or
crossing.

This field is not a reaction class. It does not enter the constitutive quotient. A source atlas may
call two contacts `factor`, `operand`, `callee-argument`, or `word-landmark`; the later behavioral
reader remains free to collapse different names or separate equal names. The field closes an
erasure seam without installing authored semantics.

`established-bounded [implemented-exact]`: the material-incidence test supplies `recruits` and
`conducts` on the same ordered endpoints. One bond returns both faces, multiplicity two, and an
exact faithful atlas receipt. Incidence-production tests require every returned higher-grain bond
to retain a nonempty face population.

## 2. A causal section is read by complete declared conduct

One `CausalSection` owns:

```text
(presentation identity, delivery lineage, oriented incidence complex,
 exact finite consequence states, root state).
```

Each state returns exact opaque observations for a common receiver family and exact successors for
the interventions available there. `CausalSectionEcology` takes ownership of the section
population and presents the resulting finite deterministic system to the pre-existing
receiver-exact compression law. Production has no host default: `read` requires a mounted
`CudaRefineExecutor` and enacts every observation/successor refinement through the generic resident
`claim_identities` quotient. Neither identity, lineage, surface, material kind, nor contact-face
name enters that system.

For roots `x` and `y`, the founded relation is exactly

```text
x ~_R y
  iff
for every admitted receiver <rho| and every admitted successor history gamma,
<rho| T_gamma |x> = <rho| T_gamma |y>.
```

The reading returns both the one-shot blocks and the stable conduct blocks. It also returns every
root preimage of a stable block as a `SectionReconstructionFiber`, every shortest distinguishing
history supplied by the compression owner, exact work populations, and the fact that the exterior
of the declared finite population remains open. It never chooses a representative.

## 3. The bounded experiment

The executable fixture
`soma/life/examples/the_operation_survives_the_codec.rs` supplied seven presentations:

| founded conduct | exterior presentations | root value |
|---|---|---:|
| sum | symbolic infix, function call, word presentation | 4 |
| product | symbolic infix, function call | 4 |
| left-minus-right | symbolic infix | 0 |
| right-minus-left | reversed-port infix | 0 |

Each presentation owned its own three-site, two-bond incidence chart and a four-state exact
consequence section over `(2,2)`, `(3,2)`, `(2,3)`, and `(3,3)`. The available interventions were
`raise-left` and `raise-right`; the receiver faces were `defined` and `value`. The driver used its
exterior law only to enact these world consequences. It supplied no operation name to the ecology.

The release run under CUDA compute-sanitizer deposited
`output/the_operation_survives_the_codec/causal-section-grade-dd936adfbc6e01645bee777f671c340d11de460e51d172c7038820f6cb67b5bb.form`
and returned:

- 7 presentations, 28 states, 14 retained contacts, 28 transitions, 56 observations, and a
  complete 378-pair state chart;
- one-shot root block sizes `[2,5]`, because value alone collapses sum with product and both
  difference hands;
- stable conduct block sizes `[1,1,2,3]`: three sum codecs in one complete fiber, two product
  codecs in one complete fiber, and the two noncommuting hands separated;
- the shortest sum/product separator `raise-left`, returning values 5 and 6;
- the shortest port-hand separator `raise-left`, returning values 1 and -1;
- one seven-member block after ablating the `value` receiver;
- the same stable block shape after a bijective renaming of every presented surface;
- all contact faces retained, no material-kind router, no selected reconstruction representative,
  and an explicitly open outside population.
- an NVIDIA GeForce RTX 4080 SUPER resident quotient, 34 exact launches, 1,024 threads per block,
  no host semantic replay, and `compute-sanitizer --tool memcheck` returning zero errors.

The first real launch found and repaired two defects in the previously ignored generic CUDA
quotient. A split `(class,key)` claim could SIMT-deadlock while a losing lane waited for a winning
lane in its own warp to publish the second word. It is now one atomic 64-bit `(u32 class,u32 key)`
claim; a 64-bit material key crosses as two exact face refinements. Release execution then exposed
raw CUDA argument pointers aimed at optimized-away temporaries. The launch now retains explicit
pointer-value locals for the whole call. These are repairs to the shared material-free quotient,
not section-specific kernels.

The exact commands were:

```text
flock /tmp/holonics-cargo.lock env PATH=/opt/cuda/bin:$PATH cargo test -q -p life causal_section -j 2
flock /tmp/holonics-cargo.lock env PATH=/opt/cuda/bin:$PATH cargo test -q -p life incidence_production -j 2
flock /tmp/holonics-cargo.lock env PATH=/opt/cuda/bin:$PATH cargo test -q -p life material_incidence -j 2
flock /tmp/holonics-cargo.lock env PATH=/opt/cuda/bin:$PATH cargo test -q -p holonic-engine the_quotient_is_one_law_on_both_charts -j 2 -- --ignored --nocapture
flock /tmp/holonics-cargo.lock env PATH=/opt/cuda/bin:$PATH cargo test -q -p life the_resident_quotient_returns_the_host_admission_reading_exactly -j 2 -- --ignored --nocapture
flock /tmp/holonics-cargo.lock env PATH=/opt/cuda/bin:$PATH cargo build -q -p life --release --example the_operation_survives_the_codec -j 2
compute-sanitizer --tool memcheck --error-exitcode=99 target/release/examples/the_operation_survives_the_codec
```

## 4. Why this is a section result rather than a surface result

The sum presentations share no common operator inscription and their bond-face populations differ.
The sum and product roots, by contrast, share the observed value `4`. Surface identity therefore
cannot explain the collapse, and one value cannot explain the separation. The returned partition
is precisely the stable successor-history partition of the declared consequence complex.

This is a bounded form of Information Chemistry: exterior contact faces are retained reactants;
receiver/history conduct founds the species visible to this receiver family; shortest separating
interventions are reaction assays; and each stable block is a reconstruction fiber rather than a
chosen lexical meaning.

## Owners

- `soma/life/src/incidence_production.rs` owns occurrences, bonds, higher-grain transport, and
  retained declared contact faces.
- `soma/life/src/material_incidence.rs` maps exact material contacts into those faces and audits
  face-preserving faithfulness.
- `soma/life/src/causal_section.rs` owns the finite section population and the carrier-neutral
  translation into behavioral compression.
- `crates/holonic-engine/src/receiver_exact_compression.rs` remains the sole semantic owner of
  stable finite receiver/history compression and shortest separating words.
- `crates/holonic-engine/src/cuda_refine.rs` and `kernels/refine_shell.cu` own the shared resident
  exact quotient; the section supplies material keys and grows no private device cabinet.
- `soma/life/examples/the_operation_survives_the_codec.rs` is the bounded exterior apparatus and
  deposits the complete grade form.

## What this does not establish

This construction does not infer the consequence graph or arithmetic laws from raw text. It does
not establish a general semantic embedding, an English grammar, an unrestricted operation
classifier, a spectral identification, or equivalence outside the two declared receivers and two
declared interventions. Its seven presentations are authored apparatus fixtures, not conditioned
corpus discoveries.

Most importantly, it does not yet return the authorized construction's final movement: condition
this same law through the repaired mixed-corpus path, detach the founding material, remount the
morphology, and demonstrate attributable conduct plus ablation. The bounded constitutive law and
its contact-preserving join now exist; corpus conditioning and recurrent return remain `open`.
