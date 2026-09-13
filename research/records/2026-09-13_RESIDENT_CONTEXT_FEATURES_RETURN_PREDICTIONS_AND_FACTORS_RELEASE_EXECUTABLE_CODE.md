# Resident context features return predictions and factors release executable code

[definition] September 13, 2026; active-goal implementation after `567b89e5`. This increment
binds a pre-target preparation to source/condition features and the existing normal predictor,
then releases executable code from returned factor graphs. The roadmap remains the construction
order. These are concrete returns toward the full Athena/Hephaestus objective, not a replacement
of that objective by the bounded cases below.

## The missing port and the shared implementation

[established-bounded; source-inspected] The earlier normal owner already accumulated
`H=I+sum uu*` and `B=sum vu*`, fit a bounded numerical operator on the GPU, and retained its
normal residual and source uncertainty. Its layout required three equally sized complex ports.
The bilinear contact already constructed source/condition products, but did not expose them as
an arbitrary-width normal input. A Rust-only width change would have disagreed with the CUDA
layout. A compatibility span alone would not have supplied the fitted predictor.

[established-bounded; implemented-exact] `ResidentConstitutiveSection::bilinear_features`
now joins corresponding rows of two retained source sections and returns their exact direct
and mixed complex coordinates. It uses the existing bilinear-source kernel and carries both
comparands; it does not broadcast, form a Cartesian product, select a source centre or read
intermediate numbers on the host. A transferred feature packet retains both direct ports before
the mixed products, with its consuming chart kept by the predictor.

[established-bounded; implemented-exact] `NormalSourceChart` distinguishes `Wave { roots }`
from `Features { source_complex }`. `ResidentNormalMaterial::found_features` admits arbitrary
positive feature counts and rectangular outputs. Read, receive, section reception, numerical
refinement and rest use that explicit extent. The legacy wave constructor and v1 rest retain
their three-port meanings; feature rest uses v2. A feature material refuses the old wave-seed
binding instead of being padded or silently treated as three equal ports. The compatibility
`roots()` reading is zero for a non-wave chart; `source_chart()` and `source_complex()` identify
its actual domain.

[established-bounded; implemented-exact] CUDA fit, moment increment, report construction,
direct execution, section execution and numerical refinement share their arithmetic cores.
Legacy wrappers supply their original three-port count. The direct source count and the
legacy tensor-target root count are separate operands. Cold geometry/witness validation
reuses the same normal-state decoder and does not replay observations.

## The public prediction release

[definition] `construct-predictor` binds two existing resident linear restrictions A and C of
one preparation x. `predict-section` computes `s=A x`, `h=C x`, then
`u=(s,h,h tensor s)` before any target arrives. `observe-section` addresses a later observed
target to its retained feature/forecast cut. The same normal owner receives that observation;
a successful native return consumes the pending handle even if subsequent observer readout
fails, preventing a retry from depositing it twice. Read-only forecasts remain available.

[established-bounded; computational-witness] The public stream test and
[executable trial](../experiments/contextual_prediction_release/README.md) supply four actual
comparison pairs in a declared two-source/one-condition complex chart. The native predictor
starts at zero, infers its coefficients from these pairs, and produces new whole sections.
The trial checks 32 new-input queries at h=±1, plus h=0 and h=i. Both restrictions and all
mixed features stay resident between the common preparation and the output receiver.

[proved-derived] With columns ordered `(s0,s1,h,h*s0,h*s1)`, the four comparisons give

```
H = [[3,0,0,0,0], [0,3,0,0,0], [0,0,5,2,2], [0,0,2,3,0], [0,0,2,0,3]]
B = [[1,1,0,1,-1], [1,1,0,-1,1]].
```

`(B/3) H=B`; H is positive definite because it is I plus source outer products. Hence the
unique normal-reference coefficient matrix is `P=B/3`. It returns

`y0=(s0+s1+h*(s0-s1))/3`, `y1=(s0+s1-h*(s0-s1))/3`.

The native numerical realization encloses these reference values; the reference coefficients
are not copied into its material. The 2/3 gain at h=±1 is the consequence of the unit prior and
four comparisons, not an unexplained output normalization.

[proved-derived] For the specified exchange targets `(2,-1)` / `(-1,2)`, that regularized
normal predictor has squared task discrepancy `5/9`. This is distinct from its small numerical
normal-reference enclosure. The retained trial now reports the full oriented prediction/target
difference as a separate observer reading, without rerunning or changing the measured timings.
The source/condition response has been fitted; exact target reconstruction is not claimed from
this prior-biased return. The coupled reaction additionally has its explicit baseline current c.

[proved-derived] This fitted family separates a shared mode and a difference mode:
`y0+y1=2(s0+s1)/3`, `y0-y1=2h(s0-s1)/3`. Relative to its h=1 action, the comparison map R(h)
fixes the shared mode and multiplies the difference mode by h. Therefore
`R(h2) R(h1)=R(h2*h1)`, by these two coordinates. At -1 it exchanges the two source coordinates;
at i it rotates the complex difference mode by a quarter turn; at zero that receiver loses the
difference mode. Zero is singular, not an identity. Equal source coordinates make this particular
output insensitive to h without establishing global source equality. This is an available modal
construction for subsequent compilation; neither a topological nor physical-force identity is
inferred merely from the matrix.

[established-bounded; computational-witness] At new source `(2,-1)` the checked reference
faces are `(4/3,-2/3)`, `(-2/3,4/3)`, `(1/3,1/3)` and `(1/3+i,1/3-i)` under h=1,-1,0,i.
Each native joint enclosure contains its reference face with radius below 1/1000. The first
pre-target forecast is zero. Observing a consumed prediction again refuses. The supplied
restrictions are explicit experimental maps; deriving and attaching contextual restrictions
from continuing field/dialogue incidence remains the next native application work.

## Executable Hephaestus functions

[established-bounded; implemented-exact] `emit-rust` serializes a retained `BilinearRealization`
through `native/mathematical/code.rs`. It preserves left/right factors, ordered products and the
receiver particular, with exact integer/rational constants and checked input extents. A linear
operator supplies its existing unit right port. No dense tensor expansion, task-label algorithm,
new solver engine or runtime compiler enters HNN execution. The target program uses borrowed
inputs and shared product values correctly across multiple receivers.

[established-bounded; computational-witness] The public trial infers a complex-product factor
circuit, changes its retained receiver, and constructs a fifth-power recurrence action. It
emits and compiles all three functions. On new rational inputs, generated code and native
application agree exactly: `337/120,-3/4`; `247/120,427/120`; and `-11/12,-5/12`. The changed
native receiver uses the retained product without recomputing it. This returns code generation
for these exact operator classes. Exporting a still-plural output law with its constraints,
contextual source editing, effects/state and a whole continuing model have further specified
contracts; this function return does not silently complete them.

## Measurements, repairs and checks

[established-bounded; measured] The first 54-request native process took 0.370711386 s including
its fresh resource observer. The final 56-request run adds the zero/quarter-turn checks and took
0.490512954 s. Its 32 measured section requests have median 486.5 microseconds; count, summed
interval and each raw cost are in the result. A section here has two complex output components.
The first query is excluded from that request-body population. Source/operator setup, delivery,
process startup and target build/execution have separately retained costs.

[established-bounded; measured] The target's initial offline build took 1.256040056 s including
its observer; the repeated build took 0.379642481 s. The final target child ran all three calls
and shape checks in the child interval recorded in `result.json`; its approximately 20 ms outer
measurement also includes the Python observer. It is not per-function latency. CPU/max-RSS
receipts and native carrier census remain distinct from GPU-context memory and physical energy.
The CUDA driver cache was populated by the native tests. Initial changed-PTX loading dominated
the first test process; it is not hidden inside a claimed submillisecond cold-start time.

[established-bounded; process-audit] The first broad native run exposed width/report regressions:
one helper passed the explicit count through the legacy tripling wrapper, and the generic direct
return wrote its report into the prior-forecast buffers. The source audit also corrected the
legacy tensor-target count and retained old H/B before increments. These were repaired in the
shared cores, then the affected tests passed. An over-broad delegated formatting command changed
unrelated files; the full diff was preserved under `.local/recovery/`, unrelated files restored
from the clean tracked baseline, and incidental formatting removed from affected wave consumers.

[established-bounded; process-audit] Checks returned:

- Engine and HNN library checks, plus the public workbench build.
- 18 focused CUDA engine checks: normal accumulation, complex/nondyadic and source enclosures,
  generic widths 2/5, rectangular outputs, refinement, legacy/generic rest, section atomicity,
  tensor targets and joined rational feature rows.
- 17 CUDA HNN checks: the new contextual section, existing mathematical/operator/family consumers,
  normal emission, delayed comparison, interruption/re-entry and rest.
- Exterior execution of all three generated Rust functions and all 34 trial reference faces.
- The cold complex source-energy validation and code receiver's incompatible-linear-chart test.

The focused native command was:

```sh
cargo test -p holonic-engine -p holonics-hna --lib -- --ignored --test-threads=1 normal::direct::tests normal::direct::section::tests normal::direct::rest::tests normal::direct::refine::tests material_transport::normal::tests joined_rows_preserve_complex_rational_sources native::mathematical::tests native::normal_wave::tests
```

The cold checks used the same packages with filters `normal::direct::rest::tests` and
`native::mathematical::code::tests` without `--ignored`. The public build/run recipe and retained
responses are in the experiment README. No Lean source changed or Lean result is newly claimed.

[definition] The next coupled binding consumes the fitted law as
`eta=M_s a+M_h h+M_mix(h tensor a)`, `a=(c-p,c,p)`, `v=c+eta`, through the existing wave/joint
owners. It must carry the actual condition/current section and material frame, then use the
declared release/self-reception contract. The generic predictor is a productive mathematical
consumer and a reusable owner; it does not replace that coupled binding. Compiling changing
programme conduct, inspected Athena text/code tasks, mathematical-session durability and wider
parameterized/stateful code release remain in the active goal. No unchanged broad corpus run
is restarted to stand in for these operations.
