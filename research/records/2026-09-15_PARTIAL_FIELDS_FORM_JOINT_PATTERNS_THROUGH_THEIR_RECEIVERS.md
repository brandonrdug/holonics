# Partial fields form joint patterns through their receivers

[project-postulate] Brandon's “Continue Athena” retains the same application and his diffusion/
embroidery correction: an interacting field forms a jointly received pattern through actual
source regions and constraints. The implementation must expose that generating relation, its
learning and outputs. A task label, copied history or another wrapper is not that relation.

## Source and receiving construction

[definition] Let `N` be the declared number of request and context regions, `V` the codec
alphabet size and `s=3 ceil(VN/3)` the complex incoming extent. Padding aligns with the existing
three-component field-node chart. The new `JointRegions` source constructs

\[
 x\in\mathbb C^s,\qquad
 h=[1,a_1,\ldots,a_N,o_1,\ldots,o_N]\in\mathbb C^{1+2N},\qquad
 \phi=[x,h,h\otimes x].
\]

[definition] `a_i` is activity, `o_i` observation, each an exact zero/one chart coordinate.
Observed request/context symbols are unit-basis currents in their regions of `x`; active
unobserved regions use an explicitly chosen zero latent seed. An unobserved region, an inactive
region and an observed numerical zero are distinct. These masks describe supplied source and
receiver geometry, not a semantic classification or an inferred topology.

[established-bounded; source-inspected] The same native neighborhood and operative field execute

\[
 r=R_M(x,h)=A_M(h)x+c_M(h),\qquad
 u=x+r,\qquad (w,b^+)={\cal S}_D(u,b),\qquad
 y=P g+Qw,\quad Q=I-P.
\]

[definition] `g` is the original given incoming section and `P` the fixed complex-coordinate
receiver projection for that occurrence. Supplied partial regions are held; requested missing
regions are free. Context/out-of-response regions are not emitted by the application decoder.
The model commits its raw joint scattering `(w,b^+)`. Its observed face `y` is an affine
receiver, not a replacement internal state or a claim that the field has Dirichlet clamps.
Text symbols are one codec of the simultaneously received section.

[established-bounded; source-inspected] `NativeFieldSession` prepares these operands and
`NativeCoupledBody::generate_received_field` consumes them. `ResidentHeldSection` is the shared
native affine receiver; it retains the given enclosure and mask, and computes the received
section on the device. If both supplied and generated branches participate, their enclosing
radii add conservatively. An exact alias to the retained given section keeps the single source
radius. No semantic float, point substitution or host evaluation of the learned operator enters
this path. Source flags and exterior symbol decoding retain their codec role.

## Learning follows the received face

[definition] For an observed target `t`, embed its requested prefix into the full output
covector with zeros outside the observed extent. The model target covector is

\[
 g_w=Q^*(t-y)=Q(t-w),\qquad
 (g_u,g_b)=(D{\cal S}_D)^*(g_w,g_{b^+}).
\]

[definition] The existing dyadic step factor multiplies that covector. A boundary-only target
has `g_{b^+}=0`; a full joint target may observe internal coordinates too. The mask acts before
the complete producing adjoint. It does **not** mask `g_u` afterward: a given/context input
can affect a free output through the scattering. Internal covectors also survive the adjoint.
The complete relevant `g_u` reaches the producing local reaction's parameter response; D uses
its existing material return. The D/M that produced the observation remain its derivative
owners even if a different comparison has since updated the live model.

[established-bounded; measured] The native test compares this masked target path against the
exact `PairedJunctionLinearization` reference. It includes a full joint target with every
visible boundary coordinate held and a nonzero internal target; the complete pullback remains
nonzero and agrees with the reference. An agent-written intermediate incorrectly masked the
input covector after the adjoint; integration removed that error before the passing run.

[definition] `P(t-g)` is separately reported as the target's disagreement with the fixed source.
A target restricted entirely to held boundary coordinates has zero D/M derivative; it consumes
its comparison without depositing the model's own output into normal statistics. Free-region
targets may still update material using observed inputs. This is a fixed-receiver differential;
it does not implement a learned derivative of `P`.

## Native owners and saved continuation

[established-bounded; source-inspected] The change extends these existing owners:

| Operation | Source |
|---|---|
| Held receiving section, bound and rest | `holonic-engine/.../normal/direct/held_section.rs`; `normal_held_section.cuh` |
| Masked/prefix target before the paired adjoint | `field/junction/operative/source/reflection_target.rs`; `field_reflection_target.cuh` |
| Raw/received generation, D/M response and producing witnesses | `holonics-hna/src/native/coupled_wave/body/field.rs` |
| Joint region source, variable receiving extent and delayed targets | `holonics-hna/src/native/field_session.rs` |
| Stream, output-delivery recovery and CLI | Existing `HnaStream::pump_field` and Workbench `hna field-session` |

[established-bounded; source-inspected] Field pending extension kind 3 retains the affine
receiver alongside producing field/reaction/input/output. Session wire version 2 adds each
pending response's receiving extent. Old field rest and session version 1 remain readable;
the legacy source chart remains the default for old specs. Receiver rest retains its actual
dyadic grain separately from the raw integer section encoding. Required immutable producing
witnesses are retained; no second mutable ecology or raw conversation archive is introduced.

## Application result and what it implies

[established-bounded; measured] The [application evidence](../experiments/athena_field/pattern/README.md)
returns 39/39 complete responses, separating **45/45 generated missing values** from **63/63
fixed supplied values**. The population includes withheld equal-color compositions, independently
supplied outer regions that disagree with the training pattern, and shorter output requests.
Development uses 97 actual targets over 24 distinct authored examples. The same 39 responses
pass while committing the raw field each time; its endpoint reopens exactly. No evaluation
target entered those continuing operations. The earlier trained version-1 text session still
returns `blue blue` for its retained correction request.

[established-bounded; source-inspected] The new chart has `1+2N` condition coordinates and
`s+(1+2N)+s(1+2N)` features, instead of materializing `V^m` categorical context combinations.
It puts the context values into the actual source. This is an explicit constitutive restriction,
not a commuting-quotient proof or exact compression of arbitrary old coefficients. At fixed
masks/D/M the implemented step is affine in `x,b`; nonlinearity from changed observation charts
or material must not be confused with already assembled content-dependent iterative diffusion.
The underlying formal normalized/current and material variations are reusable next construction
material, not newly absent theory.

[established-bounded; measured] Warm 96-target development takes 71.768705 seconds. Median
generation/update costs are 77,522 / 641,746.5 microseconds with 26,447,972 bytes peak native
section accounting. Resuming pending producing material peaks at 37,028,676 section bytes.
The resolved trained artifact is 6,170,290 bytes. These are debug-build, consumer-workstation
measurements of this 129-feature model, not a matched speedup over the different older task.
Dense normal statistics and the operative journal remain explicit costs.

[established-bounded; measured] Integration returned 171 native tests, 20 public/session tests,
two allocator-calibration tests, actual training/evaluation/reopen processes and old-session
compatibility. A first cold process failed in allocation calibration before model execution;
its record is retained. The repair retries only a demonstrably unstable calibration sample
and preserves errors after three failures. Warm success and deterministic retry tests establish
those scopes; no new cold-start reliability measurement is claimed.

[project-postulate] The next application construction continues from these usable partial
regions into content-dependent coupled refinement and broader complete sources. Recover and
compose the existing normalized field/current variations with this forward/adjoint owner,
keeping source constraints, phase, internal modes, output support and measured representation
costs together. Further development serves the same Athena consumer. The returned small
pattern population is evidence to retain, not a training loop to replay or a definition of
HNN's complete architecture.
