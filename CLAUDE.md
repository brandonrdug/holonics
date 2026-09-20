# Holonics — Claude's operating document

Holonics is Brandon's mathematical, physical and computational theory of everything, built as one
Rust + Lean + CUDA library. **HNN** (Holonic Neural Network) is the machinery, **Athena** its first
product, **Eros** the whole formative machine Athena lives inside. One human operator: Brandon. His
latest message governs. The repository is public; `.local/` is private.

Everything below is loaded into every Claude session and subagent. The mathematics here is the
implementation specification. It is never background to "the code".

## 1. The machine

An HNN is one continuing field: **a chain of interlinked tori**. Each torus carries circulating
phase modes; neighbouring tori overlap, and the shared volume is a **contact face** where currents
meet with friction, exchange energy and deposit heat. A **Holon** `|H⟩_F` is that field in a frame
`F`: a whole and a part at once, at every grain. Heads, layers, levels and time steps are charts of
the one object. A **receiver** `⟨r|` is another participating Holon with its own moving frame;
every readout, stored file and displayed image is a face `⟨r|H⟩` it receives. Plates and a
capacitating medium recur at every scale: ground/atmosphere, membrane/cytosol, neuron/neurochemistry.

```text
State            M = (K, Θ, x)        K oriented contact incidence · Θ constitutive material · x currents and modes
Output           y_F = ρ_F( b_H(x) )  b_H boundary current · ρ_F the receiver's reading
Transport        |H'⟩_F' = Ĝ_(F'←F)|H⟩_F           Interaction   C^c = I^c_ab A^a B^b
Unit             |source⟩ → H_int (standing medium) → H_pert (dynamic) → ⟨perspective|     a neck joins two media
Embedding        occurrence ↦ amplitude·e^{2πi q} on Tⁿ ; which tori link = K ; connection φ_ij on each contact
Sequence/time    helix: ξ=(ω,v), V_ξ(x)=ω×x+v, |H(s)⟩=exp(sξ̂)|H(0)⟩ ; ω=0 shift/SSM, v=0 periodic mode
Helical pair     Δ=x_a(s)−x_b(t), Q=⟨Δ|Δ⟩, DQ=(2Δ·v_a, −2Δ·v_b), D²Q keeps the Δ·a terms ; K=ω·ω', R=ω·v'+v·ω'
Attention        s_ij = β cos 2π(q_i − q_j − φ_ij),  a_i· = softmax over E_i (admitted contacts only)
                 T_F[Ψ] = Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G            (Re⟨Q_i,K_j⟩ is this cosine, amplitude-weighted)
Learning         δT = Σ a δ(UΨ) + Σ δa UΨ,   δa = J δs,  J = diag(a) − a aᵀ ; returned by the paired adjoint
                 cross-entropy covector q−p ; squared-probability covector J_p(q−p)
Native reaction  incoming = s + M·[s, c, c⊗s] ;  out = S_D(incoming, b) (scattering through D, interior b)
Normal law       H ← H + f f*,  B ← B + t f*,  W H = B          (statistics, never stored samples)
Generation       x(τ₀)=I_h(ξ), ∂_τ x = F_(Θ,K)(x,h,τ)  — whole-field refinement, never a token index
                 reference step  q' = q + κ sin 2πp,  p' = p − ∇V(q') ; implicit (I − λB)x* = (1−λ)h, dB=(dL)L+L(dL)
Decoding         receiver integrates the boundary along its cycles: A(x)=Σ ψ_i φ_i(x) ; text/image/sound are faces
Compression      E_next T = U E and D E = ρ, else keep the separator (ker E ⊄ ker E T) ; commensurate windings close:
                 a (p,q) torus knot is a finite recurrence ; identities of a configuration = kernel of its face map
Recursion        A_0=A, A_(n+1)=Φ⁻¹(A_n)∖A  first-arrival sets: fractal geometry at a fixed number of state axes
Tube             the object over time ; a tower is one frame of it ; a staircase its passage between grains/jet orders
```

**Why the big mathematics is here.** Hodge = which cycles are realized. RH = where spectral
landmarks sit (the `1/2` is a conservation of faces under a reflection). Complex Euler and
Navier–Stokes = how flux transports without and with dissipation. Iwasawa = the tower of grains.
The engine executes exactly these objects. Their conjectures are side quests; their objects are parts.
Expect commonalities between them and whatever you are building; find the owner and compose it.

**Notation.** Dirac kets/bras/brackets typed by frame; Einstein indices for Holons as tensors
(upper = ket port, lower = bra port, raise/lower only through a frame's metric); every expression
has a figure (oriented lines, vertices, loops). A sign is a passage: `−1 = e^{iπ}`, `i = e^{iπ/2}`.
A move between neighbouring blocks is an arrow (`A_↗`, `A_↘`), not an index pair. A constant
(`π`, `e`, `φ`, de Bruijn–Newman `Λ`) is a constraint mode; a float is one face of it. An abstract
expression is *unoriented* until causally framed. Full dialect: `docs/HOLONIC_NOTATION.md`.

## 2. Where it lives

| Part | Lean (`formal/elementary-holonics/ElementaryHolonics/`) | Rust (`crates/holonic-engine/src/` unless noted) | Resident on the card today |
|---|---|---|---|
| Linked toroidal carrier, contact cells | `Millennium/HolonicTorusKnots`, `Foundation/{Holon,HolonTensorLens}` | `simplicial`, `algebraic`, `analytic_field`, `traversible_chain`; reference `research/experiments/intrinsic_holonic_flow` | **No.** Native carrier is a generic section |
| Helix, helical pair, identities | `Geometry/{ScrewGeometry,TwoSidedIdentityAtlas}` | `crates/relational-geometry/src/screw.rs`, `identity_atlas` | **No** |
| Phase attention + variation | `Computation/{HolonicAdjointNormalization,AttentionModeCompression}` | `exponentiated_ratio/transport.rs::NormalizedKernel`; reference `research/experiments/connected_holonic_field` | Row-sectioned receiver, pullback, condition covector exist (Wave 11); not yet on a toroidal incidence |
| Contact, friction, energy | `Physics/{PhaseContactPassage,ReceiverStressEnergy,CoupledIncidence}` | `holonic_interaction`, `junction_law`, `neck`, `fold` | D-scattering and paired adjoint in `native_ecology/constitutive_fibre/field/` |
| Refinement and release | `Foundation/Holon.ofEvolution`, `Transport/ReceiverPotential` | `receiver_release`, `continuing_tube`, `jet_staircase` | One reaction+reflection pass; re-entry port exists |
| Receiver, decoding | `Foundation/Receiver`, `Transport/ChangingReceiver` | `receiver_atlas`, `docs/RECEIVER_HOLARCHY.md` | Unit-basis symbol selection: a text codec only |
| Closure, landmarks, compression | `Foundation/{ReceiverHistoryCompression,GeneratorModeQuotient,JointReceiverDescent}`, `Millennium/{LandmarksAndModuli,Farey,HolonicQuadraticMomentCondensation}` | `exact_linear/{contextual,kernel_modes}.rs`, `receiver_history_compression/`, `winding_inertia` | `field/internal_mode.rs`, `recurrent_condensation`; not bound to the session |
| Co-present cells on hardware | `Foundation/{SectionLayout,DeviceLaunchLaw}` | `hardware_cover`, `section_partition`, `crates/holonic-mount/src/{section_layout,launch_law}.rs` | **Not called by the field path** (#61) |

```text
crates/holonic-engine      exact library + native ecology + CUDA kernels (kernels/*.cuh, exact_resident_section.cu)
crates/holonics-hna        the HNN crate: src/native/{field_session.rs, field_session/shared.rs,
                           coupled_wave/body/field{,/section}.rs, mathematical.rs}, src/alpha/exposure.rs, src/stream.rs
crates/relational-geometry exact geometry (RatVec3, AffineMap3, screw, exact_analysis)
crates/holonic-{life,mount,body,abi,…}  lifecycle, CUDA mount/launch law, substrate
applications/holonics-workbench         CLI `holonics` (hna field-session …) ; applications/conversation-data  corpus packager
formal/elementary-holonics              ~1,350 Lean files: Millennium/ 1,004 (NS > 500, Hodge ~100), RH/ 140, Foundation, Physics, …
research/records/                       ~1,575 dated records; filenames are full-sentence titles = the cheapest index
research/experiments/ , research/papers/source/papers/{elementary-holon-generation,hnn-information-chemistry,…}
docs/                                   THE_MACHINE, HOLON, HNN_FORMULA, HELICAL_GEOMETRY, ARCHITECTURE_MAP (owner crosswalk),
                                        plans/THE_ROADMAP (order), plans/THE_ATHENA_ALPHA… (spec + field-session source map), canon/
CONSTRUCTION_STATE.md                   current position and next action
.local/                                 private: datasets/ (conversation corpus + exposure stream), evaluations/, artifacts/
~/Workspaces/laboratory                 frozen predecessor repository; Brandon's earlier reasoning lives there
```

The native crates name no torus, helix or knot anywhere. The object is realized in Lean,
`relational-geometry` and exterior reference experiments. **That gap is the work**, and it is never
evidence that the geometry is unrelated to the engine. Native code being generic linear algebra is
the thing being replaced, not the ontology.

## 3. Arithmetic and hardware are part of the mathematics

- **Exact, no floats on a deciding path.** Values are rationals or dyadic enclosures `centre ± radius`
  at a declared grain, on a signed 128-bit carrier. `rg -n '\bf32\b|\bf64\b' <files>` and account for
  every hit. Floats are fine for exterior plots and measured statistics.
- **Growth is answered by rebasing**: divide by the gcd, factor, change chart, take prime images with
  a certificate. Never widen a carrier or raise a ceiling. A refusal names its cause.
- **The card carries the current.** Region events that read shared immutable standing and write
  disjoint outputs commute, `Λ_e Λ_f = Λ_f Λ_e`: they are co-present. Certify the partition
  (`section_partition`), license placement by independence (`hardware_cover`), generate
  gather → shared operator → scatter (`SectionLayout`), launch with threads in bijection with cells
  (`launch_law`). A kernel that guards `blockIdx.x||threadIdx.x` and loops rows uses one lane of the
  card. Report cost as cells, lanes occupied/idle and service rounds `R = ceil(N/C)`. Admission of a
  device realization is `D∘K∘E = Λ` against the exact reference. Governing record:
  `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md`.
- **Lean is exterior verification.** It never runs inside cultivation or inference. Rust mirrors the
  formalized objects as a standard library; a formalized law gets its native owner.
- **Every value enters through its constructor**; wires and remounts re-validate; declared sizes are
  bounded before the work they size.

## 4. Working here

**Before planning anything**, say which part of §1 the task realizes and what the "resident" column
of §2 becomes. If the geometry does not appear in your description of the task, you have lost the
object. Then find what exists:

```bash
.agents/bin/prior-art 'prose name|LeanCamelCase|rust_snake_case|classical name'   # searches Lean, crates, docs, record titles
rg -n '<term>' docs/ARCHITECTURE_MAP.md                                          # owner crosswalk; search it, don't read it through
ls research/records | grep -i '<subject>'                                        # titles are sentences
gh issue list --state open ; gh issue view <n>                                    # itemized backlog, milestones = deliverable returns
```

Search the subject's own vocabulary, not the phrase that raised it; one hit is not the owner. Whether
machinery exists is answerable from the tree, so answer it from the tree. Most subjects Brandon
raises are already established here and he has usually said them before: recover them, and respond
from inside the framework.

**Decide and proceed.** Resolve choices from the mathematics, mark the sentence `[agent-inferred]`
with what it was inferred from, and carry on; Brandon corrects retroactively. Ask him only for a
choice the framework cannot determine. The strongest validation is execution against reality.

**Write documentation.** New documents, records and maps are wanted whenever they network the
mathematics to the implementation. Records go in `research/records/` as
`YYYY-MM-DD_FULL_SENTENCE_TITLE.md`; update `docs/ARCHITECTURE_MAP.md` when an owner changes; put the
context a task needs where the task is described (issue body, source map). State what a thing **is**,
its equation and where it lives. Claims carry one grade from `docs/canon/EPISTEMIC_GRADES.md`
(`[definition]`, `[project-postulate]`, `[proved-derived]`, `[established-bounded; …]`,
`[interpretation]`, `[agent-inferred]`).

**Report in the object's terms.** What was constructed or inferred, its equation, where it applies,
what it cost. No apology, self-blame, surprise at established subjects, or invented "walls".

**Build and check** (shell is fish: wrap pipelines in `bash -c '…'`; CUDA needs `PATH=/opt/cuda/bin:$PATH`):

```bash
cargo check -p holonic-engine --lib                                   # ~25 s warm; first CUDA build ~90 s+
cargo test  -p <crate> --lib <module::path>::                         # module scope
cargo test  -p holonic-engine -p holonics-hna -p relational-geometry --lib     # broad host run (~100 s)
flock .local/gpu.lock cargo test -p <crate> --lib <exact::test> -- --ignored --exact --test-threads=1   # device: one process at a time
bash tools/lean_check.sh [ElementaryHolonics.Framework.Geometry]      # Lean, with #print axioms on new theorems
cargo build -p holonics-workbench && target/debug/holonics --format jsonl hna field-session --source <spec.json> --input -
```

Append what you ran to `docs/VERIFICATION_RECEIPTS.tsv`; a receipt whose tree is unchanged is not
re-run. A timeout is an incomplete check. Commit and push coherent verified work on `main`; messages
end with `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`. Never `git restore`,
`checkout --`, `stash`, `reset`, `clean` or crate-wide `cargo fmt` in the shared tree. Preserve
unrelated local files. Conversation text from `.local/` never enters a commit, issue or log:
counts, schemas and timings only.

**Delegation.** At most three Opus 5 workers in parallel on disjoint owner paths, then one Sonnet 5
reviewer that spawns nothing; fewer when the work does not split; a join that consumes several
returns is sequential. Every worker prompt names the part of the machine it realizes, its issues,
its exact paths, the owners to start from, the governing records and the reference calculation to
match (`docs/WORKER_BRIEF.md` has the skeleton). The primary inspects the changed owner and its
consuming call, runs the one integrated broad run and the one serial device run, reconciles issues
and commits.

**Position.** Active: the HNN field session becoming the machine of §1 — #61 (regions across the
hardware cover), #17 (phase attention and refinement on a toroidal incidence, using the Wave 11
ports #57/#58), #16/#59 (real conversation episodes from the private exposure stream), #18, #19,
and #48/#49 (helical pair into the moment-compression and phase-closure owners). Deferred:
protein/biology runs; resident exact elimination (#50) has no HNN consumer. `CONSTRUCTION_STATE.md`
and `docs/plans/THE_ROADMAP.md` hold the live position and order; `AGENTS.md` is Astra's (Codex)
contract and holds Brandon's dated rulings.
