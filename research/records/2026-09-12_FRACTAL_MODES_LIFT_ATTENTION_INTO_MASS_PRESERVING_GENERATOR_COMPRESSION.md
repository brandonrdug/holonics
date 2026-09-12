# Fractal modes, entropic transport and mass-preserving generator compression

[project-postulate] Brandon's September 12 request joins the Transformer mathematics paper,
fractal latent reasoning and the Equational Theories Project to the existing composition and
information-chemistry drafts. Mode exclusion is to become productive compression mathematics,
with protein/DNA structures, surprise and receiver-relative code costs kept in the construction.
This return adds four formal owners and a reusable exact kernel-reduction application. It does
not change the construction order or replace the native recurrence with a proof assistant.

## 1. What the Transformer paper contributes, and what the lift repairs

[established-bounded; source-inspected] The reviewed source is Tai, Liu, Li and Chan,
[A Mathematical Explanation of Transformers, v2](https://arxiv.org/html/2510.03989v2),
April 12, 2026. The complete substantive PDF, including convolutional vision Transformers in
§6 and Appendices B–C, was read; the projection equations on page 10 and Appendix B on page 20
were also rendered and visually inspected. The local source is
`.local/scratch/2026-09-12-transformer-lift/2510.03989.pdf` (25 pages).

[established-bounded; source-inspected] The useful construction is a state field over token and
feature domains, Q/K/V integral operators, normalized nonlocal attention, reaction/nonlinearity,
constraint projection and sequential splitting. Its convolutional extension imposes relative
kernel structure and multiscale discretization. This recovers concrete operators behind
architecture names; its control objective does not itself develop the entropy/code-cost bridge.

[counterexample; formal-checked] Under the standard outward normal-cone convention, projection
of v onto C obeys `v-u ∈ N_C(u)`, not the reversed sign printed in Eq. 24. For `C=[0,∞)`,
`v=-1`, `u=0`, the normal is -1; +1 fails against the feasible point 1.
`Computation/NormalizationProjectionScope.projection_normal_sign` checks this exact separator.
The projected ReLU formula remains usable with the corrected inclusion.

[counterexample; formal-checked] Fixed mean and positive variance define a centered sphere,
not a convex constraint set. At the two-coordinate constant input `(0,0)`, both `(1,-1)` and
`(-1,1)` have mean zero and variance one, and every feasible vector has squared distance two.
Thus a unique normalized direction is not determined there.
`constant_input_retains_two_directions` proves this; `anisotropic_gain_changes_constraint_face`
also separates a common constraint surface from subsequent per-feature learned gains.

[established-bounded; source-inspected] Appendix B Eq. 72 substitutes σ₁ where its own preceding
α-dependent expression requires α. Eq. 37 omits the scale displayed earlier in Eq. 23, and
Eq. 54 uses a domain-length factor needing reconciliation with the preceding feature integral.
These require explicit parameter/measure maps when reproducing a discrete operator. Standard
featurewise gain/bias and the variance stabilizer also need their actual chart: cancellation
under ideal radial normalization is not automatically cancellation with a fixed epsilon.
Multihead output-projection blocks can be absorbed into value maps with the correct shapes;
their absence as a separate printed block is not by itself an obstruction. The authors leave
well-posedness/regularity and positional-encoding extensions open.

## 2. Attention is an entropic contact kernel, not an isolated subject

[definition] On an admitted source measure μ, let the oriented value already transported to
the receiver chart be v(i), and let `k(q,i)=exp(s(q,i))` on actual contact. Then

`A(q) = [∫ k(q,i) v(i) dμ(i)] / [∫ k(q,i) dμ(i)]`.

The numerator is a vector current; the denominator is partition mass. A mask specifies the
admitted source/contact population. Relative phase belongs in v and its transport, before
any scalar probability or intensity receiver. The normalized weights and the vector they
transport are different faces of this same operation.

[proved-derived; formal-checked] `Computation/AttentionModeCompression` identifies finite
softmax scores with the existing generator posterior at `J_i=-s_i/ln 2` and proves its
free-energy minimum. Composing `GeneratorInference.variational_gap_eq_kl_bits` gives

`F(p)=E_p[J]-H₂(p)`,

`F(p)-F(p*)=D_KL,₂(p || p*)`,   `p*_i=exp(s_i)/Σ_j exp(s_j)`.

Positive source masses are incorporated by replacing `s_i` with `s_i+ln μ_i`; zero-mass
ports are outside that positive logarithmic chart. Surprise is the resulting
`-log₂ p*_i`, and a reference-code cross-entropy is `H₂(p)+D_KL,₂(p||q)`. The vector current
and phase are not replaced by these scalars. In particular, this variational law for attention
weights does not assert that the whole state-dependent Q/K/V vector field is a gradient field.

[definition] The common typed construction has the following architecture specializations.
These are source/operator maps, not a claim that arbitrary architectures are interchangeable.

| Chart | Structure supplied to the common transport |
|---|---|
| Transformer | State-dependent contact kernel, Q/K score, V transport, head/output maps, residual and projection word |
| Convolution/CvT | Relative-position kernel sharing, spatial incidence and declared restriction/prolongation across scales |
| GNN | Actual sparse edge incidence and edge-conditioned message transport followed by node reaction |
| SSM | Retained internal state and causal transition/readout; fixed linear transitions unfold to convolution with the initial-state term |
| Selective SSM | Input-conditioned transitions whose ordered products generally cannot be replaced by one fixed convolution |
| Diffusion/reaction | A specified generator or scheduled family, source/score/drift law and boundary; stochastic charts additionally retain their admitted noise law |

[proved-derived; formal-checked] For a finite class map π on sources with a kernel constant on
each class, define `m_c=Σ_(πi=c) μ_i` and `j_c=Σ_(πi=c) μ_i v_i`. Then

`A(q) = [Σ_c k(q,c) j_c] / [Σ_c k(q,c) m_c]`.

`normalized_attention_exact` proves this for any real-module current, including paired complex
components. `weighted_summary_associative` makes `(mass,current)` the associative carrier;
`linear_summary_transport` commutes an arbitrary real linear value map through it. Normalizing
too early loses an operand: `((0+0)/2+4)/2=2`, but `(0+(0+4)/2)/2=1`.
`unweighted_mean_not_associative` now verifies that actual counterexample in Lean.

## 3. Exclusion, minimal linear modes and the future quotient

[definition] For source generators T and the declared family of future receivers R, the existing
agreement relation is `x~y iff ∀r,w, r(T_w x)=r(T_w y)`. This is a congruence under admitted
continuation, not an archive of the words actually experienced. In a linear chart its quotient
has invisible subspace `N=∩_(r,w) ker(r T_w)`. A representation q closes when every admitted
generator has a descended U with `q T_g=U_g q`. Generator functions and their linear coordinate
modes are related here by an explicit representation; they are not synonyms at every scope.

[proved-derived; formal-checked] `Foundation/GeneratorModeQuotient` composes the existing future
quotient with Gram and alternating-map laws. For real inner-product receiver space Q,

`det Gram(qv₁,…,qvₙ)=0 iff the received modes are linearly dependent`.

Every alternating volume map annihilates a dependent family; an independent family has at
most `dim Q` members. This is the algebraic exclusion of a redundant independent direction.
The existing fermionic CAR proves occupation exclusion in its antisymmetric physical chart;
the present result uses the shared exterior-algebra structure without imposing binary
occupation on every computational or semantic mode. Complex currents can be retained as real
modules, with the corresponding real, not silently complex, dimension.

[proved-derived; formal-checked] More importantly, the new owner proves a productive elimination:
if `q v*=Σ_i a_i q v_i`, then

`q(Σ_i c_i v_i + b v*) = q(Σ_i (c_i+b a_i) v_i)`.

Amplitude is incorporated into the retained coefficients. Given the generator descent square,
`eliminated_mode_every_future` proves that equality after every ordered admitted generator word.
Repeated occurrences and repeated application remain possible: doubling twice is not doubling
once. Exclusion therefore saves redundant representation without deleting multiplicity or motion.

[proved-derived] For a complete finite linear kernel K, any exact linear encoding/decoder
`K=D'E'` with r coordinates satisfies `rank K ≤ rank E' ≤ r`. A rank factorization `K=DE`
attains `r=rank K`. This proves the minimum number of linear coordinates for that complete
kernel, not a universal minimum bit length or minimum arithmetic circuit. When the receiver
family includes future actions, the same argument applies to its joint observation map; a
present-only K cannot certify an unseen future. The Rust construction below returns a
separator precisely when a requested future fails to descend.

[proved-derived; formal-checked] The existing generator-inference coarse-graining law supplies
the matching information operation: for a class c of descriptions,

`J̄(c) = -log₂ Σ_(πg=c) 2^(-J(g))`.

Class weights add before taking logarithms. Deleting duplicate descriptions without carrying
their mass changes inference. Conversely, changing spelling or splitting a description while
preserving its pushed-forward mass need not change inferred conduct. This joins the modal
quotient to code length through a defined measure, rather than identifying rank with entropy.

[definition] Receiver-relative optimal coding compares admitted executable descriptions,
shared decoder/standing, coefficients, residuals and required distinctions in a declared cost
chart. `ReceiverCodeCost` already transports a feasible minimum across an exact candidate/cost
equivalence and retains endpoint potentials and residuals under composition. Combining that
with modal elimination removes provably redundant coordinates before the code comparison.
A changed frame or cost chart can change the numerical optimum; the corresponding transport
law, not one privileged global bit counter, states what is preserved. No unrestricted
shortest-program algorithm follows from finite rank minimization.

## 4. Fractals are explicit scale mathematics

[established-bounded; source-inspected] The second source is Lai, Bao, Quinn and Gilpin,
[Fractal basins trap latent reasoning, v1](https://arxiv.org/html/2609.04963v1), submitted
September 4, 2026; the PDF header is dated September 7. The main text and supplemental methods
were read, including finite-time Lyapunov analysis, uncertainty exponents and the scale-free
versus slim-fractal distinction. Pages 4 and 11 were visually inspected. The local source is
`.local/scratch/2026-09-12-transformer-lift/2609.04963.pdf` (17 pages).

[established-bounded; source-inspected] Their experiments hold a model/problem/schedule fixed,
vary initial latents on two-dimensional orthonormal slices, and label 200×200 grids by the time
the decoded output stops changing. This is not latent-state convergence. The methods select
slices by success/cap criteria and use task-specific integration steps and caps. They report
basin entropy, uncertain-boundary scaling, finite-time sensitivity and saddles associated with
nearly correct answers. The supplement allows apparent fractal dimension to vary with scale.
These are useful measured regimes, not a theorem that all solving requires chaos or exhaustive
search. The modular linear-system example also admits polynomial Gaussian elimination.

[definition] A fractal generator here includes its restriction maps, composition order, scale
transport and boundary/separation law. The existing `Foundation/FractalPacking` already proves
Cantor children, positive sibling gaps, exact width `3⁻ⁿ` and different left/right word orders.
`BoundaryScalePassage`, `HigherDifferenceScaleDescent` and `GeneratorObservationScope` provide
the adjacent scope/scale machinery. Reusing those relations keeps fractals explicit, rather
than calling every recurring computation a fractal or founding another generic generator noun.

[proved-derived] The finite Cantor family demonstrates the two costs directly. Its two child
maps plus a depth parameter describe all depth-n cells without listing `2ⁿ` intervals. But
selecting an arbitrary one of `2ⁿ` separated cells with a fixed-length binary address needs at
least n bits: fewer than n bits supply fewer than `2ⁿ` codewords. If the receiver identifies
some cells, code their equivalence classes instead. Recursive family description and branch
information are therefore distinct operands of compression; self-similarity supplies reusable
structure without promising that every unresolved choice disappears.

[proved-derived; formal-checked] `Transport/AccumulatedReceiverDefect` compares actual fine and
coarse trajectories. With a step defect εₖ and nonnegative Lipschitz bound Lₖ it proves

`e_n ≤ e₀ ∏_(j<n) L_j + Σ_(k<n) ε_k ∏_(k<j<n) L_j`.

The triangle inequality gives `e_(k+1)≤L_k e_k+ε_k`; Mathlib's discrete Grönwall law expands it.
For exact closed summaries, ε=0 and equal initial faces remain equal. For approximate summaries,
later expansion can magnify earlier loss: `L=2`, `ε=1/8`, `e₀=0` gives `e₃≤7/8`.
This is the usable telephone-chain law. A measured local finite-time sensitivity in the fractal
paper does not automatically supply its uniform Lipschitz hypothesis.

## 5. Equational theories: the machinery inspected this time

[established-bounded; source-inspected] The inspected current
[Equational Theories Project](https://github.com/teorth/equational_theories) revision is
`1aec8a7acf223b7c56e4830977b6e90d4ef1924b`. The earlier September 10 review used
`bb5a9b5fe78c376ce1725529f235f8d574630b9f`. The proof mechanisms inspected now are
`MagmaLaw.lean`, `Completeness.lean`, substitution/evaluation in `FreeMagma`, opposite-algebra
duality in `MagmaOp`, and the finite/infinite separator in `InfModel.lean`. This is an explicit
dependency slice, not a claim to have read or rebuilt the entire large implication corpus.

[proved-standard; source-inspected] `derive` has Ax/Ref/Sym/Trans/Subst/Cong constructors.
`SubstEval` makes evaluation commute with substitution; `FreeMagmaWithLaws` quotients syntax by
derivable congruence, with the fork operation well-defined through Cong. Soundness and Birkhoff
completeness join semantic equality to derivation. Opposite-algebra duality reverses words and
the operation together; it does not make arbitrary execution orders equal.

[proved-standard; source-inspected] `InfModel.lean`, around lines 407–449 at this revision,
proves 3994⇒3588 for finite magmas using a finite image and the resulting inverse/bijection
argument, then gives an infinite natural-number parity/XOR countermodel. Finite dimension,
finite sampling and a finite carrier closed under its operation are distinct assumptions.
The four reviewed core law/completeness/substitution/duality files are unchanged from the
earlier pin; revisiting them recovers the actual mechanism rather than declaring new theory.

[definition] The Holonics lift is a typed/admissible composition congruence, extended with
measure/current, state and emitted receivers. The mass/current associativity theorem above
is an actual new formal consumer of this comparison. Dropping mass or reversing a noncommuting
word gives explicit failed equations; qT=Uq certifies the surviving rewrite scope. No ETP search,
Lean evaluation or law registry is inserted into HNN inference.

## 6. Molecular contact, folds and productive modes

[established-bounded; source-inspected] The relevant drafts are
`research/papers/source/papers/hnn-information-chemistry/main.typ`, `composition-atlas.typ`
and the sequence plates, together with the
[sequence/fold/kinetic return](2026-09-10_SEQUENCE_FOLD_AND_REACTION_CURRENT_MAKE_THE_CAUSAL_THOUGHT_CHAIN_CONCRETE.md).
Their linked-body example supplies actual opposite viscous contact forces, decaying relative
motion, heat and a finite boundary Laplacian. With `a=e^(-2t)`, its declared unit chart has
kinetic energy `2a²`, dissipated power `8a²` and accumulated heat `2(1-a²)`; their sum is two.
Thus knots/links do not supply friction by topology alone: the contact gap, normal reaction,
slip and constitutive law supply the physical current. Phase-bearing boundary transport and
heat remain separate outputs of that same body.

[established-bounded; source-inspected] The sequence construction retains 12,711 anchored FCC
conformations, sequence-dependent contact energies, actual legal moves and ligand occupancy.
Two equal-composition sequences have different partition functions and kinetic paths. Its
energy-bin aggregation fails the same qT=Uq square now used by the kernel compiler: two states
in bin C=1 have different next-bin masses. Binding also blocks an otherwise legal move through
actual occupied geometry. These are recovered source results, not rerun molecular experiments.

[proved-derived] A productive biochemical mode need not change stationary body occupancy.
The existing marked operator is `T(z)=T_noncat+z T_cat`; differentiating its transport at z=1
gives `μ'=Tμ`, `ν'=Tν+T_cat μ`. Thus the joint body/current carrier has block action
`[[T,0],[T_cat,T]]`. Any proposed reduction for this task must factor that marked action and
its product receiver, not merely T. This is directly the multi-current/source-action contract
of the new kernel owner. It connects reusable catalyst activity to emitted inference conduct
without defining cognition by body-state mutation.

[interpretation] Protein and DNA applications instantiate this construction with different
sequence/contact, torsion, pairing, solvent and boundary laws. The map is molecular
configuration/occupancy → admitted transition or rate generator → joint mode encoding →
extension, binding or emission receiver. Its preserved diagram is the marked generator
descent square; a same-summary pair with different measured extension or catalytic response
falsifies the proposed reduction. The FCC H/P source is not a DNA constitutive law. Published
[sequence-dependent single-DNA mechanics](https://www.nature.com/articles/nsb0499_346) remains
a relevant source comparison; this turn does not claim new calibrated DNA simulation results.

## 7. Reusable executable construction and measured work

[established-bounded; implemented-exact] New
`crates/holonic-engine/src/exact_linear/kernel_modes.rs` exports `KernelModeReduction`,
`KernelModeSummary`, `KernelModeAction` and `KernelModeError`. It composes the standing exact
rank-factorization and receiver-factorization owners. From a supplied nonnegative rational
kernel it derives `K=DE`, summarizes `E[μ, μv]`, and reads `D E[μ, μv]` before normalizing.
It stores immutable encoder/decoder standing and a non-cloned continuing modal current, not a
sequence of source events. Coordinates of the factorization may be signed; positivity belongs
to the supplied kernel/masses and the final admitted mass, not every basis coefficient.

[established-bounded; implemented-exact] Source transport compiles `UE=ET` or returns its actual
source-null separator. Value/phase transport acts on the current columns while retaining mass.
Both stage the next current before replacement. Wrong dimensions, absent positive receiver
mass and mismatched actual encoding frames are explicit errors. The frame check uses shared
immutable ownership, not a semantic name/hash. This is an exact mathematical builder/reference
API; this change adds no native CUDA operation or host-driven native semantic loop.

[established-bounded; computational-witness] The new
`crates/holonic-engine/examples/kernel_mode_compression.rs` supplies a four-query/six-source
kernel whose rank is derived as two. Its retained `(mass,real,imaginary)` rows are `(7,12,13)`
and `(6,9,12)`. All four decoded queries agree exactly with the full source contraction:

`(30/19,37/19)`, `(33/20,19/10)`, `(21/13,25/13)`, `(93/58,56/29)`.

Phase rotation gives `(-37/19,30/19)` on the first query. The source action 2I descends and
doubles mass/current even though the normalized face agrees. A new receiver distinguishing
the first two sources returns `(-1,1,0,0,0,0)` as an erased direction with nonzero reading;
an action scaling only the first source also fails closure with a concrete separator.

[established-bounded; computational-witness] The
[complete exact receipt](2026-09-12_kernel_mode_receipts/kernel-mode-compression.json) counts
72 full versus 24 reduced query multiplications, with eight normalization divisions each.
Packing and constructing the summary costs 48 multiplications separately. Rank-factorization
setup, allocation/runtime, decoder storage and physical/device costs are not included in those
query counts. The full query contraction is batched while the example reads reduced queries
sequentially; their dependency-span/residency counters are not a matched scheduling benchmark.
This is exact reuse of derived modes, not a claim of universal threefold execution speedup.

## Verification and integration

[established-bounded; process-audit] Under `leanprover/lean4:v4.33.0`,
`bash tools/lean_check.sh ElementaryHolonics.Framework.Computation` completed successfully
with all four new imports (8904 build jobs, many replayed). The
[focused terminal excerpt](2026-09-12_kernel_mode_receipts/formal-terminal.txt) retains the
new owners, printed axiom signatures and completion; the full local output is
`.local/scratch/2026-09-12-transformer-mode-framework.log`. The printed mode/defect proofs use
the standing `propext`, `Classical.choice` and `Quot.sound` axioms. Remaining messages are
unused-hypothesis/section-variable lints, not failed checks.

[established-bounded; process-audit] The focused exact-linear Cargo selection passed all 33
tests (`cargo test -p holonic-engine --no-default-features --lib exact_linear`), including three new kernel-mode tests; its
[terminal](2026-09-12_kernel_mode_receipts/cargo-tests.txt) retains the actual selection and
result. `cargo run -p holonic-engine --example kernel_mode_compression --no-default-features --
.local/scratch/2026-09-12-kernel-mode-compression.json` completed all exact comparisons after
formatting. Rust 2024 formatting and `git diff --check` pass. The example exercises phase transport, lawful and separating source actions,
normalization mass, modal reuse and the three-stage defect. Native kernels, the existing
protein experiment and Typst papers were unchanged and were not recompiled as a release gate.

[definition] The live owner map, composition/framework and Hephaestus guides now expose these
returns; the roadmap keeps the existing operator/recurrence construction order. The next use
of this library has an actual kernel, encoder/decoder and generator-compilation port available.
General nonlinear or changing-kernel reductions retain their own joint future family; this
finite exact construction is usable without claiming it is already a whole trained HNN.
