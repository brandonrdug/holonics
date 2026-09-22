# The framework survey binds loss, moments, fractal generators and encoding to existing owners

**Tree:** `972aac22`. **Request:** Brandon asked for thorough context across the repository before the Holonic-loss campaign,
naming generators-as-fractals and the formal corpus. Three Opus 5.5 readers surveyed the Lean
corpus (1,360 modules), docs/canon/records (1,237 records) and the native tree (~2,000 files);
the primary read the fractal-generator, fractal-mode and Holonic Encoding records directly.
Documentation only.

## Generators as fractals

[definition] Fractal generators here are recurring generator laws: a family of maps `g_i(λ)` on
declared domains with causal parameters and admissible compositions; ordered words keep their
intermediate domains ([Sep 8](2026-09-08_FRACTAL_GENERATORS_AND_LATENT_REASONING.md)). Geometry
is their population, restrictions, intersections, scale square `r∘T_fine=T_coarse∘r` and
first-arrival populations `A_(n+1)=Φ⁻¹(A_n)∖A` of one full recurrence
([Sep 14](2026-09-14_FRACTAL_GEOMETRY_BELONGS_TO_THE_INTERACTING_FIELD.md); tiled-copy IFS and
layer columns rejected). Scaling repeats an invariant unit; the generator is the compact
representative and the scale action carries (unit, count)
([Aug 13](2026-08-13_SCALING_IS_REPETITION_OF_AN_INVARIANT_UNIT_AND_THE_GENERATOR_IS_THE_COMPACT_REPRESENTATIVE.md)).
Recursive description and branch/address information are separate compression operands
(Cantor: two maps describe 2ⁿ cells; selecting one costs n bits).

[proved-derived; formal-checked] Owners: `Foundation/FractalPacking` (addressed contraction word,
`restriction_word_cannot_collapse_to_a_multiset`), `Millennium/Holon`/`SpherePacking` (packing by
reflection), `HolonicRecurrentEcology.FirstArrival`, `Millennium/Reflection` (renormalization as
interior elimination), `ContinuingTower.padicTower`/`coarseGrain`, `PhaseCarry.odometer`,
`IwasawaTower`, `ContinuingTube` (cocycle defect is holonomy). Hutchinson attractors and
similarity/Hausdorff dimension are not formalized.

[interpretation; agent-inferred] With a contracting advance the source moment
`Σ U^(n−1−k) I E(u_k)` is a `FractalPacking.descend`-type address map: the source word is the
address. `SourceMoment.identity_advance_merges_permutations` and
`restriction_word_cannot_collapse_to_a_multiset` are one law. Multi-rate generators give
concurrent grains glued by the carry cocycle — the tower — and Holonic Encoding's constituents
are reusable generator words with boundary action and decoder, BPE's adjacent pair being offset one.

## Loss

[established-bounded; source-inspected] `ℓ=log R` is anticipated and consistent: the lifted
complex cross-entropy (Sep 12; `Physics/InformationDifference`), softmax as chart transition
(Aug 14; `exponentiated_ratio`), the swing residual as a ratio `χ=DΔ⁻¹` (Jul 16), loss as a
situated Holon with cross-entropy one face (Aug 26). The survey adds its carriers and cautions
to the [contract](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#holonic-loss-is-the-logarithm-of-a-holon-ratio):
undivided pair / lift fibre, unsupported mass, branch as winding, `g∂g⁻¹`, and the two-Holon
cross-current `Im(conj z_T z_H)` as the phase part. Natively, the normalized receiver builds `p`
from Re only and `phase_participation` writes Im as zero; nothing implements the phase return.

[open] Formal gaps: `∂CE/∂s=p−e_t` is not stated in Lean (pieces in
`HolonicAdjointNormalization`); `liftedCrossEntropy` is not proved to be the log of an amplitude
ratio; the winding-shift identity is only in the Sep 12 record; no matrix/group log exists;
`SourceMoment` lacks per-generator clocks, the `Ĝ⁻¹` form, general offsets and a `StandingLaw`
statement; its z-transform `(zI−U)⁻¹I` is a `CausalChord` transfer, not yet stated.

## Unconsumed native owners

[established-bounded; source-inspected] `holonics-hna` imports the screw/pair owners but not
`exponentiated_ratio`, `surprisal`, `receiver_history_compression` (`HelicalMomentReuse`,
`ObservableMomentReceiverHistoryCompression` — no production consumer), `kernel_modes`,
`exact_linear::bilinear` factorizations (except in `mathematical/code.rs`), `grain_tower`,
`continuing_tower`, `standing` or `receiver_release`. The reaction material `M` is the normal
solution over `φ=[s,c,c⊗s]`; its `c⊗s` block is a `BilinearOperator` with existing product-core
factorization, and `KernelModeReduction`/`GeneratorModeQuotient` supply future-exact reduction.
The encoder is a one-hot codepoint table; it is not Holonic Encoding (Sep 20 correction).
