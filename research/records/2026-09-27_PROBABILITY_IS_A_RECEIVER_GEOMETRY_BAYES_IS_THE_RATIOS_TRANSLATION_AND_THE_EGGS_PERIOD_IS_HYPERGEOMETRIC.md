# Probability is a receiver geometry: Bayes is the ratio's translation, the Fisher sphere carries the faces, and the egg's period is hypergeometric

**Date:** 2026-09-27. **Occasion:** Brandon asked that probability be turned "into a geometry and
hypergeometry thing alongside the Hügelschäffer egg and optics (Holonic Interactions)", unified with
the main plan rather than pursued apart.

**Authorship.** GPT-6 Sol derived §§1–8 (read-only, from the repository, the laboratory's settled
ontology of probability and the cited sources). Claude checked each identity, cleaned the links, and
added three things:
- the existing softmax owner (§7′);
- the egg's half-turn point (§5′);
- perceptrons and rays (§7″).

It follows the [egg-packing](2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md)
and [egg-genome](2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md)
records and corrects them where §8 says. Refs #73, #62.


**Scope and grades.** Here `established-classical` denotes an external theorem (`proved-standard` in [the repository’s grade guide](../../docs/canon/EPISTEMIC_GRADES.md)); `proved-derived` denotes an exact consequence of stated hypotheses; `agent-inferred` denotes a proposed join to Holonics. Probability is a normalized *receiver face* of a declared population measure. The population passage, its phase, its receipt, and the constitution that later current meets remain distinct. This follows the laboratory’s probability and loss map (the laboratory, `src/soma/THEORY_MAP.md`) and receiving account (the laboratory, `src/soma/FORMULA.md`): the eye receives an exact plural passage; probability is a later quotient of it.

## 1. Normalization, Bayes, ratio, and Swing

**[Definition; proved-derived]** Let a receiver certify a finite, disjoint partition \(A_i\) of its admitted region \(F\), and declare a positive measure \(\mu(F)\). Its probability face is
\[
p_i=\frac{\mu(A_i\cap F)}{\mu(F)}.
\]
For a newly received condition \(E\), put \(L_i=\mu(E\mid A_i\cap F)\), assuming the denominators exist. Refining the partition by \(E\) and applying the quotient rule gives
\[
p_i'=\frac{p_iL_i}{\sum_jp_jL_j}.
\]
This is Bayes exactly; it supplies no measure, likelihood, or causal action on its own. For positive weights and likelihoods, the additive chart of the pair ratio obeys
\[
x_{ij}:=\log\frac{p_i}{p_j},
\qquad
x_{ij}'=x_{ij}+\log\frac{L_i}{L_j}.
\]
For \(S_a(x)=2a-x\), choose \(a=0\) and \(b=\tfrac12\log(L_i/L_j)\). Then \(x_{ij}'=S_bS_a(x_{ij})\) exactly. This is a chart identity for the [ratio](../../docs/ELEMENTARY_OBJECTS.md) and [Affine Swing](../../lean/Holonics/Geometry/AffineSwing.lean), not a claim that conditioning physically performs two point reflections.

**Smallest Lean return (proved, `Computation/HolonicAdjointNormalization.bayes_logOdds_twoSwings`; see Lean below):** `Receiver.bayes_logOdds_twoSwings`, stating the two displayed equalities for a finite positive measure and positive likelihoods. The Swing composition exists; this probability join does not.

## 2. Amplitude and information distance

**[Established-classical; exact calculation]** On the interior of a finite probability simplex, \(\psi(p)_i=\sqrt{p_i}\) lies in the positive orthant of the unit sphere. For tangent vectors with \(\sum_i u_i=\sum_i v_i=0\),
\[
g_p(u,v)=\sum_i\frac{u_iv_i}{p_i}
       =4\langle d\psi_p(u),d\psi_p(v)\rangle,
\quad
d_{\rm FR}(p,q)=2\arccos\!\sum_i\sqrt{p_iq_i}.
\]
Thus Fisher–Rao distance is twice the spherical, or Bhattacharyya, angle under this metric convention. The identities retain square roots and \(\arccos\) as exact constraints. A complex Born chart adds phase, \(\Psi_i=\sqrt{p_i}e^{i\phi_i}\), giving the repository’s ratio reading
\[
\log\frac{\Psi_i^T}{\Psi_i^H}
=\tfrac12\log\frac{q_i}{p_i}
+i(\phi_i^T-\phi_i^H+2\pi n_i).
\]
The positive sphere is its magnitude section; Fisher distance alone does not retain phase or winding. [Fisher metric characterization](https://arxiv.org/abs/1207.6736); the repository’s [ratio owner](../../docs/ELEMENTARY_OBJECTS.md) carries the lifted loss. The measured [Born face](../../docs/plans/THE_REBUILD.md) remains outside the selected receiving path after its negative development receipt; the geometry does not reverse that receipt.

**Smallest Lean return, owed:** `Receiver.fisher_sqrt_pullback`: \(g=4\,\psi^*g_{\rm sphere}\) on strictly positive finite faces. Existing `Objects/Ratio` owns the complex log-ratio identity; `HNN/BornFace` owns its bounded Born construction.

## 3. Chentsov and retention

**[Established-classical]** On finite sample spaces, a coherent family of smooth metrics invariant under *congruent Markov embeddings*, equivalently sufficient statistical changes with a stochastic recovery, is a positive multiple of Fisher’s metric. A general Markov map instead **contracts** Fisher information; equality requires that its output retain the relevant score. This is the precise Chentsov claim, not invariance under every stochastic map. [Chentsov theorem and sufficient statistics](https://arxiv.org/abs/1207.6736).

**[Conditional join]** A statistic \(T\) sufficient for a declared statistical family is a Holonics retention map only when **every admitted future receiver face factors through \(T\)** and the admitted transports descend through it. Classical sufficiency for one parameter family does not certify unrelated later contacts. Conversely, a lawful future-sufficient standing need not be minimal or sufficient for every statistical family. [Foundation/Standing](../../lean/Holonics/Foundation/Standing.lean) already proves `standingLaw_exists_iff_future_factors`; [Context/Standing](../../lean/Holonics/Compression/Landmark/Context/Standing.lean) proves `address_standing` and `leaf_standing` only under its shift-closure hypothesis, with an explicit unclosed-leaf counterexample.

**Smallest Lean return, owed:** `Standing.statistical_sufficiency_gives_standing`, assuming a finite family, all admitted future faces factor through its sufficient statistic, and each admitted transport descends. The existing factorization theorem should be its consumer; Chentsov’s full uniqueness theorem need not be duplicated to establish this join.

## 4. The hyperbolic face and the egg reading

**[Established-classical; proved-derived circle identity]** A nondegenerate location–scale family has a Fisher form with constant coefficients divided by \(\sigma^2\); a linear shear and rescaling give a constant multiple of the upper half-plane metric. For Gaussian mean \(\mu\) and width \(\sigma>0\),
\[
ds^2=\frac{d\mu^2+2d\sigma^2}{\sigma^2}
=2\frac{dx^2+dy^2}{y^2},
\qquad x=\mu/\sqrt2,\quad y=\sigma.
\]
For *standard hyperbolic* radius \(r\), its circle about \((x_0,y_0)\) is exactly
\[
(x-x_0)^2+(y-y_0\cosh r)^2=y_0^2\sinh^2r.
\]
Its upper and lower widths are \(y_0e^r\) and \(y_0e^{-r}\). A **Fisher** radius \(R\) uses \(r=R/\sqrt2\). This is a lopsided Euclidean picture of an equal-distance information region; “toward diffusion” applies when the receiver declares \(\sigma\) a diffusion width. The region is **egg-like by interpretation**, not the Hügelschäffer elliptic curve and not an isometry to it. The [egg audit](2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md) likewise requires a receiver and transport before its displacement becomes a physical boost. [Gaussian Fisher geometry](https://pmc.ncbi.nlm.nih.gov/articles/PMC10137715/).

**Smallest Lean return, owed:** `Receiver.hyperbolic_circle_euclidean_equation` from the upper half-plane distance identity. Keep the egg comparison graded `interpretation` until its receiver map and preserved distance or flux relation are supplied.

## 5. Hypergeometric navigation on the egg’s modular face

**[Established-classical]** Gauss’s equation
\[
z(1-z)y''+[c-(a+b+1)z]y'-aby=0
\]
has singularities \(0,1,\infty\); the ratio of independent solutions is a Schwarz map, whose continuation carries monodromy. At \((a,b,c)=(1/12,5/12,1)\), its exponent differences are \((0,1/2,1/3)\). With the cusp at \(z=0\), its inverse is \(z(\tau)=1728/j(\tau)\), up to the declared normalization and Möbius choice of solution ratio. Its orientation-preserving \((2,3,\infty)\) monodromy is
\[
\mathrm{PSL}(2,\mathbb Z)\cong\mathbb Z/2*\mathbb Z/3.
\]
The cusp makes this monodromy infinite: it is not one of Schwarz’s finite algebraic cases. [Schwarz’s original work](https://eurekamag.com/research/110/629/110629256.php), [Klein](https://commons.wikimedia.org/wiki/File%3ALectures_on_the_ikosahedron_and_the_solution_of_equations_of_the_fifth_degree_%28IA_cu31924059413439%29.pdf), [Yoshida and collaborators](https://link.springer.com/book/10.1007/978-3-322-90163-7), and [Beukers’s monodromy account](https://webspace.science.uu.nl/~beuke106/GaussHF.pdf) give the analytic lineage; [DLMF](https://dlmf.nist.gov/19.5) gives the elliptic-period chart.

**[Proved-derived modular join]** The egg record’s Legendre parameter
\[
\lambda=\left(\frac{a-w}{a+w}\right)^2
\]
has
\[
j(\lambda)=
\frac{256(1-\lambda+\lambda^2)^3}
{\lambda^2(1-\lambda)^2},
\qquad
K(\sqrt\lambda)=\frac{\pi}{2}\,{}_2F_1(1/2,1/2;1;\lambda).
\]
The \(\lambda\) period and the \(j\) Schwarz map are connected by this modular quotient; they are **different hypergeometric charts**. The [Farey owner](../../lean/HolonicsResearch/Geometry/Farey.lean) already proves unimodular Stern–Brocot steps; [HolonicTorusKnots](../../lean/Holonics/Geometry/HolonicTorusKnots.lean) proves coprime torus slopes and odd-half-twist boundary embeddings. Farey adjacency \(|hk'-h'k|=1\), Ford tangency, and a coprime \((p,q)\) torus-knot slope give distinct faces of the modular action. The Smith disk additionally needs its declared impedance-to-reflection Cayley chart. The affine Swing’s half-turn and the modular inversion \(z\mapsto-1/z\) share an abstract order-two role; identifying their actions requires an explicit conjugating chart.

**Smallest Lean returns:** `Geometry.egg_j_of_legendre_lambda`, the rational identity above (proved, see Lean below), and, owed in #62, `Geometry.modular_exponent_differences`, the three exponent differences. The full Schwarz inverse and group identification remain named analytic obligations; the existing Farey and torus-knot lemmas do not prove them.

## 5′. The real eggs meet the half-turn point once

`proved-derived` (exact over ℚ; proved in Lean as `HolonicsResearch/Geometry/EggModular.egg_j_of_legendre_lambda`).
- **The six images.** `j(λ) = 256(1 − λ + λ²)³/(λ²(1 − λ)²)` takes one value on the six anharmonic
  images `λ, 1 − λ, 1/λ, 1/(1 − λ), (λ − 1)/λ, λ/(λ − 1)`. This was checked at `λ = 1/2, 1/3, 2/7`.
  The group of the six is `S₃`, which is the two-three structure again.
- **The half-turn point.** `j(1/2) = 1728`, the modular curve's order-two elliptic point, the
  square lattice.
- **Where the real family meets it.** The egg family `λ = ((1 − β)/(1 + β))² = k⁻⁴` runs from the
  rest frame (`λ = 1`, a cusp) to the lightlike limit (`λ → 0`, a cusp). It meets `λ = 1/2`
  exactly once, at `β = 3 − 2√2`, the root of `β² − 6β + 1 = 0` in `(0, 1)`.
- **Where it does not.** The order-three point `j = 0` needs `λ = e^{±iπ/3}`, which no real egg
  reaches.

So the real eggs see the half-turn and reach the third-turn only by complex continuation.
`interpretation`: the half-turn is available to a real frame change of one egg; the third-turn is
the twist that needs the complex frame.

## 6. Counting faces and the receiving population

**[Established-classical; exact]** For a word of length \(n\), with counts \(n_i\), \(P_i=n_i/n\), and \(m\) admitted letters,
\[
|T(P)|=\frac{n!}{\prod_i n_i!},\qquad
(n+1)^{-m}2^{nH(P)}\le |T(P)|\le 2^{nH(P)}.
\]
A type is a count face of a passage, never a retained word list. [Method of types](https://pages.hmc.edu/ruye/book2/ElementsofInformationTheory.pdf). A node’s KT law is the Dirichlet-\(1/2\) predictive law,
\[
k_s(i)=\frac{n_{s,i}+1/2}{n_s+m/2};
\]
its sequential count reinforcement is the corresponding Pólya urn chart. If \(K\) counts one class in \(n\) draws with \(P\sim\mathrm{Beta}(\alpha,\beta)\), its *beta-binomial* generating polynomial is
\[
\mathbb E[t^K]={}_2F_1(-n,\alpha;\alpha+\beta;1-t).
\]
The \(-n\) makes this a finite exact polynomial, through [Euler’s integral](https://dlmf.nist.gov/15.6). Distinctly, drawing without replacement from a fixed finite composition gives a hypergeometric distribution. A finite exchangeable law is a mixture of the uniform laws on count classes; its shorter marginals are mixtures of such without-replacement draws. That finite statement is the relevant Diaconis–Freedman face, not an infinite iid representation. [Diaconis–Freedman, *Finite Exchangeable Sequences*](https://dml.mathdoc.fr/item/1176994663/).

**[Proved-derived in the current owner]** [Context/Tree](../../lean/Holonics/Compression/Landmark/Context/Tree.lean) has node likelihood \(E_s\), recursive CTW weight \(W_s=w_sE_s+(1-w_s)\prod_bW_{sb}\), and the exact posterior odds step \(\beta_s'=\beta_s k_s(c)/q_{s+1}(c)\). Its `own_mixture_over_trees`, `own_kraft_and_dominance`, `mixture_is_probability`, and `own_ratio_step` already establish the mixture and its code bound. [Context/Standing](../../lean/Holonics/Compression/Landmark/Context/Standing.lean) identifies its eligible pruned trees as candidate standings; [Context/Epoch](../../lean/Holonics/Compression/Landmark/Context/Epoch.lean) identifies a node’s arrivals with its section epochs. For candidate navigator families \(g\),
\[
w_g'=\frac{w_gL_g}{\sum_h w_hL_h}
\]
is exactly the **discrete replicator equation** with positive fitness \(L_g\). Biology is an analogy; Bayesian selection is the algebra. Positive but poor likelihood reduces relative weight without killing a candidate. Exact extinction needs zero likelihood or a separately lawful release. A newly founded candidate needs a declared prior and its description cost; conditioning a fixed zero-prior family cannot birth it. [Harper](https://arxiv.org/abs/0911.1763); [Shalizi](https://www.stat.cmu.edu/tr/tr874/tr874.pdf); [CTW original](https://research.tue.nl/en/publications/the-context-tree-weighting-method-basic-properties/).

**Smallest Lean returns:** `Context.kt_eq_dirichlet_half` for the node predictive ratio (proved); `Context.betaBinomial_pgf` for the terminating polynomial; `Context.bayes_eq_discrete_replicator` for finite positive candidate weights. The CTW mixture, dominance, and standing joins already exist. A separate full finite de Finetti formalization can begin with the finite count-class decomposition rather than an infinite theorem.

## 7. Optics and Holonic Interactions

**[Proved-derived lens chart; agent-inferred physical join]** If a receiving aperture transmits candidate \(i\) with intensity factor \(L_i\), the admitted intensity is \(Z=\sum_i p_iL_i\) and its *conditional* face is Bayes’s \(p_iL_i/Z\). The rejected flux belongs in the receipt; normalization cannot create it. With amplitudes \(a_j\) arriving in one coherent detected mode,
\[
\left|\sum_j a_j\right|^2
=\sum_j|a_j|^2+2\sum_{j<k}\Re(a_j\overline{a_k}).
\]
The classes interfere when their amplitudes reach the **same receiving mode with a retained relative phase**. Orthogonal path tags, an instrument that distinguishes them, or the declared incoherent quotient remove cross terms and yield a sum of intensities. A positive likelihood can be represented by a filter with \(|t_i|^2=L_i\) on separately resolved modes; this does not identify every Bayesian update with an optical device. This is the [Holonic Interaction](../../docs/HOLON.md) superposition law at a [declared pair contact](../../docs/HELICAL_GEOMETRY.md), followed by the receiver’s Born face.

**[Conditional frame join]** The egg’s converging and diverging descriptions can be two readings of one receiving surface: with declared clock, metric, and dynamics, the rate form \(\Sigma_G=A^*G+GA+\dot G\) has negative, positive, and null directions. Their inertia survives a lawful rechart; assigning a direction to integration or differentiation needs this form and the surface’s oriented flux pairing. A drawn convex or concave outline supplies neither an optical transfer law nor a Lorentz law. The [shadow and egg audit](2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md) already sets that boundary.

**Smallest Lean return (proved as `Physics/Wave/Interference.{intensity_eq, resolved_intensity_eq, distinct_modes_no_cross_terms}`):** `Receiver.coherent_intensity_split`, the displayed amplitude identity, with an orthogonal-tag corollary. The existing wave, Born, receiver, and pair owners consume it; the egg-to-optics map remains an `interpretation` obligation with an explicit aperture and receipt.

## 7′. The softmax ratio family is already this geometry

`proved-derived; formal-checked` in `Computation/HolonicAdjointNormalization` (read in
`HNN_FORMULA`, "Classical learning is the ratio family"):
- **The ratio family.** Softmax keeps the complete ratio family `r_ij = exp(β(s_i − s_j))` and
  forgets only the common additive origin, which is a gauge (`face_add_common`).
- **Its Jacobian.** `J = β(diag(p) − ppᵀ)`, with `vᵀJv = (β/2) Σ_ij p_i p_j (v_i − v_j)²`
  (`laplacianReturn`, `quadratic_laplacianReturn`).

With §1, `agent-inferred` and exact in its chart:
- **Bayes is this normalization** of `log p + log L`. It multiplies each `r_ij` by `L_i/L_j`, the
  translation of §1. The evidence `Z` is the forgotten origin.
- **The Laplacian return is the categorical family's Fisher information** in its natural chart.
  So the Fisher metric of §2 already has a checked owner, whose metric is that quadratic form.
- **Attention is the same interaction.** It is the attend/normalize row of the Holonic Interactions
  (`HOLON.md`), with `Computation/HolonicArchitectureCharts` reading it as input-conditioned
  contact. It is a posterior over which admitted contact is the source.

## 7″. Perceptrons and rays

`agent-inferred`, over existing objects:
- **One perceptron is one lens.** A perceptron is the parametron's locked-sheet receiver face
  (ELEMENTARY_OBJECTS, the Parametron row). Its hyperplane is a half-turn sheet boundary, and its
  output is which side a ray lands on: the two-coloring of the moiré record.
- **A layered network is an arrangement.** A layered ReLU network cuts its input space into the
  linear cells of an arrangement of such sheets, which Zaslavsky's theorem counts.
- **A ray is a candidate argument.** It is transported through the lenses, and the output face is
  where it lands.
- **Verification and search.** Tracing a given ray is verification; finding a ray that lands in an
  accepting face is search, the Bombe's problem. This is left for the P versus NP notes
  (`canon/THE_RELEVANCE_HYPOTHESIS`, `canon/TABLET_THE_CHART`, the September 13 optimal-navigation
  record), where God's algorithm is the diameter of a move group's Cayley graph.

## 8. Integration into THE_REBUILD

**Owner and order.** Put normalized partitions, moving aperture, Fisher/Born readings, and coherent reception in `RECEIVER_HOLARCHY` and its receiver/ratio owners; put the modular egg period in the egg guide or dated record and its Legendre/geometry Lean owner. The plan states only their consuming order. In steps 4–5, `compression::landmark::context` remains the receiving parametron’s storage: its candidate standings form the first measured mixture. Extend the **same** receiver mixture to declared navigator families on `holarchy::terrain`, with each family’s code, decoder, gauge fibre, and likelihood receipt. A “genome” is that navigator’s initial configuration and self-delimiting description, not a new elementary object; a “species” is its equivalence class under all admitted future faces. Kraft weights \(2^{-\ell_g}\) form a prior only after their total mass and any unused mass are declared.

The [unity audit’s receipts](2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md) fix the first measurements: recover the source’s **minimal future-equivalent** tree; on the moiré, compare each family’s charged prequential code with the exact source code and its key description, locate drawn phases and locks, and report the family’s posterior ratio and residual. The existing moiré control reads \(993+5/16+\varepsilon\) bits at determining depth against a \(30\)-bit key description; that gap is the rings’ target, not evidence already earned by them. Add arithmetic terrain through the same owner: exact digit convolution and carry, cheap residue faces, and prime gratings, with the true operands and factorization as truth gauges. Campaign 3 owns mode dormancy, founded cokernel directions, lawful release, and their aeon receipts; campaign 5 owns Holonic Encoding and charged merges of future-equivalent source words. Generation packs requested receiver consequences into keys and checks `decode(T_native(encode x)) = T(x)` at its consumer. Calling learning and generation *adjoints* additionally owes an actual pairing and adjoint square.

**Exposed wording to repair.** In the [egg population record](2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md), “failing configurations die” needs the zero-likelihood or release condition, and a sample’s recovered minimal tree does not prove unique future truth beyond its admitted family. In [egg packing](2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md), \(|ad-bc|\) counts transverse intersections of **primitive, distinct, nonparallel** torus paths, not automatically complement cells; the affine Swing is not the modular inversion without a chart; and the Smith identification needs calibrated port variables. The present [Order](../../docs/plans/THE_REBUILD.md) already mentions the egg population inside its moiré bullet. Consolidating that bullet with campaign 3’s release and campaign 5’s encoding avoids a second programme. The real conversation cut remains each campaign’s milestone; terrain with known truth diagnoses learning, while exterior conversation curation belongs to step 8.

## Lean (September 27, commit `56bc667d`)

Proved in their owners, with the standard axioms only:
- **Bayes** (`Computation/HolonicAdjointNormalization`): `bayes_logOdds_twoSwings` (the log-odds
  translation as `S_b S_0`), `bayes_eq_face`, `bayes_eq_iff_logOdds`, `bayes_eq_discrete_replicator`,
  `replicator_pos` and `replicator_eq_zero_iff` (a weight dies exactly at zero weight or likelihood).
- **The node law** (`Compression/Landmark/Context/Tree`): `kt_eq_dirichlet_half`, with the Pólya urn
  `urnSeq`.
- **Reception** (`Physics/Wave/Interference`): `resolved_intensity_eq` and
  `distinct_modes_no_cross_terms`, beside the existing coherent `intensity_eq`.
- **The egg's modular invariant** (`HolonicsResearch/Geometry/EggModular`): `legendreJ_anharmonic`,
  `legendreJ_sub_1728`, and `egg_j_of_legendre_lambda` (`λ = 1/2 ⇔ β = 3 − 2√2`, where
  `j = 1728`).
- **The torus crossings** (`Geometry/HolonicTorusKnots`): `torus_geodesic_crossings` (`|ad − bc|`
  crossings at every offset, through `slopeLattice_index`).
- **Ford circles** (`HolonicsResearch/Geometry/Farey`): `ford_separation` and
  `ford_tangent_iff_unimodular`.
- **Digits** (`Mathematics/RadixWindowReceiver`): `digit_product_is_carry_of_convolution`,
  `carried_word_is_product_digits`, `grating_on_digit_index` and `cheap_faces`.

Still owed in #62:
- the egg's hypergeometric charts: `K(√λ) = (π/2)₂F₁(½,½;1;λ)`, and the Schwarz map with inverse
  `1728/j` and exponent differences `(0, ½, ⅓)`;
- the identification of their monodromy with `PSL(2,ℤ)`;
- `fisher_sqrt_pullback`;
- `statistical_sufficiency_gives_standing`;
- the hyperbolic circle equation;
- `betaBinomial_pgf`.
