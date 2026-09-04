# Core mathematical instruments

**Status.** Boldfaced machine terms introduced below are `definition`. Normative exactness and
ownership requirements are `project-postulate`. Cross-ratio invariance, knot equivalence, and
connection/monodromy propositions are `proved-standard` under their stated hypotheses. Bridges to
computation, biology, string/M-theory, astronomy, and relativity are `interpretation`. Section 8's
construction program is `project-postulate`. Each sentence therefore has one status by its role;
none of these grades silently upgrades another.

## 1. Sameness, equivalence, and soul

A machine must never collapse these relations:

1. **Occurrence equality:** the same owner-minted situated event identity.
2. **Marked-diagram isomorphism:** an invertible map preserving typed occurrences, source marks,
   oriented incidence, admitted transitions, ports, and lineage.
3. **Doctrinal equivalence:** an explicitly declared doctrine-relative equivalence. When the
   compared doctrines are categories, this requires quasi-inverse functors and the relevant
   natural isomorphisms; parallel structure-preserving maps alone are insufficient.
4. **Observational equivalence:** equal testimony for every receiver in a versioned family,
   together with related successor conduct for every admitted history.
5. **Receiver-face equality:** equal output under one named receiver.
6. **Presentation/coordinate equality:** equality in one named presentation chart.
7. **Byte equality:** the same finite byte word under one declared encoding.
8. **Digest equality:** the same output under one named digest map.

These relations have no automatic total order. A claimed hierarchy requires explicit forgetful or
receiver maps between them. For a fixed deterministic digest map, byte equality implies digest
equality; the converse is not assumed.

A **soul** is the marked causal diagram of a continuing ecology: occurrences, source marks,
incidence, admitted transitions, receiver relations, and lineage. It is not a scalar, hash,
serialized state, or personality essence. Equal encodings may carry different souls; isomorphic
souls need not be the same occurrence. This is the exact reason rollback copies, path-derived
identity, and “same output therefore same machine” are inadmissible.

Knot theory supplies a precise comparison. A situated tame embedding `K`, its ambient-isotopy
class `[K]`, a received planar diagram, a braid presentation, a skein class, and a polynomial
invariant are distinct objects. Reidemeister moves preserve ambient-isotopy class, not occurrence
identity or causal history. Likewise, lawful recharting can preserve a machine's declared
doctrinal structure while retaining which path and return actually occurred.

Current spine: `H.0015` in [`foundations.typ`](../../research/papers/source/holonics/foundations.typ) and
`H.0287–H.0288` in
[`manifold-knot-geometry.typ`](../../research/papers/source/holonics/manifold-knot-geometry.typ). The legacy
[`causal-soul.typ`](../../research/papers/source/mathematics/definitions/causal-soul.typ),
[`soul-sameness-hierarchy.typ`](../../research/papers/source/mathematics/theorems/soul-sameness-hierarchy.typ),
and [`situated-knot-receiver.typ`](../../research/papers/source/mathematics/definitions/situated-knot-receiver.typ)
are supporting source material, not independently promoted authority.

### 1.1 Unqualified equality is occurrence identity; every other equality is typed

For situated holons, `x = y` is reserved for one owner-minted occurrence identity. A clone,
deterministic rerun, later state, rechart, reserialization, or returned loop is another occurrence.
It may be isomorphic or equivalent under a declared relation and is not literally equal.

Ordinary equality inside a declared mathematical carrier remains exact and indispensable. Write or
read it as `a =_X b`: equality in `X`, under `X`'s equality law. It does not identify two embodied
inscriptions or enactments of that equality. The historical correction is binding: **same is struck
for souls, not for typed equality.**

No universal `Soul<T>` wrapper is required or permitted. The soul is already carried by the marked
occurrences, incidence, ordered transport words, ports, returns, open fibres and lineage owned by
their exact local types. A comparison receipt names the relation it established; it does not mint a
second identity cabinet.

### 1.2 Causal signatures are receiver/history functors, not souls

For an occurrence `x`, admitted history category `H_x`, and versioned receiver family `R`, a causal
signature is the received functorial family

```text
Sigma_(x;R) : H_x -> Product_(rho in R) O_rho
```

together with the typed source marks, ports, incidence, ordered word, first separating prefix,
returned difference/obstruction, reconstruction fibre and return lineage owed by those faces.

Two signature occurrences are literally equal only when they are the same occurrence. They are
**soul-isomorphic** only through an invertible marking-, orientation-, port-, incidence-, word- and
lineage-preserving map of their complete causal diagrams. They are **receiver/history equivalent**
when a natural family of target-chart isomorphisms commutes with every admitted prefix extension,
intervention, receiver transition and return. The latter can hold after a receiver has forgotten a
source distinction and therefore never implies occurrence identity.

A deterministic rerun can consequently be soul-isomorphic and receiver/history equivalent while
remaining occurrence-distinct and physically nonidentical. Byte equality, digest equality and
apparatus-telemetry equivalence remain separate receipts.

### 1.3 Similarity, classification and activity are declared relations

For a characteristic family `K` and frame `F`, exact similarity is

```text
x ~_(K,F) y  iff  kappa_(i,F)(x) = kappa_(i,F)(y) for every kappa_i in K.
```

This becomes an equivalence relation only when the declared characteristic laws make it one. A
common classification means equality after a named classifier and says nothing by itself about
member identity, state, lineage or complete structure.

Activity likewise has no unqualified form. Every claim must name one of:

1. apparatus switching/conduction at a physical cut;
2. residency/admission on an apparatus surface;
3. parameter or transport participation in the enacted realization path; or
4. receiver-visible causal support under a matched intervention and admitted successor history.

A resident word can be path-inactive; a path-active word can be receiver-silent through
cancellation or quotient; and a nonresident word can remain potential inherited transport. Counts,
activation magnitudes and nonzero gradients do not replace these addressed populations.

## 2. Cross-ratio swing

For four distinct affine representatives over a field, define the projective swing first:

\[
\operatorname{Swing}(A,B,C,D)
=\bigl[(C-A)(D-B):(C-B)(D-A)\bigr]\in\mathbf P^1.
\]

The homogeneous determinant form makes the projective pair intrinsic up to common nonzero scale,
and it is invariant under the admitted `PGL₂` action. On the chart where the second coordinate is
nonzero, the scalar cross-ratio is its quotient
`((C-A)(D-B))/((C-B)(D-A))`. Three marked members establish a projective frame; the fourth carries
the receiver-relative projective coordinate. A **swing** is the lawful re-expression of that
four-member relation under a changed receiver/frame while preserving the projective pair and
retaining the actual transport path.

This is an essential exact navigation cell: it separates relation from absolute coordinate,
supports overlapping projective atlases, and makes perspective change computational. It is not the
universal interaction of every four objects. Coincident points, zero determinants, non-field
carriers, and nonprojective interactions require their own law or remain open.

Current spine: `H.0201–H.0202` in
[`geometry-calculus.typ`](../../research/papers/source/holonics/geometry-calculus.typ). The legacy
[`four-member-projective-swing.typ`](../../research/papers/source/mathematics/theorems/four-member-projective-swing.typ)
is supporting source material.

## 3. Bit-pure standing

The clean production contract requires exact-standing decisions to be bit-pure:

- no floating-point value enters event identity, exact standing, incidence, causal equality,
  projective equality, obstruction, lineage, or device-admission parity;
- integers, limb words, rationals, finite fields, quotient rings, homogeneous coordinates, exact
  polynomials, and certified symbolic carriers retain the needed distinctions;
- overflow is a typed refusal or causes a lineaged promotion to a wider exact carrier;
- physical sensor samples enter as bit occurrences with calibration, quantization aperture, and
  unresolved remainder; their binary encoding is exact testimony about the receiver, not a claim
  of exact access to a continuum; and
- an interval/ball may itself be an exact enclosure object, but it is not the exact enclosed value;
  any derived commitment requires a validated enclosure/factorization certificate.

“No floats” is a production invariant, not a claim that continua do not exist. It prevents an
apparatus approximation from silently deciding topology, identity, causality, or proof.

## 4. Receiver geometry and perspective

A perspective is a typed receiver map with an aperture, calibration, preserved structure, forgotten
fibers, and transition law. Projection is many-to-one unless proved otherwise. The source preimage
therefore remains available whenever a future receiver can distinguish it. Chart changes are
navigation deeds, not cosmetic coordinate rewrites; their transition maps and holonomy belong to
the receipt.

Equality is always typed: source occurrence equality, transported-chart equivalence, and equal
receiver face are separate. This discipline is shared by projective graphics, sensor fusion,
arithmetic fibers, proof codecs, and physical apparatus.

## 5. Knots, strings, branes, and weave

The common instrument is an oriented carrier with local incidence, boundary, crossing/contact,
transport, and return:

- knot diagrams expose crossings and isotopies of lineaged carriers;
- braids expose ordered interchange and its coherence obligations;
- strings/worldlines/worldsheets expose one- and two-dimensional transport with boundary;
- branes expose higher-dimensional carriers and contact loci; and
- warp/weft exposes persistent support crossed by locally serial changing currents.

Our String Theory and M-theory reading is a disciplined `interpretation`: higher-dimensional
extended carriers, dual descriptions, boundary interactions, and compactified receiver faces are
powerful models for how one causal ecology can have nonidentical but lawful presentations. A
literal physical identification is made only by a typed functor/correspondence preserving the
ports, incidence, transport, and observables owed by the receiver.

## 6. Hypergeometric navigation

The Gauss hypergeometric equation carries a local system of solution fibers over the punctured
projective line. Analytic continuation transports those fibers; monodromy records loop return.
The singular locus `0,1,∞` together with parameters `(a,b,c)`, chosen local bases, branches, and
continuation paths determines the relevant transition, exponent/residue, and monodromy data.
Contiguous relations and exact parameter transformations provide algorithmic paths between
presentations.

This is the rigorous content of a hypergeometric pathway: navigation through a family of local
solutions with explicit transition, singular, and monodromy structure. Confluent and generalized
families have different singularity laws. An implementation uses exact recurrence/algebraic data
or certified remainders and never invokes “hypergeometric” as an unexplained global solver.

## 7. Biological and astronomical recurrence

Cells, tissues, organisms, ecosystems, rotating bodies, orbital systems, stellar cycles, and
galactic structures are case studies in locally coupled currents whose recurrent macroscopic
faces arise from retained morphology, finite propagation, feedback, stress, and environmental
return. The engine draws exact operational requirements from them:

- recurrence is a returned-state or returned-fiber claim, not a loop counter;
- repeated support is weaker than complete-state recurrence;
- a stable cycle can carry irreversible lineage and resource exchange;
- stress can deform the later transport law;
- reproduction/evolution founds successor morphology through inherited structure plus caused
  variation and selection returns; and
- no local carrier needs a detached representation of the whole ecology for organismal conduct to
  emerge.

These are construction constraints and comparative interpretations. A specific biological or
astronomical law remains domain-owned and must not be replaced by a generic “life” or “cycle” type.

## 8. Information-relativistic construction program

The machine is the intermediate body in which arbitrary source ecologies may become co-present
without losing their receiver charts; actual contact remains a domain-owned typed interaction. Its
unifying construction program pairs information transport with local relativistic geometry:

| Information-transport object | Relativistic/geometric instrument | Engine obligation |
|---|---|---|
| caused occurrence and admissible communication | event and causal order/cone | no effect outside declared causal incidence |
| receiver-local continuation fiber | local chart/fiber | no privileged global observer or clock |
| codec/coordinate transition | change of chart/frame | exact transition and lineage |
| carried phase/current | connection transport | retain path and loop return |
| alternate/loop return under a declared connection | curvature/holonomy | expose the connection residual rather than flatten it |
| resource/stress return | domain constitutive response; stress-energy only for an actual relativistic matter model | returned physical difference can reform later placement/conduct |
| local boundary response | finite-region exterior testimony | condense interiors only under a stateful receiver certificate |

This is the project's `project-postulate` unification program: algorithms are enacted physical
transport, and causal computation is represented by the same local-chart, connection, boundary,
and return calculus used to express relativistic transport. It does **not** identify Shannon
entropy with spacetime curvature, computational load with a physical stress-energy tensor, or an
arbitrary incidence graph with a Lorentzian manifold. A claim of General-Relativistic physical
fidelity additionally owes a Lorentzian/domain discretization, conservation constraints,
constitutive source, convergence/consistency grade, and receiver comparison to the relevant field
equations.

GPU-local transport, receiver geometry, and morphology backreaction instantiate the
information-geometric program; they do not by themselves establish General-Relativistic fidelity.
A relativistic realization additionally owes the discretization, conservation, constitutive,
convergence, and field-equation comparison obligations above.

## 9. Standard-source boundary

Current project statements and their dependency citations are in `H.0015`, `H.0201–H.0202`, and
`H.0287–H.0288` linked above. Standard knot/topology background is routed through
[Hatcher](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) and the knot bibliography retained under
`research/papers/source/`; hypergeometric equations and transformations through
[DLMF Chapter 15](https://dlmf.nist.gov/15); and string/M-theory only as the delimited
interpretation supported by [Witten's 1995 paper](https://arxiv.org/abs/hep-th/9503124) and
[Tong's lectures](https://www.damtp.cam.ac.uk/user/tong/string/string.pdf). None of these sources
proves the information-relativistic construction program by analogy.
