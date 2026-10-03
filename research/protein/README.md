# Experimental protein receiving certificates — paused October 3, 2026

This package publishes a sequence, source contracts, exact outward geometric readings and
scoped certificates from the protein workbench. It does **not** provide a validated structure,
fold, EGFR binder, pH selectivity result, mouse result or experimental receipt. Design remains
paused. Refs [#148](https://github.com/brandonrdug/holonics/issues/148).

The sequence in [sequence.fasta](sequence.fasta) has `69 = 3·23` residues:

```text
EKLDKILKQIKQAIQEAQEKSGNSEIQEAIEKAIKQAKQVAQEVSGNSGIQEAQEVAEKVAKQVKQLVQ
```

The geometry has explicit ancestry in observed **1UBQ** coordinates, including backbone and
rigid constituent tokens. This is a different sequence from ubiquitin. The supplied charts
are transformations and substitutions of source geometry; no independent fold prediction or
de novo fold validation is claimed. Target anchors come from observed **6ARU**, chain A.
[SOURCES.md](SOURCES.md) identifies the primary entries, exact source identities and license.

## Current receipt and its limits

| Receiving partition | Exact reading |
|---|---|
| Heavy ports in the source parent | `534 = 2·3·89` |
| Reference H ports / ionized-view H ports | `574 = 2·7·41` / `573 = 3·191` |
| All reference ports / ionized-view ports | `1108 = 2²·277` / `1107 = 3³·41` |
| Retained internal comparisons | `236 = 2²·59` |
| Latest four-chart cover | `134 = 2·67` refused, one necessary pass, `155 = 5·31` unknown |
| Reference nonlocal pair readings | `610154 = 2·47·6491` |
| Nondirectional pairs unresolved by the regional screen | `967` (prime) |
| Additional internal receivers still unbuilt | `966 = 2·3·7·23` |
| Possible directional contacts unresolved by that screen | `110 = 2·5·11` |

The latest cell is `RF:0110101010`, depth `10 = 2·5`: reciprocal φ37 coordinate
`u ∈ [−1/16,0]` and finite ψ37 coordinate `σ ∈ [0,1/16]`. It clears all retained
internal comparisons and both stricter positional chord bounds over the whole cell.
The reciprocal endpoint `u=0` is the half-turn and stays in the chart. The broadphase counts
every graph-nonlocal pair, but its unresolved pairs prevent full internal fixture admission.
One of those pairs already has a retained receiver; the others do not yet have their exact
moment receivers. This count is a geometric screen, not a count of physical collisions.

No all-port endpoint or common proper pose was constructed for this latest cell, and its
full target gate was not executed. The `140 = 2²·5·7` target comparison definitions in
[comparisons.json](data/comparisons.json) remain pending a common pose. In particular,
source/target contact construction is incomplete: the positional chord condition does not
construct both contacts in one pose or certify their material interaction. Source and target
ports are participating receivers in the intended law, not a static affinity score.

The reference view keeps the terminal HXT and acid H ports; the ionized alternative removes
only terminal HXT, port 1107. Neither alternative asserts physiological population or pH
selectivity. Earlier water-orientation and methanol-torsional accuracy gates failed. Their
unpublished producers are not included, and no calibrated material or affinity ranking follows.

## Corrected and negative outcomes

The earlier three-grip source family, with `205 = 5·41` internal comparisons and necessary
anchor chord geometry, is excluded by a complete `315 = 3²·5·7`-leaf four-chart cover.
Its β circle is eliminated by the necessary phase intersection. This is an obstruction for
that declared family, not impossibility of the molecule or of other source families.

The first joint cell `RF:00011111`, reciprocal φ37 `[-5/8,-1/2]`, finite ψ37 `[-1/8,0]`,
cleared those 205 comparisons. Its later regional screen exposed additional comparisons.
Comparison 375, source ports **604 (A37 O) and 622 (K38 HB2)**, refuses the whole cell under
the declared threshold `18496/5625 Å²`. The common outer motion cancels, leaving φ37 alone.
The earlier pass was therefore withdrawn. All prior definitions were retained, and
`31` (prime) internal definitions were appended to reach 236. The original and corrected
full covers are both supplied, so an unknown region is not silently discarded.

At fixed φ26 `−19/64`, ψ37 `−51/64` and β `0`, a necessary intersection excludes the entire
φ37 circle. Allowing ψ37 to vary leads to the latest joint cover above. These certificates
do not authorize extrapolation to undeclared controls.

## Receiving certificate

The computational object is the helical pair interaction. The source incidence determines
complete graph cuts; their proper affine transports determine squared pair separation.
The existing owners are `Holonics.Transport.SerialScrewChain.AffineMap3`,
`Holonics.Geometry.ScrewGeometry` and Rust `holonics::geometry::exact`, with its
frame/Cayley chart. This exterior reader consumes their transport and ratio law:

```text
q_ab = N_ab / D_ab,      D_ab > 0
G_ab = N_ab − r_ab² D_ab
```

Five-component affine moments `(1,x,y,z,|x|²)` keep each active Cayley coordinate at degree
two. Actual common outer maps and axis pins cancel before forming the receiving face.
For a cut axis `d`, the finite denominator is `1 + |d|² t²`; the reciprocal denominator is
`u² + |d|²`, positive because the axis is nonzero. Finite and reciprocal coordinates each
cover `[-1,1]`, including the reciprocal half-turn. Rational Bernstein bounds over a cell
certify `G>0` or `G<0`; coefficient enclosures are outward at grain `2^80`.

The old word is the three declared cuts with axes `(434,433)`, `(613,612)`, `(817,816)`.
The latest word is
`O_ψ37(σ) P_φ37(ρ) I_φ26(−19/64) X`, β `0`, with complete nested cut sizes
`435 = 3·5·29`, `613` (prime), `631` (prime). P uses `(612,611)`; O uses `(613,612)`.
Both later axes are unaffected by the fixed inner map. Their endpoints are true pins.
Cell paths bisect the longer side, φ first on a tie. Prefix-free paths with Kraft sum one
certify complete covers for FF, FR, RF and RR.

The anchor squared distance is `7796949/62500 Å²`. Each candidate/target anchor window is
`[25/4,49/4] Å²`. With target chord enclosure `[d₋,d₊]`, the outward necessary candidate
chord interval is `[(d₋−7)²,(d₊+7)²]`; the stricter inner interval is
`[(d₊−7)²,(d₋+7)²]`. Clearing either interval is not construction of a common pose.

The pair aperture `r_ab² = (4/9)(r_a+r_b)²` is an **agent-inferred geometric fixture**,
using the stated radius chart. It is not a universal repulsive potential or a binding law.
One- and two-edge neighbours are excluded by actual incidence. Pairs between polar N/O/S
ports, and polar ports with an H bonded to a polar port, are flagged as **possible
directional contacts**. Their angles, constitutive interaction and uncertainty remain
unresolved; they are not reclassified as repulsive overlaps by a blanket radius cutoff.

The winding guide's six objects stay attached: helix and pair furnish the local move;
faces and placement furnish these readings; cell holonomy is not inferred without a declared
circuit; tube and tower restrictions preserve the source chart and its gluing. A global
root-count resource cap is never physical impossibility.

## The missing polymerized-amide source

An amino-acid monomer's N has the monomer incidence (including its terminal H multiplicity).
Polymerization replaces one H neighbour by the preceding carbonyl C. Matching a monomer H
joint as though this changed incidence were identical loses the carbonyl/saturated-C joint
and its H angle provenance. A primary amide `NH₂` source also has a different neighbour
multiplicity from a peptide's secondary amide `NH`. Neither equality is admitted.

CCD **NML**, N-methylacetamide, supplies a legitimate radius-one secondary-amide source.
Its N3 is single-bonded to carbonyl C2, saturated C3 and HN3; C2 is double-bonded to O2.
The admitted map is `N3→N_i`, `C2→C_(i−1)`, `C3→CA_i`, `HN3→H_i`;
O2 is a residual-only carbonyl witness. NML's methyl and a peptide Cα have different
radius-two environments, so the substitution is explicitly conditional.

Both CCD model and ideal charts are retained. Their literal coordinates have nonzero
signed H departure from the two-carbon plane. Exact planarity would contradict both sources.
The ordered frame uses carbonyl-C first, saturated-C second and their cross-product normal:

```text
h_i = N_i + F_target F_sourceᵀ (HN3 − N3)
```

This preserves proper orientation, N–H quadrance, the first normalized H projection and
signed departure from that plane. It must report both heavy/H Gram residuals, the second
angle residual, all three anchor Gram residuals and carbonyl-O orientation residual.
The declared domain is the source-only two-chart cosine-squared interval in
[amide_source_contract.json](data/amide_source_contract.json), with negative heavy-axis dot.
This is a conditional interpolation domain, not a physical confidence interval. A
representative native implementation first selects an actual neutral secondary-amide joint,
checks that domain and nonzero ordered-frame Gram determinant, transports only its H, and
returns those residuals with the source chart identity. A refused source joint remains
unassigned; it does not move heavy ports to manufacture acceptance.

## Reproduction boundary

The Python reader uses only the standard library, integers and fractions. From repository root:

```bash
python3 -B research/protein/verify.py --part amide
python3 -B research/protein/verify.py --part certificates
python3 -B research/protein/verify.py --part broadphase
```

These bounded parts check source-file identities and NML metrics, rebuild comparison
polynomials from supplied source faces, replay whole-cell certificates and complete chart
covers, and recount the regional pair partition with its unresolved identities. They perform
no design search, optimization, network access or external model call. The broadphase starts
from **supplied regional enclosures**; their upstream native decoder is not reproduced here.

`source_faces.json` supplies outward faces at grain `2^32`, source denominator guards and
`338 = 2·13²` local root-chart identity bindings. OXT retains its explicitly positive root
of `z² = 264999577539/435221445974`; H ports retain their local context identities. These
digests preserve identity but do not reconstruct omitted local decoders.

Interval arithmetic bounds only the declared mathematical charts. Experimental error and
physical transfer uncertainty are **unquantified**. CCD coordinate provenance does not certify
an experimentally observed H, and no source enclosure is an experimental confidence bound.

The native protein crate, its associated Lean additions and its integration are uncommitted
upstream work. Importing them would include other workers' dirty files, so this contribution
starts at exterior receiving faces. It adds no native law or native owner. The formal
source-decoder/substitution join and the application-wide admission are not discharged by
this reader; [#62](https://github.com/brandonrdug/holonics/issues/62) remains the formal
obligation route. [manifest.json](data/manifest.json) seals the exact published inputs and
reader. [results.json](data/results.json) preserves the paused receipt and scoped original
receipt identities. This package contains no bulk cache or private conversation.
