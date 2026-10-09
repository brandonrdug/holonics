# The Holonic Encoder explodes a source into co-present frames, and an axis exposes without authoring when no relabelling moves it

**Date.** October 9 (the lens: October 8). **Issues.** #386, #73, #148, #62, #63. **Grade.** Lens
record. Each section carries its own grade. §2 is checked by exact computation and joined to
formal-checked owners. §3 classifies the laboratory's catalogue against the governing law. The
joins in §5 are owed.

## 1. The lens

Brandon, October 8: recover the Holonic Encoder from the old laboratory. He used to say the source
has to be "exploded": the machine must see everything about it purely, not in the format it was
prescribed in, such as a file structure. The geometric representations combine with trace
reconstruction (the [key record](2026-10-08_A_KEY_IS_LOCATED_WHERE_ITS_RECEIPTS_RESONATE_AND_A_SECRET_IS_DORMANT_TO_ITS_RECEIVERS.md)).
In the same message he named a public catalogue item whose content is not identified here.

**The recovered text** [historical; source-inspected]. The laboratory (private) holds
`src/eros/um/HOLON_ENCODER.md`, written June 13 to 15. It reads, in paraphrase:
- The encoder is the reverse of encryption. Encryption drives a source's exposed structure to
  nothing a reader can resonate with. The encoder drives it to the maximum while conserving the
  information: what grows is reachability, not content.
- It is the eye for any source: a world-side port, a machine-side port, and between them a chain of
  transducer Holons, one per family of axes. Perception takes all the co-present axes at once.
- Its catalogue of axes: content, layout (rows and columns), a parse tree from an external parser,
  graph-Laplacian spectral coordinates of call and use graphs, chronology, nesting depth and
  directory enclosure. The axes are said to be measured, never authored.
- The axes combine by sum at a shared locus, by cross terms, and by an exponentiation in which one
  axis is applied to another, so that the exposed dimension multiplies.
- The transducers are frozen in structure. Only the perceiver is plastic. On June 15 the document
  itself recognized that the encoder is what the perceiver does online, and that the authored axes
  are catalysts, removable in principle.

The [Holonic Encoding record](2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md)
recovered the same file on September 11 and ruled that its byte floor, universal losslessness and
authored parser catalysts do not override current law. This record does what that one did not. It
reconciles the catalogue with "No catered machinery" (September 29) and with guard 9, and it joins
the explosion to the helical code (October 8).

## 2. The explosion, exactly

[proved-standard; checked by exact computation; formal-checked owners] **A frame turns a far relation
into a near one.** Put a source word on a strand with the uniform tick `τ(k) = k`. A receiver's
frame of period `W` reads position `k` as its residue `k mod W` and its whole winding `⌊k/W⌋`
(the guide's [helical code](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode),
item 3). Two positions `W` apart, which are far apart in serial order, share their residue and
differ by one winding: neighbours across the helix's pitch. A row-major image of width `W` read
through a frame of period `W` has its vertical neighbours on one residue in consecutive windings.
That is the laboratory's layout axis without a layout table.

[proved-standard; formal-checked owners] **Co-present coprime frames are the exponentiation rung.**
Frames of coprime periods `W₁` and `W₂` reading one lifted clock meet once per pair of residues:
`k ↦ (k mod W₁, k mod W₂)` is a bijection `ℤ/W₁W₂ ≅ ℤ/W₁ × ℤ/W₂`
(`HNN/Prediction.joint_residue_determines_position`,
`Geometry/PairResonance.diagonal_step_generates_the_coprime_torus`). With `W₁ = 3` and `W₂ = 5`,
`7 ↦ (1, 2)` and `13 ↦ (1, 3)`, and the fifteen positions take the fifteen pairs once each. The
functions on the joint reading are the tensor product of the frames' functions, of dimension
`W₁W₂`. That is the multiplying dimension the laboratory called the exponentiation rung. The joint
class is not a sum of the marginal faces (`HNN/Prediction.joint_class_not_additive`), and a joining
receiver keeps the cross terms that separate readings omit: `|Σ_j u_j|² = Σ_j |u_j|² +
2 Re Σ_(j<k) ū_j u_k` (atlas `encoding.chord-cross-terms`). The residues fix the position only
modulo `W₁W₂`; the whole winding fixes the rest.

[definition; agent-inferred] **Information conserved, reachability exploded.** A chart `E` with
`ker E = 0` loses nothing. What it changes is which receivers of bounded depth separate a relation.
In the key record's terms, a construction is secure against a receiver family when every
key-dependent difference lies in that family's kernel (atlas `receiver.security-is-dormancy`). The
encoder is the same law read from the other side: it chooses a lossless chart so that the source's
relations leave the kernel of the machine's shallow receivers. Encryption and the encoder are one
law, dormancy and exposure, read from its two sides.

[definition; formal-checked owners] **The frames are located, not declared.** A period is a key: the
navigator's clock. A word in resonance with period `p` keeps a fixed face and grows it with every
repeat, `m_(Np) = N·m_p`; off resonance its face stays bounded
(`Transport/HelicalCode.strandFace_repeatWord_of_fixed`, `strandFace_repeatWord_one_sub`; the guide's
resonating lengths). So the frames that explode a source are the periods at which its strand
resonates, found by the machine's key location. On the located route the clock advances by the
located advance `A(u)`, and the residues lift to positions through the located transport (Rust
`compression::keys::transport::LocatedTransport::lifts`, `CarryHelix::of_residues`). For a noisy
source, location by resonance across receipts is the key record's owed operation (its §6, item 3).

## 3. Which axes expose without authoring

[proved-derived owner; implemented-exact] **The test is relabelling.** The located route's encoding
does not see the exterior labels. For every permutation `π` of the exterior codes, the chart, the
encoding `E`, the cells, `D`, `ker E ∩ R` and the advances are unchanged, and only the boundary's
decoder carries the labels, `λ_(π∘x) = π∘λ_x` (atlas `hnn.encoded-located-relabelling`, Rust
`hnn::encoding::Encoded::through`). Guard 9 makes this the field's only entrance: every source
enters as `Encoded`, through a chart the field's own key location built, read in the receiving
cells and never in the labels. A chart nothing located (the byte chart, bare matrices, the moment
chart over exterior codes) is refused as unencoded (atlas `hnn.encoded-source-type`;
[THE_MACHINE](../../docs/THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible), guards 9
and 17; the [entrance record](2026-10-05_THE_FIELDS_ENTRIES_TAKE_ONLY_THE_ENCODED_SOURCE.md)).

[agent-inferred] So an axis **exposes without authoring** exactly when it is invariant under every
relabelling of the exterior codes, as the located encoding is. An axis whose value depends on what a
code means authors structure, because it hands the machine a classification it should locate. The
laboratory's catalogue sorts as follows.

| Axis | Reading | Ruling |
|---|---|---|
| Content | the codes themselves | enters through a located chart (`Encoded::through`); the identity encoding is lawful only for a known-truth terrain, whose classes are its own (`Encoded::identity`) |
| Position, chronology of the passage | residues and whole windings of located frames | native: relabelling-invariant |
| Layout of a sensor's grid (image rows, audio sample clock) | a declared exterior chart, the sensor's own period | exterior codec information, declared and revisable (§4); its period can be located (§2) |
| Layout and nesting of text (lines, indentation) | depend on which codes mean newline or indent | authored unless the carry at those codes is located by the machine's own advance |
| Parse tree from an external grammar | a classification by code meaning | refused as a drive (no hand-written grammar or parser stands in for learning); lawful only outside the field, to generate a known-truth terrain or to grade one |
| Graph-Laplacian spectral coordinates | modes of an incidence | native when the incidence is the machine's located contacts, since they are then the constitution's modes `Kv = ω²Cv`; refused when the incidence is a parser's or compiler's graph |
| File, commit and directory provenance | exterior addresses | exterior codec information, never a native semantic identity (CLAUDE.md, the repository paragraph) |

## 4. "Frozen" becomes "declared exterior and revisable"

[definition; agent-inferred] The laboratory trusted its transducers because they were frozen. The
governing law trusts a chart only through its checked squares, `D E = ρ` and `E T = U E`, and it
holds the current data types as revisable hypotheses (the
[operator contract](../../docs/ELEMENTARY_OBJECTS.md#operator-contract)'s October 7 clause). An
exterior chart is admitted at the boundary when four conditions hold:
- it is declared as exterior;
- it carries its decoder;
- it computes no task's answer;
- the machine can replace it by a chart founded from its own reached covectors. Founding closes a
  reached covector under the adjoints, `V_(n+1) = V_n + Σ_a T_a* V_n`, and a basis of the stable
  rung gives `E T_a = U_a E` (the guide's
  [keys, locks and navigation](../../docs/ELEMENTARY_OBJECTS.md#keys-locks-and-navigation), "It
  founds from its residual"; Lean `Compression/Landmark/Context/Birth`). The field's encoding is
  founded this way today: `hnn::encoding::{PassageChart, Encoding}` found a passage chart's minimal
  realization with the same closure, forward from the openings and backward from the receiving
  forms (the
  [September 29 encoding record](2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_THE_SQUARES_CLOSE_ON_KNOWN_TRUTH_AND_TEXT_FOUNDS_ONLY_ITS_REACHED_CELLS.md)).

The replacement is checked by the same squares. A result that is perfect because a catalyst
supplied it is a failed build. This is the laboratory's own June 15 recognition: the encoder is
what the perceiver does, and the transducer is a catalyst removable in principle, now stated as a
law with a test.

## 5. What the repository already owns, and the joins owed

**Owned.**
- The entrance: `hnn::encoding::{Encoded::identity, Encoded::through, Encoded::check_step}`, Lean
  `HNN/Encoding` (atlas `encoding.separator`: a reading factors through `E` exactly when no merged
  direction separates it; `encoding.minimal-realization`).
- The frames: `HNN/Prediction.joint_residue_determines_position`, `joint_class_not_additive`,
  `Geometry/PairResonance.diagonal_step_generates_the_coprime_torus`.
- The located transport: `LocatedTransport::lifts`, `CarryHelix::of_residues`; atlas
  `hnn.encoding-helix-dimension` (the encoding founded on located transports keeps every helix
  mode except the `D_low − 1` the receiving grain is silent on).
- The helical code's strand and resonance: `Transport/HelicalCode`.
- Holonic Encoding as a law of transformations, not of spellings (atlas `encoding.holonic-encoding`;
  the September 11 record).

**Owed.**
1. **Frames located by resonance** (#386, #73). The consumer is `Encoded::through`. A source's
   frame periods are read from the strand's resonating lengths, and every located frame is
   admitted only by the existing squares. The equation at the consumer is the separator law:
   `ρ = D E` for every admitted receiver, or the merged direction `v` with `E v = 0`, `ρ v ≠ 0` is
   returned.
2. **The relabelling test as a stated property of every admitted axis** (Lean, #62). For every
   permutation `π` of the exterior codes, `E_(π∘x) = E_x` and `λ_(π∘x) = π∘λ_x`. It is proved today
   for the located route (`hnn.encoded-located-relabelling`, implemented-exact on twelve
   permutations of five classes); the general statement over the encoding's founding is owed.
3. **Exposure as a measurable** (#148). For a declared lossless chart and the machine's admitted
   receivers, report which source relations leave their kernel. That is exposure, read exactly as a
   kernel difference, never as a code length.
4. **A declared exterior chart's revision path** (#73). Each exterior codec chart, such as a sensor
   grid, names the founded chart that would replace it and the squares that would admit the
   replacement.

**Acceptance for the first loop** (fixed before any build). A known-truth terrain generated by exact
routines: words written row-major on grids of undeclared widths `W`, in a second modality the same
construction on a sampled tone of undeclared period. The machine locates `W` (or the period) through
its own encoding, on unseen terrains, and reads the vertical relation as residue adjacency. Report
the located period and the separator law's verdict exactly. Nothing passes because a width was
declared.

**Recorded failures checked.**
- An authored routine standing in for learning: the parse and provenance axes are refused as
  drives (§3), and every frame is located.
- Text run as the exception: the construction is the same for text, images, sound and motor words.
  Only the boundary codec differs.
- A design thought in the programming language: the explosion is stated as residues, windings and
  coprime frames, not as layout arrays or offset tables.
- Bits read as progress: exposure is read as a kernel difference, not as compression.
