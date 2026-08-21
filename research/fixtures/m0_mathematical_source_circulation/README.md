# M0 mathematical source-circulation fixture

This fixture is exterior material for Deed M0. It does not encode a mathematical operation graph
and it does not testify that any source relation is true.

The synthetic family has one shared Typst source function and three source occurrences:

- `harmonic-baseline.typ`: the negative cross-ratio hand;
- `harmonic-reflow.typ`: the same source relation under a wider page, different placement and
  reflow;
- `harmonic-perturbed.typ`: the positive cross-ratio hand, the declared semantic perturbation;
- `harmonic-conjugation.svg`: an authored vector construction face with ordered point-label,
  prime-mark and infinity/eight controls.

The natural control is the unchanged
`tmp/pdfs/2608.13553-heat-kernel-geometry.pdf` (Jian Ge, arXiv:2608.13553v1). Only PDF pages 5 and
10 are admitted. The driver derives each page's text/bounding-box, SVG and PNG faces independently
and retains the whole source-PDF identity and each derived-face identity.

Bounding-box decimals emitted by Poppler remain exact lexical apparatus testimony. They never enter
a floating-point comparison and never decide an incidence relation.

`tools/build_m0_source_fixture.sh` creates the exterior faces under
`output/m0_mathematical_source_circulation/faces/`, including the synthetic born-digital PDF at
`faces/synthetic/harmonic-calibration.pdf`. The Rust M0 driver reads those files as apparatus
testimony; the script neither recovers nor labels mathematical semantics.
