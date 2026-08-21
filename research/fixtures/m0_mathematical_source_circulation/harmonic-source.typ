#let harmonic-sheet(semantic-perturbation: false, reflow: false) = {
  set text(font: "Libertinus Serif", size: if reflow { 12pt } else { 11pt })
  set par(justify: true, leading: 0.7em)
  let relation-hand = if semantic-perturbation { $+$ } else { $-$ }
  [
  #align(center)[
    #text(size: 18pt, weight: "bold")[Harmonic-conjugation calibration]

    #v(0.35em)
    declared relation-hand control
  ]

  #v(0.8em)

  $ chi_(B,D)(A^prime) = #relation-hand chi_(B,D)(A), quad
    chi_(B,D)(X) = frac(X-B, X-D) $

  #v(0.5em)

  $ A^prime = frac((A-B)D + (A-D)B, 2A-B-D) $

  #v(0.5em)

  $ D arrow.r infinity quad ==> quad A^prime = 2B-A $

  #v(if reflow { 1.1em } else { 0.7em })

  *Declared source controls.* The prime on $A^prime$, the infinity sign
  $infinity$, the glyph 8, the minus sign, the nested fraction bars, and
  ordered point labels remain distinct exterior occurrences.

  #v(0.7em)
  #text(size: 9pt, fill: rgb("555555"))[
    M0 boundary: this page supplies source and layout testimony only. It does
    not assert a recovered operation complex, proof, group action, or manifold.
  ]
  ]
}
