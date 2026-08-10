// Dirac notation, defined once for the whole corpus.
//
// The role typing is the point, not the glyphs: a ket is a construction, a bra
// is a receiver (a declared linear functional), and a bracket is the face that
// receiver returns from that construction. See H.0266 and
// `mathematics/definitions/bra-receiver-ket-construction.typ`.
//
// Built from the corpus's existing `chevron` idiom so that no LaTeX-shaped
// syntax enters a tree that uses Typst symbol names throughout.

#let ket(body) = $lr(bar.v #body chevron.r)$
#let bra(body) = $lr(chevron.l #body bar.v)$

/// `braket(a, psi)` is the face; `braket(psi, E, psi)` is the sandwiched form.
/// Any number of parts is admitted and they are separated by the bar.
#let braket(..parts) = {
  let items = parts.pos()
  $lr(chevron.l #items.join($bar.v$) chevron.r)$
}

/// Receive with the right, emit with the left. The order is visible.
#let ketbra(left, right) = $#ket(left) #bra(right)$
