#import "../../lib/dirac.typ": bra, ket, braket, ketbra

#let bra-receiver-ket-construction = (
  key: "definition:bra-receiver-ket-construction",
  kind: [Definition],
  title: [Dirac notation: the ket is the construction, the bra is the receiver],
  status: [Project definition; standard Dirac notation, adopted because it types apart what a symmetric inner product conflates],
  depends: (
    "definition:receiver",
    "lemma:receiver-nonreconstruction",
  ),
  claim: [
    Let $cal(H)$ be a complex Hilbert space and $cal(H)^*$ its continuous dual.
    Dirac notation assigns *different symbols to different roles*:
    $
      ket(psi) in cal(H)
      quad "the construction",
      wide
      bra(a) in cal(H)^*
      quad "the receiver",
      wide
      braket(a, psi) in CC
      quad "the face".
      quad "(THE THREE ROLES)"
    $
    A ket is a participating construction. A bra is a *declared linear
    functional* $cal(H) -> CC$ -- a receiver in the sense of
    #emph[definition:receiver], with $q_(bra(a))=braket(a, dot)$. The bracket is
    that receiver's face of that construction, and it is a number precisely
    because a face is what a receiver returns and not what the construction is.

    The outer product is the transport:
    $
      ketbra(phi, a):cal(H) -> cal(H),
      quad
      ketbra(phi, a) ket(psi)=braket(a, psi) ket(phi).
      quad "(RECEIVE, THEN EMIT)"
    $
    It reads with $bra(a)$ and writes with $ket(phi)$, in that order, and the
    order is visible in the symbol.

    *A declared receiver family is complete exactly when it resolves the
    identity.* For a family ${bra(a_i)}$ with kets $ket(a_i)$,
    $
      sum_i ketbra(a_i, a_i) = I
      quad &lt;==&gt; quad
      "every construction is reconstructible from its faces",
      quad "(RESOLUTION OF IDENTITY)"
    $
    and when the sum is a proper sub-projection $P != I$, the defect $I-P$ is
    exactly what the family cannot see. Receiver non-reconstruction is therefore
    not an obstacle to this notation; it is the statement
    $sum_i ketbra(a_i, a_i) != I$, written in it.

    A positive operator-valued measure ${E_i}$ with $sum_i E_i=I$ is a complete
    declared receiver family whose faces are the quotients
    $p(i)=braket(psi, E_i, psi)$.
  ],
  proof: none,
  boundary: [
    *Why this replaces the symmetric form.* Writing $chevron.l psi,phi chevron.r$
    for the same number makes the two arguments look like two constructions of
    one species, and the framework's central claim is that they are not: one is
    what is presented and the other is what presents. Riesz representation gives
    an isomorphism $cal(H) tilde.eq cal(H)^*$, so the conflation is *harmless for
    computing the number and lossy for reading it* -- the isomorphism is
    antilinear and depends on the inner product, which is to say on a choice the
    symmetric notation hides. Nothing computed here changes; what changes is that
    the receiver is visible in the symbol.

    This is notation, not physics. Adopting it asserts no Born rule, no
    measurement postulate, no collapse dynamics, and no claim that any particular
    ecology's constructions live in a Hilbert space. Where an ecology's returns
    are not complex scalars, only ("THE THREE ROLES") survives, and the bracket
    must be replaced by that ecology's own pairing.
  ],
)
