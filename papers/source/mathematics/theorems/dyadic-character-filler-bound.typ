#let dyadic-character-filler-bound = (
  key: "theorem:dyadic-character-filler-bound",
  kind: [Theorem],
  title: [The dyadic prime defect is a \(C_2\)-character signature and forces a symmetric filler],
  status: [Exact local operator constraint; the cross-channel filler remains unconstructed],
  depends: (
    "theorem:dyadic-euler-boundary-polarization",
    "theorem:weil-signature-transport",
  ),
  claim: [
    In the dyadic cell $cal(V)_4=op("span"){e_1,e_2,e_3,e_4}$, define the
    core--shell exchange
    $
      R e_1=e_3,
      quad R e_3=e_1,
      quad
      R e_2=e_4,
      quad R e_4=e_2.
    $
    Then $R=R^*=R^(-1)$ and, for the compressed translation $T$ of the
    dyadic polarization theorem,
    $
      R=T+T^*.
    $
    Its two exact character projectors are
    $
      P_+=(I+R)/2,
      quad
      P_-=(I-R)/2.
      quad "(CHARACTERS)"
    $
    Their ranges are respectively spanned by
    $
      s_1=(e_1+e_3)/sqrt(2),
      quad
      s_2=(e_2+e_4)/sqrt(2),
    $
    and
    $
      a_1=(e_1-e_3)/sqrt(2),
      quad
      a_2=(e_2-e_4)/sqrt(2).
    $

    Put $a=2^(-1/2)$, $ell=log 2$, and let $cal(D)_2$ be the Hermitian
    operator contributed by $-W_2$ to the completed-defect recurrence on
    this cell.  Then
    $
      cal(D)_2
      =
      ell(B_-^*B_--B_+^*B_+)
      =
      -ell a R
      =
      c(P_--P_+),
      quad
      c=frac(log 2,sqrt(2)).
      quad "(SIGNATURE)"
    $
    Thus the symmetric character space is exactly the two-dimensional
    negative subspace and the antisymmetric character space is exactly the
    two-dimensional positive subspace.  This inertia is invariant under
    every invertible rechart.

    Let an anchored linear section of admitted test currents carry
    $x in cal(V)_4$ to a current $f_x$ whose logarithmic prime channel is
    $x$.  Suppose the remaining predecessor and aperture terms define a
    bounded Hermitian operator $F_4$ by
    $
      chevron.l x,F_4x chevron.r
      =
      D_S(f_x)-kappa_(S,2)(f_x).
    $
    Positivity of the compressed successor defect requires
    $
      F_4+cal(D)_2>=0.
      quad "(SUCCESSOR)"
    $
    In particular,
    $
      P_+F_4P_+>=c P_+.
      quad "(SYMMETRIC DEMAND)"
    $
    Relative to $cal(V)_4=P_+cal(V)_4 ⊕ P_-cal(V)_4$, write
    $
      F_4=
      mat(
        F_(++),F_(+-);
        F_(-+),F_(--)
      ).
    $
    If $F_(--)+c I$ is strictly positive, ("SUCCESSOR") is equivalent to the
    Schur-complement condition
    $
      F_(--)+c I>0,
      quad
      F_(++)-c I
      >=
      F_(+-)(F_(--)+c I)^(-1)F_(-+).
      quad "(MIXED DEMAND)"
    $

    Finally, among positive operators $H>=0$ used to repair the isolated
    dyadic contribution,
    $
      cal(D)_2+H>=0,
    $
    every such filler obeys
    $
      P_+H P_+>=c P_+,
      quad
      op("Tr")(H)>=2c.
    $
    The unique minimum-trace filler is
    $
      H_min=c P_+,
      quad
      cal(D)_2+H_min=c P_-.
      quad "(MINIMUM FILLER)"
    $
  ],
  proof: [
    The displayed action of $T$ gives
    $T e_3=e_1$, $T e_4=e_2$, and zero on $e_1,e_2$; its adjoint reverses
    those arrows.  Hence $T+T^*=R$.  The exchange is a self-adjoint
    involution, so ("CHARACTERS") are its orthogonal spectral projectors and
    the displayed symmetric and antisymmetric vectors are their bases.

    The dyadic polarization theorem gives
    $
      B_-^*B_--B_+^*B_+=-a(T+T^*).
    $
    Multiplying by $ell$ and substituting $R=P_+-P_-$ proves
    ("SIGNATURE").  The signature statement and its invariance follow from
    the spectral decomposition and Hermitian inertia.

    Compressing ("SUCCESSOR") to $P_+cal(V)_4$ gives
    ("SYMMETRIC DEMAND").  In the character decomposition, the successor
    operator is
    $
      mat(
        F_(++)-c I,F_(+-);
        F_(-+),F_(--)+c I
      ),
    $
    whose positivity is equivalent to ("MIXED DEMAND") by the ordinary
    Schur-complement theorem under the stated strict-positivity hypothesis.

    If $cal(D)_2+H>=0$, compression to the negative character space gives
    $P_+ H P_+>=c P_+$ and therefore $op("Tr")(H)>=2c$.  The operator
    $H_min=c P_+$ reaches the bound and leaves $c P_-$.  Equality of the trace
    forces the $P_-$ compression of a positive $H$ to vanish; positivity
    then forces its cross blocks to vanish as well, proving uniqueness.
  ],
  boundary: [
    This theorem does not construct $F_4$, the Poisson--Sonin passage, or a
    global positive carrier.  It gives a necessary local signature which
    every such construction must satisfy after anchoring to this dyadic
    section.  The minimum filler is minimal only among additive positive
    repairs of the isolated prime contribution; the actual semilocal
    relation may be larger and may mix the two character spaces, in which
    case the Schur term is owed as well.

    The $1/2$ in the projectors $(I plus.minus R)/2$ is finite $C_2$
    character normalization.  The equality $a^2=1/2$ is the separate dyadic
    Euler balance.  Neither is the Mellin half-density merely because their
    rational glyphs agree.
  ],
)
