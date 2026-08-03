#let conditioned-effective-tension = (
  key: "theorem:conditioned-effective-tension",
  kind: [Theorem],
  title: [Shorting returns the shell's effective tension after the old body relaxes],
  status: [
    Exact variational, inertia, and sequential-short law; applied exactly to
    the first Weil support successor
  ],
  depends: (
    "theorem:conditioned-support-quotient-shorting",
    "theorem:weil-support-induction-reduction",
  ),
  claim: [
    Let a densely defined closed Hermitian form $q$ be written, after one
    conditioned quotient lift, on an old fiber $cal(V)_o$ and a quotient
    fiber $cal(B)$ as
    $
      q(x+tilde(J)y)
      =
      chevron.l A x,x chevron.r
      +2 op("Re")chevron.l C y,x chevron.r
      +chevron.l D y,y chevron.r.
      quad "(BLOCK ENERGY)"
    $
    Suppose the old operator has a strict gap
    $
      A>=lambda_o I,
      quad lambda_o>0.
      quad "(OLD GAP)"
    $
    Then the old response to a supplied quotient direction is the unique
    relaxed configuration
    $
      x_y=-A^(-1)C y.
      quad "(RELAXATION)"
    $
    The energy remaining after that response is represented by
    $
      S=D-C^*A^(-1)C,
      quad
      s(y)=chevron.l S y,y chevron.r
      =
      inf_(x in cal(V)_o)q(x+tilde(J)y).
      quad "(EFFECTIVE TENSION)"
    $
    More precisely,
    $
      q(x+tilde(J)y)
      =
      norm(A^(1/2)(x+A^(-1)C y))^2
      +chevron.l S y,y chevron.r.
      quad "(RELAXED INTERIOR)"
    $

    If $S$ is read as an operator from quotient displacement to its residual
    generalized force, then
    $
      tau_"eff"(y)=S y
    $
    is the effective tension seen at that quotient after every old-interior
    direction has equilibrated.  It is the nonlocal
    Dirichlet-to-Neumann or Steklov face of the declared decomposition:
    supplied boundary data go in; the unexplained returned force comes out.
    This statement uses only the variational relation and does not require a
    local differential equation.

    The block form is congruent to the relaxed diagonal form:
    $
      mat(A,&C;C^*,&D)
      =
      mat(I,&0;C^*A^(-1),&I)
      mat(A,&0;0,&S)
      mat(I,&A^(-1)C;0,&I).
      quad "(INERTIA SPLIT)"
    $
    Consequently all negative and null directions not already present in the
    strictly positive old body belong exactly to $S$.  In particular,
    $
      q>=0
      quad arrow.l.r quad
      S>=0.
      quad "(STABILITY)"
    $
    The reduced boundary energy
    $
      E_"eff"(y)=inf_x q(x+tilde(J)y)=chevron.l S y,y chevron.r
    $
    has Hessian $2S$.  Thus positive, null, and negative tension are exactly
    convex, flat, and concave directions of the relaxed response.  Along a
    parameterized family, a zero mode of $S$ is the discriminant at which
    one reduced direction can pass between convexity and concavity.

    Shorting is associative.  For nested old interiors
    $cal(V)_0 subset cal(V)_1 subset cal(V)_2$, whenever the displayed
    relaxations exist,
    $
      (q/cal(V)_0)/(cal(V)_1/cal(V)_0)
      =
      q/cal(V)_1,
      quad "(ASSOCIATIVE SHORT)"
    $
    because both sides minimize $q$ over the same complete
    $cal(V)_1$ interior.  Thus a completed lower-grain response may depart
    while its effective boundary law becomes the next standing form.

    There is a necessary distinction between effective tension and an
    arbitrary equilibrium Hessian.  If $A v=lambda v$ with $norm(v)=1$ is a
    ground state, the constrained second variation on
    $v^perp$ is
    $
      2 chevron.l (A-lambda I)eta,eta chevron.r.
      quad "(MODE HESSIAN)"
    $
    Replacing $A$ by $A-c I$ replaces $lambda$ by $lambda-c$ and leaves
    ("MODE HESSIAN") unchanged.  Therefore standing-wave modes, nodes,
    antinodes, and local equilibrium stability cannot by themselves determine
    whether the absolute ground value is positive.  The zero of the Weil
    response must remain calibrated by the explicit formula.

    Apply this theorem to the first conditioned Weil successor.  Let
    $A_2$ represent the strictly positive $P(2)$ form, let $C_(2,3)$ be the
    already-carried old/shell cross, and let $D_(2,3)$ be the conditioned
    shell block of the exact zeta screw kernel.  Then
    $
      S_(2,3)
      =
      D_(2,3)-C_(2,3)^*A_2^(-1)C_(2,3)
      =
      D_(2,3)-Y_(2,3)^*Y_(2,3).
      quad "(FIRST TENSION)"
    $
    Here $C_(2,3)=A_2^(1/2)Y_(2,3)$ is the reduced cross carrier.  Hence
    $S_(2,3)$ is not an additional global Gram object.  The component Gram
    expansion is one coordinate expansion of the energy absorbed by the
    single old response $A_2^(-1)C_(2,3)y$.  The first RH-support obligation
    is exactly that the returned effective tension ("FIRST TENSION") have no
    negative mode.
  ],
  proof: [
    Differentiate ("BLOCK ENERGY") in an arbitrary old direction.  The
    stationarity equation is
    $
      A x+C y=0,
    $
    and ("OLD GAP") makes its solution unique, proving ("RELAXATION").
    Substitute that solution, or complete the square, to obtain
    ("EFFECTIVE TENSION") and ("RELAXED INTERIOR").  Differentiating the
    effective quadratic form in a quotient direction gives $S y$, which is
    precisely the residual force after the old stationarity equation has
    been solved.

    Direct multiplication proves ("INERTIA SPLIT").  Congruence by an
    invertible triangular operator preserves inertia, proving ("STABILITY").
    For ("ASSOCIATIVE SHORT"), write a representative as $x_0+x_1+y$ and
    observe
    $
      inf_(x_1)inf_(x_0)q(x_0+x_1+y)
      =
      inf_(x in cal(V)_1)q(x+y).
    $

    The Lagrange multiplier equation for the unit sphere is
    $A v=lambda v$.  Its second variation is ("MODE HESSIAN").  The displayed
    scalar shift cancels between the operator and its ground value, proving
    the calibration warning.

    In the first Weil cell, the published strict base gap makes $A_2^(-1)$
    bounded on the old carrier.  The conditioned-support theorem supplies
    $C_(2,3)=A_2^(1/2)Y_(2,3)$.  Substitution into
    ("EFFECTIVE TENSION") gives ("FIRST TENSION"), while the inertia split
    proves its exact equivalence to the first successor sign.
  ],
  boundary: [
    This theorem replaces the phrase “global Gram dominance” with the
    invariant object it was trying to name: effective tension after internal
    relaxation.  It does not prove that $S_(2,3)>=0$.  It proves that no
    separate knot energy, favorable perspective, equilibrium picture, or
    componentwise prime estimate can decide that sign.  A proof must bound
    the source-derived zeta screw kernel's conditioned
    Dirichlet-to-Neumann operator at its explicit-formula zero level.
  ],
)
