#let dyadic-poisson-half-filler = (
  key: "theorem:dyadic-poisson-half-filler",
  kind: [Theorem],
  title: [Dyadic periodization constructs the minimum positive half-filler],
  status: [
    Exact local Poisson quotient and isolated dyadic filler; it is a
    successor-metric defect face, not a semilocal successor map
  ],
  depends: (
    "theorem:dyadic-euler-boundary-polarization",
    "theorem:dyadic-character-filler-bound",
    "theorem:oriented-half-density-crossing",
  ),
  claim: [
    Retain the dyadic logarithmic cell
    $
      cal(V)_4=op("span"){e_1,e_2,e_3,e_4},
      quad
      ell=log 2,
    $
    of the boundary-polarization theorem, with
    $e_1=U_ell e_3$ and $e_2=U_ell e_4$. Let
    $
      F=[-ell/2,ell/2]
    $
    be a fundamental domain for the lattice $ell ZZ$, and let
    $
      (Pi_ell h)(u)
      =
      sum_(k in ZZ)h(u+k ell),
      quad u in F,
      quad "(PERIODIZATION)"
    $
    be logarithmic periodization. On $cal(V)_4$, there are orthonormal,
    disjointly supported $q_1,q_2 in L^2(F)$ such that
    $
      Pi_ell e_1=Pi_ell e_3=q_1,
      quad
      Pi_ell e_2=Pi_ell e_4=q_2.
    $
    Therefore
    $
      Pi_ell^*Pi_ell=2P_+,
      quad
      op("ker")(Pi_ell)=P_- cal(V)_4,
      quad
      overline(Pi)_ell=Pi_ell/sqrt(2),
      quad
      overline(Pi)_ell^*overline(Pi)_ell=P_+.
      quad "(POSITIVE HALF QUOTIENT)"
    $
    Here $P_+=(I+R)/2$ is the symmetric core--shell character projector.
    Its rank is two of four, so its normalized operator area is exactly
    $op("Tr")(P_+)/op("Tr")(I)=1/2$.

    Put
    $
      a=2^(-1/2),
      quad
      c=ell a=frac(log 2,sqrt(2)).
    $
    The source-normalized dyadic Poisson amplitude
    $
      A_("Pois",2)
      =
      sqrt(c) overline(Pi)_ell
      quad "(POISSON AMPLITUDE)"
    $
    has the exact Gram operator
    $
      A_("Pois",2)^*A_("Pois",2)
      =
      c P_+
      =
      H_min.
      quad "(LOCAL FILLER)"
    $
    Consequently the isolated dyadic completed-defect cell closes as
    $
      cal(D)_2+A_("Pois",2)^* A_("Pois",2)
      =
      c P_-
      >=0.
      quad "(CLOSED LOCAL CELL)"
    $

    Formula ("PERIODIZATION") is an actual Poisson relation: with
    $hat(h)(xi)=integral_RR h(u)e^(-i xi u)dif u$,
    $
      Pi_ell h(u)
      =
      frac(1,ell)
      sum_(n in ZZ)
      hat(h)(2 pi n/ell)e^(2 pi i n u/ell).
      quad "(POISSON SERIES)"
    $
    The coefficient $a$ in ("POISSON AMPLITUDE") is independently fixed by
    the $n=2$ arm of the global scaling map,
    $
      e^(u/2) f(2e^u)=2^(-1/2) h(u+ell),
    $
    while $ell$ is its logarithmic Euler weight. The remaining factor
    $1/sqrt(2)$ is the exact normalization of the two-to-one quotient in
    ("POSITIVE HALF QUOTIENT").
  ],
  proof: [
    Only one translate of each $e_j$ meets the fundamental domain. Since
    $e_1=U_ell e_3$ and $e_2=U_ell e_4$, periodization identifies each
    translated pair. Thus, for
    $x=sum_j x_j e_j$,
    $
      Pi_ell x
      =
      (x_1+x_3)q_1+(x_2+x_4)q_2.
    $
    Its Gram matrix is the direct sum of two matrices
    $
      mat(1,1;1,1)
      =
      2 mat(1/2,1/2;1/2,1/2),
    $
    proving ("POSITIVE HALF QUOTIENT"). The kernel is the antisymmetric
    character space.

    Multiplying the normalized quotient by $sqrt(c)$ gives
    ("LOCAL FILLER"). The dyadic character theorem gives
    $
      cal(D)_2=c(P_--P_+),
    $
    so addition cancels exactly the symmetric negative component and proves
    ("CLOSED LOCAL CELL"). Formula ("POISSON SERIES") is the ordinary
    Poisson summation formula on the lattice $ell ZZ$. The half-density
    calculation of the scaling map gives the displayed coefficient $a$;
    differentiating its scale character supplies the factor $ell$.
  ],
  boundary: [
    This theorem closes the unique minimum-trace filler for the isolated
    four-cell dyadic defect by an actual lattice quotient.  It cannot be the
    restriction of the semilocal Sonin successor: the quotient has the
    nonzero kernel $P_-cal(V)_4$, whereas prime admission and its dual return
    are invertible.  The semilocal Sonin theorem already makes prime
    admission commute with every nested aperture.

    The remaining RH-bearing statement is therefore form-level.  The
    support successor must couple the old positive body to the newly admitted
    shell, realize this local quotient as a defect face of that coupling, and
    pay the resulting cross-character shorted-shell term.
  ],
)
