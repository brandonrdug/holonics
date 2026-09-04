#let causal-parity-kirchhoff-return = (
  key: "theorem:causal-parity-kirchhoff-return",
  kind: [Theorem],
  title: [Causal parity carries balance, Kirchhoff duality, and phase return],
  status: [
    Exact chain/cochain, junction-scattering, and positive-real return law
    under the displayed additive and constitutive hypotheses
  ],
  depends: (
    "definition:causal-time-parity",
    "theorem:transported-fundamental-theorem",
    "theorem:passive-incidence-kron-composition",
  ),
  claim: [
    Let $B:C_1(X;A) arrow.r C_0(X;A)$ be the oriented incidence of a
    finite occurrence complex and let $d=B^*$ be its coboundary in a
    supplied inner-product chart.  Let an additive $A$-valued current on
    each causal grain have stored cut-value $q_k$, integrated edge current
    $j_k$, and source or exterior return $r_k$.  Discrete Stokes on
    ("ONE CAUSAL GRAIN") gives
    $
      q_(k+1)-q_k+B j_k=r_k.
      quad "(EVENT BALANCE)"
    $
    Causal time parity then gives, for every completed order of time,
    $
      q_n-q_m
      +
      B sum_(k=m)^(n-1)j_k
      =
      sum_(k=m)^(n-1)r_k.
      quad "(INTERVAL BALANCE)"
    $
    Thus zero instantaneous incidence is not required: a nonzero $B j_k$
    can be carried by storage change.  If $q_n=q_m$ and the interval is
    source-free, the integrated current is a cycle.

    For a relative node potential $phi$, put $v=d phi$.  Every current cycle
    $c in ker B$ satisfies
    $
      chevron.l v,c chevron.r
      =
      chevron.l phi,B c chevron.r
      =
      0.
      quad "(KIRCHHOFF LOOP)"
    $
    More generally, for a connection cochain $a$ and a supplied comparison
    face $Sigma$,
    $
      chevron.l a,partial Sigma chevron.r
      =
      chevron.l d a,Sigma chevron.r.
      quad "(CURVED LOOP)"
    $
    The zero-voltage loop is the exact or flat case; nonzero loop return is
    the curvature or changing interior carried by the spanning face.

    At one lossless junction let $a_j,b_j$ be incoming and outgoing
    amplitudes on branches with positive admittances $Y_j$.  Continuity and
    oriented current balance are
    $
      u=a_j+b_j,
      quad
      sum_j Y_j(b_j-a_j)=0.
    $
    Hence
    $
      u
      =
      2 frac(sum_j Y_j a_j,sum_j Y_j),
      quad
      b_j
      =
      2 frac(sum_l Y_l a_l,sum_l Y_l)-a_j.
      quad "(JUNCTION RETURN)"
    $
    The resulting scattering map $S:a mapsto b$ preserves the
    $Y$-weighted flux.  With one incoming parent and daughter branches its
    reflected amplitude is
    $
      frac(
        Y_"parent"-sum_d Y_d,
        Y_"parent"+sum_d Y_d
      ).
      quad "(BRANCH REFLECTION)"
    $
    It vanishes exactly at admittance matching.

    Let an edge of exact length $ell_e$ carry phase
    $P_e(kappa)=e^(i kappa ell_e)$ and let $P(kappa)$ be the diagonal
    propagation law.  A standing current is precisely a fixed current of
    one complete propagation and junction return:
    $
      S P(kappa)a=a.
      quad "(STANDING RETURN)"
    $
    Along a closed path this is the phase-closure relation
    $
      sum_e kappa_e ell_e+sum_j delta_j=n Theta,
    $
    where $Theta$ is one full turn and the $delta_j$ are junction turns.
    In a uniform branch the least positive closure length is therefore
    $
      lambda=Theta/abs(kappa).
      quad "(WAVELENGTH)"
    $

    Finally let $W>=0$ be an edge conductance or stiffness and $G>=0$ a
    storage operator.  For $op("Re")z>0$ define the dynamic incidence law
    $
      L(z)=d^* W d+z G.
      quad "(DYNAMIC BODY)"
    $
    Split its variables into interior and boundary ports and write
    $
      L(z)=mat(A(z),&B(z);C(z),&D(z)).
    $
    Whenever $A(z)$ is invertible, imposing zero interior injection returns
    the boundary response
    $
      S_B(z)
      =
      D(z)-C(z)A(z)^(-1)B(z).
      quad "(DYNAMIC SHORT)"
    $
    It is positive real:
    $
      op("Re")
      chevron.l S_B(z)y,y chevron.r
      >=0
      quad
      "for "op("Re")z>0.
      quad "(PASSIVE RETURN)"
    $
  ],
  proof: [
    Pairing an additive current with the oriented boundary of one event
    gives ("EVENT BALANCE").  Summing those identities cancels every
    intermediate $q_k$ by causal time parity and proves
    ("INTERVAL BALANCE").

    The Kirchhoff identity is the adjoint relation
    $chevron.l d phi,c chevron.r=chevron.l phi,B c chevron.r$.
    ("CURVED LOOP") is discrete Stokes.  It also shows why a loop with
    changing enclosed flux has a returned interior term rather than
    violating conservation.

    At the junction, $b_j=u-a_j$.  Substitution into current balance gives
    $u sum_j Y_j=2 sum_j Y_j a_j$, proving ("JUNCTION RETURN") and
    ("BRANCH REFLECTION").  In matrix form,
    $
      S
      =
      2 bold(1) Y/(bold(1)^* Y bold(1))-I,
    $
    so direct multiplication gives $S^*Y S=Y$.  Propagation preserves the
    same flux when the phases have unit modulus.  A standing current is
    therefore a unit-return eigenvector; multiplying its edge and junction
    phases around a closed path gives ("WAVELENGTH").

    For the dynamic body,
    $
      op("Re")chevron.l L(z)x,x chevron.r
      =
      norm(W^(1/2) d x)^2
      +
      op("Re")(z)norm(G^(1/2)x)^2
      >=0.
    $
    Given boundary value $y$, put
    $x=-A(z)^(-1) B(z) y$.  Then
    $L(z)(x⊕y)=0⊕S_B(z) y$, so
    $
      op("Re")
      chevron.l S_B(z)y,y chevron.r
      =
      op("Re")
      chevron.l L(z)(x⊕y),x⊕y chevron.r
      >=0.
    $
    This proves ("PASSIVE RETURN").
  ],
  boundary: [
    The oriented complex supplies legal composition and cancellation; it
    does not select $A$, $W$, $G$, $Y$, a metric, or a coefficient system.
    Those are parameters of the represented ecology.  The theorem applies
    equally when the coefficients represent electrical charge, chemical
    storage, mechanical action, probability amplitude, or an analytic
    boundary field, provided the displayed hypotheses are actually
    supplied.  A lossy junction gives a weighted contraction rather than a
    flux isometry.  A globally nonexact connection may carry nontrivial
    loop holonomy even where its local curvature vanishes.
  ],
)
