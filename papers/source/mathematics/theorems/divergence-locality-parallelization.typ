#let divergence-locality-parallelization = (
  key: "theorem:divergence-locality-parallelization",
  kind: [Theorem],
  title: [Flux locality is the parallelization license, and a global constraint is the barrier],
  status: [Exact for the divergence and Schur statements; the apparatus reading is a corollary and is named as one],
  depends: (
    "definition:causal-time-parity",
    "theorem:transported-fundamental-theorem",
    "definition:receiver-configuration-calculus",
  ),
  claim: [
    *(DIVERGENCE)* For a compact region $V$ with piecewise-smooth boundary and a
    $C^1$ field $F$,
    $
      integral_V nabla dot F dif v = integral.cont_(partial V) F dot n dif a.
      quad "(DIVERGENCE THEOREM)"
    $
    This is #emph[theorem:transported-fundamental-theorem] at top degree: the
    interior integral of a derivative equals the boundary pairing, and the
    boundary is the only place the interior speaks.

    *(CONTINUITY, WITH STORAGE)* Conservation is the continuity relation
    $
      (partial rho)/(partial t) + nabla dot J = s,
      quad "(CONTINUITY)"
    $
    whose discrete form is the spine's chain law
    $q_(k+1)-q_k+B j_k=r_k$ with $B$ the oriented incidence. Kirchhoff's current
    law is the *special case* $partial rho\/partial t = 0$: the sum of currents at
    a node vanishes only when nothing is stored there. A capacitor is precisely a
    node where $partial rho\/partial t != 0$, so instantaneous balance is not a
    law but a declared regime, and the general law is the telescoping identity
    over orders of time.

    *(LOCALITY)* Partition $V$ into subdomains ${V_alpha}$. By ("DIVERGENCE
    THEOREM") the coupling between $V_alpha$ and its complement is *entirely* the
    flux through $partial V_alpha$. Hence:

    #block(inset: (left: 10pt))[
      *A computation over a partition decouples exactly to the extent that its
      terms are boundary fluxes. Every term that is not a flux is a barrier.*
    ]

    *(THE BUILT INSTANCE)* For a discrete transport operator $M$ ordered as
    interior $I$ and interface $partial$, eliminating the interiors gives the
    Schur complement
    $
      S = M_(partial partial)-M_(partial I)M_(I I)^(-1)M_(I partial),
      quad
      u_I = -M_(I I)^(-1)M_(I partial)f,
      quad "(INTERIOR ELIMINATION)"
    $
    and $M_(I I)$ is block diagonal over the subdomains, so *every interior
    elimination is independent and the interface solve is the only meeting.*
    That is domain decomposition, and it is ("LOCALITY") as an algorithm.

    *(THE BARRIER)* A constraint that is not a flux does not decouple. In the
    incompressible Navier--Stokes system
    $
      (partial u)/(partial t)+(u dot nabla)u
      =-1/rho nabla p+nu nabla^2 u,
      wide
      nabla dot u = 0,
      quad "(NAVIER--STOKES)"
    $
    advection and diffusion are local stencils and parallelize over any
    partition; the constraint $nabla dot u=0$ determines $p$ through
    $nabla^2 p = -rho nabla dot ((u dot nabla)u)$, an elliptic solve coupling the
    *whole* domain at once. The pressure projection is the barrier, and it is
    the barrier because incompressibility is a statement about the domain rather
    than about any cell.

    *(CHART TRANSPORT)* Between charts $phi:U -> V$ the measure carries the
    Jacobian,
    $
      integral_V f(y) dif y = integral_U f(phi(x))abs(det D phi_x) dif x,
    $
    so a density is a top-degree form and the Jacobian is its rebase weight. The
    weight under which transport is unitary with no preferred measure is the
    *square root*, and its sign ambiguity is the half turn.
  ],
  proof: [
    ("DIVERGENCE THEOREM") is the generalized Stokes theorem for the
    $(n-1)$-form $iota_F dif v$, and ("CONTINUITY") is its integral form applied
    to a fixed region with $rho$ the retained content. The discrete statement is
    the chain law with $B$ the coboundary of the incidence complex.

    For ("INTERIOR ELIMINATION"), block-eliminate: from
    $M_(I I)u_I + M_(I partial)u_partial = f_I$ one has
    $u_I = M_(I I)^(-1)(f_I - M_(I partial)u_partial)$, and substituting into the
    interface row gives $S u_partial = f_partial - M_(partial I)M_(I I)^(-1)f_I$.
    $M_(I I)$ is block diagonal over subdomains because a coupling between two
    distinct interiors would be an interior--interior term that is not on any
    interface, and the partition places every such term on $partial$.

    ("THE BARRIER"): take the divergence of the momentum equation and impose
    $nabla dot u = 0$; the time-derivative and viscous terms drop and the
    stated Poisson equation remains. Its solution operator is the inverse
    Laplacian, whose Green's function has global support, so no partition
    decouples it.
  ],
  boundary: [
    ("DIVERGENCE THEOREM") requires the stated regularity; it is false for fields
    with non-integrable divergence, and a discrete complex must supply its own
    incidence rather than inherit it.

    *("LOCALITY") is a statement about coupling, not about cost.* It says which
    terms can be evaluated without communication; it does not say that doing so
    is faster, that the interface solve is cheap, or that a given partition is
    balanced. Load, latency, and residency are apparatus testimony and belong to
    a measured receipt, never to this statement.

    *The apparatus reading is a corollary and inherits nothing beyond its
    hypothesis.* A computation whose coupling is *not* a flux may still
    parallelize for reasons this theorem does not supply, and a computation whose
    coupling is a flux may still fail to parallelize because its schedule is
    order-dependent. Interchange of co-present events must be proved for the
    material at hand; ("LOCALITY") licenses the decomposition, not the schedule.

    Navier--Stokes is used here as the canonical instance of a global
    constraint. Nothing asserts that any ecology in this project obeys it.
  ],
)
