#let three-frame-counting-correspondence = (
  key: "definition:three-frame-counting-correspondence",
  kind: [Definition],
  title: [Three-frame counting correspondence],
  status: [Project definition; asynchronous relational base with no master clock],
  depends: (
    "definition:situated-event-correspondence",
    "definition:receiver",
  ),
  claim: [
    For $i in {1,2,3}$, a *local counting frame* is a tuple
    $
      cal(F)_i
      =
      (
        B_i,
        pi_i:cal(H)_i arrow.r B_i,
        nabla_i,
        rho_i
      ).
    $
    Here $B_i$ is the frame's oriented lineage of actual local events,
    $cal(H)_(i,b)$ is the family of constructions participating at
    $b in B_i$, $nabla_i$ is the admitted partial transport along that
    lineage, and $rho_i$ is a family of receiver maps.  A numeral or other
    glyph
    $
      n_(i,b)(v)=rho_(i,b)(v)
    $
    is a face of the counted construction $v$ in that receiver; it is not
    the identity of $v$ or of its lineage.

    Co-presence of the three frames is an incidence object $E$ with structure
    maps
    $
      tau_i:E arrow.r B_i,
      quad
      tau=(tau_1,tau_2,tau_3):
      E arrow.r B_1 times B_2 times B_3.
      quad "(INCIDENCE)"
    $
    The Cartesian product only addresses the three local positions.
    $E$ contains the incidences which actually occur and may distinguish
    multiple occurrences with the same addressed triple.  It need not be the
    full product and does not impose a common order on the $B_i$.

    At $e in E$, abbreviate
    $
      cal(H)_(i,e)=cal(H)_(i,tau_i(e)).
    $
    An oriented triangular comparison consists of partial cross-frame
    transports
    $
      T_(12,e):D_(12,e) arrow.r cal(H)_(2,e),
      quad
      T_(23,e):D_(23,e) arrow.r cal(H)_(3,e),
      quad
      T_(31,e):D_(31,e) arrow.r cal(H)_(1,e),
    $
    where
    $
      D_(12,e) subset cal(H)_(1,e),
      quad
      D_(23,e) subset cal(H)_(2,e),
      quad
      D_(31,e) subset cal(H)_(3,e).
    $
    Its complete admissible return domain is
    $
      D_(123,e)
      =
      D_(12,e)
      inter T_(12,e)^(-1)(D_(23,e))
      inter
      (T_(23,e)T_(12,e))^(-1)(D_(31,e)).
    $
    On this domain the first closed relational operator is
    $
      M_(123,e)
      =
      T_(31,e)T_(23,e)T_(12,e):
      D_(123,e) arrow.r cal(H)_(1,e).
      quad "(RETURN)"
    $
    If the transports are connection isomorphisms around a closed comparison
    cell, $M_(123,e)$ is its triangular holonomy.  If its domain is invariant,
    the returned defect
    $
      Omega_(123,e)=M_(123,e)-I
    $
    records failure of that oriented triangle to commute.

    When the incidence changes the participating frames, its successor must
    be supplied jointly:
    $
      (
        cal(F)_1^+,
        cal(F)_2^+,
        cal(F)_3^+
      )
      =
      Phi_e(
        cal(F)_1,
        cal(F)_2,
        cal(F)_3;
        T_(12,e),
        T_(23,e),
        T_(31,e)
      ).
      quad "(JOINT SUCCESSOR)"
    $
    No one edge, counter, or receiver owns that successor.
  ],
  proof: none,
  boundary: [
    The three lineage bases may each be discrete, continuous, or mixed, but
    any calculus used on them must be declared locally.  A parameter
    $t$ may enumerate one chosen receiver section through $E$; it is then a
    chart on that section, not a clock shared by all three frames.

    The definition does not assert that arbitrary frames admit transports,
    that the transports are invertible, or that a returned defect is
    positive.  A partial or noninvertible comparison remains a correspondence
    rather than a groupoid arrow.  The triangular return is the least closed
    relational face; it does not reconstruct the complete three lineages or
    reduce higher incidences to triples.
  ],
)
