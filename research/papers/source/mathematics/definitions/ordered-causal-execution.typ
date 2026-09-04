#let ordered-causal-execution = (
  key: "definition:ordered-causal-execution",
  kind: [Definition],
  title: [Ordered causal execution and its positive residual subcategory],
  status: [Project definition; analytic representation of a holonic process],
  depends: (
    "definition:holonic-process-double-category",
    "definition:situated-event-correspondence",
  ),
  claim: [
    Let $op("Exec")_plus.minus$ be the following category. An object is a
    receiver boundary
    $
      (cal(A),omega),
      quad
      omega in cal(A)^*_+,
    $
    where $cal(A)$ is a unital C-star-algebra of distinctions available at
    that boundary and $omega$ is a positive response functional.

    An arrow
    $
      e:(cal(A),omega) arrow.r (cal(B),nu)
    $
    is a pair $(alpha_e,Delta_e)$ consisting of a completely positive map
    $
      alpha_e:cal(B) arrow.r cal(A)
    $
    and a Hermitian functional $Delta_e in cal(B)^*_"h"$ such that
    $
      nu=omega compose alpha_e+Delta_e.
      quad "(EXECUTION BALANCE)"
    $
    The map $alpha_e$ is the carried receiver transport. The functional
    $Delta_e$ is the event residual after the later boundary has been pulled
    back to the earlier one.

    The identity is $(1,0)$. If
    $
      e=(alpha,Delta):
      (cal(A),omega) arrow.r (cal(B),nu)
    $
    and
    $
      f=(beta,E):
      (cal(B),nu) arrow.r (cal(C),mu),
    $
    then
    $
      f compose e
      =
      (
        alpha compose beta,
        Delta compose beta+E
      ).
      quad "(RESIDUAL COMPOSITION)"
    $

    The wide subcategory $op("Exec")_+$ contains exactly the arrows with
    $Delta_e>=0$. A domain-level *ordered causal execution representation*
    is a composition-preserving representation
    $
      Phi_D:
      op("HolProc")_cal(D)^0
      arrow.r
      op("Exec")_plus.minus.
    $
    An event selected by $Lambda_F$ is positive in that domain precisely
    when its image lands in $op("Exec")_+$; positivity is not imposed on
    every holonic event.

    Complete positivity makes the carried transport stable under arbitrary
    finite co-presence:
    $
      op("id")_(M_n) ⊗ alpha_e
    $
    preserves the positive cone for every $n$. Thus one event is tested on
    complete finite receiver complexes, not only on isolated scalar
    diagonals.

    If $r mapsto omega_r$ is a weakly differentiable path on one anchored
    receiver algebra, its identity-carried tangent residual is
    $
      Gamma_r=partial_r omega_r.
    $
    It is a *positive execution current* when $Gamma_r>=0$. Whenever this
    holds on $[r_1,r_2]$, the transported fundamental theorem gives the
    finite positive-residual event
    $
      omega_(r_2)
      =
      omega_(r_1)
      +
      integral_(r_1)^(r_2) Gamma_r dif r.
      quad "(CURRENT-TO-EVENT)"
    $
  ],
  proof: [
    Substituting the first execution balance into the second gives
    $
      mu
      =
      nu compose beta+E
      =
      omega compose alpha compose beta
      +
      Delta compose beta
      +
      E,
    $
    which is exactly residual composition. Associativity follows from
    associativity of map composition and addition of functionals. The pair
    $(1,0)$ is a two-sided identity.

    If $Delta>=0$, $E>=0$, and $beta$ is completely positive, then
    $Delta compose beta>=0$ and therefore
    $
      Delta compose beta+E>=0.
    $
    Hence positive-residual arrows are closed under composition. Stability
    under co-presence is the defining matrix-amplification property of a
    completely positive map.
  ],
  boundary: [
    The source boundary is supplied; this definition does not create an
    initial state, vocabulary, or observable algebra from nothing.
    $Lambda_F$ selects an admissible causal process, while $Phi_D$ gives that
    process its domain-specific analytic meaning.

    A negative or indefinite residual is a lawful signed or OPEN event in
    $op("Exec")_plus.minus$ rather than a contradiction in the carrier.
    Declaring every residual positive would insert the desired domain
    theorem as an axiom. Complete positivity governs carried transport under
    co-presence; it does not prove that the separately exposed residual is
    positive.
  ],
)
