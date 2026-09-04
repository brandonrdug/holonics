#let causal-time-parity = (
  key: "definition:causal-time-parity",
  kind: [Definition],
  title: [Causal time parity is opposed incidence on one shared time face],
  status: [Project definition in an ordinary oriented chain complex],
  depends: (
    "definition:situated-event-correspondence",
    "definition:holonic-process-double-category",
  ),
  claim: [
    Let $(C_*(X;A),partial)$ be an oriented occurrence complex with
    coefficients in an abelian group $A$.  A causal event grain from a
    receiving cut $Sigma_k$ to a later cut $Sigma_(k+1)$ is an oriented
    chain $E_k$ whose boundary has the form
    $
      partial E_k
      =
      Sigma_(k+1)-Sigma_k+Gamma_k,
      quad "(ONE CAUSAL GRAIN)"
    $
    where $Gamma_k$ is its exposed lateral world boundary.

    A composable family has *causal time parity* when the output cut of
    $E_k$ and the input cut of $E_(k+1)$ are the same occurrence-chain with
    their induced boundary orientations opposed.  Consequently,
    $
      partial
      (
        sum_(k=m)^(n-1)E_k
      )
      =
      Sigma_n-Sigma_m
      +
      sum_(k=m)^(n-1)Gamma_k.
      quad "(CAUSAL SWEEP)"
    $
    Every interior time face therefore cancels from the boundary of the
    composed sweep while remaining part of its causal interior.

    The same law applies between adjacent chain degrees: an interior
    $(r-1)$-face shared by oriented $r$-cells occurs once with each induced
    hand.  It is the incidence content of $partial_(r-1)partial_r=0$ and the
    discrete boundary face of telescoping and the fundamental theorem.
  ],
  proof: none,
  boundary: [
    Causal time parity is not an inverse event, a reconstruction of an
    earlier occurrence, or a claim that a physical process is reversible.
    It concerns the opposed incidence of one shared face under forward
    composition.  A conserved quantity additionally requires an additive
    coefficient-valued current or cocycle; parity supplies the cancellation
    by which that declared quantity composes.
  ],
)
