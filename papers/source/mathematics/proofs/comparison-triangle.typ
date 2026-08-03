#import "../../lib/elements.typ": *

// A reusable geometric proof face for theorem:comparison-boundary. The same
// edge occurrences recur in the problem, construction, figure, and equation.

#let comparison-triangle-proof = (
  key: "proof:comparison-triangle",
  title: [Construct the comparison face],
  status: [Exact geometric demonstration],
  depends: (
    "definition:comparison-face",
    "theorem:comparison-boundary",
  ),
  render: () => construction-card(
    title: [Proposition I -- Construct the comparison face],
    problem: [
      Given actual occurrences $A,B,C$, the
      #segment-token(by-blue, name: [$u$]) path from $A$ to $B$, the
      #segment-token(by-yellow, name: [$v$]) path from $B$ to $C$, and the
      #segment-token(by-red, name: [$w$]) path from $A$ to $C$, construct the
      oriented comparison admitted between the composite route and the direct
      route.
    ],
    diagram: comparison-triangle-figure(),
    demonstration: [
      Join #point-token(by-black, name: [$A$]) to
      #point-token(by-black, name: [$B$]) by
      #segment-token(by-blue, name: [$u$]); join
      #point-token(by-black, name: [$B$]) to
      #point-token(by-black, name: [$C$]) by
      #segment-token(by-yellow, name: [$v$]); and join
      #point-token(by-black, name: [$A$]) directly to
      #point-token(by-black, name: [$C$]) by
      #segment-token(by-red, name: [$w$]).

      The supplied comparison is the oriented face $tau$ whose boundary
      traverses #segment-token(by-blue, name: [$u$]), then
      #segment-token(by-yellow, name: [$v$]), and returns against
      #segment-token(by-red, name: [$w$]).
    ],
    algebra: [
      $
        partial tau
        = #colored-term(by-yellow, $v$)
          - #colored-term(by-red, $w$)
          + #colored-term(by-blue, $u$),
      $
      with
      $
        partial u=B-A, quad
        partial v=C-B, quad
        partial w=C-A.
      $
    ],
    conclusion: [
      $partial^2 tau=0$. The same vertex occurrences cancel with opposed
      orientation. This certifies the boundary of the supplied comparison; it
      does not assert that $T_v compose T_u=T_w$.
    ],
  ),
)
