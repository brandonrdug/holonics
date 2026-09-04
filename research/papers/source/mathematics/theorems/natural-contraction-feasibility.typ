#let natural-contraction-feasibility = (
  key: "theorem:natural-contraction-feasibility",
  kind: [Theorem],
  title: [Coherent contractive fillers form a convex feasibility set],
  status: [Exact operator-theoretic reduction],
  depends: (
    "theorem:semilocal-successor-defect-contraction",
    "theorem:positive-perspective-descent",
  ),
  claim: [
    Let $cal(J)$ be a small category of support, prime, and receiver
    transitions. Let $cal(T),cal(K)_X,cal(K)_Y:cal(J) arrow.r op("Hilb")$
    be Hilbert-space functors and let
    $
      X:cal(T) arrow.r cal(K)_X,
      quad
      Y:cal(T) arrow.r cal(K)_Y
    $
    be natural amplitude transformations.

    Define $cal(C)(X,Y)$ to be the families of bounded maps
    $Gamma_j:cal(K)_(X,j) arrow.r cal(K)_(Y,j)$ satisfying
    $
      Gamma_j X_j=Y_j,
      quad norm(Gamma_j)<=1,
    $
    and, for every $a:j arrow.r k$,
    $
      cal(K)_Y(a) Gamma_j
      =
      Gamma_k cal(K)_X(a).
    $
    Then $cal(C)(X,Y)$ is convex and weak-operator closed. In finite
    dimensions its contraction condition is the linear matrix inequality
    $
      mat(
        1, Gamma_j^*;
        Gamma_j, 1
      ) >= 0.
    $

    If every finite collection of equations ("F"), ("N"), and ("LMI") has a
    simultaneous solution, then $cal(C)(X,Y)$ is nonempty. For every
    $Gamma in cal(C)(X,Y)$ and every $j$,
    $
      norm(X_j f)^2-norm(Y_j f)^2
      =
      norm((1-Gamma_j^* Gamma_j)^(1/2) X_j f)^2
      >=0.
    $
  ],
  proof: [
    Factorization and naturality are affine linear equations in the
    components $Gamma_j$. Operator unit balls are convex, so their
    intersection with those equations is convex. The unit ball is
    weak-operator compact and the displayed equations are weak-operator
    closed. Their product over $j$ is compact. Feasibility of every finite
    collection gives the finite-intersection property, hence a simultaneous
    family exists.

    In finite dimensions, the Schur complement identifies the displayed
    block inequality with
    $1-Gamma_j^* Gamma_j>=0$ in the operator order. Substituting
    $Y_j=Gamma_j X_j$ yields
    the displayed defect identity. Componentwise, the equivalence between norm domination and
    contractive factorization is the Douglas factorization principle.
  ],
  boundary: [
    Pointwise contractions need not satisfy naturality. Finite numerical
    feasibility does not establish feasibility for every finite constraint
    family, and approximate feasibility does not establish the exact
    factorization. The compactness clause reduces a coherent infinite
    construction to exact finite compatibility; it does not supply the
    arithmetic reason those finite feasible sets are nonempty. Because
    $Gamma_j X_j=Y_j$ is inhomogeneous when $Y_j!=0$, this set is generally
    not a cone: scaling a filler need not leave it feasible.
  ],
)
