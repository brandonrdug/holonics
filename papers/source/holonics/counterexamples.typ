#import "schema.typ": entry

#let counterexamples = (
  entry(
    id: "C.0001",
    kind: "Counterexample",
    grade: "counterexample",
    title: [Contraction does not pass through arbitrary analysis and synthesis maps],
    depends: ("RH.0010",),
    statement: [
      The implication
      $
        K^*K<=I
        and
        C E=I
        arrow.r
        (C K E)^*(C K E)<=I
      $
      is false.
    ],
    derivation: [
      Take
      $
        C=mat(1,0),
        quad
        E=mat(1;2),
        quad
        K=mat(0,1;1,0).
      $
      Then $C E=1$ and $K^*K=I$, but $C K E=2$, so
      $(C K E)^*(C K E)=4>1$.
    ],
    transformations: [
      A valid lift needs
      $
        K^*C^*C K<=C^*C
      $
      on the relevant range, or directly
      $
        E^*K^*C^*C K E<=I.
      $
    ],
    boundary: [
      This rejects only the unsupported pull-through implication. It does not
      reject a route that separately proves the weighted inequality.
    ],
    source: [Exact laboratory counterexample to a recent Volterra/Weyl lift.],
  ),
  entry(
    id: "C.0002",
    kind: "Counterexample",
    grade: "counterexample",
    title: [Stationarity on a constraint fiber does not imply positivity],
    depends: ("H.0013",),
    statement: [
      Nonnegativity on a constraint kernel together with an orthogonal or
      stationary chosen representative need not make the full quadratic form
      nonnegative.
    ],
    derivation: [
      Let
      $
        Q(x,y)=y^2-3x^2,
        quad
        R(x,y)=x.
      $
      On $ker R={x=0}$, $Q(0,y)=y^2>=0$. The representative $(x,0)$ is
      stationary/orthogonal in the fiber direction, yet
      $Q(x,0)=-3x^2<0$ for $x!=0$.
    ],
    boundary: [
      Euler--Lagrange orthogonality supplies a criticality condition, not the
      missing global sign.
    ],
    source: [Exact laboratory counterexample.],
  ),
  entry(
    id: "C.0003",
    kind: "Counterexample",
    grade: "counterexample",
    title: [Finite verification cannot discharge an unbounded criterion],
    depends: ("RH.0030", "RH.0060", "RH.0140"),
    statement: [
      From $P(n)$ for all $n<=N$ one cannot infer
      $forall n in NN: P(n)$ without an induction, monotonicity, finite
      reduction, or other theorem connecting the tail.
    ],
    derivation: [
      For any chosen $N$, define $P(n)$ to be $n<=N$. Every checked case
      succeeds and $P(N+1)$ fails.
    ],
    boundary: [
      This does not diminish computational witnesses. It fixes their grade and
      identifies the exact bridge an infinite claim still owes.
    ],
    source: [Elementary logical counterexample.],
  ),
  entry(
    id: "C.0004",
    kind: "Counterexample",
    grade: "counterexample",
    title: [Positive source moments need not survive a nonlinear logarithmic transform],
    depends: ("RH.0040",),
    statement: [
      Positivity of the coefficients or moments of a source function does not
      by itself imply that the coefficients of its logarithmic derivative form
      a Stieltjes moment sequence.
    ],
    derivation: [
      The polynomial $A(w)=1+w+w^2$ has positive coefficients, but its zeros
      are the nonreal primitive cube roots of unity. Hence $A'/A$ has nonreal
      poles and cannot be a Stieltjes transform of a positive measure supported
      on $[0,infinity)$ after the required negative-axis convention.
    ],
    boundary: [
      The theta source may possess additional total-positivity or variation
      structure; that structure must be proved to survive the logarithmic
      transform rather than inferred from coefficient positivity.
    ],
    source: [Elementary polynomial counterexample.],
  ),
  entry(
    id: "C.0005",
    kind: "Counterexample",
    grade: "counterexample",
    title: [Pointwise convergence does not imply Hilbert-space closure],
    depends: ("RH.0050",),
    statement: [
      Pointwise convergence of $f_n$ to $f$ does not imply
      $norm(f_n-f)_2 arrow.r 0$.
    ],
    derivation: [
      On $(0,1)$ let
      $
        f_n(x)=sqrt(n)1_((0,1/n))(x).
      $
      For every fixed $x>0$, $f_n(x) arrow.r 0$, but
      $
        norm(f_n)_2^2=n(1/n)=1
      $
      for all $n$.
    ],
    boundary: [
      A Nyman--Beurling finite-span sequence must converge in its declared
      $L^2$ norm, not merely at sampled points.
    ],
    source: [Standard analysis counterexample.],
  ),
  entry(
    id: "C.0006",
    kind: "Boundary",
    grade: "historical-toy",
    title: [The historical natural-square-root surrogate is not RH],
    depends: ("RH.0000",),
    statement: [
      The old proposition
      $
        forall n in NN:
        s(n)^2<=n<(s(n)+1)^2
      $
      for an integer square-root algorithm is true by construction but has no
      interpretation map to the nontrivial zeros of $zeta$.
    ],
    derivation: [
      It quantifies over natural numbers and the correctness of integer square
      root. RH.0000 quantifies over complex zeros of the analytically continued
      completed zeta function. No map carrying zeros, real parts, or the
      functional equation into the surrogate was proved.
    ],
    boundary: [
      The old Lean file may remain historical testimony. It cannot be imported
      as an RH theorem or holonic soundness result.
    ],
    source: [`src/labyrinth/mathematics/lean/App_RH.lean`.],
  ),
  entry(
    id: "C.0007",
    kind: "Boundary",
    grade: "historical-toy",
    title: [An inhabited OPEN sentinel proves no open conjecture],
    depends: ("H.0001",),
    statement: [
      If
      $
        "inductive OPEN where | stillOpen : OPEN",
      $
      then a theorem returning `OPEN.stillOpen` proves only that the custom type
      `OPEN` is inhabited. It does not prove or even state Goldbach, RH,
      Navier--Stokes, or another named conjecture.
    ],
    boundary: [
      An open conjecture must be encoded as its actual proposition with no
      supplied inhabitant. Conditional results accept it as an explicit
      hypothesis.
    ],
    source: [Audit of the historical Labyrinth Lean corpus.],
  ),
  entry(
    id: "C.0008",
    kind: "Counterexample",
    grade: "counterexample",
    title: [A digest is neither identity nor proof],
    depends: ("H.0015",),
    statement: [
      A hash $h : X arrow.r B$ can locate or compare serialized faces. Unless
      injectivity on the declared domain is proved, $h(x)=h(y)$ does not imply
      $x=y$; even injectivity of bytes would not prove equality of causal
      diagrams represented by those bytes.
    ],
    derivation: [
      A finite digest codomain and a larger finite or infinite source domain
      force collisions by the pigeonhole principle. Separately, one byte string
      may be decoded by nonidentical semantics.
    ],
    boundary: [
      Digests remain useful provenance and certificate locators. They do not
      replace independent checking or soul-equivalence.
    ],
    source: [Elementary cardinality and semantic-boundary argument.],
  ),
)
