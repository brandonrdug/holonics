#let prime-valuation-atlas = (
  key: "definition:prime-valuation-atlas",
  kind: [Definition],
  title: [Prime-valuation atlas and its graded fibers],
  status: [Classical arithmetic object; laboratory atlas presentation],
  depends: ("definition:receiver",),
  claim: [
    Let $S$ be a finite set of primes.  Its valuation lattice and positive
    valuation monoid are
    $
      V_S=ZZ^S,
      quad
      V_S^+=NN^S.
    $
    Every positive integer supported on $S$ has the unique address
    $
      nu_S(n)=(v_p(n))_(p in S),
      quad
      n=product_(p in S) p^(v_p(n)).
    $
    The total multiplicative degree
    $
      deg(n)=abs(nu_S(n))_1=sum_(p in S)v_p(n)
    $
    grades $V_S^+$ into finite simplicial fibers
    $
      Delta_(S,d)={alpha in NN^S:sum_p alpha_p=d}.
    $
    A change of prime support $S subset.eq T$ supplies an inclusion of
    lattices and a restriction map; an analytic receiver $s$ may specialize
    an address by
    $
      Phi_s(alpha)
      =product_(p in S)p^(-s alpha_p)
      =exp(-s sum_(p in S) alpha_p log p).
    $
  ],
  proof: none,
  boundary: [
    The valuation address is canonical for a declared finite prime support.
    A Euclidean drawing of that address, a residue chart, and the analytic
    specialization $Phi_s$ are receiver faces, not additional intrinsic
    properties of the integer.  Enlarging $S$ changes the available atlas;
    it does not change the already established factorization.
  ],
)
