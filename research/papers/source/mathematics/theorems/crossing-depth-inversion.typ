#let crossing-depth-inversion = (
  key: "theorem:crossing-depth-inversion",
  kind: [Theorem],
  title: [Crossing depth carries the hand, and the alternating sum is a reversion],
  status: [Exact; classical Möbius inversion, with the crossing reading and the diagram identification named],
  depends: (
    "theorem:tower-cross-term-identity",
    "definition:comparison-face",
  ),
  claim: [
    Let $A_1,dots,A_n$ be regions of one ambient face. Their arrangement
    partitions that face into the *regions of a Venn diagram*, and there are
    exactly
    $
      sum_(k=0)^n binom(n,k) = 2^n
      quad "(THE FORK COUNT)"
    $
    of them: one for each word in ${"in","out"}^n$. A region is *not* a set and
    *not* a number -- it is a word, and the fork is per curve.

    Grade a region by its *crossing depth* $k$, the number of $A_i$ containing
    it. Measure supplied on the ambient face then satisfies
    $
      mu(union.big_(i=1)^n A_i)
      = sum_k (-1)^(k-1) sum_(abs(S)=k) mu(inter.big_(i in S)A_i).
      quad "(INCLUSION--EXCLUSION)"
    $

    *The sign is not bookkeeping.* $(-1)^(k-1)$ is the Möbius function of the
    Boolean lattice on $n$ letters, $mu_"Bool"(emptyset,S)=(-1)^(abs(S))$, and
    Möbius inversion is by definition the *reversion* of that lattice's zeta
    function: for $f=zeta g$ one has $g=mu f$, with $mu=zeta^(-1)$ in the
    incidence algebra. So ("INCLUSION--EXCLUSION") is an inverted series, the
    alternating sign is the inverse's, and by
    #emph[theorem:tower-cross-term-identity] a sign is the accumulated hand of a
    half turn: *each additional crossing reverses the hand.*

    Three consequences travel together:

    + *Depth one is the sum; depth $&gt;= 2$ is the correction.* The $k=1$ terms are
      what the parts carry alone; every higher term is what a meeting carries
      that no part carries, which is the cross term of the tower at arity $k$.
    + *A crossing is where the load sits.* The regions of depth $&gt;= 2$ are exactly
      the ones constrained by more than one carrier, and removing a single $A_i$
      changes every term of depth $&gt;= 2$ that contains it. Depth-one regions are
      independent; crossings are not.
    + *Reversion is the general operation.* Recovering a construction from the
      faces of its parts is inverting a composition, and the classical carriers of
      that inversion -- Lagrange--Good reversion, and Faà di Bruno for the
      composition it inverts -- are exactly what a diagrammatic expansion computes.
  ],
  proof: [
    ("THE FORK COUNT") counts the subsets of ${1,dots,n}$, one per membership
    word, and $sum_k binom(n,k)=2^n$ by the binomial theorem at $x=1$.

    For ("INCLUSION--EXCLUSION"), fix a point of depth $k &gt;= 1$. It is counted
    once for each nonempty $S$ contained in its own $k$ containing regions, with
    sign $(-1)^(abs(S)-1)$, so its total coefficient is
    $-sum_(j=1)^k binom(k,j)(-1)^j = -((1-1)^k - 1) = 1$. A point of depth $0$ is
    counted in no term. Hence each point of the union contributes exactly its own
    measure once.

    The Möbius identification is the definition of the incidence algebra of the
    Boolean lattice: $mu(emptyset,S)=(-1)^(abs(S))$ satisfies
    $sum_(T subset.eq S)mu(emptyset,T)=[S=emptyset]$, which is the inverse of the
    zeta function $zeta(emptyset,S)=1$, and inversion in the incidence algebra
    is reversion of the corresponding series.
  ],
  boundary: [
    ("INCLUSION--EXCLUSION") requires a *finitely additive measure supplied on
    the ambient face*. It is a theorem about that measure, not about the regions,
    and it says nothing about which measure an ecology should declare.

    The reversion reading is an identification of operations, not a claim that
    every alternating expansion converges or that a diagrammatic series
    determines its sum. The composition it inverts is formal; whether the
    inverted series can be *summed* is a separate question with its own carrier
    (see #emph[theorem:diagram-word-resummation]).

    "The crossings bear the load" is exact here for measure and is an *analogy*
    for mechanical tension, which requires its own constitutive law. Nothing in
    this statement supplies one.
  ],
)
