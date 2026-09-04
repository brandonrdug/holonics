#let theta-parity-execution-reduction = (
  key: "theorem:theta-parity-execution-reduction",
  kind: [Theorem],
  title: [The full theta coordinate executor is one bipolar contraction],
  status: [Exact parity and operator-factorization reduction],
  depends: (
    "definition:ordered-causal-execution",
    "lemma:theta-crossing-layer-indefiniteness",
  ),
  claim: [
    Let $K=cal(P)_0$ act by its quadratic form on a declared dense test
    space in $L^2(RR)$. Since
    $
      K(-a,-b)=K(a,b),
    $
    it commutes with parity. On the positive half-line define the same-hand
    and opposed-hand kernels
    $
      A(x,y)=K(x,y),
      quad
      B(x,y)=K(x,-y),
      quad x,y>=0.
    $
    Under the unitary parity receiver
    $
      (U f)_plus.minus(x)
      =
      frac(f(x) plus.minus f(-x),sqrt(2)),
    $
    the complete coordinate operator becomes
    $
      U K U^*
      =
      (A+B) ⊕ (A-B).
      quad "(PARITY EXECUTION)"
    $

    Consequently the following are equivalent:

    - $K>=0$ on the full coordinate test space;
    - $A+B>=0$ and $A-B>=0$;
    - $A>=0$ and $-A<=B<=A$; and
    - on the support of $A$, there is a self-adjoint contraction $T$ such
      that
      $
        B=A^(1/2)T A^(1/2),
        quad norm(T)<=1.
        quad "(BIPOLAR TRANSPORT)"
      $

    When these conditions hold, the explicit parity residual executor is
    $
      cal(R)_plus.minus
      =
      (1 plus.minus T)^(1/2)A^(1/2),
    $
    and
    $
      chevron.l f,K f chevron.r
      =
      norm(cal(R)_+ f_+)^2
      +
      norm(cal(R)_- f_-)^2.
      quad "(BIPOLAR GRAM CLOSURE)"
    $
  ],
  proof: [
    Simultaneous sign reversal fixes $abs((a+b)/2)$ and reverses
    $(a-b)/2$. Evenness of $Phi$ interchanges the two theta factors, proving
    $K(-a,-b)=K(a,b)$. Direct substitution of
    $
      f(x)=frac(f_+(x)+f_-(x),sqrt(2)),
      quad
      f(-x)=frac(f_+(x)-f_-(x),sqrt(2))
    $
    into the full-line quadratic form gives ("PARITY EXECUTION").

    The first three conditions are then algebraically equivalent. The
    operator interval $-A<=B<=A$ implies that $B$ vanishes on the null space
    of $A$ and, by the Douglas factorization principle, has the form
    $
      A^(1/2)T A^(1/2)
    $
    for a self-adjoint contraction $T$ on the support of $A$. Conversely
    such a contraction gives
    $
      A plus.minus B
      =
      A^(1/2)(1 plus.minus T)A^(1/2)>=0.
    $
    Taking their positive square roots proves ("BIPOLAR GRAM CLOSURE").
  ],
  boundary: [
    Full coordinate positivity is stronger than the RH-equivalent
    positivity required only after bilateral-exponential pullback. This
    theorem therefore identifies one sufficient source executor, not a new
    equivalent formulation of RH.

    The theorem does not construct $T$. It proves that the correct
    full-coordinate task is relative: the opposed crossing $B$ need not be
    positive, but it must be contractively carried by the available
    same-hand storage $A$. `lemma:theta-crossing-layer-indefiniteness` shows
    why no such $T$ exists independently at every fixed sweep layer; it can
    emerge only after ordered accumulation.
  ],
)
