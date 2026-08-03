#let radix-residue-phase-decomposition = (
  key: "theorem:radix-residue-phase-decomposition",
  kind: [Theorem],
  title: [A radix receiver splits exactly into finite locality and cyclic winding],
  status: [Classical CRT and character calculation; laboratory transport statement],
  depends: (
    "definition:radix-residue-character-cell",
    "definition:prime-valuation-atlas",
  ),
  claim: [
    In a radix-residue-character cell, factor
    $
      q=q_parallel q_perp,
      quad
      q_parallel
      =
      product_(p divides b)p^(v_p(q)),
      quad
      gcd(b,q_perp)=1.
      quad "(SPLIT)"
    $
    Thus $q_parallel$ is the largest divisor of $q$ supported on prime axes
    already present in $b$, and CRT gives
    $
      C_q tilde.eq C_(q_parallel) times C_(q_perp).
    $
    Put
    $
      K_parallel
      =
      max_(p divides q_parallel)
      ceil(v_p(q)/v_p(b)),
    $
    with $K_parallel=0$ when $q_parallel=1$.  Then
    $
      b^k=0 quad "in" C_(q_parallel)
      quad "for every" k>=K_parallel.
      quad "(LOCAL)"
    $
    Hence the $q_parallel$ receiver depends only on the finite suffix
    $(d_0,...,d_(K_parallel-1))$.

    If $q_perp>1$, let
    $
      r=op("ord")_(q_perp)(b).
    $
    Multiplication by $b$ is invertible on $C_(q_perp)$ and
    $
      b^(k+r)=b^k quad "in" C_(q_perp)
      quad "for every" k>=0.
      quad "(WINDING)"
    $
    The coprime receiver can therefore be written
    $
      rho_perp(d)
      =
      sum_(c=0)^(r-1)
      b^c
      (
        sum_(0<=k<K, k=c mod r)d_k
      )
      quad "in" C_(q_perp).
      quad "(PHASE CLASSES)"
    $
    The complete place-incidence word $b^k mod q$ is consequently periodic
    after the finite local cutoff.  It is purely local when $q_perp=1$ and
    purely cyclic when $q_parallel=1$.

    For a reduced rational number $a/q$, its radix-$b$ expansion terminates
    exactly when $q_perp=1$, equivalently when $q$ divides $b^K$ for some
    $K$.  In the character face, the complete population factors as
    $
      hat(G)(j)
      =
      product_(k=0)^(K-1)
      sum_(d=0)^(b-1)
      omega_q^(j d b^k),
      quad "(DIAGONALIZED POPULATION)"
    $
    so the place winding changes the factors while character inversion
    returns the same residue fibers exactly.

    Finally, let $O^+$ be a common positive integer occurrence set whose
    prime support is contained in a finite set $S$.  The same occurrence has
    the radix face $r_b(n)$, residue face $pi_q(n)$, valuation face
    $nu_S(n)$, logarithmic length
    $
      ell_S(n)=sum_(p in S)v_p(n)log p,
    $
    and Mellin character face
    $
      Phi_s(n)
      =
      exp(-s ell_S(n))
      =
      product_(p in S)p^(-s v_p(n)).
      quad "(VALUATION--MELLIN)"
    $
    Radix recharting changes the place-incidence word but leaves this
    common occurrence and its valuation--Mellin identity exact.
  ],
  proof: [
    The two factors in ("SPLIT") are coprime by construction, so CRT applies.
    For each $p$ dividing $q_parallel$ and $k>=K_parallel$,
    $
      v_p(b^k)=k v_p(b)>=v_p(q),
    $
    which proves ("LOCAL").  Since $b$ is a unit modulo $q_perp$, its powers
    form a finite cyclic subgroup and have the stated multiplicative order.
    Grouping ("PLACE") by congruence classes of $k$ modulo $r$ proves
    ("PHASE CLASSES").

    A reduced denominator terminates in base $b$ exactly when it divides a
    power of $b$; prime valuations make this equivalent to $q_perp=1$.
    Evaluating each group-algebra factor at $omega_q^j$ proves the
    diagonalized product, and finite-character orthogonality gives its exact
    inverse.  The final identity follows from unique factorization and
    $n=product_p p^(v_p(n))$.
  ],
  boundary: [
    Radix locality does not make the shared prime factors of $b$ intrinsically
    simpler; it makes their residue face accessible from a finite suffix in
    that radix.  Cyclic winding is not randomness.  Equal residue or
    character faces do not reconstruct the digit word, integer occurrence,
    valuation address, or path.  The finite Fourier transform and the Mellin
    character are both character receivers of abelian transport, but they
    are not the same transform and no direct isomorphism between their
    domains is asserted.
  ],
)
