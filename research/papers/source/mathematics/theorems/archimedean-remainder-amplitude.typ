#let archimedean-remainder-amplitude = (
  key: "theorem:archimedean-remainder-amplitude",
  kind: [Theorem],
  title: [The conditioned archimedean remainder has an explicit spectral amplitude],
  status: [
    Exact factorization of the Connes--Consani archimedean remainder under
    their support and two vanishing conditions
  ],
  depends: (
    "lemma:mellin-half-density-chart",
    "definition:covariant-coarea-carrier",
  ),
  claim: [
    Let
    $
      I_2=[-log(2)/2,log(2)/2],
      quad
      cal(H)_2=L^2(I_2,dif x),
    $
    and let $xi_0=(log 2)^(-1/2)$ be the normalized constant vector.
    Write $P_0$ for the orthogonal projection onto
    $cal(H)_0=xi_0^perp$.

    Connes and Consani independently construct a self-adjoint operator
    $
      N_2=-2 epsilon'(1^+)(I-K_2)
    $
    on $cal(H)_2$, where $K_2$ is the Hilbert--Schmidt integral operator
    determined by the prolate/Sonin kernel $Q epsilon$.  Their spectral
    estimate gives
    $
      chevron.l xi,N_2 xi chevron.r
      <=gamma norm((I-P_0)xi)^2.
    $
    Hence
    $
      B_2=-P_0 N_2 P_0|_(cal(H)_0)>=0
    $
    and its positive square root
    $
      A_2=B_2^(1/2)
    $
    is defined without using the desired Weil defect.

    Let $g in C_c^infinity(RR_(>0))$ have support in
    $[2^(-1/2),2^(1/2)]$ and satisfy, in the final-theorem convention of
    the source,
    $
      hat(g)(-i/2)=0,
      quad
      hat(g)(0)=0.
    $
    Define
    $
      k_g(u)
      =
      u^(1/2) integral_0^u v^(-1/2)g(v) dif^*v,
      quad
      xi_g(x)=k_g(e^x).
    $
    Then $xi_g in cal(H)_0$ and the difference between the archimedean
    Weil response and the positive Sonin trace is exactly
    $
      W_infinity(g ast g^*)
      -
      op("Tr")(
        Theta_infinity(g) bold(S) Theta_infinity(g)^*
      )
      =
      norm(A_2 xi_g)^2.
    $

    If $E_2$ is the spectral resolution of $B_2$, the same carrier has the
    direct-integral face
    $
      norm(A_2 xi_g)^2
      =
      integral_([0,infinity))
      lambda dif
      chevron.l xi_g,E_2(lambda)xi_g chevron.r.
    $
  ],
  proof: [
    The source proves
    $
      op("Tr")(Theta_infinity(g)bold(S)Theta_infinity(g)^*)
      =
      W_infinity(g ast g^*)+E(g ast g^*)
    $
    and, after the displayed logarithmic lift,
    $
      E(g ast g^*)=chevron.l xi_g,N_2 xi_g chevron.r.
    $
    Its identities
    $
      hat(k_g)(0)=-2hat(g)(0)
    $
    and $hat(g)(-i/2)=0$ put $xi_g$ respectively in
    $xi_0^perp$ and inside $I_2$.  The quoted spectral estimate therefore
    makes the compression $-P_0 N_2 P_0$ positive.  The positive
    square-root theorem gives the norm identity, and the spectral theorem
    gives its direct-integral form.
  ],
  boundary: [
    This is a genuine independently sourced remainder carrier, not an
    abstract square root of a defect declared positive in advance.  It is
    proved only at the one-place support aperture and on the conditioned
    current subspace.  It does not construct the corresponding remainder
    operator after support growth or admission of a finite place.
  ],
)
