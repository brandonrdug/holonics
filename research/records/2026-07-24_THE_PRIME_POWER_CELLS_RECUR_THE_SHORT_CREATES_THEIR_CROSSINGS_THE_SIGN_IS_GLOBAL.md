# THE PRIME-POWER CELLS RECUR; THE SHORT CREATES THEIR CROSSINGS; THE SIGN IS GLOBAL

**Status:** DERIVED / DEPOSITED / SYMBOLIC SUPPORT-SUCCESSOR COMBINATORICS
CLOSED / INDEPENDENT POSITIVE-CELL FACTORIZATION OBSTRUCTED / GLOBAL GRAM
DOMINANCE OPEN / NO SOMA CHANGE / NO NUMERICAL SWEEP

## Present question and stopping condition

The question was:

> Does the support successor \(P(n)\to P(n+1)\) have a uniform
> prime-power cell law which scales the first \(2\to3\) construction, and
> does that law factor the conditioned remainder into positive boundary
> pieces?

The standing evidence already isolated the first conditional remainder
\(S_{2,3}\), but it did not derive the general prime-power cell complex or
say whether those cells actually supplied its sign.

The derivation stops at an explicit obstruction:

1. the cell recurrence and its census are exact and uniform;
2. every raw prime-power hinge is a **signed** edge-energy/potential balance;
3. conditioning and old-interior elimination create cross-terms among all
   active carriers; and
4. the remaining theorem is one global Gram-dominance identity, not further
   combinatorial induction.

This is a conclusion, not a request for another finite run.

## 1. The finite-prime screw face is an integrated crossing measure

Write

\[
g_{\mathrm{fin}}(t)
=
\sum_{m\ge2}
\frac{\Lambda(m)}{\sqrt m}
\bigl(|t|-\log m\bigr)_+ .
\]

Only prime powers contribute, since

\[
\Lambda(m)
=
\begin{cases}
\log p,&m=p^k,\\
0,&\text{otherwise}.
\end{cases}
\]

The sum is locally finite. Distributionally,

\[
\boxed{
g_{\mathrm{fin}}''(t)
=
\sum_{m\ge2}
\frac{\Lambda(m)}{\sqrt m}
\left(
\delta(t-\log m)+\delta(t+\log m)
\right).
}
\]

Thus the prime-power population has three exact geometric orders:

- the atoms at \(\pm\log m\) are the crossings;
- integrating once produces the changing slope after each crossing; and
- integrating twice produces the triangular hinge
  \((|t|-\log m)_+\).

The positive coefficient of the crossing measure does **not** mean that the
Weil quadratic contribution is positive. The localized form differentiates
the kernel twice and therefore receives \(-g_{\mathrm{fin}}''\).

## 2. The normalized aperture contains paired triangular cells

Let

\[
L_R=\log R,
\qquad
I_R=\left[-\frac{L_R}{2},\frac{L_R}{2}\right],
\]

and rescale the aperture square by

\[
x=L_R\xi,
\qquad
y=L_R\eta,
\qquad
(\xi,\eta)\in
\left[-\frac12,\frac12\right]^2.
\]

For \(m=p^k<R\), put

\[
\alpha_m(R)=\frac{\log m}{\log R}.
\]

The \(m\)-hinge is nonzero on exactly two opposed triangles:

\[
T^+_{m,R}
=
\{(\xi,\eta):\xi-\eta>\alpha_m(R)\},
\]

\[
T^-_{m,R}
=
\{(\xi,\eta):\eta-\xi>\alpha_m(R)\}.
\]

Each has normalized leg

\[
1-\alpha_m(R)
\]

and physical leg

\[
\log R-\log m
=
\log\frac{R}{m}.
\]

The hinge is affine on these cells:

\[
\frac{\Lambda(m)}{\sqrt m}
L_R
\left(
|\xi-\eta|-\alpha_m(R)
\right).
\]

It is born with zero area at \(R=m\), then grows continuously from the two
opposed corners. At \(R=m^2\), its normalized threshold is \(1/2\). This is
the already-observed half-overlap, now located inside the full cell
evolution rather than treated as first admission.

## 3. The complete successor census is exact

Define the active threshold population

\[
\mathcal P_R
=
\{m\ge2:\Lambda(m)>0,\ m<R\}.
\]

The threshold lines

\[
\xi-\eta=\pm\alpha_m(R)
\]

are parallel. They divide the normalized square into

\[
\boxed{2|\mathcal P_R|+1}
\]

connected open strata.

At \(I_n\), the active integer thresholds satisfy \(m<n\). At
\(I_{n+1}\), they satisfy \(m\le n\). Therefore:

\[
\boxed{
\text{the incidence poset changes at }n\to n+1
\iff n=p^k.
}
\]

If \(n\) is a prime power, one new pair of corner cells is born. If it is
not, no new finite-prime cell appears; all existing cells merely deform as
the receiver rebases.

At the endpoint \(I_{n+1}\), the number of active traversals belonging to
one prime axis is

\[
N_p(n+1)
=
\left\lfloor\frac{\log n}{\log p}\right\rfloor.
\]

The total number of active prime-power thresholds is therefore

\[
\boxed{
|\mathcal P_{n+1}|
=
\sum_{p\le n}
\left\lfloor\frac{\log n}{\log p}\right\rfloor .
}
\]

This answers the earlier question about “members per prime axis” exactly.
For each fixed \(p\),

\[
\log(p^k)=k\log p
\]

gives equal spacing in logarithmic displacement, while

\[
\frac{\Lambda(p^k)}{\sqrt{p^k}}
=
(\log p)p^{-k/2}
\]

gives geometric half-density decay. Each prime axis is therefore a
fundamental logarithmic interval together with its weighted traversals.

The different prime axes interlace by the ordinary ordering of their prime
powers. Their raw threshold lines do not intersect: all are parallel in the
difference coordinate. The consequential cross-axis interactions arise one
stage later.

## 4. Every hinge is a signed edge law

Let \(v\in H_0^1(I_R)\), extended by zero outside \(I_R\), and let

\[
(U_\ell v)(x)=v(x-\ell).
\]

For \(m=p^k<R\), the exact hinge contribution to the localized Weil form is

\[
\boxed{
q_{m,R}(v)
=
-2(\log p)p^{-k/2}
\operatorname{Re}
\langle U_{k\log p}v,v\rangle .
}
\]

Define the weighted difference edge

\[
\Delta_m
=
I-m^{-1/2}U_{\log m}.
\]

Unitarity of translation on the zero-extended whole-line carrier gives

\[
\|\Delta_m v\|^2
=
(1+m^{-1})\|v\|^2
-2m^{-1/2}
\operatorname{Re}\langle U_{\log m}v,v\rangle.
\]

Hence

\[
\boxed{
q_{m,R}(v)
=
(\log p)
\left(
\|\Delta_m v\|^2
-(1+m^{-1})\|v\|^2
\right).
}
\]

This is a graph-Schrödinger form:

- \(\|\Delta_m v\|^2\) is a nonnegative translation-difference energy;
- \((1+m^{-1})\|v\|^2\) is the exact diagonal potential; and
- their difference is the prime-power current.

The raw hinge has both signs. Choose a small bump \(f\) whose first few
\(\log m\)-translates are disjoint, and set

\[
v_+=f+U_{\log m}f,
\qquad
v_-=f-U_{\log m}f.
\]

Then

\[
\operatorname{Re}\langle U_{\log m}v_+,v_+\rangle
=\|f\|^2,
\]

while

\[
\operatorname{Re}\langle U_{\log m}v_-,v_-\rangle
=-\|f\|^2.
\]

Thus \(q_{m,R}(v_+)<0\) and \(q_{m,R}(v_-)>0\).

The obstruction is now exact: the prime-power cells cannot themselves be
declared positive boundary constituents. Their relative phase is material.

## 5. Conditioning creates the cross-axis complex

At one finite aperture, decompose the complete form on its common domain as

\[
q_{n+1}
=
\sum_{\alpha\in\mathcal A_n}q_{\alpha,n+1},
\qquad
\mathcal A_n
=
\{\infty\}\cup\mathcal P_{n+1},
\]

where \(\infty\) denotes the complete non-finite-prime face.

Let \(\widetilde J_ny\) be a moment-conditioned quotient direction. When the
component cross functionals

\[
\ell_{\alpha,y}(x)
=
q_{\alpha,n+1}(x,\widetilde J_ny)
\]

are continuous in the old energy norm, let
\(c_{\alpha,y}\in\mathcal E_n\) be their Riesz carriers. Linearity and
uniqueness give the carrier of the complete cross:

\[
\boxed{
c_y
=
\sum_{\alpha\in\mathcal A_n}c_{\alpha,y}.
}
\]

The invariant short is therefore

\[
\boxed{
s_n(y)
=
\sum_{\alpha\in\mathcal A_n}
q_{\alpha,n+1}(\widetilde J_ny)
-
\left\|
\sum_{\alpha\in\mathcal A_n}c_{\alpha,y}
\right\|_{\mathcal E_n}^2 .
}
\]

Expanding the square,

\[
\boxed{
s_n(y)
=
\sum_\alpha q_{\alpha,n+1}(\widetilde J_ny)
-
\sum_{\alpha,\beta}
\langle c_{\alpha,y},c_{\beta,y}\rangle_{\mathcal E_n}.
}
\]

This is the missing combinatorial interior. The raw screw kernel is additive
over prime powers, but shorting is not. Eliminating the shared old interior
creates:

- self-terms for each archimedean or prime-power carrier;
- pairwise cross-terms between different traversals of one prime;
- pairwise cross-terms between different prime axes; and
- pairwise cross-terms between every finite-prime carrier and the
  archimedean carrier.

These are not extra decorations placed on the manifold. They are induced by
the fact that all supplied directions must be carried through the same old
energy body before the unexplained boundary consequence can be read.

At \(2\to3\), the carrier is already the coherent sum of the archimedean and
dyadic carriers. The first residual is therefore not

\[
S_{\infty}+S_2.
\]

It includes the interference

\[
-\langle c_{\infty,y},c_{2,y}\rangle
-\langle c_{2,y},c_{\infty,y}\rangle.
\]

This is why separately inspecting an “archimedean contribution” and a
“prime contribution” can show restoration numerically while failing to
explain it analytically.

## 6. What scales, and what remains genuinely analytic

Three structures now scale uniformly:

1. **Cell birth.** A new paired cell appears exactly at a prime power.
2. **Axis recurrence.** The \(p\)-axis has locations \(k\log p\) and weights
   \((\log p)p^{-k/2}\).
3. **Constraint rank.** Every amplitude successor is a rank-two moment
   graph; every derivative-current successor is its rank-three integrated
   face. The coefficients change with the aperture, but the number and
   nature of the carried constraints do not.

What does not follow combinatorially is the sign of the coupled short. The
uniform obligation is

\[
\boxed{
\sum_{\alpha\in\mathcal A_n}
q_{\alpha,n+1}(\widetilde J_ny)
\ge
\left\|
\sum_{\alpha\in\mathcal A_n}c_{\alpha,y}
\right\|_{\mathcal E_n}^2
\quad
\text{for every admitted }y.
}
\]

If the old form has a radical, every component cross must also descend
through it. At the first cell, the published strict base gap already closes
that carriage issue, leaving exactly

\[
S_{2,3}\ge0.
\]

The hoped-for factorization

\[
\sum_\alpha \partial_\alpha^*W_\alpha\partial_\alpha,
\qquad
W_\alpha\succeq0,
\]

cannot be obtained by assigning one independent positive \(W_\alpha\) to
each raw hinge. A valid positive factorization, if derived, must factor the
entire coupled Gram deficit after the archimedean kernel, moment rebase, and
old energy inverse are all present.

That is the exact stopping wall.

## 7. Why this is also the relevant learning geometry

The mathematical result clarifies the laboratory's learning hypothesis
without importing a separate machine-learning ontology.

The reusable object is the transformation law

\[
\Delta_m=I-m^{-1/2}U_{\log m},
\]

not a retained scalar score for one prior occurrence. Every recurrence uses
the same law at a different logarithmic span and in a different contemporary
field.

The contextual consequence is the conditioned short. Once the old interior
is eliminated, previously separate supplied transformations acquire induced
cross-terms. In that precise sense:

- context reorients the whole active field;
- recurrence reuses a law without copying an event;
- compression preserves the boundary consequence after internal directions
  are shorted away; and
- “nearby” means nearby in the old energy geometry, not merely nearby in
  source order or Euclidean coordinates.

The result does not prove a general learning algorithm. It identifies the
elementary mechanism that such an algorithm must preserve: local recurring
edge laws plus context-created carrier incidence.

## Conclusion

The user's scaling intuition was partly correct and can now be stated
without vagueness:

> The support filtration is a genuine combinatorial induction. Prime powers
> are quantized births of paired affine hinge cells, grouped into logarithmic
> prime axes with geometric half-density weights.

The further conclusion is equally important:

> The RH sign is not carried by those cells independently. Their raw forms
> are signed, and the conditioned successor creates a complete Gram of
> induced interactions through the common old energy body.

The next mathematical obligation has therefore stopped moving. It is the
global Gram-dominance inequality above. For the first cell, that is exactly
\(S_{2,3}\ge0\). For all cells, its uniform form plus ordinary induction
would imply Weil positivity and RH.

## Primary sources

- Masatoshi Suzuki, *Weil's Quadratic Form via the Screw Function*,
  arXiv:2606.09096, especially the continuous screw kernel and the exact
  translated prime-power correlations.
- Alain Connes and Caterina Consani, *Weil Positivity and Trace Formula, the
  Archimedean Place*, arXiv:2006.13771.
- Alain Connes and Caterina Consani, *Spectral Triples and Zeta-Cycles*,
  *L'Enseignement Mathématique* 69 (2023), 93--148.

