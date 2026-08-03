# THE OLD BODY RELAXES; THE SHELL RETURNS EFFECTIVE TENSION; THE FIRST PRIME WINDOW OPENS

**Date:** 2026-07-24  
**Grade:** RH DERIVATION / EFFECTIVE-TENSION IDENTITY EXACT / INERTIA
LOCALIZATION EXACT / SEQUENTIAL SHORTING EXACT / FIRST PRIME-ACTIVE
POSITIVITY INTERVAL PROVED NONQUANTITATIVELY / \(R=3\) NOT REACHED / RH
OPEN / SOMA SOURCE UNCHANGED / NO NUMERICAL RUN

---

## 0. Present question, standing insufficiency, sought object, and stop

The present question was:

> Can the conditioned Weil successor be expressed as a receiver-relative
> tension after its inherited interior has responded, and does the published
> base gap already carry positivity across the first prime seam?

The standing record had already derived the first conditioned support split,
the old/shell cross, and the residual

\[
S_{2,3}=D_{2,3}-Y_{2,3}^{*}Y_{2,3}.
\]

It called the general component inequality “global Gram dominance.” That
phrase was insufficient in two ways.

1. It made a coordinate expansion look like another global field.
2. It did not explain how the user's tension, standing-wave, knot, and
   departure intuitions met the actual Weil operator.

The sought object was an intrinsic variational law: supply one new boundary
direction, let every inherited interior direction relax, and identify the
force and energy still returned at that boundary. The stopping condition was
the first exact analytic estimate not already implied by the published base
theorem and continuity. No prime census, zero sampling, Galerkin sweep,
visualization, engine work, or generic knot energy entered.

## 1. The old body has one induced response

Write a conditioned successor form as

\[
q(x+\widetilde Jy)
=
\langle Ax,x\rangle
+2\operatorname{Re}\langle Cy,x\rangle
+\langle Dy,y\rangle ,
\]

where \(x\) is carried by the old body, \(y\) is supplied at the new
quotient, and

\[
A\ge \lambda_o I,\qquad \lambda_o>0.
\]

For fixed \(y\), stationarity in every old direction gives

\[
Ax+Cy=0.
\]

The strict old gap therefore determines one response:

\[
\boxed{x_y=-A^{-1}Cy.}
\]

The old body does not merely store a list of pairwise crossings. It responds
as one coupled interior. If the cross is expanded into component carriers,
their mixed Gram terms are the coordinate shadow of this single response.

## 2. The returned object is effective tension

Completing the square gives

\[
q(x+\widetilde Jy)
=
\left\|A^{1/2}\left(x+A^{-1}Cy\right)\right\|^2
+\langle Sy,y\rangle ,
\]

where

\[
\boxed{S=D-C^{*}A^{-1}C.}
\]

Equivalently,

\[
\boxed{
\langle Sy,y\rangle
=
\inf_x q(x+\widetilde Jy).
}
\]

The operator \(S\) is the effective tension seen at the supplied quotient
after the inherited interior has equilibrated. It is the abstract
Dirichlet-to-Neumann or Steklov face of this decomposition:

- \(y\) is the supplied boundary displacement;
- \(-A^{-1}Cy\) is the induced interior response; and
- \(Sy\) is the residual generalized force returned at the boundary.

No local PDE is required for this interpretation. The variational relation
is the definition.

The exact congruence

\[
\begin{pmatrix}
A&C\\ C^{*}&D
\end{pmatrix}
=
\begin{pmatrix}
I&0\\ C^{*}A^{-1}&I
\end{pmatrix}
\begin{pmatrix}
A&0\\ 0&S
\end{pmatrix}
\begin{pmatrix}
I&A^{-1}C\\ 0&I
\end{pmatrix}
\]

shows that the full successor and \(A\oplus S\) have the same inertia.
Because \(A\) is strictly positive, every new negative direction and every
new null direction belongs exactly to \(S\). Thus

\[
q\ge0
\quad\Longleftrightarrow\quad
S\ge0.
\]

“Global Gram dominance” is therefore replaced by one intrinsic question:

> Is the source-derived effective tension nonnegative after all available
> inherited directions have responded?

The convexity language is now literal rather than visual. The relaxed
boundary energy

\[
E_{\mathrm{eff}}(y)=\inf_x q(x+\widetilde Jy)=\langle Sy,y\rangle
\]

has Hessian \(2S\). Positive, null, and negative tension are exactly convex,
flat, and concave directions of the reduced response. In a parameterized
family, a zero mode is the discriminant at which one reduced direction may
pass between convexity and concavity. Reorienting coordinates does not
change that inertia.

## 3. Compression is sequential relaxation, not deletion

For nested interiors

\[
\mathcal V_0\subset\mathcal V_1\subset\mathcal V_2,
\]

shorting is associative:

\[
\boxed{
(q/\mathcal V_0)/(\mathcal V_1/\mathcal V_0)
=
q/\mathcal V_1.
}
\]

Both sides minimize the original form over the same complete
\(\mathcal V_1\) interior. This is the exact analytic face of hand-up and
departure:

- a lower interior responds;
- its complete response is factored out of the active description; and
- its effective boundary law remains available to the next grain.

No event history or detached component ledger is required.

## 4. Knot tension locates modes but does not calibrate the Weil zero

The user's knot and standing-wave intuition is useful, but only at its exact
boundary. If

\[
Av=\lambda v,\qquad \|v\|=1,
\]

then the constrained second variation is

\[
2\langle(A-\lambda I)\eta,\eta\rangle
\qquad(\eta\perp v).
\]

Under the scalar shift

\[
A\mapsto A-cI,\qquad
\lambda\mapsto\lambda-c,
\]

this Hessian is unchanged. Nodes, antinodes, visible crossings, and relative
equilibrium therefore cannot determine whether the absolute ground value is
positive, zero, or negative.

This does not make knot geometry irrelevant. It says exactly what must join
it: the explicit formula fixes the zero of the response. Once that
calibration is retained, a null effective-tension mode is a genuine
degeneracy rather than a receiver artifact.

Increasing combinatorial possibility also does not by itself force
positivity. Enlarging the admissible interior gives the supplied boundary
more ways to relax and can lower its effective energy. The proof must control
the source-derived response, not count its possible reconfigurations.

## 5. The first Weil successor has this exact form

In the first support cell, let:

- \(A_2\) be the strictly positive \(P(2)\) old body;
- \(C_{2,3}\) be the carried conditioned cross; and
- \(D_{2,3}\) be the conditioned shell block of the zeta screw kernel.

Then

\[
\boxed{
S_{2,3}
=
D_{2,3}-C_{2,3}^{*}A_2^{-1}C_{2,3}
=
D_{2,3}-Y_{2,3}^{*}Y_{2,3}.
}
\]

The first-support implication is exactly

\[
P(2)\Longrightarrow P(3)
\quad\Longleftrightarrow\quad
S_{2,3}\ge0.
\]

The cross is no longer the missing datum. It is carried through the old
energy body by the published strict base gap. The missing datum is the sign
of the resulting effective tension.

## 6. Positivity already enters a genuinely prime-active interval

Let \(q_a\) be Suzuki's localized Weil form on \((-a,a)\), and let

\[
\lambda(a)
=
\inf_{v\ne0}\frac{q_a(v)}{\|v\|^2}
\]

be its attained lowest spectral value. Set

\[
a_2=\frac{\log2}{2},
\qquad
a_3=\frac{\log3}{2}.
\]

The published base result gives

\[
\lambda(a_2)>0.
\]

Suzuki proves that \(a\mapsto\lambda(a)\) is continuous. Therefore some

\[
0<\delta<a_3-a_2
\]

satisfies

\[
\lambda(a)>0
\qquad
\text{for every }a\in[a_2,a_2+\delta].
\]

With

\[
R_*=e^{2(a_2+\delta)}=2e^{2\delta}>2,
\]

Weil positivity is proved for every \(2\le R\le R_*\). For \(R>2\) in this
interval, the \(p=2\) crossing is genuinely active while the \(p=3\)
crossing is absent. This is not another prime-free base statement.

The advance is exact but nonquantitative. Continuity does not determine
\(\delta\), so it does not carry the sign to \(R=3\).

If RH is false, let

\[
a_*=\inf\{a\ge a_2:\lambda(a)\le0\}.
\]

Continuity gives \(\lambda(a_*)=0\). Relative to any earlier strictly
positive aperture, the effective tension at \(a_*\) has a nonzero null mode.
The first possible failure is therefore exactly a zero-tension standing mode
of the source-derived continuation.

## 7. The complete first finite-place motion is one boundary-strip hinge

Suzuki's scaled formula transports every localized form to the fixed
receiver \((-1,1)\). For

\[
a\in\left(\frac{\log2}{2},\frac{\log3}{2}\right),
\qquad
h(a)=\frac{\log2}{a},
\]

one has \(1<h(a)<2\). Translation by \(h(a)\) therefore carries the left
boundary strip

\[
(-1,1-h(a))
\]

unitarily onto the disjoint right strip

\[
(-1+h(a),1).
\]

Let \(V_a\) be that partial isometry, extended by zero, and set

\[
T_a=V_a+V_a^*.
\]

Then

\[
T_a^2=P_L(a)+P_R(a),
\qquad
\operatorname{spec}(T_a)=\{-1,0,1\}.
\]

The positive and negative eigenfaces are the paired configurations
\(f\oplus V_af\) and \(f\oplus(-V_af)\); the central region is the zero
face. The coefficient is exactly

\[
\alpha_2=\frac{\Lambda(2)}{\sqrt2}
=\frac{\log2}{\sqrt2}.
\]

No other nonzero finite-place term occurs before the \(p=3\) threshold.
Writing \(\mathcal H_a\) for Suzuki's declared archimedean logarithmic form
and smooth screw-kernel remainder, the complete fixed-domain condition is

\[
\boxed{
\mathcal H_a-\alpha_2T_a\ge0
\quad
\text{for }
a\in\left[\frac{\log2}{2},\frac{\log3}{2}\right].
}
\]

The moving strip is the complete first-prime combinatorics. Its exact norm
\(\|T_a\|=1\) is not enough: \(\mathcal H_a\) does not commute with the
hinge, and the available source argument proves continuity rather than a
quantitative domination bound.

## 8. The exact remaining obligation

The immediate first-cell problem is now:

\[
\boxed{
S_a
=
D_a-C_a^{*}A_2^{-1}C_a
\ge0
\quad
\text{for }
a\in\left[\frac{\log2}{2},\frac{\log3}{2}\right].
}
\]

An equivalent result would be a quantitative lower bound or modulus of
continuity for \(\lambda(a)\) strong enough to prevent it from reaching zero
on that interval.

After this first cell, full RH still requires a uniform symbolic successor
law \(S_n\ge0\) at every aperture. Prime stages introduce a new Euler
admission/return pair; prime-power stages add another traversal of an
existing axis; other stages move only the support boundary. Associativity of
shorting supplies the induction grammar, but it does not supply the sign.

This is the stopping wall. The next valid RH move must estimate the explicit
zeta screw kernel's effective-tension family—equivalently the fixed-domain
family \(\mathcal H_a-\alpha_2T_a\)—or derive a strictly equivalent analytic
inequality. Another census, coordinate change, favorable receiver, generic
knot energy, or finite sample does not advance this obligation.

## Sources

- Enrico Bombieri, “Remarks on Weil's Quadratic Functional in the Theory of
  Prime Numbers, I” (2000),
  <http://www.bdim.eu/item?id=RLIN_2000_9_11_3_183_0>.
- Masatoshi Suzuki, “Weil's Quadratic Form via the Screw Function” (2026),
  <https://arxiv.org/abs/2606.09096>.
- Alain Connes and Caterina Consani, “Spectral Triples and Zeta-Cycles”
  (2023), <https://ems.press/journals/lem/articles/44477>.
