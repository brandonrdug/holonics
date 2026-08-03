# THE PRIME CROSS IS THE OPEN CAPACITOR; THE ARCHIMEDEAN BODY OWES ITS ENDPOINT STORAGE

**Date:** 2026-07-24  
**Grade:** DERIVED / DEPOSITED  
**Scope:** first Weil cell only; mathematics and RH paper updated; no Soma source change; no
numerical run

## Present question

Can the first Weil successor be realized as a passive terminal circuit whose prime cross and
archimedean storage arise together, so that internal current balance and Kron reduction prove the
returned effective tension nonnegative?

The prior record had already identified the returned object
\[
S_{2,3}=D_{2,3}-C_{2,3}^{*}A_2^{-1}C_{2,3},
\]
but it had not distinguished legal incidence, conservation, and passivity. That distinction is
decisive. Incidence gives the topology, conservation balances conduction with changing storage,
and passivity owes a nonnegative constitutive energy. Only the last property signs a Schur
complement.

## 1. Passive incidence composes and survives shorting

Let \(\partial:\mathcal E\to\mathcal V_I\oplus\mathcal V_B\) be an oriented incidence operator,
\(d=\partial^*\), \(W\ge0\) an edge constitutive law, and \(G\ge0\) a vertex-storage law. Then
\[
\mathscr E(v)
=\|W^{1/2}dv\|^2+\|G^{1/2}v\|^2
=\langle Lv,v\rangle,
\qquad
L=d^*Wd+G
\]
is a passive network form. If
\[
L=
\begin{pmatrix}
A&C\\
C^*&D
\end{pmatrix},
\qquad A>0,
\]
zero interior injection gives \(x_y=-A^{-1}Cy\), and the exposed response is
\[
i_B
=\bigl(D-C^*A^{-1}C\bigr)y
=Sy.
\]
Moreover,
\[
\langle Sy,y\rangle=\inf_x\mathscr E(x\oplus y)\ge0.
\]

This is simultaneously the Dirichlet-to-Neumann map, Kron reduction, and the conditioned
effective tension already derived in the RH line. Parallel composition, port gluing, and nested
shorting preserve this relation.

For a capacitive storage \(G\), charge is \(\rho=Gv\), and complete balance reads
\[
\partial j+\dot\rho=s.
\]
Thus an apparent terminal imbalance at one cut can be changing internal charge. Conservation is
over the complete conduction-plus-storage event. It does not require visible terminal currents to
cancel at every cut.

The important boundary is equally exact:
\[
\partial^2=0
\quad\text{does not imply}\quad
W\ge0,\ G\ge0.
\]
A lawful topology and a conservation law do not manufacture passivity.

## 2. The first-prime mutual coupling has an exact capacitor completion

Throughout
\[
a\in\left[\frac{\log2}{2},\frac{\log3}{2}\right],
\]
let \(P_L(a)\) and \(P_R(a)\) project onto the two active boundary strips, and let \(V_a\) translate
the left strip onto the right strip. Put
\[
P_a=P_L(a)+P_R(a),
\qquad
T_a=V_a+V_a^*,
\qquad
\alpha_2=\frac{\log2}{\sqrt2}.
\]
Define the oriented prime incidence
\[
\delta_aw=P_R(a)w-V_aP_L(a)w.
\]
The partial-isometry identities give
\[
\delta_a^*\delta_a=P_a-T_a.
\]
Therefore the entire \(p=2\) contribution obeys
\[
-\alpha_2\langle T_aw,w\rangle
=
\alpha_2\|\delta_aw\|^2
-\alpha_2\|P_aw\|^2.
\]

The first term is exactly the positive difference energy of a branch joining corresponding left
and right strip values. The second term is exactly the missing endpoint self-storage. A passive
two-terminal capacitor contains both its negative mutual coupling and its positive diagonal
self-terms; the raw prime translation contains only the mutual coupling. It is therefore an
**open capacitor**, not a passive constituent in isolation.

This is also why separating “the prime contribution” from “the archimedean contribution” is
ontologically misleading. Their co-present composition must supply one complete energy.

## 3. The source already contains a real nonlocal network

Suzuki's fixed-domain archimedean form is
\[
\mathcal L(w)
=
\frac14\int_{-1}^{1}\int_{-1}^{1}
\frac{|w(x)-w(y)|^2}{|x-y|}\,dx\,dy
+
\frac12\int_{-1}^{1}
\bigl(-\log(1-x^2)\bigr)|w(x)|^2\,dx.
\]
This is not circuit metaphor. The first term is a continuum pair-incidence energy with positive
conductance kernel; the second is positive boundary-to-ground storage. It is a closed Dirichlet
form with a strict lower gap and compact resolvent.

Let
\[
\mathcal H_a
=
\mathcal L-(\log a+2A_\zeta+1)I-a\mathcal R_a
\]
be the remaining source-defined operator. The first-cell form is
\[
\overline q_a=\mathcal H_a-\alpha_2T_a.
\]
Using the capacitor completion, define
\[
\mathcal E_a(w)
=\mathcal L(w)+\alpha_2\|\delta_aw\|^2
\]
and
\[
\mathcal D_a(w)
=
(\log a+2A_\zeta+1)\|w\|^2
+a\langle\mathcal R_aw,w\rangle
+\alpha_2\|P_aw\|^2.
\]
Then the exact source balance is
\[
\boxed{\overline q_a(w)=\mathcal E_a(w)-\mathcal D_a(w).}
\]

\(\mathcal E_a\) is positive storage/incidence. \(\mathcal D_a\) is a Hermitian load; its smooth
kernel contribution is not assumed to have one sign.

## 4. The first wall is a unit-gain condition

Because \(\mathcal E_a\) has a gap and compact resolvent while \(\mathcal D_a\) is bounded, the
relative load
\[
\Gamma_a
=
\mathcal E_a^{-1/2}\mathcal D_a\mathcal E_a^{-1/2}
\]
is compact self-adjoint. Hence
\[
\overline q_a\ge0
\quad\Longleftrightarrow\quad
\lambda_{\max}(\Gamma_a)\le1.
\]

This is the precise continuum operator estimate which the voltage language was approaching. It
does not ask whether one isolated term is positive. It asks whether the complete load ever exceeds
the storage and incidence afforded by the same contemporary body.

At equality, a nonzero mode \(w\) satisfies
\[
\mathcal D_a(w,z)=\mathcal E_a(w,z)
\qquad\text{for every }z.
\]
This is a unit-gain standing mode: exactly zero returned tension after every internal response has
been included.

The strip geometry sharpens where such a mode can live:

- aligned recurrence \(f+V_af\) has \(\delta_a(f+V_af)=0\);
- opposed configuration \(f-V_af\) receives \(2\alpha_2\) of branch stiffness.

Therefore the prime branch cannot repair a deficit entirely inside the aligned/central kernel.
The necessary coherent condition is
\[
\bigl(\mathcal H_a-\alpha_2P_a\bigr)\big|_{\ker\delta_a}\ge0.
\]
The stronger global condition
\[
\mathcal H_a-\alpha_2P_a\ge0
\]
would suffice, but is not necessary and is not the correct target. Existing numerical evidence
that the isolated archimedean form becomes negative inside the first cell makes that stronger
route especially implausible, while the complete archimedean-plus-\(p=2\) form remains numerically
positive.

## 5. Consequence for the RH induction

The circuit proposal survives, but in a more exact form:

1. the old body and the new incidence must be composed before either is judged;
2. the source must expose a positive storage/incidence form \(\mathcal E_n\) and a coupled load
   \(\mathcal D_n\);
3. completed interior currents are balanced and shorted;
4. the returned boundary law is nonnegative exactly when its relative load stays at most one; and
5. that returned law may become the next standing body by associative shorting.

For the first cell, steps 1--4 are now reduced to the explicit compact operator \(\Gamma_a\).
What remains is not an unspecified “continuum estimate” and not a missing conservation principle.
It is the source inequality
\[
\sup_{a\in[\log2/2,\log3/2]}\lambda_{\max}(\Gamma_a)\le1.
\]
The exact circuit decomposition derives the object whose gain must be controlled. It does not yet
derive that bound.

## Evidence

- Masatoshi Suzuki, [*Weil's Quadratic Form via the Screw
  Function*](https://arxiv.org/abs/2606.09096), supplies the fixed-domain screw form, its
  nonlocal Dirichlet energy, compact embedding, and continuous lowest eigenvalue.
- Florian Dörfler and Francesco Bullo, [*Kron Reduction of Graphs with Applications to Electrical
  Networks*](https://arxiv.org/abs/1102.2950), identifies electrical terminal reduction with the
  Schur complement of the interior conductance block.
- Arjan van der Schaft and Bernhard Maschke, [*Port-Hamiltonian Systems on
  Graphs*](https://arxiv.org/abs/1107.2006), derives incidence-based power-conserving
  interconnection with energy-storing and dissipative relations at edges, internal vertices, and
  boundary ports.
- Alain Connes and Caterina Consani, [*Spectral Triples and
  \(\zeta\)-Cycles*](https://ems.press/content/serial-article-files/44477), reports the numerical
  loss of isolated archimedean positivity beyond the first seam and its restoration by the exact
  \(p=2\) contribution through the first prime-active cell.

