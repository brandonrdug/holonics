# THE SHELL RETURNS THROUGH THE OLD MOMENTS; THE FIRST CROSS IS CARRIED; THE CONDITIONAL INTERIOR REMAINS

**Status:** DERIVED / DEPOSITED / SOURCE-CORRECTED / FIRST \(P(2)\to P(3)\)
CROSS CARRIAGE CLOSED / ONE CONDITIONAL SIGN OPEN / NO SOMA CHANGE / NO
NUMERICAL SWEEP

## Present question and stopping condition

The question was not “what experiment comes next?” It was:

> Starting from the published \(P(2)\) Weil-positive aperture, derive the
> actual \(P(2)\to P(3)\) passage after the source's conditions are imposed.
> Stop only at a positive factorization, an obstruction, or one exact missing
> theorem.

The derivation reaches one exact missing theorem. It also corrects two
structural errors in the preceding paper:

1. the source's amplitude fiber was misidentified; and
2. raw off-diagonal prime incidence was incorrectly carried into the
   conditioned quotient as if it remained off-diagonal.

No prime enumeration, zero sampling, floating-point Galerkin run, or
visualization can settle the remaining statement.

## 1. The source keeps the amplitude and returned convolution distinct

Let \(u=\log \rho\). In the final convention used by Connes--Consani, the
base amplitude \(g\), supported in

\[
I_2=\left[-\frac{\log 2}{2},\frac{\log 2}{2}\right],
\]

obeys

\[
\widehat g(0)=0,
\qquad
\widehat g\!\left(-\frac{i}{2}\right)=0.
\]

After reflection, the second sign reverses without changing the symmetric
interval geometry. Introduce \(\sigma^2=1\) to retain either Fourier
convention. The correct Hilbert amplitude fiber is therefore

\[
\mathcal T_R
=
\ker M_R,
\qquad
M_R g
=
\left(
\int_{I_R}g(u)\,du,\;
\int_{I_R}e^{\sigma u/2}g(u)\,du
\right),
\]

where

\[
I_R=\left(-\frac{\log R}{2},\frac{\log R}{2}\right).
\]

The differential operator

\[
\mathcal Q
=
-\left(\rho\frac{\partial}{\partial\rho}\right)^2+\frac14
\]

has a different job in the source. It imposes the two half-character
conditions on the *returned convolution*. It is not the definition of the
canonical amplitude fiber. The former expression
\(\mathcal T_R=\mathcal Q C_c^\infty(I_R)\) conflated these two faces.

## 2. The conditioned successor is a graph, not a detached shell

Set

\[
I_o=I_2,\qquad I=I_3,\qquad S=I\setminus I_o,
\]

and split the ambient Hilbert receiver as

\[
L^2(I)=H_o\oplus H_s,
\qquad
H_o=L^2(I_o),\quad H_s=L^2(S).
\]

Let \(M_o\) and \(M_s\) be the restrictions of \(M_3\). Since the two old
moment vectors \(1\) and \(e^{\sigma u/2}\) are linearly independent,

\[
G_o=M_oM_o^*
\]

is positive definite. Its exact matrix is

\[
G_o=
\begin{pmatrix}
\log 2 & 4\sinh(\log 2/4)\\
4\sinh(\log 2/4) & 1/\sqrt2
\end{pmatrix}.
\]

Define

\[
L=-M_o^*G_o^{-1}M_s,
\qquad
Jy=(Ly)\oplus y.
\]

Then \(M_oLy=-M_sy\), and hence

\[
\boxed{\mathcal T_3=\mathcal T_2\oplus JH_s}
\]

orthogonally in the ambient \(L^2\) receiver. Moreover,

\[
J^*J=I+M_s^*G_o^{-1}M_s.
\]

Shell restriction does identify the quotient
\(\mathcal T_3/\mathcal T_2\) with \(H_s\), but its conditioned
representative is not \(0\oplus y\). It is \(Jy=(Ly)\oplus y\): every new
direction returns through an old-region compensator in order to preserve the
two carried moments.

This is the exact support-growth face of the user's repeated point that a
new local direction reorients the present field. The constraint is not
applied after the shell is added; it determines what the shell direction is.

## 3. Raw blocks and conditioned blocks are different objects

Suppose a Hermitian operator or form on the raw split has blocks

\[
K=
\begin{pmatrix}
A&B\\
B^*&D
\end{pmatrix}.
\]

Writing a conditioned vector as \((x+Ly,y)\), with
\(x\in\mathcal T_2\), gives

\[
H_2=P_oA|_{\mathcal T_2},
\qquad
C=P_o(AL+B),
\]

and

\[
\boxed{
D_{\mathrm{cond}}
=
L^*AL+L^*B+B^*L+D.
}
\]

Here \(P_o\) projects \(H_o\) onto \(\mathcal T_2\).

At the first admission of a prime, the raw finite-place block really is
off-diagonal:

\[
K_p=
\begin{pmatrix}
0&B_p\\
B_p^*&0
\end{pmatrix}.
\]

But after conditioning,

\[
C_p=P_oB_p,
\qquad
\boxed{
D_{p,\mathrm{cond}}
=
L^*B_p+B_p^*L.
}
\]

Thus the earlier statement “the new prime contributes only to the cross
block and zero to both diagonal blocks” was true only before conditioning.
It was false for the actual successor fiber.

This correction does **not** make a prime an independently positive
constituent. It says that raw crossing and the old moment compensation
jointly create a conditioned diagonal face whose sign must be evaluated
together with the archimedean response.

## 4. The source-native form short

Let \(q_3\) be the closed localized Weil form and
\(q_2=q_3|_{\mathcal T_2}\ge 0\). Let

\[
\mathcal N_2=\{x:q_2(x)=0\},
\]

and complete \(\mathcal T_2/\mathcal N_2\) in the \(q_2\)-norm to obtain
the old energy carrier \(\mathcal E_2\).

A sharp \(L^2\) cut need not preserve the form domain. Therefore choose any
form-domain section \(\widetilde J\) of the same quotient and define

\[
\ell_y(x)=q_3(x,\widetilde Jy).
\]

The cross can be carried through the old energy exactly when \(\ell_y\)
annihilates \(\mathcal N_2\) and is \(q_2\)-continuous. Its Riesz carrier
\(c_y\in\mathcal E_2\) then gives the invariant short

\[
\boxed{
s_2(y)
=
q_3(\widetilde Jy)-\|c_y\|_{\mathcal E_2}^2.
}
\]

Changing the section by an old vector translates \(c_y\) by the same old
energy vector and leaves \(s_2\) unchanged. Completion of the square yields

\[
q_3(x+\widetilde Jy)
=
\|[x]+c_y\|_{\mathcal E_2}^2+s_2(y).
\]

Consequently,

\[
P(2)\Longrightarrow P(3)
\quad\Longleftrightarrow\quad
s_2(y)\ge 0\ \text{for every quotient direction }y,
\]

once cross carriage is established.

## 5. The first cross carriage follows from the published base gap

The preceding draft treated cross carriage as an additional open
Moore--Penrose condition. It is not open in the first cell.

Bombieri records Yoshida's positive-definite result at
\(a=\log 2/2\). The modern localized form has compact resolvent and an
attained ground value. Restricting to the conditioned fiber preserves
compactness. Positive definiteness therefore gives

\[
q_2(v)\ge \lambda_2\|v\|_{L^2}^2,
\qquad
\lambda_2>0.
\]

The successor \(q_3\) is closed and lower-semibounded. Choose \(\beta\) so
that

\[
a_3(z)=q_3(z)+(\beta+1)\|z\|_{L^2}^2
\]

is positive. For \(x\) in the old domain and a fixed successor direction
\(z\), Cauchy--Schwarz in \(a_3\), followed by the base gap, gives

\[
|q_3(x,z)|
\le K_z\sqrt{q_2(x)}.
\]

Hence every first-step cross functional is continuous in the old energy
norm.

In the bounded screw-current chart this is precisely the Douglas range
condition. If \(C_{2,3}\) is the conditioned cross and \(G_2\) is the old
positive screw operator, there is a bounded reduced carrier \(Y_{2,3}\)
such that

\[
C_{2,3}=G_2^{1/2}Y_{2,3},
\qquad
C_{2,3}C_{2,3}^*\le cG_2
\]

for some finite \(c\). No closed-range assumption and no bounded
Moore--Penrose inverse are required.

## 6. The exact continuous-kernel object

Suzuki's screw function is

\[
\begin{aligned}
g_\zeta(t)
={}&-4(e^{t/2}+e^{-t/2}-2)
+\sum_{n\le e^{|t|}}\frac{\Lambda(n)}{\sqrt n}
  (|t|-\log n)\\
&-\frac{|t|}{2}\bigl(\psi(1/4)-\log\pi\bigr)\\
&-\frac14\left(
\Phi(1,2,1/4)
-e^{-|t|/2}\Phi(e^{-2|t|},2,1/4)
\right).
\end{aligned}
\]

Let \(G_R\) be its localized continuous-kernel operator. For
\(D=i\,d/du\) with Dirichlet boundary conditions,

\[
q_R(v)=\langle G_RDv,Dv\rangle.
\]

If \(w=Dv\), integration by parts turns the two amplitude moments into the
three current moments

\[
\int w=0,\qquad
\int u\,w(u)\,du=0,\qquad
\int e^{\sigma u/2}w(u)\,du=0.
\]

Thus the exact current fiber is

\[
\mathcal K_R
=
\left\{
w\in L^2(I_R):
\int w=\int uw=\int e^{\sigma u/2}w=0
\right\}.
\]

Repeating the finite-moment graph construction gives the current lift
\(J_D\). If the raw \(G_3\) block is

\[
\begin{pmatrix}
A&B\\
B^*&D
\end{pmatrix},
\]

then

\[
C_{2,3}=P_{\mathcal K_2}(AL_D+B),
\]

\[
D_{2,3}
=
L_D^*AL_D+L_D^*B+B^*L_D+D.
\]

For differences \(|t|\le\log 3\), the only finite-prime hinge in
\(g_\zeta(t)\) is

\[
\frac{\log 2}{\sqrt2}(|t|-\log 2)_+.
\]

This locates the complete \(p=2\) raw incidence inside the same continuous
kernel as the archimedean response; it is not an external prime scalar.

## 7. The one remaining proof obligation

Let \(Y_{2,3}\) be the already-established reduced cross carrier. Define

\[
\boxed{
S_{2,3}
=
D_{2,3}-Y_{2,3}^*Y_{2,3}.
}
\]

The exact remaining theorem is

\[
\boxed{S_{2,3}\ge 0.}
\]

Equivalently,

\[
\langle S_{2,3}y,y\rangle
=
\inf_{x\in\operatorname{dom}(q_2)}
q_3(x+\widetilde Jy)
\ge 0
\]

for every conditioned quotient direction \(y\).

This is the conditional interior: minimize the successor energy over every
old configuration capable of carrying the new direction, then ask whether
the energy that cannot be explained by the old body is nonnegative.

The published sources provide:

- the positive \(P(2)\) base and its strict ground gap;
- lower-semibounded closed localized Weil forms;
- the explicit continuous screw kernel;
- the raw first-prime hinge;
- the semilocal Sonin space transport; and
- the finite-moment conditioned quotient.

They do not provide the sign of \(S_{2,3}\). Proving that sign closes
\(P(2)\to P(3)\). A uniform version of the same conditional-energy theorem
over all support successors would complete the ordinary induction and hence
the Weil criterion.

Connes--Consani's 2023 Galerkin study gives directly relevant evidence:
after the archimedean contribution loses positivity beyond the prime-free
boundary, adding the exact \(p=2\) term restores the computed sign through
the first prime-active window ending at \(R=3\). That result is explicitly
numerical. In the present coordinates it is evidence for
\(S_{2,3}\ge0\), not a proof of the continuum operator inequality.

This is where the derivation stops. It does not move responsibility back to
Brandon: the missing datum is a specific analytic operator inequality, not
an intuition, parameter choice, experiment, or undefined “next object.”

## Primary sources used

- Alain Connes and Caterina Consani, *Weil Positivity and Trace Formula, the
  Archimedean Place*, arXiv:2006.13771.
- Enrico Bombieri, *Remarks on Weil's Quadratic Functional in the Theory of
  Prime Numbers, I* (2000).
- Masatoshi Suzuki, *Weil's Quadratic Form via the Screw Function*,
  arXiv:2606.09096.
- Alain Connes and Caterina Consani, *Spectral Triples and Zeta-Cycles*,
  L'Enseignement Mathématique 69 (2023), 93--148.
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*,
  arXiv:1910.14368.
