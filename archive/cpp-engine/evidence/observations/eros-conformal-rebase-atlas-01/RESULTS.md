# Eros Conformal Rebase Atlas 01

**Status:** ACCEPTED  
**Date:** 23 July 2026  
**Primary artifact:** `REPORT.json`  
**Instrument:** `life/examples/eros_conformal_rebase_atlas.rs`  
**Arithmetic:** exact integers, reduced ratios, complex ratios, and symbolic
series words only; no floating-point causal datum  
**Execution:** four independent CPU workers on a host exposing 24 hardware
threads  
**Report SHA-256:** `e045ac4606bd617bdc86a9d7af795080205441cd3b89a6e53a6db290b5f1816c`  
**Embedded pre-digest SHA-256:**
`96357100562f90b0b4274a8339e97e7694ef44fae495eb8989ff2b06ed0d1514`

## The question

Can the transformed-grid geometry of a holomorphic function, the completed
zeta symmetry, logarithmic scale rebase, and a centered Smith chart be
carried as one exact atlas rather than rendered as unrelated pictures?

The required artifact was not another absolute camera view. It was a
receiver-relative carrier which retained:

1. the source lineage and first nonzero local holomorphic term;
2. the distinction among a regular point, a zero, a critical point, and two
   distinct sources reaching one output;
3. the two different completed-zeta hands
   \(R(s)=1-s\) and \(J(s)=1-\overline{s}\);
4. the fixed and normal components of \(s\) under \(J\);
5. the exact log-radius and phase of rebase; and
6. the exact unit-shell residual after the centered Cayley/Smith map.

The construction stopped after the first bounded exact report. It did not
search a range of zeta zeros, sample a floating grid, launch CUDA, or rebuild
the observatory.

## The joined carrier

Write

\[
s=\frac12+\varepsilon+it.
\]

The antiholomorphic involution \(J(s)=1-\overline{s}\) gives the exact
projectors

\[
P_{\mathrm{fix}}(s)
  =\frac{s+J(s)}2
  =\frac12+it,
\qquad
P_{\mathrm{normal}}(s)
  =\frac{s-J(s)}2
  =\varepsilon.
\]

This is the first important correction. The value \(1/2\) is not supplied by
an absolute positivity convention or by taking a visual midpoint after the
fact. It is the fixed component of an order-two orbit. The sign of
\(\varepsilon\) is orientation: it distinguishes the two normal hands
without declaring either hand intrinsically positive or negative.

For logarithmic source scale \(u=\log(x/x_0)\), the same centered coordinate
acts through the exact symbolic character

\[
\rho_{\varepsilon,t}(u)
  =\exp(\varepsilon u)\exp(itu).
\]

The report stores the primary row

\[
(u,\ \varepsilon u,\ tu)
\]

as source scale, log-radius, and phase. It never evaluates an exponential,
sine, cosine, or decimal value of \(\pi\). Consequently:

- \(\varepsilon=0\) is constant-radius conduct;
- \(\varepsilon>0\) and \(\varepsilon<0\) are oppositely directed logarithmic
  spirals; and
- the functional partners \(+\varepsilon\) and \(-\varepsilon\) have the
  same phase and reciprocal amplitudes at every retained source scale.

Finally, with \(w=\varepsilon+it\) and rational scale \(a>0\), the centered
Cayley/Smith chart

\[
W_a(w)=\frac{w-a}{w+a}
\]

has the exact residual

\[
|W_a(w)|^2-1
  =\frac{-4a\varepsilon}{|w+a|^2}.
\]

Thus the fixed seam, constant-radius rebase, and unit Smith shell are not
three analogies. They are three receiver faces of the same carried normal
coordinate:

\[
\varepsilon=0
\quad\Longleftrightarrow\quad
\text{fixed under }J
\quad\Longleftrightarrow\quad
\text{constant rebase radius}
\quad\Longleftrightarrow\quad
|W_a(w)|=1.
\]

## What a transformed-grid crossing can actually be

The local germ census prevents one flattened visual “kink” from silently
standing for several different events.

| Exact germ | Local datum | Geometric consequence |
|---|---:|---|
| \(F(z_0+\delta)=F(z_0)+(2+3i)\delta\) | degree \(1\), \(F(z_0)\ne0\), \(F'(z_0)\ne0\) | a regular conformal crossing; the two source axes remain orthogonal |
| \(F(\delta)=(1+i)\delta\) | simple zero, degree \(1\) | radius collapses, phase winds once, and the local tangent remains regular |
| \(F(\delta)=1+\delta^2\) | nonzero critical point, degree \(2\) | the derivative vanishes and four alternating amplitude/phase rays replace a false tangent |
| \(F(\delta)=\delta^3\) | zero order \(3\), critical order \(2\) | axis collapse, triple phase winding, and cubic branching coexist |

For the regular affine cell the report carries the exact conjugate-harmonic
gradients

\[
\nabla U=
\left(\frac{399}{205},-\frac{1008}{205}\right),
\qquad
\nabla V=
\left(\frac{1008}{205},\frac{399}{205}\right).
\]

Their dot product is exactly zero and their squared norms are exactly equal.
This is the data form of the angle-preservation described by a transformed
holomorphic grid.

The separate cell \(F(z)=z^2\) retains the two source lineages \(z=1\) and
\(z=-1\). Both reach the output \(1\), but their derivative hands are \(2\)
and \(-2\). Equal codomain placement therefore does not merge the paths that
arrived there. A rendered self-intersection must first be classified as a
same-source critical germ or a distinct-source coincidence; the picture
alone cannot decide.

## The completed zeta orbit

Two involutions must remain typed:

\[
R(s)=1-s
\quad\text{is holomorphic, with}\quad
\xi(R(s))=\xi(s),
\]

whereas

\[
J(s)=1-\overline{s}
\quad\text{is antiholomorphic, with}\quad
\xi(J(s))=\overline{\xi(s)}.
\]

On the fixed seam, a response and its \(J\)-partner form a self-pair
\(A(s)\overline{A(J(s))}=|A(s)|^2\). Away from the seam they are a
cross-pair. Calling the latter “positive” would erase the normal hand that
the atlas is built to retain.

The report also keeps raw \(\zeta\) and completed \(\xi\) as different charts:

- \(\zeta(2)=\pi^2/6\), while
  \(\xi(2)=\xi(-1)=\pi/6\);
- \(\zeta(0)=-1/2\) and \(\zeta\) has a pole at \(1\), while
  \(\xi(0)=\xi(1)=1/2\); and
- \(\zeta(-2)=0\) is a simple trivial zero, while the Gamma pole cancels it
  in completion and
  \(\xi(-2)=\xi(3)=3\zeta(3)/(2\pi)\).

The last path is particularly important for observation. A raw zeta axis
hit is not necessarily a completed-xi axis hit. Revolving only the raw zeta
image would therefore conflate two different local species.

The appearances of \(\pi\) above are symbolic completed-function identities.
The exact retained series carrier for \(\pi\), including the Machin
Gaussian factorization and its finite-prime support, remains in the
transcendental-presentation-topology record. Completion joins that carrier
to the infinite place; it does not replace it with a decimal constant.

## One exact reciprocal path

At height \(t=3/2\), the two normal sheets

\[
w_+=\frac14+\frac32i,
\qquad
w_-=-\frac14+\frac32i
\]

produce

\[
W_1(w_+)=\frac{21}{61}+\frac{48}{61}i,
\qquad
W_1(w_-)=\frac{7}{15}+\frac{16}{15}i.
\]

Their squared magnitudes are

\[
|W_1(w_+)|^2=\frac{45}{61},
\qquad
|W_1(w_-)|^2=\frac{61}{45},
\]

so the product is exactly one. Their planar shell residuals are
\(-16/61\) and \(16/45\). These are not additive opposites because the two
Cayley denominators differ; reciprocity, not Euclidean reflection of the
rendered radii, is the invariant.

After the rational sphere lift, the same pair becomes

\[
\left(\frac{21}{53},\frac{48}{53},-\frac{8}{53}\right),
\qquad
\left(\frac{21}{53},\frac{48}{53},\frac{8}{53}\right).
\]

The tangential coordinates are identical and the normal hands are exact
opposites. This is the clean geometric form of the reciprocal sheets the
earlier revolving-Smith discussion was reaching for.

On the fixed seam, two exact examples are

\[
w=\frac32i
\mapsto
\left(\frac5{13},\frac{12}{13},0\right),
\qquad
w=2i
\mapsto
\left(\frac35,\frac45,0\right).
\]

Both lie on the unit shell with zero normal coordinate. Only these
constant-radius rows license revolution by their actual rebase phase.
Off-seam rows are retained as spirals; copying them around a fixed shell
would fabricate a symmetry that their own scale current does not possess.

## Consequence for the RH construction

For a nontrivial completed zero mode

\[
s=\frac12+\varepsilon+i\gamma,
\]

the geometric RH statement can now be written without treating the complex
plane as an absolute picture:

\[
\varepsilon=0.
\]

In the joined atlas this one statement has four simultaneous faces:

1. the zero occurs on the fixed locus of \(J\);
2. the normal projector vanishes;
3. its logarithmic rebase is unitary/constant-radius rather than spiral; and
4. its centered Smith image lies on the unit shell.

This is an exact equivalence of local charts after completion. It is more
informative than saying that a plotted point happens to have real part
\(1/2\), because it specifies what is preserved when the representation
changes.

The remaining proof-bearing relation is now narrower. The atlas still needs
one global carrier—equivalently an all-probe sign law or an operator with the
required complete spectral relation—which excludes nontrivial zero modes
with \(\varepsilon\ne0\). More local samples, prettier revolution, or a
choice of orientation cannot supply that exclusion. The next construction
must transport the completed response through arbitrary admitted
presentation changes while retaining adjoint, boundary, and holonomy.

## What this construction changes

The formerly proposed “parameterized family atlas” is no longer empty at
the local level. It now has:

- exact germ transport and local-degree rebasing;
- source-preserving coincidence classification;
- exact fixed/normal orbit projectors;
- exact circle/spiral conduct under logarithmic scale;
- exact reciprocal functional partners; and
- exact Smith-shell incidence from the same normal hand.

The open work is cross-presentation and global completed transport, not
another enumeration of prime or zero coordinates. A future observatory view
may derive from these rows, but it must let the active source, germ, and
receiver determine the camera. The exact report is already the primary
analytical object.

## Reproduction

From the laboratory root:

```sh
cargo check --quiet --manifest-path src/soma/Cargo.toml \
  -p life --example eros_conformal_rebase_atlas

cargo build --release --quiet --manifest-path src/soma/Cargo.toml \
  -p life --example eros_conformal_rebase_atlas

src/soma/target/release/examples/eros_conformal_rebase_atlas \
  src/soma/observations/eros-conformal-rebase-atlas-01/REPORT.json
```

The instrument is bounded, deterministic, and data-first. It uses four
independent exact workers and emits the complete carrier into one report.
