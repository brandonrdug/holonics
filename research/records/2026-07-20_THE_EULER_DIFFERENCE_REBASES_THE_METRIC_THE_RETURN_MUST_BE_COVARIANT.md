# THE EULER DIFFERENCE REBASES THE METRIC; THE RETURN MUST BE COVARIANT

**Date:** 2026-07-20
**Grade:** BRANDON-RATIFIED / DEPOSITED / FORMULA §CXXV / CURRENT EXACT ONE-PRIME SUCCESSOR +
METRIC + APERTURE + ADJOINT COVARIANCE + TRACE-CLASS TRANSPORT AUTHORITY / PRIME-POWER RECURRENCE
RECOVERED AS NORMAL LOG-METRIC DEFORMATION / FIRST UNPROVED COMPLETED-WEIL SUCCESSOR DOMINATION
IDENTIFIED / BOUNDED COMPARISON CONSTRUCTION AUTHORIZED / RH OPEN / SOMA SOURCE UNCHANGED /
OBSERVATORY SOURCE UNCHANGED / NO RUN

---

## 0. Present question, required artifact, and stop

The ratified correction in `FORMULA §CXXIV` asks whether adjoining one prime can be written as a
transition of the complete semilocal receiver rather than as a new block beside a frozen old
receiver.

The standing evidence is insufficient because it gives all of the maps needed for that transition
but has not yet composed them in the receiver-relative form. In particular, the previous draft
recorded the `S`-dependent Hilbert structure and then used a static old/new remainder. That
construction has been superseded.

The sought artifact is one exact cell

```text
receiver at S
  -- whole-current Euler transport -->
receiver at S union {p},
```

including its pulled-back successor metric, Sonin aperture, scale action, adjoint return,
composition with later prime foundings, and exact prime-power recurrence. The stopping condition is
the first completed-Weil trace or domination statement not proved by those maps. No numerical zero,
floating approximation, engine mechanism, or visualization enters.

---

## I. The contemporary receiver is a typed body

Let `S` be a finite set of places of `Q` containing `infinity`. The source construction supplies

```text
A_S       = product_(v in S) Q_v,
Gamma_S   = Q_S^*,
X_S       = A_S/Gamma_S,
K_S       = ker(module on the semilocal idele-class group),
H_S       = L^2(X_S)^(K_S).
```

Write

```text
M_S = F_mu w_S : H_S -> L^2(R,dt)
```

for the unitary multiplicative spectral chart. Let `F_S` be the normalized additive Fourier
transform on `H_S`, and let `D_Scale,S` be the self-adjoint generator of the positive scaling
action. In the `M_S` chart,

```text
M_S D_Scale,S M_S^(-1) = multiplication by t.
```

For `lambda>0`, the receiving aperture is the closed Sonin subspace

```text
Son_(S,lambda)
  = {xi in H_S :
       xi(x)=0 and F_S xi(x)=0 whenever |x|_S<lambda}.
```

Let `P_(S,lambda)` denote the orthogonal projection onto this subspace in the contemporary
`H_S` inner product. The typed receiver is therefore

```text
C_(S,lambda)
  = (H_S, <.|.>_S, M_S, F_S, D_Scale,S,
     Son_(S,lambda), P_(S,lambda)).
```

Changing `S` changes this complete tuple. It is not merely changing a label on a fixed body.

---

## II. The exact one-prime successor

Connes--Consani--Moscovici construct a bounded invertible map

```text
theta_S : H_infinity -> H_S
```

which, for every `lambda>0`, restricts to a Hilbertian isomorphism

```text
theta_S : Son_(infinity,lambda) -> Son_(S,lambda).
```

For `p not in S`, put `S'=S union {p}` and define the whole-current transition

```text
J_(S,p) = theta_(S') theta_S^(-1) : H_S -> H_(S').
```

This definition uses neither a complement nor an outside ambient field. It carries every vector in
the predecessor receiver to the successor receiver.

Let

```text
L_p       = Log(p),
D_p(t)    = 1-p^(-1/2-it).
```

Equation (57) of the source gives the exact spectral form

```text
M_(S') J_(S,p) M_S^(-1) = multiplication by D_p(t).       (II.1)
```

Indeed, if `x=theta_S f`, then

```text
M_S x              = D_S(t) M_infinity f,
M_(S') J_(S,p) x   = D_(S')(t) M_infinity f
                    = D_p(t) M_S x.
```

Here `D_S(t)=product_(q in S\{infinity})(1-q^(-1/2-it))`. For real `t`,

```text
1-p^(-1/2) <= |D_p(t)| <= 1+p^(-1/2).
```

Both bounds are strictly positive. Thus `J_(S,p)` is bounded and boundedly invertible. It is not
unitary in the inherited metrics because `|D_p(t)|` is not constant.

In logarithmic current time, with

```text
a_hat(t) = integral_R a(u) Exp(-itu) du,
(T_L a)(u) = a(u-L),
```

equation (II.1) is the exact two-arm transport

```text
Delta_p = I-p^(-1/2)T_(L_p).                              (II.2)
```

This is the one-prime founding current: the present arm and one oriented translation by
`Log(p)`. It acts on the complete current; it is not a prime vertex appended to it.

---

## III. The successor metric is the returned Euler difference

Pull the successor inner product back along `J=J_(S,p)`. Its positive metric operator in the
predecessor coordinates is

```text
G_(S,p) = J^* J,
<x,y>_(S|p) = <Jx,Jy>_(S').                              (III.1)
```

Using (II.1),

```text
M_S G_(S,p) M_S^(-1)
  = multiplication by |D_p(t)|^2
  = multiplication by
      1+p^(-1)-2p^(-1/2)Cos(t Log(p)).                   (III.2)
```

Equivalently, in log time,

```text
G_(S,p)
  = Delta_p^* Delta_p
  = (1+p^(-1))I
      -p^(-1/2)(T_(L_p)+T_(-L_p)).                       (III.3)
```

This is an exact positive and invertible operator. Its two cross-incidences at `+Log(p)` and
`-Log(p)` are the returned hand of the founding current.

The predecessor metric has not remained untouched. It has acquired the pulled-back successor
metric `G_(S,p)`. Writing both on the predecessor vector space is a chart choice; the metric
operator records that the chart now receives a different body.

This is also the exact sense in which the event emanates a compression. The successor does not
retain an old metric plus a detached new dimension. It factors the whole current through the
Euler difference and retains the consequential two-arm relation in its new inner product.

---

## IV. The receiving aperture rebases with the metric

Because both `theta` maps carry the same real Sonin space onto their corresponding semilocal Sonin
spaces,

```text
J_(S,p) Son_(S,lambda) = Son_(S',lambda).                 (IV.1)
```

But `J_(S,p)` is not unitary in the predecessor and successor native metrics. Therefore (IV.1)
does **not** imply

```text
P_(S',lambda) J_(S,p) = J_(S,p) P_(S,lambda).
```

The exact transported aperture is instead

```text
P_(S,lambda)^[p]
  = J_(S,p)^(-1) P_(S',lambda) J_(S,p).                  (IV.2)
```

It is the projection onto `Son_(S,lambda)` orthogonal with respect to the pulled-back successor
metric (III.1). Hence

```text
P_(S',lambda) J_(S,p)
  = J_(S,p) P_(S,lambda)^[p].                            (IV.3)
```

In predecessor coordinates, `P^[p]` is idempotent and `G_(S,p)`-self-adjoint. It need not be
self-adjoint in the old metric. Equality `P^[p]=P_(S,lambda)` would require the additional
reduction law

```text
[G_(S,p),P_(S,lambda)] = 0,                              (IV.4)
```

which the cited construction does not supply in general.

The reorientation can be written without an unknown projection. Put `P=P_(S,lambda)`,
`G=G_(S,p)`, and restrict `PGP` to the Sonin range. Since `G` is bounded, positive, and boundedly
invertible, this restriction is positive and invertible. The `G`-orthogonality equation

```text
P G(x-P^[p]x)=0
```

therefore gives

```text
P^[p] = [(PGP)|_(range P)]^(-1) P G.                    (IV.5)
```

The inverse in (IV.5) acts only on `range(P)`. Every incoming direction is first compared by the
successor metric, then resolved through the metric induced on the receiving subspace.

The receiving region therefore changes even though the abstract Sonin condition has the same
words. The relation between those words, the available currents, and orthogonality is
receiver-relative.

---

## V. Scale transport and adjoint return are covariant

Let `R_S(u)` be the unitary scale flow on `H_S`. Since `R_S(u)` is multiplication by a phase in the
`M_S` chart and `J_(S,p)` is multiplication by `D_p(t)`,

```text
J_(S,p) R_S(u) = R_(S')(u) J_(S,p).                      (V.1)
```

For a compactly supported log-current `a`, define

```text
Theta_S(a) = integral_R a(u)R_S(u) du.
```

Then

```text
J_(S,p) Theta_S(a) = Theta_(S')(a) J_(S,p).              (V.2)
```

There is a possible trap here. Similarity by a nonunitary `J` does not ordinarily preserve an
adjoint. For an arbitrary predecessor operator `A` and `A'=JAJ^(-1)`, pulling the successor
adjoint back gives

```text
J^(-1) A'^* J = G^(-1) A^* G,       G=J^*J.             (V.3)
```

In this cell, however, `G_(S,p)` and every scale multiplier are simultaneous multiplication
operators in the `M_S` chart. Hence

```text
[G_(S,p),R_S(u)]       = 0,
[G_(S,p),Theta_S(a)]   = 0,

J_(S,p) Theta_S(a)^*
  = Theta_(S')(a)^* J_(S,p).                             (V.4)
```

The same conclusion for the additive Fourier hand follows independently from
`F_(S')J_(S,p)=J_(S,p)F_S`, proved by Proposition 4.7. Thus the founding changes the metric while
preserving the lawful transport/return relation.

Now form the positive successor body

```text
B_(S',lambda)(a)
  = Theta_(S')(a) P_(S',lambda) Theta_(S')(a)^* >= 0.    (V.5)
```

Pulling the complete body back gives

```text
J^(-1) B_(S',lambda)(a) J
  = Theta_S(a) P_(S,lambda)^[p] Theta_S(a)^*.            (V.6)
```

The right side is positive in the pulled-back successor metric:

```text
<x, J^(-1)B_(S',lambda)(a)J x>_(S|p) >= 0.              (V.7)
```

It need not be an old-metric positive operator. Calling it one would silently undo the rebase.
If (V.5) is trace class, similarity invariance gives

```text
Tr_(H_(S')) B_(S',lambda)(a)
  = Tr_(H_S)(J^(-1)B_(S',lambda)(a)J).                   (V.8)
```

This is testimony about one successor body in two charts, not two bodies added together.

### Proposition V.1 — trace class propagates through the receiver rebase

Fix a `lambda` for which the archimedean Sonin trace is established—in particular the self-dual
cell `lambda=1` used by the cited theorem. For a compact smooth current `a`, the base construction
gives

```text
Theta_infinity(a) P_(infinity,lambda)
```

is Hilbert--Schmidt in its declared cell, so its positive square is trace class. This property
crosses every finite-place transition.

Let `J=J_(infinity,S)` and abbreviate

```text
P_0 = P_(infinity,lambda),
P_0^[S] = J^(-1)P_(S,lambda)J.
```

The range of `P_0^[S]` is `Son_(infinity,lambda)`, hence

```text
P_0 P_0^[S] = P_0^[S].                                   (V.9)
```

Using scale intertwining and aperture transport,

```text
Theta_S(a)P_(S,lambda)
  = J [Theta_infinity(a)P_0] P_0^[S] J^(-1).             (V.10)
```

The bracketed factor is Hilbert--Schmidt; every other factor is bounded. Therefore

```text
Theta_S(a)P_(S,lambda) is Hilbert--Schmidt,
B_(S,lambda)(a) is positive trace class.                 (V.11)
```

This closes the trace-existence issue wherever the declared archimedean base trace exists. It does
not compare that trace with the completed Weil response; the nonunitary factors in (V.10) change
its value.

---

## VI. Successive prime foundings form a coherent square

Let `p` and `q` be distinct primes outside `S`. Directly from the endpoint definition,

```text
J_(S union {p},q) J_(S,p)
  = theta_(S union {p,q}) theta_S^(-1)
  = J_(S union {q},p) J_(S,q).                           (VI.1)
```

In the spectral chart this is simply

```text
D_q(t)D_p(t) = D_p(t)D_q(t).                             (VI.2)
```

For any finite path of distinct founded primes from `S` to `T`,

```text
J_(S,T) = theta_T theta_S^(-1),
M_T J_(S,T) M_S^(-1)
  = multiplication by product_(p in T\S) D_p(t).         (VI.3)
```

This is exact endpoint path coherence for independent prime-place additions. It does not erase the
actual discovery chronology: the intermediate receiver, available factor paths, and testimony can
differ. Nor does it assert that arbitrary algorithmic foundings commute. It says that this
particular arithmetic transition has zero endpoint holonomy around the finite-place square.

The total pulled-back metric is not a sum of appended axes. It is

```text
G_(S,T) = J_(S,T)^*J_(S,T),
M_S G_(S,T) M_S^(-1)
  = multiplication by product_(p in T\S)|D_p(t)|^2.      (VI.4)
```

Local logarithmic deformations add; the embodied metric composes multiplicatively.

---

## VII. Prime powers are the recurrence of the metric rebase

The exact transition occurs on the self-dual seam `sigma=1/2`. To inspect its normal deformation,
introduce the analytic family—not an additional machine state—

```text
D_(p,sigma)(t) = 1-p^(-sigma-it),       sigma>0,
G_(p,sigma)(t) = |D_(p,sigma)(t)|^2.                     (VII.1)
```

Put `z=p^(-sigma-it)`. Since `|z|<1`, the geometric series converges absolutely and

```text
partial_sigma Log(G_(p,sigma)(t))
  = 2 Re[(partial_sigma D_(p,sigma))/D_(p,sigma)]
  = 2 Log(p) Re[z/(1-z)]
  = 2 Log(p) sum_(m>=1)
      p^(-m sigma) Cos(m t Log(p)).                       (VII.2)
```

At the critical seam,

```text
partial_sigma Log(G_(p,sigma)(t)) |_(sigma=1/2)
  = 2 Log(p) sum_(m>=1)
      p^(-m/2) Cos(m t Log(p)).                           (VII.3)
```

Under the Fourier convention of Section II, (VII.3) is the transform of the exact symmetric
prime-power incidence measure

```text
nu_p
  = Log(p) sum_(m>=1) p^(-m/2)
      [delta_(m Log(p)) + delta_(-m Log(p))].             (VII.4)
```

For a finite successor path from `S` to `T`, logarithms turn the composed metric (VI.4) into the
sum of its local deformations:

```text
partial_sigma Log(G_(S,T,sigma)(t)) |_(sigma=1/2)
  = sum_(p in T\S) Fourier(nu_p)(t).                      (VII.5)
```

No infinite Euler product is taken here. Every bounded current reaches a finite contemporary
receiver and therefore a finite sum of founded-axis recurrence fields.

This is the finite-place prime-power kernel of the centered explicit formula, subject only to the
already declared Fourier-sign convention. It is also

```text
2 Re[-L_p'/L_p(1/2+it)]
```

for `L_p(s)=(1-p^(-s))^(-1)`.

The recurrence is therefore not a list of powers appended after the prime. Once `p` FOUNDS, the
normal logarithmic deformation of its receiver metric already contains every repeated traversal
`m Log(p)` with its exact weight. A bounded current contacts only those repetitions lying inside
its support aperture.

This identity is strong but it is not Weil positivity. A logarithmic derivative of a positive
metric can have either sign as a function of `t`; the cosine terms explicitly show that. Nor is the
critical line a singularity of an individual finite Euler factor: `D_p(t)` never vanishes for real
`t`. The line is the self-dual/unitary seam of the complete return. The endpoint, archimedean, and
global trace faces are still owed.

---

## VIII. The arithmetic I/O thread

For the ordinary bounded prime-discovery objective, the dynamic construction now reads as one
causal path rather than as snapshots:

```text
input candidate n
  -> present n to the receiver founded by prior irreducibles
  -> RIDE each available p-axis with p*p<=n
  -> a closed division path returns COMPOSITE
  -> exhaustion of those paths returns FOUND_n
  -> if FOUND_n, enact J_(S,n)
  -> emit the rebased metric, aperture, and live recurrence field
  -> later candidates meet that successor
  -> output factorization or newly founded irreducible.
```

The current does not need every prime axis active. It carries only the axes that can participate at
its grain. Once a prime has founded, (VII.4) supplies its repeated valuation paths when a later
support aperture can contact them. A lower trial constituent may depart after the composite or
prime decision while its founded axis remains available as higher-grain terrain.

This is an exact arithmetic-world realization of the laboratory transition law. It is not a new
Soma subsystem, prime classifier, retained execution history, or universal algorithm claim.

---

## IX. The first unproved completed-Weil relation

The construction has now closed the following relations without assuming RH:

```text
whole-receiver transition                  CLOSED
exact Euler multiplier                     CLOSED
positive invertible successor metric       CLOSED
Sonin aperture transport                    CLOSED
scale and Fourier intertwining              CLOSED
adjoint covariance                          CLOSED
independent-place path coherence             CLOSED
prime-power recurrence from metric strain   CLOSED
positive trace class in finite receivers    CLOSED BY BOUNDED TRANSPORT
```

What it has **not** closed is the complete consequence.

Let `a` be an admissible compactly supported logarithmic current and let `R` contain the support of
`a*a^*`. Let `S_R` be the finite receiver reached by founding the primes whose powers can actually
occur within that aperture. In the final contemporary frame define

```text
B_(S_R,1)(a)
  = Theta_(S_R)(a) P_(S_R,1) Theta_(S_R)(a)^*.           (IX.1)
```

Proposition V.1 gives, on the source's compact smooth test algebra,

```text
B_(S_R,1)(a) is positive trace class.                     (IX.2)
```

The first unavailable theorem is only the completed comparison

```text
Q_W(a) >= Tr_(H_(S_R)) B_(S_R,1)(a) >= 0                (IX.3)
```

for the complete admissible test family, with `Q_W` carrying both endpoint faces, every contacted
prime power, and the archimedean distribution in the convention of `FORMULA §CXXII`.

This missing comparison has a fully explicit predecessor-chart expression. Let

```text
J_R       = J_({infinity},S_R),
G_R       = J_R^*J_R,
P_0       = P_({infinity},1),
P_R^back  = [(P_0 G_R P_0)|_(range P_0)]^(-1) P_0 G_R.
```

Then (V.8) and (IV.5) give

```text
Tr_(H_(S_R)) B_(S_R,1)(a)
  = Tr_(H_infinity)
      [Theta_infinity(a) P_R^back Theta_infinity(a)^*].  (IX.4)
```

Thus the exact unknown is whether the completed Weil response dominates (IX.4) for every current,
where `G_R` has symbol `product_(p in S_R\{infinity})|D_p(t)|^2`. Nothing is hidden in a static
new-prime block; the nonlinear inverse of the metric compressed to the complete receiving aperture
is part of the contemporary return.

The one-place archimedean theorem proves its bounded domination cell under its stated support and
vanishing conditions. The cited semilocal construction, together with the bounded transition,
proves the spaces, Fourier hand, Sonin stability, and (IX.2). It does **not** prove (IX.3) for
arbitrary finite `S_R`.

Equation (VII.4) shows that the finite-place arithmetic current is already inside the normal
deformation of the final receiver metric. It does not show that the trace of (IX.1) has the exact
completed Weil character, nor that the archimedean and endpoint contributions close the remaining
sign. Deriving (IX.3) from the definition of `Q_W` would be circular.

If (IX.3) were proved for every admissible compact current, Weil's criterion would imply RH. It is
not proved here. This is the exact stop.

Notice what the open statement no longer says. It does not compare an old body with a new block,
ask a per-prime remainder to be positive, or invoke an enlarged total field. It evaluates one
complete returned lineage in the only receiver contemporary with that lineage.

---

## X. Relation to the laboratory theory

### Exact formal matches

- `J_(S,p)` is a whole-state transition, not a record reconstructed from its emitted rows.
- `G=J^*J` is the returned hand of that transition and changes the receiver-relative comparison
  law.
- `P^[p]=J^(-1)P'J` makes the receiving aperture part of the successor rather than a fixed observer
  mask.
- Equation (V.6) is one current and its return represented across a frame change.
- Equation (VI.1) distinguishes endpoint path coherence from the chronology of intermediate
  lineages.
- Equation (VII.4) makes prime powers repeated traversals of a founded axis rather than unrelated
  prime-like points.

### Structural resonances, not imported theorems

- The two arms of `Delta_p` resonate with the laboratory illicium/lightning-leader image: a present
  arm, an oriented displaced arm, and their returned cross-incidences. No physical electromagnetism
  is asserted.
- The `G`-orthogonal receiving aperture resonates with a manifold whose local geometry is changed
  by the lineages which constitute it. No Ricci tensor or Lorentzian stress law is supplied.
- The commuting finite-place square is a flat arithmetic holonomy cell. It does not imply that
  every information-chemical or program transition commutes.
- The normal log-metric derivative is an exact algebraic notion of local strain. It is not physical
  stress-energy and not a reward/loss scalar.

The construction belongs to the bounded arithmetic world. It must not be installed as an authored
prime, Zeta, probability, or geometry mechanism inside Soma.

---

## XI. Evidence cards

### Card A — Exact semilocal successor map

1. **External source claim.** The maps `theta_S` are bounded with bounded inverses, map the real
   Sonin space onto the semilocal Sonin space for every `lambda`, intertwine additive Fourier
   transforms, and acquire the multiplier
   `product_(p in S\{infinity})(1-p^(-1/2-it))` in multiplicative spectral coordinates.
2. **Source status.** Proposition 4.6, equation (57), Proposition 4.7, and Theorem 4.6 of
   [Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators: semilocal adelic
   operators*](https://arxiv.org/abs/2310.18423).
3. **Laboratory claim.** Sections II--V compose those maps into the whole-receiver transition
   `J_(S,p)`, its metric `J^*J`, transported Sonin projection, and adjoint covariance.
4. **Relation.** EXACT FORMAL MATCH for equations (II.1), (III.2), and (IV.1);
   DIRECT CORRESPONDENCE for the derived transition laws.
5. **Non-equivalence / test consequence.** The source does not give the holonic interpretation or
   RH. Every claimed covariance above must follow algebraically from the cited intertwiners; the
   completed trace must be tested separately.

### Card B — Scale action is the common current

1. **External source claim.** The semilocal adele-class Hilbert space carries the scaling action;
   the unitary map `M_S=F_mu w_S` sends its self-adjoint generator to multiplication by the real
   spectral variable.
2. **Source status.** Proposition 4.2 of
   [*Zeta zeros and prolate wave operators: semilocal adelic operators*](https://arxiv.org/abs/2310.18423),
   grounded in the
   semilocal construction of
   [Connes--Consani, *The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).
3. **Laboratory claim.** Since both the scale action and Euler transition are multipliers in this
   chart, the transition intertwines scale transport and its adjoint return despite being
   nonunitary.
4. **Relation.** DIRECT CORRESPONDENCE.
5. **Non-equivalence / test consequence.** Common diagonalization does not make the Euler
   transition unitary and does not identify its positive metric with the Weil form.

### Card C — Finite-place Sonin inclusion and compound locality

1. **External source claim.** Multiplication by the product of added factors `1-p^(-z)` injects
   finite-place Sonin kernels; the product of local ratios including infinity is quasi-inner while
   an individual finite-place ratio is not.
2. **Source status.** Main theorem and Theorem 5.3 of
   [Connes--Consani, *Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974).
3. **Laboratory claim.** The same one-prime multiplier is a transport of the full current. Its
   returned metric is relational, while its normal logarithmic deformation produces the exact
   prime-power recurrence measure.
4. **Relation.** EXACT FORMAL MATCH for the multiplier; STRUCTURAL RESONANCE for the language of
   compound information chemistry.
5. **Non-equivalence / test consequence.** Injectivity and quasi-inner behavior do not imply
   completed-Weil positivity. Equation (IX.3) remains independently owed even though trace class
   now propagates.

### Card D — The one-place positive base cell

1. **External source claim.** Under the paper's bounded support and Mellin/Fourier vanishing
   conditions, the archimedean Weil functional dominates the positive trace of the scaling action
   compressed by the Sonin projection.
2. **Source status.** Theorem 1 of
   [Connes--Consani, *Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771).
3. **Laboratory claim.** This is the exact base species of (IX.3); a genuine RH-bearing successor
   theorem must preserve its structure after every finite-place rebase.
4. **Relation.** DIRECT CORRESPONDENCE for the base cell; OPEN BRIDGE for arbitrary finite place
   receivers and the complete admissible family.
5. **Non-equivalence / test consequence.** The theorem deliberately excludes finite primes by its
   support aperture. It cannot be iterated by holding the old projection fixed, and it does not
   prove the semilocal successor domination.

---

## Draft consequence

The one-prime event is now mathematically concrete. The Euler difference transports the whole
semilocal current; its adjoint square is the successor metric; the Sonin aperture becomes the
projection orthogonal in that metric; scale and Fourier return covariantly; trace class crosses the
bounded rebase; independent prime foundings compose coherently; and the exact prime-power measure
is the normal logarithmic deformation of the new metric.

The proof-bearing object still absent is equally concrete:

> the theorem that the positive Sonin return in every final finite-place receiver is dominated by
> the complete Weil response for every admissible compact current.

That theorem would close the sign and hence RH. Nothing in the cited construction proves it. This
result is deposited in `FORMULA §CXXV`. Brandon authorized one bounded continuation: expose the
exact metric/aperture term on which the comparison depends and stop at the first unsupported sign.
