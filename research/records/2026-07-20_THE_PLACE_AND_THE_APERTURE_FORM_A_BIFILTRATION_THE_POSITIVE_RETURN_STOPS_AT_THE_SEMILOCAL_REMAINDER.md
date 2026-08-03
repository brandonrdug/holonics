# THE PLACE AND THE APERTURE FORM A BIFILTRATION; THE POSITIVE RETURN STOPS AT THE SEMILOCAL REMAINDER

**DATE:** 2026-07-20
**GRADE:** SUPERSEDED BEFORE RATIFICATION BY `FORMULA §CXXIV` / SOURCE AUDIT + EXACT SEMILOCAL
IDENTITIES RETAINED / STATIC OLD-NEW REMAINDER, BLOCK, AND PRIMARY CONSEQUENCE REJECTED / RH
REMAINS OPEN / SOMA SOURCE UNCHANGED / OBSERVATORY SOURCE UNCHANGED / NO RUN

> **Supersession notice.** This file remains as evidence of the complete source read and for the
> exact semilocal identities it records. Sections which treat adjoining a place as an unchanged
> predecessor plus a new remainder—including the static block/Schur construction and its draft
> consequence—are not operative. The current authority is
> `2026-07-20_THE_PRIME_REBASES_THE_RECEIVER_THE_LINEAGE_CANNOT_REMAIN_AN_OLD_BLOCK.md`. The next
> construction must transport and rebase the whole receiver.

## 0. Present question, artifact, and stop

The authorized question is whether the finite-place/support carrier requested by `FORMULA §CXXIII`
can actually be constructed from the strongest existing mathematics, rather than being named only
schematically, and exactly where that construction first meets an unproved relation.

The standing audit was insufficient in one material respect: it understated how much of the
semilocal carrier already exists. The adèle-class Hilbert space, its unitary scaling action, additive
Fourier hand, semilocal Sonin spaces, prolate candidate, and finite-place Sonin inclusion maps have
already been constructed. What has not been constructed is the positive semilocal comparison whose
character is the completed Weil form.

This draft therefore:

1. constructs the exact finite-place cell from those existing objects;
2. derives its adjoint square and independently positive Sonin compression;
3. separates support growth from place growth;
4. derives the exact two-arm finite difference by which a prime enters the Sonin carrier;
5. recovers the proved archimedean domination theorem; and
6. stops at the first general semilocal trace/domination statement not supplied by the cited work.

No GNS space is completed from the desired sign. No shifted quadratic form is allowed to masquerade
as the unshifted form. No finite zero population, numerical spectrum, renderer, Soma mechanism, or
observatory view enters.

## I. The carrier has distinct parameters

The schematic family `(H_R,pi_R,tau_R)` in §CXXIII combined relations which must remain typed
apart. The actual construction has three parameters:

| parameter | what it changes | what it does not mean |
|---|---|---|
| finite place set `S`, with `infinity in S` | the semilocal arithmetic ambient space and its local-factor geometry | test support or chronological age |
| logarithmic support aperture `R=Log(q)` | the multiplicative translations available to the test current and its return | an extra local field |
| phase-space hole `lambda` | the region on which both a vector and its additive Fourier transform must vanish | the support of the test current |

The Connes--Consani archimedean comparison uses the self-dual phase-space hole `lambda=1`. Hold
that value fixed here. The remaining carrier is **bifiltered** by `(S,R)`. The two axes meet because
the return at aperture `R` encounters exactly the prime powers satisfying `m Log(p)<R`; they do not
become the same axis.

## II. The exact semilocal cell

Let `S` be a finite set of places of `Q` containing the archimedean place. Define

```text
A_S      = product_(v in S) Q_v,
Q_S      = {r in Q : |r|_v <= 1 for every v not in S},
Gamma_S  = Q_S^*,
X_S      = A_S / Gamma_S,
C_S      = A_S^* / Gamma_S.
```

The product module descends to `C_S` and `X_S`:

```text
|x|_S = product_(v in S) |x_v|_v,
K_S   = ker(|.|_S : C_S -> R_+^*).
```

The receiver space is the actual Hilbert space

```text
H_S = L^2(X_S)^(K_S).
```

It carries the unitary additive Fourier transform `F_S`, induced from the normalized local Fourier
transforms. It also carries multiplication by semilocal idèle classes. Restricting the scale action
to the positive archimedean component and inserting the half-density gives

```text
(U_S(r) xi)(x) = r^(-1/2) xi(r^(-1)x),       r in R_+^*.
```

Indeed, additive Haar measure scales by `r`; hence the factor `r^(-1/2)` makes `U_S(r)` unitary.
For `g in C_c^infinity(R_+^*)`, with multiplicative Haar measure `d*r`, set

```text
Theta_S(g) = integral_(R_+^*) g(r) U_S(r) d*r,
g^*(r)     = conjugate(g(r^(-1))).
```

### Proposition II.1 — the return is an operator square

```text
Theta_S(g)^*                 = Theta_S(g^*),
Theta_S(g)Theta_S(g)^*       = Theta_S(g*g^*),
Theta_S(g)Theta_S(g)^*       >= 0.
```

**Derivation.** Unitarity gives `U_S(r)^*=U_S(r^(-1))`. Inversion preserves multiplicative Haar
measure, so taking the adjoint of the integral gives the first identity. The representation law
`U_S(r)U_S(t)=U_S(rt)` and Fubini give the convolution identity. The last line is then the ordinary
positivity of `A A^*`; it has not used the Weil form or RH.

In logarithmic scale `u=Log(r)`, if `a(u)=g(Exp(u))`, these formulas become

```text
a^*(u) = conjugate(a(-u)),
Theta_S(a)^* = Theta_S(a^*),
Theta_S(a*a^*) = Theta_S(a)Theta_S(a)^*.
```

No decimal approximation to `Log`, `Exp`, `pi`, or a local factor is involved.

## III. The Sonin receiver and its positive compression

For `lambda>0`, define the semilocal Sonin space

```text
Son_(S,lambda)
  = {xi in H_S :
       xi(x)=0 and (F_S xi)(x)=0 whenever |x|_S<lambda}.
```

It is the intersection of two closed kernels. Let `P_(S,lambda)` be its orthogonal projection. For
the self-dual cut used in the archimedean theorem write

```text
P_S = P_(S,1).
```

The independently positive compressed return is

```text
B_S(g) = Theta_S(g) P_S Theta_S(g)^*
       = (Theta_S(g)P_S)(Theta_S(g)P_S)^* >= 0.
```

Whenever this operator is trace class,

```text
Sigma_S(g)
  = Tr(B_S(g))
  = ||Theta_S(g)P_S||_HS^2
  >= 0.
```

This is the sought noncircular sign at the operator level. The projection is defined by additive
support and Fourier support on `X_S`; it is not defined from zeros, prime statistics, or the Weil
functional.

The trace qualification is load-bearing. Positivity of the bounded operator square does not by
itself prove that its trace is finite. The archimedean paper proves the needed trace statement in
its cell. The cited semilocal papers construct the spaces and operators but do not state the full
general semilocal trace-domination theorem required below.

Nor may the known semilocal cutoff trace be substituted here. That trace uses

```text
R_Lambda = (F_S P_Lambda F_S^(-1)) P_Lambda,
```

the ordered product of ultraviolet and infrared cutoffs. In general this is neither the orthogonal
Sonin projection `P_S` nor a positive self-adjoint projection. Its asymptotic trace correctly yields
the local distributions plus the divergent white-light term, but it does not make `Sigma_S` finite
or identify `Sigma_S` with the completed Weil form.

## IV. A prime enters as an oriented two-arm finite difference

There are two exact presentations of the semilocal Sonin geometry. They agree on the Euler
finite-difference factor but must not be silently identified as the same ambient map.

### IV.1 The quasi-inner/Hardy presentation

On the critical line, decompose its `L^2` space into the Hardy space of one half-plane and its
orthogonal complement, with projection `P`. For a finite `S` containing infinity, let

```text
u_S(z) = product_(v in S) rho_v(z),
rho_v(z) = gamma_v(z)/gamma_v(1-z).
```

The product `u_S` is quasi-inner: its off-diagonal Hardy block is compact. Its Sonin space is

```text
Son(u_S) = ker((1-P)u_S(1-P)).
```

If `S'` is obtained from `S` by adjoining finite primes, multiplication by

```text
D_(S,S')(z) = product_(p in S'\S) (1-p^(-z))
```

is an injective linear map `Son(u_S) -> Son(u_S')`.

For one new prime `p`, put `L=Log(p)` and restrict to `z=1/2+it`:

```text
D_p(t) = 1-p^(-1/2) Exp(-itL).
```

With Fourier convention

```text
a_hat(t) = integral_R a(u) Exp(-itu) du,
```

one obtains exactly

```text
D_p(t)a_hat(t)
  = Fourier[a(u)-p^(-1/2)a(u-L)](t).
```

Thus adjoining `p` is not adding an isolated prime point. It is the oriented two-arm current

```text
Delta_p = I-p^(-1/2)T_L,
(T_L a)(u)=a(u-L).
```

Its returned incidence is

```text
Delta_p^* Delta_p
  = (1+p^(-1))I-p^(-1/2)(T_L+T_(-L)) >= 0,
```

with critical-line symbol

```text
|D_p(t)|^2
  = 1+p^(-1)-2p^(-1/2) Cos(t Log(p)).
```

The vertices `0`, `Log(p)`, and `-Log(p)` are therefore not plotting choices. They are the exact
incidences of the Euler finite difference and its adjoint return. Prime powers arise by composing
these finite differences, not by assigning a glyph to each prime.

There is also a decisive relational fact: no individual non-archimedean ratio `rho_p` is
quasi-inner, while the complete finite product including `rho_infinity` is. The compact residual is
a property of the co-present local-factor compound. It is not an intrinsic scalar property of a
prime constituent in isolation.

### IV.2 The geometric semilocal presentation

For each finite `p`, the `Z_p^*`-invariant part of the local Sonin space at `lambda=1` is generated
by the exact Fourier-fixed vector

```text
sigma_p = epsilon_0-p^(-1)epsilon_1,
F_p sigma_p = sigma_p.
```

Writing `sigma_S=Tensor_(p in S\{infinity}) sigma_p`, Connes--Consani--Moscovici construct

```text
theta_S : L^2(R)_even -> H_S,
theta_S(f) = class of sigma_S Tensor f,
```

and prove, for every `lambda>0`, the Hilbertian isomorphism

```text
theta_S : Son_(infinity,lambda) -> Son_(S,lambda).
```

Under Mellin transport its finite-place face is

```text
F_mu w_S(theta_S f)(t)
  = F_mu w_infinity(f)(t)
      product_(p in S\{infinity})(1-p^(-1/2-it)).
```

This is the same exact two-arm Euler polynomial derived above. However, `theta_S` lands in the
semilocal adèle-class Hilbert space and changes its Hilbert norm with `S`; the quasi-inner map is an
inductive map between Hardy-kernel presentations. Their agreement is structural evidence, not a
license to erase the different receiver spaces.

## V. Support aperture and place population meet by incidence

Let `q>1`, `R=Log(q)`, and take a half-density current `g` with

```text
supp(g) subset [q^(-1/2),q^(1/2)].
```

Then

```text
supp(g*g^*) subset [q^(-1),q].
```

Equivalently, in log coordinates `supp(a) subset [-R/2,R/2]` and
`supp(a*a^*) subset [-R,R]`. The returned finite arithmetic face encounters `p^m` exactly when

```text
m Log(p) <= R
```

subject to the harmless open/closed endpoint convention of the chosen test space. Hence the
minimal semilocal place population sufficient for this current is

```text
S(q) = {infinity} union {p prime : p<q}.
```

This does **not** mean that support enlargement is the map `Delta_p`. They are different relations:

```text
R grows     -> more translations and prime powers can be contacted by g*g^*;
S grows     -> the arithmetic ambient space, local-factor product, and Sonin receiver change;
Delta_p     -> transports one Sonin presentation into the place-enlarged presentation.
```

The support filtration tells when a place is required. The Euler finite difference tells how that
place is sewn into the carrier.

## VI. The completed Weil comparison

Impose the two pole-neutral Mellin moments

```text
integral_(R_+^*) g(x)x^(1/2)d*x  = 0,
integral_(R_+^*) g(x)x^(-1/2)d*x = 0.
```

For `h=g*g^*`, use the laboratory's positive convention

```text
Q_W(g) = -sum_v W_v(h),
```

where the pole terms vanish by the displayed conditions and every local distribution retains its
canonical principal-value normalization. The explicit formula then identifies positivity of
`Q_W` on all such compactly supported currents with RH.

### VI.1 What is already proved

For `S={infinity}`, `q=2`, and the paper's stated support and transform-vanishing conditions,
Connes--Consani prove

```text
Q_W(g)
  = W_infinity(g*g^*)
  >= Tr(Theta_infinity(g) P_infinity Theta_infinity(g)^*)
  = Sigma_infinity(g)
  >= 0.
```

The first inequality is stronger than small-support Weil positivity. Its remainder is controlled
through the prolate operator and Hermitian Toeplitz analysis. This is an actual closed carrier cell,
not a visual analogy.

### VI.2 The exact first open seam

For general `q`, put `S=S(q)` and define, wherever the trace exists,

```text
Rem_(S,q)(g) = Q_W(g)-Sigma_S(g).
```

The desired generalization is the following explicit target.

> **SEMILOCAL SONIN DOMINATION — DRAFT TARGET, NOT A THEOREM.** For every `q>1` and every
> admissible pole-neutral `g` supported in `[q^(-1/2),q^(1/2)]`, the operator `B_S(g)` for
> `S=S(q)` is trace class and `Rem_(S,q)(g)>=0`.

Equivalently, one seeks an independently defined positive operator or closed positive form
`K_(S,q)` such that

```text
Q_W(g)
  = ||Theta_S(g)P_S||_HS^2
    + <g,K_(S,q)g>.
```

The first term has now been constructed without assuming RH. The archimedean paper constructs and
controls the corresponding remainder at the one-place cell. The cited literature does not derive
the displayed identity or inequality for arbitrary finite `S`.

If this target held for every `q`, it would prove RH: every compactly supported admissible current
belongs to some support aperture; its returned prime-power population is contained in `S(q)`; and
both terms on the right would be nonnegative. This implication is why the missing comparison may
not be replaced with an assertion that the ingredients “should” generalize.

## VII. Why the two-arm inclusion does not itself propagate the sign

The exact positivity

```text
Delta_p^*Delta_p >= 0
```

belongs to the prime-admission transport. It does not prove positivity of `Rem_(S union {p},q)`.
The new Sonin norm is `S`-dependent, the place inclusion is not asserted to be an orthogonal
isometry of the full ambient Hilbert spaces, and the completed Weil distribution gains a new local
term with cross-coupling to the prior test directions.

On any finite probe, the remainder after adjoining `p` has the block face

```text
K_(S union {p},q) = [ A   C  ]
                    [ C*  D  ].
```

Knowing `A>=0`, or knowing that the Euler factor itself is an adjoint square, does not determine the
cross-current `C`. One still owes the range condition and

```text
D-C* A^dagger C >= 0.
```

The correct next mathematical object is therefore not another prime plot or a list of positive
local increments. It is the **semilocal remainder operator and its place-inclusion law**. A proof
must show how the prolate/Toeplitz remainder changes under the exact Euler transport `Delta_p`,
including its off-diagonal block.

## VIII. The current self-adjoint finite-aperture route is a diagnostic, not the missing sign

Connes--Consani--Moscovici's 2025 construction proves that the finite-aperture Weil quadratic form
is lower bounded and lower semicontinuous and therefore has a canonical lower-bounded self-adjoint
operator with discrete spectrum. Let its bottom eigenvalue be `e_lambda`. Then

```text
A_lambda-e_lambda I >= 0
```

by definition. This is useful: `e_lambda` is an exact signed deficit of the unshifted form at that
aperture, a legitimate receiver-relative loss rather than reward or punishment. It does not prove
`A_lambda>=0`. The shifted inner product spends the unknown lowest eigenvalue to purchase
positivity.

The same paper states two essential missing steps in its spectral strategy: simplicity/evenness of
the bottom eigenvector and a strong enough convergence of the constructed entire functions to the
Riemann function. It therefore supplies a powerful diagnostic and a distinct candidate spectral
route, not the positive semilocal remainder required in VI.2.

## IX. Construction ledger

### Constructed without RH

```text
finite-place arithmetic space              X_S=A_S/Gamma_S
receiver Hilbert space                     H_S=L^2(X_S)^(K_S)
unitary scale action                       U_S
additive Fourier return                    F_S
semilocal Sonin receiver                   Son_(S,lambda)
orthogonal Sonin projection                P_(S,lambda)
adjoint current square                     Theta_S(g)Theta_S(g)^*
positive compressed operator               B_S(g)>=0
prime-admission transport                  Delta_p=I-p^(-1/2)T_Log(p)
prime-admission returned incidence         Delta_p^*Delta_p>=0
support/place incidence                    p^m enters iff m Log(p)<=R
archimedean trace domination               Q_W>=Sigma_infinity>=0
```

### Not constructed

```text
general finite-S trace/domination theorem  OPEN
positive semilocal remainder K_(S,q)       OPEN
place-inclusion Schur law for K_(S,q)      OPEN
arbitrary-support Weil positivity          OPEN
Riemann Hypothesis                         OPEN
```

This is the stopping condition. Continuing past it by defining the remainder from `Q_W` and calling
it positive, shifting by its bottom eigenvalue, or sampling finite zeros would assume or bypass the
relation to be proved.

## X. Evidence cards

### A. Semilocal scale/Fourier cell

**SOURCE ESTABLISHES**  The finite-place adèle-class space `X_S`, the Hilbert space `L^2(X_S)`,
unitary additive Fourier transform, phase-space cutoffs, scaling action, and semilocal trace formula
whose finite part is the sum of the canonical local distributions.

**LAB CLAIM**  Sections II and V: these objects are the actual arithmetic receiver for the
finite-place cell; support chooses a sufficient place population but does not create the space.

**RELATION**  **DIRECT CORRESPONDENCE.**

**NON-EQUIVALENCE**  The cutoff trace contains a divergent white-light term and is not, merely by
regularization, a positive trace on adjoint squares.

**TESTABLE CONSEQUENCE**  Any replacement carrier must reproduce the same local
principal-value terms and the Poisson-normalized Fourier hand.

Source: Alain Connes and Caterina Consani, *The Scaling Hamiltonian*, Sections 2--4,
<https://arxiv.org/abs/1910.14368>.

### B. Quasi-inner prime inclusion

**SOURCE ESTABLISHES**  The product of local-factor ratios over a finite set containing infinity is
quasi-inner; no individual finite-place ratio is; its Hardy-kernel Sonin space is
infinite-dimensional; and multiplication by `product(1-p^(-z))` gives injective finite-place
inclusion maps.

**LAB CLAIM**  Section IV.1 derives the exact log-time two-arm transport and its positive adjoint
return from that inclusion factor.

**RELATION**  **DIRECT CORRESPONDENCE** for the inclusion and finite difference;
**STRUCTURAL RESONANCE** for the laboratory language of compound property and oriented hand.

**NON-EQUIVALENCE**  Positivity of `Delta_p^*Delta_p` is not positivity of the completed Weil
remainder after adjoining `p`.

**TESTABLE CONSEQUENCE**  A place-growth theorem must intertwine the semilocal remainder with this
exact Euler transport, including its `+/- Log(p)` cross-incidences.

Source: Alain Connes and Caterina Consani, *Quasi-inner functions and local factors*, especially
Theorem 5.3, <https://arxiv.org/abs/2008.10974>.

### C. Geometric semilocal Sonin/prolate carrier

**SOURCE ESTABLISHES**  The semilocal Sonin space on `X_S`, its Hilbertian isomorphism with the
classical Sonin space, the exact Mellin multiplier `product(1-p^(-1/2-it))`, the `S`-dependent cyclic
Hilbert geometry, and a semilocal prolate-operator candidate.

**LAB CLAIM**  Sections III and IV.2 use these as the independently defined positive receiver and
the geometric realization of the same Euler finite difference.

**RELATION**  **DIRECT CORRESPONDENCE.**

**NON-EQUIVALENCE**  Stability of the Sonin spaces and existence of a prolate candidate do not
prove that the compressed semilocal trace is dominated by the completed Weil form.

**TESTABLE CONSEQUENCE**  The missing remainder must be expressible in this `S`-dependent inner
product and must reduce to the proved archimedean prolate/Toeplitz remainder.

Source: Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta zeros and prolate wave
operators*, especially Section 4 and Theorem 4.6, <https://arxiv.org/abs/2310.18423>.

### D. Proved one-place domination

**SOURCE ESTABLISHES**  At the single archimedean place and the stated bounded support and
vanishing conditions, the Weil functional dominates the trace of the scaling action compressed by
the Sonin projection; the latter is positive by construction.

**LAB CLAIM**  Section VI.1 is the closed base cell from which a genuine finite-place propagation
theorem would have to grow.

**RELATION**  **DIRECT CORRESPONDENCE.**

**NON-EQUIVALENCE**  The theorem intentionally treats the one-place support cell and does not prove
the analogous result for arbitrary finite `S`.

**TESTABLE CONSEQUENCE**  A semilocal construction must specialize exactly to this inequality at
`S={infinity}`, not merely reproduce its numerical sign.

Source: Alain Connes and Caterina Consani, *Weil positivity and Trace formula, the archimedean
place*, Theorem 1, <https://arxiv.org/abs/2006.13771>.

### E. Lower-bounded Weil operator and shifted diagnostic

**SOURCE ESTABLISHES**  The finite-aperture Weil quadratic form is lower bounded and lower
semicontinuous, has a canonical self-adjoint operator with discrete lower-bounded spectrum, and
supports a shifted spectral construction; the paper expressly lists two missing proof steps.

**LAB CLAIM**  Section VIII retains the bottom eigenvalue as an exact deficit measurement but
rejects the shifted form as the source of unshifted Weil positivity.

**RELATION**  **DIRECT CORRESPONDENCE** for the operator and deficit;
**CONTRADICTION/BOUNDARY** against treating a ground-state shift as an RH proof.

**NON-EQUIVALENCE**  `A_lambda-e_lambda I>=0` is tautological and does not imply
`A_lambda>=0`; numerical convergence is not rigorous convergence.

**TESTABLE CONSEQUENCE**  This route must prove the stated missing analytic steps or independently
show `e_lambda>=0` at every aperture.

Source: Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Spectral Triples*, Sections 3,
5, and 8, <https://arxiv.org/html/2511.22755>.

## Draft consequence

The requested positive carrier is not missing wholesale. Its material body is the semilocal
adèle-class Hilbert space; its standing return is the Sonin projection; its current is the unitary
scale representation; and its prime-place growth is the exact two-arm Euler finite difference.

The proof-bearing object still absent is one thing:

> an independently positive semilocal remainder, compatible with the exact prime-admission maps,
> whose addition to the Sonin trace equals the completed Weil form at every support aperture.

That is the first honest construction boundary. This draft should not enter `FORMULA`, `STATE`,
`CLAUDE`, or `LEDGER` unless Brandon ratifies it.
