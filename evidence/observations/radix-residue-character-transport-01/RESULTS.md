# Radix–residue–character transport 01

**24 July 2026 · exact bounded host construction · complete fibers retained · no floating-point
or transcendental evaluation · Soma interior unchanged**

## Question

How does a radix change the geometry of counting without changing the integer occurrence itself?
In particular:

1. when does a residue receiver become local to finitely many digits;
2. when does it require cyclic winding through arbitrarily high places;
3. what does the finite-character basis preserve or forget;
4. where do the factors \(1/q\) and \(1/2\) actually come from; and
5. how does the same occurrence enter the prime-valuation and Mellin faces used by the zeta
   relation?

The reusable objects are:

- `definition:radix-residue-character-cell`;
- `theorem:radix-residue-phase-decomposition`; and
- `lemma:weighted-mellin-basis-rebase`.

The complete bounded testimony is [`REPORT.json`](REPORT.json). It contains every member of every
digit-box residue fiber, every member of the common decimal/ternary occurrence fibers, exact
cyclotomic character coordinates, prime valuations, and formal Mellin characters.

## The exact split

For radix \(b\) and modulus \(q\), write

\[
q=q_{\parallel}q_{\perp},
\]

where \(q_{\parallel}\) contains the prime powers of \(q\) whose primes divide \(b\), while
\(\gcd(b,q_{\perp})=1\). The place word

\[
w_k=b^k\bmod q
\]

then has two nonidentical components:

- modulo \(q_{\parallel}\), \(w_k\) becomes zero after a finite cutoff, so only a finite
  least-significant suffix can affect the receiver;
- modulo \(q_{\perp}\), multiplication by \(b\) is invertible, so \(w_k\) winds periodically with
  period \(\operatorname{ord}_{q_{\perp}}(b)\).

This is not a statistical classification. It follows exactly from prime valuations and the
Chinese remainder theorem.

| bounded cell | place word | local component | cyclic component | complete residue population |
|---|---|---:|---:|---|
| two decimal digits mod \(5\) | \(1,0\) | \(q_{\parallel}=5\), cutoff \(1\) | none | \(20,20,20,20,20\) |
| four ternary digits mod \(5\) | \(1,3,4,2\) | none | \(q_{\perp}=5\), period \(4\) | \(17,16,16,16,16\) |
| two decimal digits mod \(11\) | \(1,10\equiv-1\) | none | \(q_{\perp}=11\), period \(2\) | \(10,9,\ldots,9\) |

The decimal divisibility rule for \(5\) is therefore not a special property of the integer
line. It is the local face produced because the radix already contains the prime axis \(5\).
The alternating decimal rule for \(11\) and the four-phase ternary rule for \(5\) are the
coprime winding face of the same theorem.

## One occurrence, two radically different paths

The shared atlas retains every integer from \(0\) through \(80\). Each integer is represented in
two decimal digits and four ternary digits and then received modulo \(5\). The complete receiver
fibers are identical:

\[
\begin{aligned}
C_0&=\{0,5,10,\ldots,80\},\\
C_1&=\{1,6,11,\ldots,76\},\\
C_2&=\{2,7,12,\ldots,77\},\\
C_3&=\{3,8,13,\ldots,78\},\\
C_4&=\{4,9,14,\ldots,79\}.
\end{aligned}
\]

Their sizes are

\[
(17,16,16,16,16).
\]

The agreement does not mean the paths are the same. For \(17\),

\[
17=(7,1)_{10,\mathrm{LSF}},
\qquad
17=(2,2,1,0)_{3,\mathrm{LSF}}.
\]

Decimal transport modulo \(5\) is

\[
7\cdot1+1\cdot0\equiv2,
\]

whereas ternary transport is

\[
2\cdot1+2\cdot3+1\cdot4+0\cdot2
\equiv 2+1+4+0
\equiv2.
\]

For \(80\), the difference is stronger:

\[
(0,8)_{10,\mathrm{LSF}}
\longmapsto
0\cdot1+8\cdot0\equiv0,
\]

while

\[
(2,2,2,2)_{3,\mathrm{LSF}}
\longmapsto
2+1+3+4\equiv0.
\]

The decimal receiver makes every higher-place contribution dark. The ternary receiver needs all
four phase classes and closes only after their oriented sum. The same quotient is therefore
receiver-exact while being unable to reconstruct the transport that produced it. This is a
finite, complete example of receiver non-reconstruction.

## The character face reads the population, not the radix path

For

\[
G(X)=\sum_{a\in C_q}c_aX^a\in\mathbb Z[C_q],
\]

the exact character coordinates are

\[
\widehat G(j)=\sum_ac_a\omega_q^{ja}.
\]

The report represents these in the integral cyclotomic basis; no numerical root of unity is
evaluated.

- The complete two-digit decimal box modulo \(5\) is uniform. Its character coordinates are
  \((100,0,0,0,0)\): every nontrivial character vanishes.
- The complete four-digit ternary box is \(0,\ldots,80\), so residue \(0\) has one additional
  occurrence. Its coordinates are \((81,1,1,1,1)\).
- The two-digit decimal box modulo \(11\) similarly has one complete extra occurrence at residue
  \(0\), giving \((100,1,\ldots,1)\).

The repeated nontrivial coefficient \(1\) records the boundary excess of the bounded interval.
It does **not** identify the period-four ternary winding with the period-two decimal alternation.
Character coordinates preserve the residue population and diagonalize cyclic translation; they
forget the radix path unless that incidence is carried separately.

The inverse factor

\[
\frac1q
\]

comes from exact character orthogonality over the \(q\) members of \(C_q\). Changing the radix
changes the place word \(b^k\bmod q\), but it does not change this group-average normalization.

## The valuation and Mellin face

Every positive member in the shared atlas also carries its exact prime valuation. For example,

\[
80=2^4\cdot5
\longmapsto
4\log2+\log5
\longmapsto
2^{-4s}5^{-s}
=
\exp\!\left[-s(4\log2+\log5)\right].
\]

For the prime occurrence \(41\),

\[
41
\longmapsto
e_{41}
\longmapsto
\log41
\longmapsto
41^{-s}.
\]

The decimal and ternary presentations are reversible charts of the bounded integer occurrence.
Prime valuation is another reversible presentation on the declared positive support. Reduction
modulo \(5\) is a quotient. Mellin specialization is a character receiver of logarithmic
valuation length. Those arrows now have distinct mathematical types instead of being collected
under the ambiguous phrase “basis change.”

## Why the critical \(1/2\) is a different species

For the weighted multiplicative measure

\[
d\mu_\beta(r)=r^\beta\frac{dr}{r},
\]

the logarithmic chart \(r=e^u\) carries the exact square-root density

\[
(\mathcal U_\beta F)(u)=e^{\beta u/2}F(e^u).
\]

Fourier transformation of this carried amplitude is the Mellin transform on

\[
\operatorname{Re}(s)=\frac{\beta}{2},
\]

and weighted reciprocal conjugation has involution

\[
J_\beta(s)=\beta-\overline{s}.
\]

The completed zeta normalization used by the RH paper is the \(\beta=1\) member, producing the
displayed seam \(\operatorname{Re}(s)=1/2\). Carrying the function, measure, and involution to a
different \(\beta\) conjugates the seam. Altering only one changes the mathematical problem.

Thus:

- \(1/q\) is finite-group averaging;
- \(\beta/2\) is a transported half-density and fixed seam;
- the decimal relevance of \(2\) and \(5\) is radix locality.

Their numerals may overlap, but their causal operations do not.

## Consequence for the RH line

This construction closes the basis question which preceded the next RH comparison. The
coordinate label \(1/2\) is neither an absolute line floating outside the completed relation nor
a base-ten artifact. The invariant object is the completed reciprocal involution together with
the measure and amplitude that make its fixed seam unitary. Under a lawful rechart, those data
move together.

The construction does not change the remaining RH sign obligation. It does remove two invalid
routes:

1. a different numeral radix cannot move zeros onto the critical seam; and
2. equality after a residue or character receiver cannot identify the arithmetic path that must
   participate in the completed return.

The informative continuation is therefore not another radix sweep. It is to instantiate the
arithmetic valuation, Archimedean Fourier–Poisson–Mellin, and receiving test/aperture frames with
these arrow types explicit: reversible chart, quotient, character transform, measure rebase, or
genuinely new transport. That prevents the missing cross-channel relation from being hidden
inside the word “basis.”

## Integrity

The optimized host construction wrote 213,908 bytes. The complete report SHA-256 is:

```text
3d0a881dbe4af8f0c20a5d1ebf712c7e761cfe5ed41a042e071cc1ea1c846e83
```

Its internal digest, computed before inserting the digest field, is:

```text
b2d6c74aa0c20a43f14499a3fd11bb148bf08404cbc7e5e019e71c76b4a175d9
```
