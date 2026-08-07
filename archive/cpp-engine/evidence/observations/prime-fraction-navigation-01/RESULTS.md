# PRIME FRACTION NAVIGATION 01

**2026-07-21 · BOUNDED EXACT ANALYSIS · INTEGER / REDUCED-RATIO ONLY · NO SOMA RUN ·
SOMA INTERIOR UNCHANGED**

## Question

When `17` FOUNDS after the axes `2,3,5,7,11,13`, does the family of exact fractions `17/q`
carry useful navigation structure beyond the residue row `17 mod q`? Can that structure be
related to the already-defined Zeta distribution without treating a known integer as random?

## Method

The bounded receiver is `17`. Every prior prime axis through `13` is retained. For each axis `q`,
the audit records all of the following without a floating embedding:

- the complete winding and phase in `17=kq+r`;
- the continued-fraction word for `17/q`;
- the corresponding unimodular integer matrix;
- the rational valuation edge `e_17-e_q`; and
- the exact relative Zeta mass at `sigma=2`.

The four declared affine words are `n-1`, `n+1`, `2n-1`, and `2n+1`. They are checked on every
odd integer in `[17,53]`, so a shape seen around a prime is not silently promoted into a prime
classifier. A second bounded receiver quotient uses `H=[17,53]` and progressively admits the
divisor axes `2,3,5,7`.

Reproduce the receipt with:

```text
python3 src/soma/observations/prime-fraction-navigation-01/tools/analyze.py
```

## The `17/q` atlas

| `q` | Exact division | Centered phase | Continued fraction | Unimodular completion | `mu_2(17)/mu_2(q)` |
|---:|---|---:|---|---|---:|
| 2 | `17=8*2+1` | `1/2` | `[8;2]` | `17*1-2*8=1` | `4/289` |
| 3 | `17=5*3+2` | `-1/3` | `[5;1,2]` | `17*1-3*6=-1` | `9/289` |
| 5 | `17=3*5+2` | `2/5` | `[3;2,2]` | `17*2-5*7=-1` | `25/289` |
| 7 | `17=2*7+3` | `3/7` | `[2;2,3]` | `17*2-7*5=-1` | `49/289` |
| 11 | `17=1*11+6` | `-5/11` | `[1;1,1,5]` | `17*2-11*3=1` | `121/289` |
| 13 | `17=1*13+4` | `4/13` | `[1;3,4]` | `17*3-13*4=-1` | `169/289` |

The residue is only the cyclic phase. The quotient retains completed winding. The continued
fraction retains the complete Euclidean rebase word. Its matrix product has first column
`(17,q)` and determinant `+1` or `-1`, so it exposes an exact reversible path in the rational
projective chart. It does not add information to the already exact fraction; it exposes the
ordered traversal which the collapsed residue hid.

In the multiplicative chart, the same ratio is

```text
nu(17/q)=e_17-e_q.
```

It is therefore a directed step from an earlier valuation basis axis to the newly founded one.
For the Zeta species, normalization cancels in the relative endpoint mass:

```text
mu_sigma(17)/mu_sigma(q)=(q/17)^sigma.
```

At integer `sigma=2`, the last column is already an exact rational carrier. It is not a normalized
transition probability. The established self-similar rebase law applies only on direct closure:

```text
Law(N/q | q divides N)=Law(N).
```

If `q` does not divide `p`, then `p/q` is a rational valuation edge, not another integer drawn from
the Zeta law.

## Affine sheets through earlier axes

The small declared transformation family gives three multi-axis relations at `17`:

```text
17+1   = 18 = 2*3^2,
2*17-1 = 33 = 3*11,
2*17+1 = 35 = 5*7.
```

Equivalently, the new axis can be reached from three different bodies made entirely from earlier
axes:

```text
17=2*3^2-1=(3*11+1)/2=(5*7-1)/2.
```

This is a real cross-axis navigation atlas. It is not prime-exclusive. Under the same fixed four
affine words, all `10/10` primes and all `9/9` odd composites in `[17,53]` have at least one
multi-axis closure. The useful relation is therefore the complete topology consisting of direct
divisor closure, Euclidean words, and affine sheets—not the bare existence of an offset pattern.

The direct controls make the distinction exact:

```text
49/7=[7],   51/3=[17],   55/5=[11].
```

A one-digit continued fraction is immediate closure on that axis. A longer word is continued
coprime navigation, but it is not by itself evidence that the numerator is prime.

## First-person receiver quotient

For a declared finite horizon `H`, observation word `O_t`, and the compatible fiber

```text
F_t(x)={m in H : O_t(m)=O_t(x)},
```

the exact Zeta-weighted prime quotient is

```text
Pi_(sigma,H)(prime | O_t(x))
  = sum_(m in F_t(x), m prime) m^(-sigma)
    / sum_(m in F_t(x)) m^(-sigma).
```

This is uncertainty relative to the receiver's current distinction, not chance inside a fully
known integer. In `H=[17,53]`, progressive nonclosure gives:

| Axes found nondividing | Compatible primes / values | Counting quotient | Exact finite Zeta quotient, `sigma=2` |
|---|---:|---:|---|
| none | `10/37` | `10/37` | `70278180418958397085428747652780609906944000/226055453237386376271684204669698700946732001` |
| `2` | `10/19` | `10/19` | `343155177826945298268695056898342821811250/578320005330857539966007733579509436745651` |
| `2,3` | `10/13` | `10/13` | `23019238522263342841325752420461250/28025652207167332588125665415116581` |
| `2,3,5` | `10/11` | `10/11` | `36830781635621348546121203872738/38008484219696622539722688933819` |
| `2,3,5,7` | `10/10` | `1` | `1` |

The last row closes because every composite at most `53` has a prime factor at most `7`. For the
specific candidate `17`, only `2` and `3` belong to its primality-proof horizon because
`3<=sqrt(17)<5`; the larger prior axes remain lawful navigation receivers but are not needed to
certify `17`.

For the unbounded Zeta law and a finite tested prime-axis set `S`, valuation independence gives

```text
Pr_sigma(v_q(N)=0 for every q in S)=product_(q in S)(1-q^(-sigma)),

Pr_sigma(N is prime | every tested axis remains open)
  = [P(sigma)-sum_(q in S)q^(-sigma)]
    / [zeta(sigma) product_(q in S)(1-q^(-sigma))],
```

where `P(sigma)=sum_(p prime)p^(-sigma)` is the prime-Zeta sum. This is a posterior quotient over
the still-compatible population. It is not a causal probability scalar inside Soma.

## Result

The proposed subject is relevant. `p/q` supplies three coordinated but nonidentical faces:

1. winding plus residue phase in the cyclic axis chart;
2. an exact Euclidean/unimodular rebase word in the rational chart; and
3. the valuation edge `e_p-e_q` with exact relative Zeta mass in the multiplicative chart.

Affine transforms then expose multi-axis sheets made from previously founded primes. The bounded
control shows why the whole relational atlas matters: offset factorization is common to primes and
composites, while direct closure against the proof horizon is decisive. No engine mechanism or RH
claim follows from the measurement. The immediate analytical gain is an exact, data-readable
navigation carrier and a precise first-person Bayesian/Zeta quotient.
