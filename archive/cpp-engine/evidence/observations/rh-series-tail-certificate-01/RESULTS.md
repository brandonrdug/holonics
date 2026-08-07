# RH SERIES-DERIVED TAIL CERTIFICATE 01

**Date:** 2026-07-25  
**Grade:** EXACT RATIONAL SERIES CERTIFICATE / NO FLOATING POINT /
SEVENTH-MODE HIGH TAIL POSITIVE / LOW FINITE SCHUR BLOCK OPEN / RH OPEN

## Certified statement

\[
\delta_7
=
\frac{363}{140}
-\gamma
-\log(\pi\log3)
-\frac{\log3}{4}
-\frac{\log2}{\sqrt2}
>
\frac1{96}
>0.
\]

The verifier uses only `fractions.Fraction`, integer square root, finite
series, and rational remainder bounds:

- the atanh series for \(\log2\) and \(\log3\);
- Machin's arctangent identity for \(\pi\);
- adjacent dyadic bounds for \(\sqrt2\);
- Euler--Maclaurin at \(n=64\) for \(\gamma\); and
- another atanh series for \(\log(\pi\log3)\).

No decimal approximation participates in the sign.

## Reproduction

```sh
python3 src/soma/observations/rh-series-tail-certificate-01/verify.py
```

Expected result:

```text
all_endpoints_are_rational = True
all_intervals_are_ordered = True
delta_7_lower_endpoint_is_positive = True
delta_7_is_greater_than_1_over_96 = True
```

This certifies the high-mode carrier in the existing Legendre reduction. It
does not decide the finite low-mode Schur block.

