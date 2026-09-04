#let seventh-harmonic-tail-series-certificate = (
  key: "lemma:seventh-harmonic-tail-series-certificate",
  kind: [Lemma],
  title: [The seventh harmonic archimedean tail margin is strictly positive],
  status: [Exact rational-series certificate],
  depends: ("theorem:conditioned-effective-tension",),
  claim: [
    Put
    $
      delta_7
      =
      frac(363,140)
      -gamma
      -log(pi log 3)
      -frac(log 3,4)
      -frac(log 2,sqrt(2)).
    $
    Then
    $
      delta_7>frac(1,96)>0.
      quad "(SEVENTH-MODE MARGIN)"
    $
  ],
  proof: [
    Every comparison is made between rational endpoints. For $y>1$, set
    $z=(y-1)/(y+1)$ and use
    $
      log y
      =
      2sum_(k=0)^(N-1)frac(z^(2k+1),2k+1)+R_N,
      quad
      0<R_N<
      frac(2z^(2N+1), (2N+1)(1-z^2)).
    $
    This encloses $log 2$ with $N=32$ and $log 3$ with $N=40$.
    Machin's identity
    $
      pi=16 arctan(1/5)-4 arctan(1/239)
    $
    is enclosed by the alternating arctangent series after respectively
    eighteen and six terms. Adjacent dyadic rationals with denominator
    $2^96$ enclose $sqrt(2)$. At $n=64$, Euler--Maclaurin gives
    $
      H_n-log n-frac(1,2n)+frac(1,12n^2)-frac(1,120n^4)
      <gamma
    $
    and
    $
      gamma
      <
      H_n-log n-frac(1,2n)+frac(1,12n^2)-frac(1,120n^4)
      +frac(1,252n^6).
    $
    Applying the logarithm series for fifty-six terms to the rational
    enclosure of $pi log 3$, then substituting every upper endpoint into the
    subtracted terms, gives by exact integer cross-multiplication
    $delta_7>1/96$.
  ],
  boundary: [
    This lemma certifies the already-derived uniform high-mode margin. It
    does not sign the finite low-mode Schur block, establish the symbolic
    successor law, or by itself prove RH.
  ],
)
