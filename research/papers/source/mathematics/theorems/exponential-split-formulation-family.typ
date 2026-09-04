#let exponential-split-formulation-family = (
  key: "theorem:exponential-split-formulation-family",
  kind: [Theorem],
  title: [The entire two-stage formulation family for e],
  status: [Exact elementary derivation],
  depends: (
    "definition:formulation-span-atlas",
    "lemma:formulation-span-composition",
  ),
  claim: [
    On the complex parameter base $B_e=CC$ define
    $
      E(t)=exp(t)exp(1-t)
      quad "and" quad
      tau_e(t)=1-t.
    $
    Then
    $
      E(t)=e
      quad "for every" t in CC,
      quad
      tau_e^2=id,
    $
    and $tau_e$ supplies an exact rechart which exchanges the two exponential
    stages. Its unique fixed parameter is $t=1/2$. The complete two-stage
    receiver
    $
      q_"stage"(t)=(exp(t),exp(1-t))
    $
    varies with $t$, while multiplication is the noninjective value receiver
    which returns $e$. The parameter involution has only the fixed point
    $1/2$, whereas the quotient stage values coincide at
    $
      t=1/2+pi i k,
      quad k in ZZ.
    $
  ],
  proof: [
    The exponential group law gives
    $exp(t)exp(1-t)=exp(1)=e$. Substitution gives
    $tau_e(tau_e(t))=t$, and its fixed-point equation is
    $t=1-t$. Swapping the ordered stages does not change their product because
    complex multiplication is commutative. The two stage values agree exactly
    when $exp(2t-1)=1$, hence at $t=1/2+pi i k$. Thus periodic receiver
    isotropy is larger than the fixed locus of the parameter rechart.
  ],
  boundary: [
    This family is entire and has no finite analytic discriminant. Its
    $2 pi i$ receiver periodicity must not be confused with equality of
    parameter occurrences. A
    particular numerical series, continued fraction, ODE solver, or hardware
    enactment may have its own convergence, truncation, and cost seams; those
    belong to the corresponding decorated formulation family rather than to
    the exponential identity alone.
  ],
)
