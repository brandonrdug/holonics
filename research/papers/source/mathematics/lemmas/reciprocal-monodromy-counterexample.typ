#let reciprocal-monodromy-counterexample = (
  key: "lemma:reciprocal-monodromy-counterexample",
  kind: [Lemma],
  title: [Reciprocal monodromy does not force unit modulus],
  status: [Exact two-dimensional counterexample; standard figure-eight homological monodromy],
  depends: ("lemma:critical-seam-conjugacy",),
  claim: [
    Let
    $
      M=mat(2,1;1,1),
      quad
      Omega=mat(0,1;-1,0).
    $
    Then
    $
      M^T Omega M=Omega,
    $
    so $M$ preserves the oriented symplectic pairing. Its characteristic
    polynomial and eigenvalues are
    $
      det(t I-M)=t^2-3t+1,
      quad
      lambda_(plus.minus)=(3 plus.minus sqrt(5))/2.
    $
    Hence
    $
      lambda_+ lambda_-=1,
      quad
      lambda_+>1,
      quad
      0<lambda_-<1.
    $
    The return therefore has exact reciprocal symmetry while neither
    eigenvalue lies on the unit circle.

    The matrix is a homological monodromy representative for the fibered
    figure-eight knot, and its characteristic polynomial is the knot's
    Alexander polynomial up to multiplication by a unit and the usual choice
    of sign.
  ],
  proof: [
    Direct multiplication gives $M^T Omega M=Omega$. The determinant
    expansion gives $t^2-3t+1$, whose quadratic roots are the displayed
    reciprocal pair. Since $sqrt(5)>1$, one root is greater than one and the
    other is its positive reciprocal.
  ],
  boundary: [
    A symplectic or reciprocal return preserves oriented incidence, not a
    positive Hermitian norm. This is the exact finite-dimensional reason that
    the completed reflection $s mapsto 1-s$ cannot by itself imply RH.
    Forcing unit modulus requires an independently positive metric preserved
    by the return, not another reciprocal presentation.
  ],
)
