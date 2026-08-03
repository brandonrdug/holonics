#let graded-arithmetic-accessibility-current = (
  key: "definition:graded-arithmetic-accessibility-current",
  kind: [Definition],
  title: [Graded arithmetic accessibility current],
  status: [Project definition; exact chain-valued refinement of a finite arithmetic census],
  depends: (
    "definition:receiver-configuration-calculus",
    "definition:prime-valuation-atlas",
  ),
  claim: [
    Let $C_e$ be an oriented locally finite chain of arithmetic occurrences
    in the accessible configuration $Omega_e$.  Let $P_e$ be its declared
    finite prime aperture and let
    $
      nu_e:C_e arrow.r NN^(P_e)
    $
    assign the exact prime-valuation address of every arithmetic occurrence
    on which that address is defined.  For
    $alpha in NN^(P_e)$, write
    $
      C_(alpha,e)
      =
      C_e|_(Omega_e inter nu_e^(-1)(alpha)).
    $
    The *graded arithmetic accessibility current* is
    $
      frak(A)_e(bold(X))
      =
      sum_(alpha in NN^(P_e))
      [C_(alpha,e)] bold(X)^alpha,
      quad
      bold(X)^alpha=product_(p in P_e) X_p^(alpha_p).
      quad "(ACCESSIBILITY CURRENT)"
    $
    Its coefficients are chains or signed occurrence populations, not
    scalar probabilities.  Orientation, multiplicity, boundary, and source
    incidence remain available before any augmentation.

    Total valuation degree gives
    $
      frak(A)_e
      =
      sum_(d>=0) frak(A)_e^((d)),
      quad
      frak(A)_e^((d))
      =
      sum_(abs(alpha)_1=d) [C_(alpha,e)] bold(X)^alpha.
    $
    Degree one contains the primitive integer-prime axes $X_p$.  Degree two
    separates the two nonidentical faces
    $
      X_p^2
      quad "and" quad
      X_p X_q
      quad (p != q),
    $
    so prime squares and distinct-prime semiprimes are not collapsed.

    A declared augmentation
    $
      epsilon:C_bullet(Omega_e;ZZ) arrow.r ZZ
    $
    may later return signed cardinality, mass, or another exact census:
    $
      Z_e(bold(X))=epsilon(frak(A)_e(bold(X))).
    $
    That quotient is a receiver of the current.  It is not the current's
    identity.
  ],
  proof: none,
  boundary: [
    Integer valuation is one lawful decoration of a general configuration,
    not a universal taxonomy.  The prime aperture may grow, and an occurrence
    outside it retains an unresolved valuation residual rather than being
    assigned a false zero coordinate.  If the arithmetic objects live in a
    ring other than the positive integers, its units and prime species must
    be declared anew.  Infinite sums require a topology or formal-series
    interpretation; every bounded cell in this definition is exact.
  ],
)
