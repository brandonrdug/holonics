import ElementaryHolonics.Millennium.NavierStokesTorusFourier

/-!
# Addressed Fourier triads and their finite skew cancellation

The integer-frequency triangle `p + q + k = 0` is the smallest closed polygon carrying one
quadratic Fourier interaction.  For a fixed advecting mode `p`, incompressibility says
`p · û(p) = 0`; closure then says `q + k = -p`.  Consequently the two coefficient faces obtained
by exchanging the transported and receiving modes cancel exactly.

This is a **finite algebraic carrier**.  It neither defines nor sums the infinite Fourier
convolution of the Navier--Stokes nonlinearity, and it supplies no convergence, regularity, or
continuation estimate for that convolution.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesFourierTriads

open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- An addressed closed triangle in the integer character lattice.  The three fields retain which
mode advects, which mode is transported, and which mode receives the coefficient face. -/
structure AddressedClosedFourierTriad where
  advecting : SpatialFrequency
  transported : SpatialFrequency
  receiver : SpatialFrequency
  closed : advecting + transported + receiver = 0

namespace AddressedClosedFourierTriad

/-- Closing the addressed triangle isolates the two modes opposite the advecting pin. -/
theorem transported_add_receiver_eq_neg_advecting
    (triad : AddressedClosedFourierTriad) :
    triad.transported + triad.receiver = -triad.advecting := by
  apply eq_neg_of_add_eq_zero_right
  simpa only [add_assoc] using triad.closed

/-- Cyclically rotate the address while preserving the same closed frequency triangle. -/
def rotate (triad : AddressedClosedFourierTriad) : AddressedClosedFourierTriad where
  advecting := triad.transported
  transported := triad.receiver
  receiver := triad.advecting
  closed := by
    simpa only [add_assoc, add_comm, add_left_comm] using triad.closed

@[simp]
theorem rotate_advecting (triad : AddressedClosedFourierTriad) :
    triad.rotate.advecting = triad.transported := rfl

@[simp]
theorem rotate_transported (triad : AddressedClosedFourierTriad) :
    triad.rotate.transported = triad.receiver := rfl

@[simp]
theorem rotate_receiver (triad : AddressedClosedFourierTriad) :
    triad.rotate.receiver = triad.advecting := rfl

end AddressedClosedFourierTriad

/-- The integer-frequency embedding is additive before any norm or shell receiver is taken. -/
def complexFrequencyEmbedding : SpatialFrequency →+ ComplexVector where
  toFun := complexFrequencyVector
  map_zero' := by
    ext j
    simp [complexFrequencyVector]
  map_add' p q := by
    ext j
    simp [complexFrequencyVector]

@[simp]
theorem complexFrequencyEmbedding_apply (k : SpatialFrequency) :
    complexFrequencyEmbedding k = complexFrequencyVector k := rfl

/-- The Fourier coefficient of `(û(p) · ∇)û(q)` at the algebraic mode level.  For fixed
frequencies it is bilinear in the two complex mode amplitudes. -/
def complexAdvectiveInteraction
    (_p q : SpatialFrequency) (advectingMode transportedMode : ComplexVector) : ComplexVector :=
  ((2 * (Real.pi : ℂ) * Complex.I) *
      complexDot (complexFrequencyVector q) advectingMode) • transportedMode

/-- The bilinear dot receiver pairs one advective interaction with the remaining triad mode.
This is the coefficient-level face used below; it is not by itself the real, sesquilinear kinetic
energy of a full Fourier field. -/
def triadicEnergyFace
    (p q : SpatialFrequency)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  complexDot (complexAdvectiveInteraction p q advectingMode transportedMode) receiverMode

/-- Closure plus divergence freedom makes the two derivative-frequency factors opposite. -/
theorem exchanged_frequency_dot_cancel
    (triad : AddressedClosedFourierTriad)
    (advectingMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    complexDot (complexFrequencyVector triad.transported) advectingMode +
        complexDot (complexFrequencyVector triad.receiver) advectingMode = 0 := by
  have hfrequency :
      complexFrequencyVector triad.transported +
          complexFrequencyVector triad.receiver =
        -complexFrequencyVector triad.advecting := by
    change complexFrequencyEmbedding triad.transported +
        complexFrequencyEmbedding triad.receiver =
      -complexFrequencyEmbedding triad.advecting
    rw [← map_add complexFrequencyEmbedding]
    rw [triad.transported_add_receiver_eq_neg_advecting]
    exact (map_neg complexFrequencyEmbedding triad.advecting)
  have hdivergence' :
      dotProduct (complexFrequencyVector triad.advecting) advectingMode = 0 :=
    hdivergence
  change
    dotProduct (complexFrequencyVector triad.transported) advectingMode +
        dotProduct (complexFrequencyVector triad.receiver) advectingMode = 0
  rw [← add_dotProduct, hfrequency, neg_dotProduct, hdivergence', neg_zero]

/-- **Exact exchanged-face cancellation for one closed triad.**  Holding the advecting pin fixed,
the `q`-transport/`k`-receiver face and the `k`-transport/`q`-receiver face cancel.  The only
dynamical hypothesis is divergence freedom of the advecting mode. -/
theorem exchanged_triadicEnergyFace_cancel
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode +
        triadicEnergyFace triad.advecting triad.receiver
          advectingMode receiverMode transportedMode = 0 := by
  have hfrequency := exchanged_frequency_dot_cancel triad advectingMode hdivergence
  simp only [triadicEnergyFace, complexAdvectiveInteraction, complexDot, smul_dotProduct,
    smul_eq_mul]
  rw [dotProduct_comm receiverMode transportedMode]
  calc
    ((2 * (Real.pi : ℂ) * Complex.I) *
          dotProduct (complexFrequencyVector triad.transported) advectingMode) *
          dotProduct transportedMode receiverMode +
        ((2 * (Real.pi : ℂ) * Complex.I) *
          dotProduct (complexFrequencyVector triad.receiver) advectingMode) *
          dotProduct transportedMode receiverMode =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (dotProduct (complexFrequencyVector triad.transported) advectingMode +
          dotProduct (complexFrequencyVector triad.receiver) advectingMode) *
        dotProduct transportedMode receiverMode := by ring
    _ = 0 := by
      change (2 * (Real.pi : ℂ) * Complex.I) *
        (complexDot (complexFrequencyVector triad.transported) advectingMode +
          complexDot (complexFrequencyVector triad.receiver) advectingMode) *
        dotProduct transportedMode receiverMode = 0
      rw [hfrequency]
      ring

/-- The three cyclic choices of advecting pin each contribute one exchanged pair.  If all three
mode amplitudes are divergence-free, the six finite faces cancel in three addressed pairs. -/
theorem cyclic_exchanged_triadicEnergyFaces_cancel
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    (triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode +
      triadicEnergyFace triad.advecting triad.receiver
        advectingMode receiverMode transportedMode) +
    (triadicEnergyFace triad.transported triad.receiver
        transportedMode receiverMode advectingMode +
      triadicEnergyFace triad.transported triad.advecting
        transportedMode advectingMode receiverMode) +
    (triadicEnergyFace triad.receiver triad.advecting
        receiverMode advectingMode transportedMode +
      triadicEnergyFace triad.receiver triad.transported
        receiverMode transportedMode advectingMode) = 0 := by
  have hfirst := exchanged_triadicEnergyFace_cancel triad
    advectingMode transportedMode receiverMode hadvecting
  have hsecond :
      triadicEnergyFace triad.transported triad.receiver
          transportedMode receiverMode advectingMode +
        triadicEnergyFace triad.transported triad.advecting
          transportedMode advectingMode receiverMode = 0 := by
    simpa using exchanged_triadicEnergyFace_cancel triad.rotate
      transportedMode receiverMode advectingMode htransported
  have hthird :
      triadicEnergyFace triad.receiver triad.advecting
          receiverMode advectingMode transportedMode +
        triadicEnergyFace triad.receiver triad.transported
          receiverMode transportedMode advectingMode = 0 := by
    simpa using exchanged_triadicEnergyFace_cancel triad.rotate.rotate
      receiverMode advectingMode transportedMode hreceiver
  rw [hfirst, hsecond, hthird]
  simp

/-! ## Frequency parallelograms and finite polygon boundaries -/

/-- Two addressed decompositions of the same output frequency.  This is the coefficient-lattice
parallelogram `p + q = p' + q'`, before any analytic summation over decompositions. -/
structure FrequencyParallelogramComparison where
  firstLeft : SpatialFrequency
  firstRight : SpatialFrequency
  secondLeft : SpatialFrequency
  secondRight : SpatialFrequency
  sameOutput : firstLeft + firstRight = secondLeft + secondRight

/-- Equal output frequency remains equal in the complex derivative-frequency chart. -/
theorem FrequencyParallelogramComparison.complex_diagonal_eq
    (comparison : FrequencyParallelogramComparison) :
    complexFrequencyVector comparison.firstLeft +
        complexFrequencyVector comparison.firstRight =
      complexFrequencyVector comparison.secondLeft +
        complexFrequencyVector comparison.secondRight := by
  change complexFrequencyEmbedding comparison.firstLeft +
      complexFrequencyEmbedding comparison.firstRight =
    complexFrequencyEmbedding comparison.secondLeft +
      complexFrequencyEmbedding comparison.secondRight
  rw [← map_add, ← map_add, comparison.sameOutput]

/-! ## Finite polygon boundary carriers -/

/-- Oriented boundary of a finite frequency polygon.  Repetition and ordering remain present in
the list even though this particular boundary receiver is their additive quotient. -/
def frequencyPolygonBoundary (edges : List SpatialFrequency) : SpatialFrequency := edges.sum

/-- The same finite boundary after embedding the integer lattice in the complex coefficient
chart. -/
def complexFrequencyPolygonBoundary (edges : List SpatialFrequency) : ComplexVector :=
  (edges.map complexFrequencyVector).sum

/-- The complex boundary receiver commutes with the additive frequency embedding. -/
theorem complexFrequencyPolygonBoundary_eq_embedding
    (edges : List SpatialFrequency) :
    complexFrequencyPolygonBoundary edges =
      complexFrequencyVector (frequencyPolygonBoundary edges) := by
  change (edges.map complexFrequencyEmbedding).sum =
    complexFrequencyEmbedding edges.sum
  exact (map_list_sum complexFrequencyEmbedding edges).symm

/-- Concatenating two finite polygons adds their oriented boundaries exactly. -/
theorem frequencyPolygonBoundary_append (left right : List SpatialFrequency) :
    frequencyPolygonBoundary (left ++ right) =
      frequencyPolygonBoundary left + frequencyPolygonBoundary right := by
  simp [frequencyPolygonBoundary]

/-- A closed integer-frequency polygon remains closed in the complex frequency chart. -/
theorem complexFrequencyPolygonBoundary_eq_zero_of_closed
    (edges : List SpatialFrequency)
    (hclosed : frequencyPolygonBoundary edges = 0) :
    complexFrequencyPolygonBoundary edges = 0 := by
  rw [complexFrequencyPolygonBoundary_eq_embedding, hclosed]
  exact map_zero complexFrequencyEmbedding

#print axioms exchanged_frequency_dot_cancel
#print axioms exchanged_triadicEnergyFace_cancel
#print axioms cyclic_exchanged_triadicEnergyFaces_cancel
#print axioms FrequencyParallelogramComparison.complex_diagonal_eq
#print axioms complexFrequencyPolygonBoundary_eq_embedding
#print axioms frequencyPolygonBoundary_append
#print axioms complexFrequencyPolygonBoundary_eq_zero_of_closed

end Soma.Holonics.Millennium.NavierStokesFourierTriads
