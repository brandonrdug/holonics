import ElementaryHolonics.Millennium.FamilyTunnellHopfSourceCensus

/-!
# The modulo-four theta census of the quaternionic Hopf source

The norm-`p` Hopf source is cut out of the four-square shell by one exact
modulo-four winding condition.  This file opens that condition on its complete
finite residue body.  Opposite odd residue orientations are folded only through
the coordinate-negation equivalence which will be used by the theta receiver.

The resulting residue polynomial factors as

`8 B (A+C) (A²+C²+2B²)`.

The unrestricted odd four-square body factors as

`8 B (A+C) ((A+C)²+4B²)`.

Consequently the returned difference is exactly

`2 source - ambient = 8 B (A+C) (A-C)²`.

This is a finite 256-cell theorem.  It neither assumes a theta identity nor a
modular-form dimension argument; those enter only when the residue variables
are evaluated at their addressed square streams.
-/

namespace Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus

set_option maxRecDepth 100000

abbrev QuarterResidue := Fin 4
abbrev FoldedQuarterResidue := Fin 3
abbrev ResidueQuaternion :=
  QuarterResidue × QuarterResidue × QuarterResidue × QuarterResidue

/-- Residues `1` and `3` are opposite orientations of the same odd square
stream; residues `0` and `2` remain distinct. -/
def foldQuarterResidue : QuarterResidue → FoldedQuarterResidue
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 1

/-- The four-square norm parity of a residue quaternion. -/
def residueNormOdd (q : ResidueQuaternion) : Prop :=
  (q.1.val ^ 2 + q.2.1.val ^ 2 + q.2.2.1.val ^ 2 + q.2.2.2.val ^ 2) % 2 = 1

instance : DecidablePred residueNormOdd := fun q => by
  unfold residueNormOdd
  infer_instance

/-- The Hopf transverse difference, computed on the exact modulo-four
receiver. -/
def residueWindingDifference (q : ResidueQuaternion) : ZMod 4 :=
  let a : ZMod 4 := q.1.val
  let b : ZMod 4 := q.2.1.val
  let c : ZMod 4 := q.2.2.1.val
  let d : ZMod 4 := q.2.2.2.val
  a * d + b * c - (b * d - a * c)

def residueWindingCloses (q : ResidueQuaternion) : Prop :=
  residueWindingDifference q = 0

instance : DecidablePred residueWindingCloses := fun q => by
  unfold residueWindingCloses
  infer_instance

/-- Exponents of the three folded residue streams.  Every cell has total
degree four, hence each exponent lies in `Fin 5`. -/
abbrev ResidueExponent := Fin 5 × Fin 5 × Fin 5

/-- A bounded exact coefficient body.  This is the degree-four fragment of
`ℤ[A,B,C]`, represented directly so its complete finite census is executable
by Lean's kernel compiler rather than hidden behind a quotient presentation. -/
abbrev ResiduePolynomial := ResidueExponent → ℤ

private def indicator (P : Prop) [Decidable P] : Nat := if P then 1 else 0

/-- Multiplicity of one folded stream in an addressed residue cell. -/
def foldedMultiplicity (i : FoldedQuarterResidue) (q : ResidueQuaternion) : Fin 5 :=
  ⟨indicator (foldQuarterResidue q.1 = i) +
      indicator (foldQuarterResidue q.2.1 = i) +
      indicator (foldQuarterResidue q.2.2.1 = i) +
      indicator (foldQuarterResidue q.2.2.2 = i), by
    unfold indicator
    split_ifs <;> omega⟩

/-- The folded exponent carried by one addressed residue cell. -/
def foldedResidueExponent (q : ResidueQuaternion) : ResidueExponent :=
  (foldedMultiplicity 0 q, foldedMultiplicity 1 q, foldedMultiplicity 2 q)

/-- The complete folded residue polynomial of the admitted Hopf source. -/
def hopfSourceResiduePolynomial : ResiduePolynomial := fun e =>
  ∑ q : ResidueQuaternion,
    if residueNormOdd q ∧ residueWindingCloses q ∧ foldedResidueExponent q = e
      then 1 else 0

/-- The complete folded residue polynomial of the ambient odd four-square
body. -/
def oddFourSquareResiduePolynomial : ResiduePolynomial := fun e =>
  ∑ q : ResidueQuaternion,
    if residueNormOdd q ∧ foldedResidueExponent q = e then 1 else 0

def residueZero : ResiduePolynomial := fun _ => 0

def residueAdd (P Q : ResiduePolynomial) : ResiduePolynomial := fun e => P e + Q e

def residueSub (P Q : ResiduePolynomial) : ResiduePolynomial := fun e => P e - Q e

def residueScale (z : ℤ) (P : ResiduePolynomial) : ResiduePolynomial := fun e => z * P e

/-- Exact degree-four convolution.  All factorisations below have total degree
at most four, so no admitted coefficient is truncated. -/
def residueProduct (P Q : ResiduePolynomial) : ResiduePolynomial := fun e =>
  ∑ i : ResidueExponent, ∑ j : ResidueExponent,
    if i.1.val + j.1.val = e.1.val ∧
        i.2.1.val + j.2.1.val = e.2.1.val ∧
        i.2.2.val + j.2.2.val = e.2.2.val
      then P i * Q j else 0

def residueVariable (i : FoldedQuarterResidue) : ResiduePolynomial := fun e =>
  if e = (if i = 0 then (1, 0, 0) else if i = 1 then (0, 1, 0) else (0, 0, 1))
    then 1 else 0

local notation "A" => residueVariable 0
local notation "B" => residueVariable 1
local notation "C" => residueVariable 2
local infixl:65 " +ᵣ " => residueAdd
local infixl:65 " -ᵣ " => residueSub
local infixl:70 " *ᵣ " => residueProduct
local notation z " •ᵣ " P => residueScale z P

/-- The six nonzero coefficients of
`8 B (A+C) (A²+C²+2B²)`.  Storing the sparse body is part of the exact
construction: the receiver need not recompute millions of zero convolution
cells in order to recover the same polynomial. -/
def sourceFactorizedPolynomial : ResiduePolynomial := fun e =>
  if e = ((3 : Fin 5), (1 : Fin 5), (0 : Fin 5)) then 8
  else if e = ((1 : Fin 5), (1 : Fin 5), (2 : Fin 5)) then 8
  else if e = ((1 : Fin 5), (3 : Fin 5), (0 : Fin 5)) then 16
  else if e = ((2 : Fin 5), (1 : Fin 5), (1 : Fin 5)) then 8
  else if e = ((0 : Fin 5), (1 : Fin 5), (3 : Fin 5)) then 8
  else if e = ((0 : Fin 5), (3 : Fin 5), (1 : Fin 5)) then 16
  else 0

/-- The six nonzero coefficients of
`8 B (A+C) ((A+C)²+4B²)`. -/
def ambientFactorizedPolynomial : ResiduePolynomial := fun e =>
  if e = ((3 : Fin 5), (1 : Fin 5), (0 : Fin 5)) then 8
  else if e = ((2 : Fin 5), (1 : Fin 5), (1 : Fin 5)) then 24
  else if e = ((1 : Fin 5), (1 : Fin 5), (2 : Fin 5)) then 24
  else if e = ((0 : Fin 5), (1 : Fin 5), (3 : Fin 5)) then 8
  else if e = ((1 : Fin 5), (3 : Fin 5), (0 : Fin 5)) then 32
  else if e = ((0 : Fin 5), (3 : Fin 5), (1 : Fin 5)) then 32
  else 0

/-- The four nonzero coefficients of `8 B (A+C) (A-C)²`. -/
def differenceFactorizedPolynomial : ResiduePolynomial := fun e =>
  if e = ((3 : Fin 5), (1 : Fin 5), (0 : Fin 5)) then 8
  else if e = ((2 : Fin 5), (1 : Fin 5), (1 : Fin 5)) then -8
  else if e = ((1 : Fin 5), (1 : Fin 5), (2 : Fin 5)) then -8
  else if e = ((0 : Fin 5), (1 : Fin 5), (3 : Fin 5)) then 8
  else 0

private theorem sourceCoefficientCensus :
    ∀ e : ResidueExponent,
      hopfSourceResiduePolynomial e = sourceFactorizedPolynomial e := by
  decide

private theorem ambientCoefficientCensus :
    ∀ e : ResidueExponent,
      oddFourSquareResiduePolynomial e = ambientFactorizedPolynomial e := by
  decide

/-- **THE COMPLETE MODULO-FOUR HOPF BODY FACTORS.** -/
theorem hopfSourceResiduePolynomial_eq :
    hopfSourceResiduePolynomial = sourceFactorizedPolynomial := by
  funext e
  exact sourceCoefficientCensus e

/-- The same finite census before imposing the winding seam. -/
theorem oddFourSquareResiduePolynomial_eq :
    oddFourSquareResiduePolynomial = ambientFactorizedPolynomial := by
  funext e
  exact ambientCoefficientCensus e

/-- **THE HECKE CURRENT IS THE RETURNED RESIDUE DIFFERENCE.**  Doubling the
admitted population and subtracting the ambient one leaves the square of the
orientation difference `A-C`. -/
theorem hopfResidueDifference_eq :
    residueSub (residueScale 2 hopfSourceResiduePolynomial)
        oddFourSquareResiduePolynomial =
      differenceFactorizedPolynomial := by
  funext e
  have h : ∀ e : ResidueExponent,
      residueSub (residueScale 2 sourceFactorizedPolynomial)
          ambientFactorizedPolynomial e =
        differenceFactorizedPolynomial e := by
    decide
  rw [hopfSourceResiduePolynomial_eq, oddFourSquareResiduePolynomial_eq]
  exact h e

#print axioms hopfSourceResiduePolynomial_eq
#print axioms oddFourSquareResiduePolynomial_eq
#print axioms hopfResidueDifference_eq

end Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
