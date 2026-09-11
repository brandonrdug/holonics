import Mathlib

/-!
# A finite enzyme reaction current

This is a declared four-species reaction chart for
`E + S ⇄ ES → E + P`.  The source is built from the stoichiometric columns
and mass-action rates, so the two conserved totals below are derived by
canceling those columns rather than assumed.  A sequence-dependent
conformation enters through an explicit accessibility port; this file does not
silently identify that port with a particular folding or biochemical law.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicComplexParametron

structure ReactionState where
  enzyme : ℝ
  substrate : ℝ
  complex : ℝ
  product : ℝ

structure ReactionRates where
  forward : ℝ
  reverse : ℝ
  catalytic : ℝ

/-- Mass-action rates for binding, unbinding, and catalytic release. -/
def massActionRates (kf kr kc : ℝ) (state : ReactionState) : ReactionRates :=
  { forward := kf * state.enzyme * state.substrate
    reverse := kr * state.complex
    catalytic := kc * state.complex }

/-- Stoichiometric source assembled from the three actual reaction currents. -/
def reactionSource (rates : ReactionRates) : ReactionState :=
  { enzyme := -rates.forward + rates.reverse + rates.catalytic
    substrate := -rates.forward + rates.reverse
    complex := rates.forward - rates.reverse - rates.catalytic
    product := rates.catalytic }

/-- Enzyme total is conserved by the stoichiometric source. -/
theorem enzyme_total_source_conserved (rates : ReactionRates) :
    (reactionSource rates).enzyme + (reactionSource rates).complex = 0 := by
  simp [reactionSource]

/-- Substrate plus bound complex plus product is conserved by the source. -/
theorem substrate_total_source_conserved (rates : ReactionRates) :
    (reactionSource rates).substrate + (reactionSource rates).complex +
        (reactionSource rates).product = 0 := by
  simp [reactionSource]
  ring

/-- The concrete mass-action current and its two conservation identities. -/
def massActionSource (kf kr kc : ℝ) (state : ReactionState) : ReactionState :=
  reactionSource (massActionRates kf kr kc state)

theorem massActionSource_conserves (kf kr kc : ℝ) (state : ReactionState) :
    (massActionSource kf kr kc state).enzyme +
        (massActionSource kf kr kc state).complex = 0 ∧
      (massActionSource kf kr kc state).substrate +
        (massActionSource kf kr kc state).complex +
        (massActionSource kf kr kc state).product = 0 := by
  exact ⟨enzyme_total_source_conserved _, substrate_total_source_conserved _⟩

/-- The caller supplies conformation-dependent accessibility. The exterior FCC ligand source
instantiates it with the actual population of sterically open binding directions. -/
def sequenceAccessibleRates {Config : Type*}
    (kf kr kc : ℝ) (accessibility : Config → ℝ)
    (conformation : ℝ → Config) (state : ReactionState) (time : ℝ) : ReactionRates :=
  massActionRates (kf * accessibility (conformation time)) kr kc state

/-- Accessibility changes the forward current while retaining stoichiometric return. -/
def sequenceReactionSource {Config : Type*}
    (kf kr kc : ℝ) (accessibility : Config → ℝ)
    (conformation : ℝ → Config) (state : ReactionState) (time : ℝ) : ReactionState :=
  reactionSource (sequenceAccessibleRates kf kr kc accessibility conformation state time)

theorem sequenceReactionSource_conserves
    {Config : Type*} (kf kr kc : ℝ) (accessibility : Config → ℝ)
    (conformation : ℝ → Config) (state : ReactionState) (time : ℝ) :
    (sequenceReactionSource kf kr kc accessibility conformation state time).enzyme +
        (sequenceReactionSource kf kr kc accessibility conformation state time).complex = 0 ∧
      (sequenceReactionSource kf kr kc accessibility conformation state time).substrate +
        (sequenceReactionSource kf kr kc accessibility conformation state time).complex +
        (sequenceReactionSource kf kr kc accessibility conformation state time).product = 0 := by
  exact ⟨enzyme_total_source_conserved _, substrate_total_source_conserved _⟩

/-- Nonnegative concentrations and rate constants give nonnegative currents. -/
theorem massActionRates_nonneg
    (kf kr kc : ℝ) (state : ReactionState)
    (hkf : 0 ≤ kf) (hkr : 0 ≤ kr) (hkc : 0 ≤ kc)
    (hE : 0 ≤ state.enzyme) (hS : 0 ≤ state.substrate)
    (hES : 0 ≤ state.complex) :
    0 ≤ (massActionRates kf kr kc state).forward ∧
      0 ≤ (massActionRates kf kr kc state).reverse ∧
      0 ≤ (massActionRates kf kr kc state).catalytic := by
  simp only [massActionRates]
  exact ⟨mul_nonneg (mul_nonneg hkf hE) hS,
    mul_nonneg hkr hES, mul_nonneg hkc hES⟩

/-! ## Joint fold/accessibility witness -/

abbrev JointFoldPopulation := (ℝ × ℝ) × (ℝ × ℝ)

/-- Binding flux sees free population together with its fold-specific access. -/
def bindingFlux (a b : ℝ) (population : JointFoldPopulation) : ℝ :=
  a * population.1.1 + b * population.2.1

def foldMarginal (population : JointFoldPopulation) : ℝ × ℝ :=
  (population.1.1 + population.1.2, population.2.1 + population.2.2)

def freeTotal (population : JointFoldPopulation) : ℝ :=
  population.1.1 + population.2.1

def jointPopulationOne : JointFoldPopulation := ((1 / 2, 0), (0, 1 / 2))
def jointPopulationTwo : JointFoldPopulation := ((0, 1 / 2), (1 / 2, 0))

theorem joint_population_same_fold_marginals :
    foldMarginal jointPopulationOne = foldMarginal jointPopulationTwo := by
  norm_num [foldMarginal, jointPopulationOne, jointPopulationTwo]

theorem joint_population_same_free_total :
    freeTotal jointPopulationOne = freeTotal jointPopulationTwo := by
  norm_num [freeTotal, jointPopulationOne, jointPopulationTwo]

theorem joint_population_binding_fluxes :
    bindingFlux a b jointPopulationOne = a / 2 ∧
      bindingFlux a b jointPopulationTwo = b / 2 := by
  constructor <;> norm_num [bindingFlux, jointPopulationOne, jointPopulationTwo]
  <;> ring

theorem joint_population_binding_flux_difference :
    bindingFlux a b jointPopulationTwo - bindingFlux a b jointPopulationOne =
      (b - a) / 2 := by
  norm_num [bindingFlux, jointPopulationOne, jointPopulationTwo]
  ring

theorem joint_population_binding_flux_ne
    {a b : ℝ} (hab : a ≠ b) :
    bindingFlux a b jointPopulationOne ≠ bindingFlux a b jointPopulationTwo := by
  rcases joint_population_binding_fluxes (a := a) (b := b) with ⟨hone, htwo⟩
  rw [hone, htwo]
  intro h
  apply hab
  linarith

/-- Reverse and catalytic returns can share body change while emitting different labels. -/
theorem reactionSource_labeled_emission_distinguishes :
    let reverseOnly : ReactionRates := { forward := 0, reverse := 1, catalytic := 0 }
    let catalyticOnly : ReactionRates := { forward := 0, reverse := 0, catalytic := 1 }
    (reactionSource reverseOnly).enzyme = (reactionSource catalyticOnly).enzyme ∧
      (reactionSource reverseOnly).complex = (reactionSource catalyticOnly).complex ∧
      (reactionSource reverseOnly).substrate = 1 ∧
      (reactionSource reverseOnly).product = 0 ∧
      (reactionSource catalyticOnly).substrate = 0 ∧
      (reactionSource catalyticOnly).product = 1 ∧
      (reactionSource reverseOnly).substrate ≠
        (reactionSource catalyticOnly).substrate := by
  norm_num [reactionSource]

end Soma.Holonics.Millennium.HolonicComplexParametron
