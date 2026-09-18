import ElementaryHolonics.Foundation.AperturedGradedComplex
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.Nodup

/-!
# What intake preserves: exact codeword decoding, outward projection, and the environment index

[definition] This file states the law behind
`docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md` item **B2**: what a library intake
of an exterior physical occurrence actually preserves, and what it refuses to found.

Three things are stated, in this order.

1. **Decoding an exterior codeword is exact and total on finite words.** A stored IEEE-754 word is
   read as three integer fields and its value is a dyadic rational; `decode` returns `some` on
   exactly the finite words and returns the word's *own* value, never a rounding of it. Widening
   the format cannot lose a value: the dyadic grid of a wider significand contains the narrower
   one's, which is why admitting `<f4` beside `<f2` strictly improves what intake represents.
2. **An outward projection never flips a decision.** A written decimal token's enclosure is its own
   last place; a projection onto a coarser grid floors the lower endpoint and ceils the upper, so
   the projected interval contains the source one. Containment can turn a decided contact
   `openContact` and can never turn `inside` into `outside` or the reverse.
3. **An occurrence cannot be founded without its environment index.** The uncertainty array's index
   type *is* the environment's token population, so an array without that population is not a
   well-typed occurrence at all; and the partial founding from an exterior presentation returns
   `none` exactly when the environment is absent. The addressed pair population is then exactly the
   array, and a reading is directional: `(i,j)` and `(j,i)` are separate and are never symmetrized.

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-engine/src/physical_intake.rs` with its
`mmcif` and `numpy` submodules, which names this file and every declaration below. The
correspondence, both directions:

| Lean | Rust |
|---|---|
| `FloatFormat`, `binary16`, `binary32`, `binary64` | `physical_intake/numpy.rs::UncertaintyWordFormat` |
| `Codeword`, `Codeword.value`, `Codeword.Finite` | `physical_intake/numpy.rs::ExactWord`; `exact_value.rs::ieee754::BinaryFloatDatum` |
| `decode`, `decode_total_on_finite`, `decode_exact_on_finite` | `physical_intake/numpy.rs::ExactWord::decode` returning `Ok` with the exact value |
| `decode_refuses_nonfinite` | `physical_intake.rs::IntakeRefusal::NonFiniteUncertaintyWord` |
| `BoundedDyadic`, `wider_format_carries_every_value`, `binary32_strictly_refines_binary16` | admitting `<f4` and `<f8` beside `<f2` in `UncertaintyWordFormat::ADMITTED` |
| `DecimalToken`, `DecimalToken.enclosure`, `enclosure_contains_centre` | `physical_intake/mmcif.rs::DecimalToken::{exact_centre, source_enclosure}` |
| `projectOutward`, `projection_contains_source` | `physical_intake/mmcif.rs::DecimalToken::{projected_wire, projected_enclosure}` |
| `widening_never_flips_a_decision`, `decided_under_projection_is_decided_at_source` | the coordinate-exactness discipline stated in `physical_intake/mmcif.rs`'s header |
| `TargetEcology`, `DesignLineage`, `TokenAddress`, `EnvironmentIndex` | `physical_intake.rs::{TargetEcology, DesignLineage, TokenAddress, EnvironmentIndex}` |
| `Occurrence`, whose `word` is indexed by `environment.tokens` | `physical_intake.rs::AddressedUncertainty`, whose only constructor takes the index by value |
| `found`, `found_none_of_environment_absent`, `no_occurrence_without_environment` | `physical_intake.rs::AddressedUncertainty::found`; `EnvironmentIndex::from_numpy_source` refusing with `EnvironmentArraysAbsent` |
| `found_environment` | `AddressedUncertainty::environment` is total |
| `addressedPairs`, `addressed_pair_population` | `AddressedUncertainty::pair_uncertainty`, whose cardinality is `|left| · |right|` |
| `token_index_unique`, `reading_total_on_addressed_pairs` | `EnvironmentIndex::token_index` and the `addresses_are_distinct` check |
| `reading_is_directional` | `PairUncertainty::{row_given_column, column_given_row}` retained separately |
| `intake_contract` | the whole `physical_intake` module contract |

## The measured fact this states the law for

[established-bounded; measured] The M5 uncertainty wire carries eleven arrays: `pae` and the ten
that name the environment and lineage it was produced under. An external predictor emits only
`pae` — the Boltz-2 run at `.local/boltz-smoke/out/boltz_results_test/predictions/test/` writes a
`.npz` with that one member and nothing else — so the adapter's real work is requiring the
environment index. `found` returns `none` there until a caller declares one, and that refusal is
`found_none_of_environment_absent`.
-/

namespace Soma.Holonics.Foundation.ExteriorIntake

open Soma.Holonics.Foundation.AperturedGradedComplex

/-! ## 1. The exterior codeword and its exact decoding -/

/-- [definition] An IEEE-754 binary interchange format, as the two field widths that determine it.

Rust counterpart: `crates/holonic-engine/src/physical_intake/numpy.rs::UncertaintyWordFormat`. -/
structure FloatFormat where
  /-- Stored significand bits: `10`, `23`, `52` for `binary16`, `binary32`, `binary64`. -/
  significandBits : ℕ
  /-- Exponent field bits: `5`, `8`, `11`. -/
  exponentBits : ℕ
  deriving DecidableEq, Repr

/-- [definition] `<f2`. -/
def binary16 : FloatFormat := ⟨10, 5⟩

/-- [definition] `<f4`. -/
def binary32 : FloatFormat := ⟨23, 8⟩

/-- [definition] `<f8`. -/
def binary64 : FloatFormat := ⟨52, 11⟩

/-- [definition] The format's exponent bias. -/
def FloatFormat.bias (f : FloatFormat) : ℤ := 2 ^ (f.exponentBits - 1) - 1

/-- [definition] One stored word, read as the three integer fields IEEE-754 defines. No float
appears: the fields are natural numbers and a sign bit.

Rust counterpart: the `bits` field of `physical_intake/numpy.rs::ExactWord`, decoded through
`exact_value.rs::ieee754::decode_bits`. -/
structure Codeword (f : FloatFormat) where
  /-- The sign bit, retained separately from the magnitude. -/
  negative : Bool
  /-- The stored exponent field. -/
  rawExponent : ℕ
  /-- The stored fraction field. -/
  fraction : ℕ
  /-- The exponent field fits its width. -/
  rawExponent_lt : rawExponent < 2 ^ f.exponentBits
  /-- The fraction field fits its width. -/
  fraction_lt : fraction < 2 ^ f.significandBits

namespace Codeword

variable {f : FloatFormat}

/-- [definition] The unsigned integer significand, with a normal value's hidden leading one
restored. -/
def significand (w : Codeword f) : ℕ :=
  if w.rawExponent = 0 then w.fraction else 2 ^ f.significandBits + w.fraction

/-- [definition] `value = ± significand · 2 ^ ulpExponent`, and `2 ^ ulpExponent` is one unit in
the last place. -/
def ulpExponent (w : Codeword f) : ℤ :=
  (if w.rawExponent = 0 then 1 else (w.rawExponent : ℤ)) - f.bias - (f.significandBits : ℤ)

/-- [definition] The exact value. This is not an approximation of the word; it **is** the word.

Rust counterpart: `physical_intake/numpy.rs::ExactWord.value`. -/
def value (w : Codeword f) : ℚ :=
  (if w.negative then (-1 : ℚ) else 1) * (w.significand : ℚ) * (2 : ℚ) ^ w.ulpExponent

/-- [definition] A word is finite when its exponent field is not all ones. The all-ones field is
an infinity or a NaN and is a value of no format this intake admits. -/
def Finite (w : Codeword f) : Prop := w.rawExponent + 1 < 2 ^ f.exponentBits

instance (w : Codeword f) : Decidable w.Finite := by
  unfold Finite; infer_instance

/-- [proved-derived; formal-checked] The significand is bounded by `2 ^ (significandBits + 1)`,
which is what puts the value on the format's own dyadic grid. -/
theorem significand_lt (w : Codeword f) : w.significand < 2 ^ (f.significandBits + 1) := by
  have hf := w.fraction_lt
  have hpow : (2 : ℕ) ^ (f.significandBits + 1) = 2 ^ f.significandBits * 2 := pow_succ 2 _
  unfold significand
  split
  · omega
  · omega

end Codeword

/-- [definition] Decoding one exterior codeword. A finite word returns its exact value; a
non-finite word returns nothing at all, and the refusal names it.

Rust counterpart: `physical_intake/numpy.rs::ExactWord::decode`, whose `Err` arm is
`physical_intake.rs::IntakeRefusal::NonFiniteUncertaintyWord`. -/
def decode {f : FloatFormat} (w : Codeword f) : Option ℚ :=
  if w.Finite then some w.value else none

/-- [proved-derived; formal-checked] **Decoding is total on finite words.** -/
theorem decode_total_on_finite {f : FloatFormat} (w : Codeword f) (h : w.Finite) :
    (decode w).isSome := by
  simp [decode, h]

/-- [proved-derived; formal-checked] **Decoding is exact.** What comes back is the codeword's own
value, not a rounding of it and not an enclosure of it. -/
theorem decode_exact_on_finite {f : FloatFormat} (w : Codeword f) (h : w.Finite) :
    decode w = some w.value := by
  simp [decode, h]

/-- [proved-derived; formal-checked] A non-finite word decodes to nothing; nothing is invented for
it. -/
theorem decode_refuses_nonfinite {f : FloatFormat} (w : Codeword f) (h : ¬ w.Finite) :
    decode w = none := by
  simp [decode, h]

/-- [proved-derived; formal-checked] The two arms exhaust the words: `decode` is defined on every
codeword and its `isSome` is exactly finiteness. -/
theorem decode_isSome_iff {f : FloatFormat} (w : Codeword f) :
    (decode w).isSome ↔ w.Finite := by
  by_cases h : w.Finite <;> simp [decode, h]

/-! ### Widening the format cannot lose a value -/

/-- [definition] A dyadic rational carried on a declared significand width: the value grid a
format of that width has. -/
structure BoundedDyadic (bits : ℕ) where
  /-- The sign. -/
  negative : Bool
  /-- The unsigned significand. -/
  significand : ℕ
  /-- The exponent of one unit in the last place. -/
  ulpExponent : ℤ
  /-- The significand fits the declared width. -/
  significand_lt : significand < 2 ^ (bits + 1)

/-- [definition] The exact value of a bounded dyadic. -/
def BoundedDyadic.value {bits : ℕ} (d : BoundedDyadic bits) : ℚ :=
  (if d.negative then (-1 : ℚ) else 1) * (d.significand : ℚ) * (2 : ℚ) ^ d.ulpExponent

/-- [definition] Every codeword sits on its format's own dyadic grid. -/
def Codeword.toBoundedDyadic {f : FloatFormat} (w : Codeword f) :
    BoundedDyadic f.significandBits :=
  ⟨w.negative, w.significand, w.ulpExponent, w.significand_lt⟩

/-- [proved-derived; formal-checked] And the grid carries the codeword's value unchanged. -/
theorem Codeword.toBoundedDyadic_value {f : FloatFormat} (w : Codeword f) :
    w.toBoundedDyadic.value = w.value := rfl

/-- [proved-derived; formal-checked] **A wider significand carries every value of a narrower one.**
Scaling the significand by `2 ^ (bits' - bits)` and lowering the ulp exponent by the same amount is
an identity on the value, and the scaled significand still fits the wider width.

This is why `physical_intake/numpy.rs` admits `<f4` and `<f8` beside `<f2`: widening the exterior
wire strictly enlarges the representable set and degrades nothing. -/
theorem wider_format_carries_every_value {bits bits' : ℕ} (h : bits ≤ bits')
    (d : BoundedDyadic bits) : ∃ e : BoundedDyadic bits', e.value = d.value := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨⟨d.negative, d.significand * 2 ^ k, d.ulpExponent - (k : ℤ), ?_⟩, ?_⟩
  · have hk : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
    calc d.significand * 2 ^ k < 2 ^ (bits + 1) * 2 ^ k :=
          mul_lt_mul_of_pos_right d.significand_lt hk
      _ = 2 ^ (bits + k + 1) := by rw [← pow_add]; congr 1; omega
  · have h2 : (2 : ℚ) ≠ 0 := by norm_num
    have hk : ((2 : ℚ) ^ k) ≠ 0 := by positivity
    simp only [BoundedDyadic.value, zpow_sub₀ h2, zpow_natCast]
    push_cast
    field_simp

/-- [proved-derived; formal-checked] `binary32` is strictly finer than `binary16`, and `binary64`
strictly finer than `binary32`. -/
theorem binary32_strictly_refines_binary16 :
    binary16.significandBits < binary32.significandBits ∧
      binary32.significandBits < binary64.significandBits := by
  constructor <;> decide

/-! ## 2. The written decimal token, its enclosure, and outward projection -/

/-- [definition] One written decimal coordinate token: the integer significand and the number of
decimal places the source declared.

Rust counterpart: `crates/holonic-engine/src/physical_intake/mmcif.rs::DecimalToken`. -/
structure DecimalToken where
  /-- The token with its decimal point removed. -/
  significand : ℤ
  /-- How many decimal places the token declares. -/
  decimalPlaces : ℕ
  deriving DecidableEq, Repr

namespace DecimalToken

/-- [definition] `10 ^ decimalPlaces`, the token's own denominator. -/
def denominator (t : DecimalToken) : ℚ := (10 : ℚ) ^ t.decimalPlaces

theorem denominator_pos (t : DecimalToken) : 0 < t.denominator := by
  unfold denominator; positivity

/-- [definition] The exact rational the token names. -/
def centre (t : DecimalToken) : ℚ := (t.significand : ℚ) / t.denominator

/-- [definition] The source enclosure: one complete last-place unit outward on each side.

Rust counterpart: `mmcif.rs::DecimalToken::source_enclosure`. -/
def enclosure (t : DecimalToken) : ExactInterval ℚ where
  lower := ((t.significand : ℚ) - 1) / t.denominator
  upper := ((t.significand : ℚ) + 1) / t.denominator
  ordered := by
    have hpos := t.denominator_pos
    rw [div_le_div_iff_of_pos_right hpos]
    linarith

/-- [proved-derived; formal-checked] The enclosure contains the centre. -/
theorem enclosure_contains_centre (t : DecimalToken) :
    (t.enclosure).lower ≤ t.centre ∧ t.centre ≤ (t.enclosure).upper := by
  have hpos := t.denominator_pos
  constructor
  · rw [enclosure, centre, div_le_div_iff_of_pos_right hpos]
    linarith
  · rw [enclosure, centre, div_le_div_iff_of_pos_right hpos]
    linarith

end DecimalToken

/-- [definition] One interval contains another. -/
def Contains (outer inner : ExactInterval ℚ) : Prop :=
  outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper

/-- [definition] The outward projection of an exact interval onto the grid `1 / 10 ^ places`: the
lower endpoint floors and the upper ceils. Both are integer operations.

Rust counterpart: `mmcif.rs::DecimalToken::projected_wire`, whose `div_euclid` is the floor and
whose negated `div_euclid` of the negation is the ceiling. -/
def projectOutward (places : ℕ) (d : ExactInterval ℚ) : ExactInterval ℚ where
  lower := (⌊d.lower * (10 : ℚ) ^ places⌋ : ℚ) / (10 : ℚ) ^ places
  upper := (⌈d.upper * (10 : ℚ) ^ places⌉ : ℚ) / (10 : ℚ) ^ places
  ordered := by
    have hpos : (0 : ℚ) < (10 : ℚ) ^ places := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    have h1 : (⌊d.lower * (10 : ℚ) ^ places⌋ : ℚ) ≤ d.lower * (10 : ℚ) ^ places := Int.floor_le _
    have h2 : d.upper * (10 : ℚ) ^ places ≤ (⌈d.upper * (10 : ℚ) ^ places⌉ : ℚ) := Int.le_ceil _
    have h3 : d.lower * (10 : ℚ) ^ places ≤ d.upper * (10 : ℚ) ^ places :=
      mul_le_mul_of_nonneg_right d.ordered (le_of_lt hpos)
    linarith

/-- [proved-derived; formal-checked] **An outward projection contains what it projected.** Nothing
the source declared is lost; the grid is only ever coarser. -/
theorem projection_contains_source (places : ℕ) (d : ExactInterval ℚ) :
    Contains (projectOutward places d) d := by
  have hpos : (0 : ℚ) < (10 : ℚ) ^ places := by positivity
  constructor
  · rw [projectOutward, div_le_iff₀ hpos]
    exact Int.floor_le _
  · rw [projectOutward, le_div_iff₀ hpos]
    exact Int.le_ceil _

/-- [proved-derived; formal-checked] **Widening never flips a decision.** If the outer interval is
decided, the inner one is decided the same way. A widened interval can therefore turn a decided
contact `openContact`, and can never turn `inside` into `outside` or the reverse.

This is the whole justification for the library's coordinate discipline: the per-token enclosure is
the tightest reading the source licenses, and a projection onto a declared resident denominator is
a **safe** coarsening with a stated law rather than a silent rounding. -/
theorem widening_never_flips_a_decision (aperture : ℚ) (inner outer : ExactInterval ℚ)
    (h : Contains outer inner) :
    (classify aperture outer = ContactClass.inside →
        classify aperture inner = ContactClass.inside) ∧
      (classify aperture outer = ContactClass.outside →
        classify aperture inner = ContactClass.outside) := by
  obtain ⟨hlow, hup⟩ := h
  constructor
  · intro hin
    rw [classify_eq_inside_iff] at hin ⊢
    exact le_trans hup hin
  · intro hout
    rw [classify_eq_outside_iff] at hout ⊢
    exact lt_of_lt_of_le hout hlow

/-- [proved-derived; formal-checked] The consequence at the token: a contact decided on the
projected resident wire is decided the same way on the token's own enclosure. -/
theorem decided_under_projection_is_decided_at_source (aperture : ℚ) (places : ℕ)
    (d : ExactInterval ℚ) :
    (classify aperture (projectOutward places d) = ContactClass.inside →
        classify aperture d = ContactClass.inside) ∧
      (classify aperture (projectOutward places d) = ContactClass.outside →
        classify aperture d = ContactClass.outside) :=
  widening_never_flips_a_decision aperture d (projectOutward places d)
    (projection_contains_source places d)

/-! ## 3. The environment index, and why no occurrence exists without it -/

/-- [definition] The environment `eta` one prediction was produced under.

Rust counterpart: `crates/holonic-engine/src/physical_intake.rs::TargetEcology`. -/
structure TargetEcology where
  /-- The addressed target. -/
  target : String
  /-- Which conformational or assembly form was presented. -/
  targetForm : String
  /-- The presented stoichiometry. -/
  stoichiometry : String
  /-- The cofolding model that produced the prediction. -/
  cofoldingModel : String
  deriving DecidableEq, Repr

/-- [definition] The causal lineage of the design the prediction was made about.

Rust counterpart: `physical_intake.rs::DesignLineage`. -/
structure DesignLineage where
  /-- The design's stable identifier. -/
  designUuid : String
  /-- The design's presented name. -/
  designName : String
  /-- The sampling seed of this prediction occurrence. -/
  seed : String
  deriving DecidableEq, Repr

/-- [definition] One row and column address of the uncertainty array.

Rust counterpart: `physical_intake.rs::TokenAddress`. -/
structure TokenAddress where
  /-- The chain this token belongs to. -/
  chain : String
  /-- The residue ordinal within that chain. -/
  residue : ℤ
  deriving DecidableEq, Repr

/-- [definition] The complete environment index one uncertainty array was produced under.

Rust counterpart: `physical_intake.rs::EnvironmentIndex`. -/
structure EnvironmentIndex where
  /-- The environment. -/
  ecology : TargetEcology
  /-- The design lineage. -/
  lineage : DesignLineage
  /-- The addressed token population, in array order. -/
  tokens : List TokenAddress

/-- [definition] **An addressed occurrence.** Its array is indexed by the environment's own token
population, so an array without that population is not a well-typed occurrence at all — the
requirement is carried by the type and not by a check a caller could skip.

Rust counterpart: `physical_intake.rs::AddressedUncertainty`, whose one constructor
`AddressedUncertainty::found` takes the index by value and refuses a token population that does not
address the array. -/
structure Occurrence where
  /-- The environment index. A field, never an option. -/
  environment : EnvironmentIndex
  /-- The directional reading at each addressed cell. -/
  word : Fin environment.tokens.length → Fin environment.tokens.length → ℚ
  /-- Every token address occurs once, so the addressing is unambiguous. -/
  distinct : environment.tokens.Nodup

/-- [proved-derived; formal-checked] **No occurrence without an environment index.** The
projection is total: every occurrence has one, by construction. -/
theorem no_occurrence_without_environment (o : Occurrence) :
    ∃ eta : EnvironmentIndex, o.environment = eta := ⟨o.environment, rfl⟩

/-- [definition] What an exterior source presents: an array of some declared extent always, and an
environment index only when the writer deposited one. Boltz-2 writes the first and not the second.

Rust counterpart: `physical_intake::numpy::NumpySource` together with
`EnvironmentIndex::from_numpy_source`, which returns `EnvironmentArraysAbsent` when the ten
environment arrays are not there. -/
structure Presentation where
  /-- The declared square extent of the presented array. -/
  extent : ℕ
  /-- The presented cells. -/
  word : Fin extent → Fin extent → ℚ
  /-- The environment index, when the source carried one. -/
  environment : Option EnvironmentIndex

/-- [definition] Founding an occurrence from a presentation. There is no default, no fallthrough
and no inference: an absent environment returns nothing.

Rust counterpart: `physical_intake.rs::AddressedUncertainty::{read_self_indexed,
read_with_declared_environment}`. -/
def foundWith (p : Presentation) (eta : EnvironmentIndex) : Option Occurrence :=
  if hlen : eta.tokens.length = p.extent then
    if hnd : eta.tokens.Nodup then
      some { environment := eta
             word := fun i j => p.word (Fin.cast hlen i) (Fin.cast hlen j)
             distinct := hnd }
    else none
  else none

/-- [proved-derived; formal-checked] A founded occurrence carries the declared index itself. -/
theorem foundWith_environment (p : Presentation) (eta : EnvironmentIndex) (o : Occurrence)
    (h : foundWith p eta = some o) : o.environment = eta := by
  unfold foundWith at h
  split at h
  · split at h
    · rw [← Option.some.inj h]
    · simp at h
  · simp at h

/-- [definition] Founding an occurrence from a presentation. There is no default, no fallthrough
and no inference: an absent environment returns nothing. -/
def found (p : Presentation) : Option Occurrence :=
  match p.environment with
  | none => none
  | some eta => foundWith p eta

/-- [proved-derived; formal-checked] **An occurrence cannot be founded without its environment.**
This is the theorem the Boltz-shaped path exhibits: the run emits only the uncertainty array and
intake returns nothing until a caller declares the index that array was produced under. -/
theorem found_none_of_environment_absent (p : Presentation) (h : p.environment = none) :
    found p = none := by
  simp [found, h]

/-- [proved-derived; formal-checked] And when one *is* founded, its environment is the presented
one: nothing is substituted. -/
theorem found_environment (p : Presentation) (o : Occurrence) (h : found p = some o) :
    p.environment = some o.environment := by
  unfold found at h
  cases hp : p.environment with
  | none => rw [hp] at h; simp at h
  | some eta =>
      rw [hp] at h
      rw [foundWith_environment p eta o h]

/-! ## 4. The array and the addressed pair population -/

namespace Occurrence

/-- [definition] The addressed pair population: every ordered pair of addressed tokens.

Rust counterpart: the key set of `AddressedUncertainty::pair_uncertainty`. -/
def addressedPairs (o : Occurrence) : List (TokenAddress × TokenAddress) :=
  o.environment.tokens.flatMap fun a => o.environment.tokens.map fun b => (a, b)

end Occurrence

/-- [proved-derived; formal-checked] The pair population of two lists is their product. -/
theorem length_pairsOver {α : Type _} (l m : List α) :
    (l.flatMap fun a => m.map fun b => (a, b)).length = l.length * m.length := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- [proved-derived; formal-checked] **The addressed pair population is exactly the array.** The
intake's return is total on it and invents nothing outside it, which is the relation between the
presented uncertainty array and the population it addresses. -/
theorem addressed_pair_population (o : Occurrence) :
    o.addressedPairs.length = o.environment.tokens.length * o.environment.tokens.length :=
  length_pairsOver _ _

/-- [proved-derived; formal-checked] Every addressed token has exactly one array index, because the
environment's token list has no duplicate.

Rust counterpart: `EnvironmentIndex::token_index` together with the
`EnvironmentIndex::addresses_are_distinct` check `AddressedUncertainty::found` enforces. -/
theorem token_index_unique (o : Occurrence) (t : TokenAddress)
    (h : t ∈ o.environment.tokens) :
    ∃! i : Fin o.environment.tokens.length, o.environment.tokens.get i = t := by
  obtain ⟨i, hi⟩ := List.get_of_mem h
  refine ⟨i, hi, fun j hj => ?_⟩
  exact List.nodup_iff_injective_get.mp o.distinct (hj.trans hi.symm)

/-- [proved-derived; formal-checked] **Every addressed pair has exactly one reading.** Totality on
the addressed population, stated where it is checkable. -/
theorem reading_total_on_addressed_pairs (o : Occurrence) (a b : TokenAddress)
    (ha : a ∈ o.environment.tokens) (hb : b ∈ o.environment.tokens) :
    ∃! r : ℚ, ∃ i j : Fin o.environment.tokens.length,
      o.environment.tokens.get i = a ∧ o.environment.tokens.get j = b ∧ o.word i j = r := by
  obtain ⟨i, hi, hiu⟩ := token_index_unique o a ha
  obtain ⟨j, hj, hju⟩ := token_index_unique o b hb
  refine ⟨o.word i j, ⟨i, j, hi, hj, rfl⟩, ?_⟩
  rintro r ⟨i', j', hi', hj', rfl⟩
  rw [hiu i' hi', hju j' hj']

/-- [proved-derived; formal-checked] **A reading is directional.** There is an occurrence whose
`(i,j)` and `(j,i)` cells differ, so symmetrizing the array would destroy testimony the source
gave. `physical_intake.rs` retains both directions in
`PairUncertainty::{row_given_column, column_given_row}` and never averages them. -/
def asymmetricOccurrence : Occurrence where
  environment :=
    { ecology := ⟨"target", "form", "1to1", "model"⟩
      lineage := ⟨"uuid", "name", "0"⟩
      tokens := [⟨"A", 1⟩, ⟨"A", 2⟩] }
  word := fun i _ => (i.val : ℚ)
  distinct := by decide

/-- [proved-derived; formal-checked] It addresses two tokens. -/
theorem asymmetricOccurrence_tokens_length :
    asymmetricOccurrence.environment.tokens.length = 2 := rfl

theorem reading_is_directional :
    ∃ (o : Occurrence) (i j : Fin o.environment.tokens.length), o.word i j ≠ o.word j i := by
  refine ⟨asymmetricOccurrence, ⟨0, ?_⟩, ⟨1, ?_⟩, ?_⟩
  · rw [asymmetricOccurrence_tokens_length]; norm_num
  · rw [asymmetricOccurrence_tokens_length]; norm_num
  · show ((0 : ℕ) : ℚ) ≠ ((1 : ℕ) : ℚ)
    norm_num

/-! ## The contract -/

/-- [proved-derived; formal-checked] **What intake preserves.** Decoding an exterior codeword is
exact and total on finite words; an outward projection onto a coarser grid contains the source and
so never flips a decision; and no occurrence is founded without its environment index.

Rust owner: `crates/holonic-engine/src/physical_intake.rs` with its `mmcif` and `numpy`
submodules. -/
theorem intake_contract :
    (∀ (f : FloatFormat) (w : Codeword f), w.Finite → decode w = some w.value) ∧
      (∀ (places : ℕ) (d : ExactInterval ℚ), Contains (projectOutward places d) d) ∧
      (∀ p : Presentation, p.environment = none → found p = none) :=
  ⟨fun _ w h => decode_exact_on_finite w h, projection_contains_source,
    found_none_of_environment_absent⟩

section Audit

#print axioms decode_total_on_finite
#print axioms decode_exact_on_finite
#print axioms decode_refuses_nonfinite
#print axioms decode_isSome_iff
#print axioms wider_format_carries_every_value
#print axioms binary32_strictly_refines_binary16
#print axioms DecimalToken.enclosure_contains_centre
#print axioms projection_contains_source
#print axioms widening_never_flips_a_decision
#print axioms decided_under_projection_is_decided_at_source
#print axioms no_occurrence_without_environment
#print axioms found_none_of_environment_absent
#print axioms foundWith_environment
#print axioms found_environment
#print axioms addressed_pair_population
#print axioms token_index_unique
#print axioms reading_total_on_addressed_pairs
#print axioms reading_is_directional
#print axioms intake_contract

end Audit

end Soma.Holonics.Foundation.ExteriorIntake
