//! A declared-option modeling surface: the holonic answer to Mathematica's option convention.
//!
//! Record: `research/records/2026-08-08_THE_WINDING_IS_THE_PHASE_THE_OPTION_IS_A_DECLARED_RECEIVER.md`.
//! Contract: `archive/plans/THE_PRESENTATION_ORGAN.md`.
//!
//! ## What is imported from Wolfram, and what is refused
//!
//! Mathematica's modeling surface is built on an option convention that is genuinely excellent and
//! is adopted here wholesale in structure: a call names the object and the domain, and every other
//! degree of freedom is a **named, defaulted, inspectable option** — `PlotPoints`, `MeshFunctions`,
//! `ScalingFunctions`, `ColorFunction`, `RegionFunction`, `Exclusions`. Its virtue is that the
//! knobs are *declared* rather than buried: you can read a call and know what was assumed.
//!
//! Wolfram's `ComplexPlot3D[f, {z, z_min, z_max}]` plots `Abs[f]` as height and colours by
//! `Arg[f]`. Both faculties are refused here, for one reason each, and the refusals are the whole
//! design:
//!
//! - **`Arg` cannot be computed.** It is transcendental, and `atan2` appears nowhere in this body —
//!   verified by search across both repositories. A rational point has no rational argument. So the
//!   phase face is **not approximated**: it is replaced by the exact object that Wolfram's colour
//!   wheel is a lossy picture *of* — the **winding number**, an integer, certified by
//!   `eta_boundary_winding` from sign-of-cross-product ray crossings with no angle anywhere.
//! - **`Abs` cannot be computed either** (`sqrt` is transcendental), so height is carried by the
//!   exact squared modulus or by a declared exact scaling function, never by a float magnitude.
//!
//! This is not a workaround. A winding number over a closed boundary is a *stronger* statement than
//! a sampled phase field: it counts the zeros inside, exactly, and Wolfram's own documentation
//! concedes that its samplers may miss features. Phase colour shows you where a zero probably is;
//! the winding certificate proves how many there are.
//!
//! ## The option convention, holonically
//!
//! Wolfram's options are receiver coordinates in this body's vocabulary: they say how a receiver
//! looks, not what the object is. So `ModelOptions` carries them explicitly, every field defaulted
//! and inspectable, and the emitted artifact records the options it was produced under. An option
//! that changed the object rather than the view would be a defect; the falsifier in
//! `presentation_gauge` already enforces that for colour, and `option_change_never_moves_the_object`
//! enforces it here for the rest.

use std::collections::BTreeMap;

use num_traits::{Signed, Zero};
use relational_geometry::{Rat, format_rat, integer};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Which exact scalar a face reads off a complex value.
///
/// Wolfram's `ScalingFunctions` and the `#2` slot of `MeshFunctions` take arbitrary expressions;
/// here the admissible readings are enumerated, because each must be exactly computable over
/// `Rat` and an open-ended expression language cannot promise that. An enumeration that refuses
/// what it cannot compute is preferable to a slot that silently accepts `Arg` and returns a float.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactReading {
    /// Re(z). Exact.
    RealPart,
    /// Im(z). Exact.
    ImaginaryPart,
    /// |z|^2 = Re^2 + Im^2. Exact — the squared modulus, NOT |z|, because sqrt is transcendental.
    ///
    /// `z * conj(z)`: the phase is **deleted**. Read this against `HarmonicReal` one line below,
    /// which is `Re(z * z)` and **doubles** it. The two live four lines apart because they are
    /// the two halves of one operation — the quotient by the phase circle, and the squaring that
    /// the quotient's sign ambiguity is the erased half-turn of.
    SquaredModulus,
    /// Re(z)^2 - Im(z)^2, the harmonic conjugate pair's real part. Exact.
    ///
    /// # This is the exact carrier of the founding predicate's form
    ///
    /// `crates/holonic-body/src/arrow.rs` reads a relating from a pole as the pair `(aim, cross)` — the
    /// cohere `W+` that STANDS and the gyration `W-` that FLOWS — and gates the founding on an
    /// indefinite form of signature `(1,1)`. Identify the pair with one complex rational,
    ///
    /// ```text
    ///     z = aim + i * cross
    ///     Re(z * z) = aim^2 - cross^2 = HarmonicReal.read(aim, cross)
    /// ```
    ///
    /// and the arrow's two readings fall out of this one scalar, exactly and with no threshold:
    ///
    /// ```text
    ///     Arrow::founds()          cross^2 - aim^2 >= 0    <=>  HarmonicReal <= 0
    ///     Causal::TransportDominant                        <=>  HarmonicReal <  0
    ///     Causal::Balanced          the cone wall           <=>  HarmonicReal == 0
    ///     Causal::StorageDominant                          <=>  HarmonicReal >  0
    /// ```
    ///
    /// `Arrow::sense()` reads the sign of `aim = Re(z)`. Applied to `z * z` it reads the sign of
    /// `Re(z^2)`, which is this reading — so **the causal class is the hand composed with
    /// squaring**, and squaring is exactly what doubles the phase. That is why the arrow's wall
    /// sits at a quarter turn (`|cross| = |aim|`) and this scalar's sign flips at a half turn:
    /// they are one locus seen before and after the doubling.
    ///
    /// **Where it is strictly coarser, and this is the whole of the difference.** `z = 0` — the
    /// arrow at its own horizon, both faces null — returns `HarmonicReal == 0`, the same value
    /// the cone wall returns. `Arrow::causal_class` separates them as `Unread` because it
    /// consults `at_horizon()` first, which is a reading of the *pair* and not of this scalar.
    /// A single reading off `z^2` cannot recover it, because squaring sends `0` and nothing else
    /// to `0` but sends the whole wall there too.
    ///
    /// **This is a citation, not a dependency.** `crates/holonic-body` has zero dependencies and cannot
    /// import this crate; the test `the_harmonic_real_is_the_arrows_founding_form` below carries
    /// the correspondence by re-deriving `(aim, cross)` from `arrow.rs`'s own declared points
    /// over `Rat`, so the classes are computed from the material rather than declared.
    HarmonicReal,
    /// The quadrant index 0..3, an exact integer classification of sign pairs. This is the
    /// coarsest honest phase reading available without transcendentals.
    Quadrant,
}

impl ExactReading {
    /// Read the value exactly. Returns `None` at a point where the reading is undefined.
    pub fn read(&self, re: &Rat, im: &Rat) -> Option<Rat> {
        Some(match self {
            ExactReading::RealPart => re.clone(),
            ExactReading::ImaginaryPart => im.clone(),
            ExactReading::SquaredModulus => re * re + im * im,
            ExactReading::HarmonicReal => re * re - im * im,
            ExactReading::Quadrant => {
                // The origin has no quadrant, and saying so is the point: a reading that
                // invented one there would be manufacturing phase where none exists.
                if re.is_zero() && im.is_zero() {
                    return None;
                }
                integer(i64::from(quadrant_of(re, im)?))
            }
        })
    }

    pub fn name(&self) -> &'static str {
        match self {
            ExactReading::RealPart => "re",
            ExactReading::ImaginaryPart => "im",
            ExactReading::SquaredModulus => "abs2",
            ExactReading::HarmonicReal => "harmonic_re",
            ExactReading::Quadrant => "quadrant",
        }
    }
}

/// The exact quadrant of a nonzero complex rational, 0..3 counter-clockwise from the positive
/// real axis. Axis points belong to the quadrant they open into, which keeps the classification
/// total on the punctured plane.
///
/// This is the honest replacement for a coarse `Arg`: it is exact, it is an integer, and it
/// carries the only phase information a rational point actually determines without transcendentals.
pub fn quadrant_of(re: &Rat, im: &Rat) -> Option<u8> {
    if re.is_zero() && im.is_zero() {
        return None;
    }
    Some(match (re.is_negative(), im.is_negative()) {
        (false, false) => 0,
        (true, false) => 1,
        (true, true) => 2,
        (false, true) => 3,
    })
}

/// Signed quadrant transitions along an ordered walk, summed.
///
/// This is the discrete winding — Wolfram's `Arg` colour wheel reduced to what is exactly
/// knowable. A step that crosses more than one quadrant boundary at once is **not** resolved by
/// guessing the direction: it is returned as an ambiguity, because the walk did not sample finely
/// enough to determine the turn, and inventing a direction there is exactly the silent-omission
/// failure this body refuses.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnReading {
    /// Net quarter-turns, counter-clockwise positive. Divide by 4 for whole turns.
    pub quarter_turns: i64,
    /// Steps whose turn direction the sampling could not determine.
    pub ambiguous_steps: Vec<usize>,
    /// Steps that landed exactly on the origin, where phase does not exist.
    pub origin_steps: Vec<usize>,
}

impl TurnReading {
    pub fn is_determined(&self) -> bool {
        self.ambiguous_steps.is_empty() && self.origin_steps.is_empty()
    }
}

/// Read the accumulated turn of an ordered sequence of exact complex points.
///
/// No angle is computed. Each step's turn is decided by the quadrant pair, and for the ambiguous
/// diagonal case by the exact sign of the cross product — the same primitive
/// `eta_boundary_winding` uses.
pub fn read_turn(points: &[(Rat, Rat)]) -> TurnReading {
    let mut quarter_turns = 0i64;
    let mut ambiguous_steps = Vec::new();
    let mut origin_steps = Vec::new();

    for index in 0..points.len().saturating_sub(1) {
        let (re0, im0) = &points[index];
        let (re1, im1) = &points[index + 1];
        let (Some(from), Some(to)) = (quadrant_of(re0, im0), quadrant_of(re1, im1)) else {
            origin_steps.push(index);
            continue;
        };
        let delta = (i64::from(to) - i64::from(from)).rem_euclid(4);
        match delta {
            0 => {}
            1 => quarter_turns += 1,
            3 => quarter_turns -= 1,
            _ => {
                // Two quadrants in one step: the direction is not determined by the endpoints
                // alone. The exact cross product decides it when the step does not pass through
                // the origin, and otherwise the step is reported as ambiguous rather than guessed.
                let cross = re0 * im1 - im0 * re1;
                if cross.is_positive() {
                    quarter_turns += 2;
                } else if cross.is_negative() {
                    quarter_turns -= 2;
                } else {
                    ambiguous_steps.push(index);
                }
            }
        }
    }

    TurnReading {
        quarter_turns,
        ambiguous_steps,
        origin_steps,
    }
}

/// A declared level set: the exact analogue of one entry of Wolfram's `MeshFunctions`.
///
/// Wolfram draws a mesh line where an expression takes evenly spaced values, found by
/// interpolation between samples. Here a level is a **certified sign change** of
/// `reading(z) - level` between consecutive stations: the crossing is bracketed exactly, and the
/// bracket is what is drawn. A mesh line is therefore a statement with a witness, not a curve
/// fitted through samples.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MeshFunction {
    pub reading: ExactReading,
    pub levels: Vec<Rat>,
}

impl MeshFunction {
    pub fn new(reading: ExactReading, levels: Vec<Rat>) -> Self {
        Self { reading, levels }
    }
}

/// One certified crossing of a declared mesh level, bracketed between two stations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MeshCrossing {
    pub reading: String,
    pub level: Rat,
    /// The station index before the crossing; the crossing lies in `[index, index+1]`.
    pub lower_station: usize,
    /// Exact values at the bracketing stations, so a reader can check the sign change.
    pub value_before: Rat,
    pub value_after: Rat,
}

/// Find every certified crossing of every declared level along an ordered walk.
///
/// A crossing is admitted only where the sign of `reading - level` genuinely changes. Where the
/// reading is exactly the level at a station, that is recorded as a crossing at that station
/// rather than being perturbed away.
pub fn certified_crossings(points: &[(Rat, Rat)], mesh: &MeshFunction) -> Vec<MeshCrossing> {
    let values: Vec<Option<Rat>> = points
        .iter()
        .map(|(re, im)| mesh.reading.read(re, im))
        .collect();
    let mut crossings = Vec::new();
    for level in &mesh.levels {
        for index in 0..values.len().saturating_sub(1) {
            let (Some(before), Some(after)) = (&values[index], &values[index + 1]) else {
                continue;
            };
            let left = before - level;
            let right = after - level;
            let crosses = (left.is_negative() && right.is_positive())
                || (left.is_positive() && right.is_negative())
                || left.is_zero();
            if crosses {
                crossings.push(MeshCrossing {
                    reading: mesh.reading.name().to_string(),
                    level: level.clone(),
                    lower_station: index,
                    value_before: before.clone(),
                    value_after: after.clone(),
                });
            }
        }
    }
    crossings
}

/// How a scalar is compressed for display: Wolfram's `ScalingFunctions`, exactly.
///
/// `Log` is refused outright rather than approximated. Its role in Wolfram — making a field with
/// poles legible — is served here by `IntegerDecades`, which returns the exact integer decade
/// `k` such that `10^k <= |v| < 10^(k+1)` by integer comparison alone. That is the honest part of
/// a log scale: the part that is an integer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScalingFunction {
    /// No compression.
    Identity,
    /// The exact integer decade of the magnitude, computed by repeated exact comparison. Returns
    /// `None` at zero, which has no decade.
    IntegerDecades,
    /// Exact reciprocal, for fields that grow toward a pole. `None` at zero.
    Reciprocal,
}

impl ScalingFunction {
    pub fn apply(&self, value: &Rat) -> Option<Rat> {
        match self {
            ScalingFunction::Identity => Some(value.clone()),
            ScalingFunction::Reciprocal => {
                if value.is_zero() {
                    None
                } else {
                    Some(Rat::from_integer(1.into()) / value)
                }
            }
            ScalingFunction::IntegerDecades => integer_decade(value).map(integer),
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            ScalingFunction::Identity => "identity",
            ScalingFunction::IntegerDecades => "integer_decades",
            ScalingFunction::Reciprocal => "reciprocal",
        }
    }
}

/// The exact integer decade of a nonzero rational: `k` with `10^k <= |v| < 10^(k+1)`.
///
/// Computed by exact rational comparison against powers of ten. No logarithm is taken and no float
/// is constructed; the answer is an integer and it is right.
pub fn integer_decade(value: &Rat) -> Option<i64> {
    if value.is_zero() {
        return None;
    }
    let magnitude = value.abs();
    let ten = Rat::from_integer(10.into());
    let one = Rat::from_integer(1.into());
    let mut decade = 0i64;
    let mut scaled = magnitude;
    // Bounded so a pathological input cannot spin: 10^±512 brackets any rational this body builds.
    while scaled >= ten && decade < 512 {
        scaled /= &ten;
        decade += 1;
    }
    while scaled < one && decade > -512 {
        scaled *= &ten;
        decade -= 1;
    }
    Some(decade)
}

/// Which stations a receiver admits: Wolfram's `RegionFunction`, exactly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RegionFunction {
    /// Everything the window contains.
    All,
    /// Only where the declared reading is non-negative.
    NonNegative(ExactReading),
    /// Only outside a square of the given half-width about the origin, in the max-norm. Stated in
    /// the max-norm rather than the Euclidean norm because that is exactly decidable over `Rat`.
    OutsideOriginSquare(Rat),
}

impl RegionFunction {
    pub fn admits(&self, re: &Rat, im: &Rat) -> bool {
        match self {
            RegionFunction::All => true,
            RegionFunction::NonNegative(reading) => reading
                .read(re, im)
                .map(|value| !value.is_negative())
                .unwrap_or(false),
            RegionFunction::OutsideOriginSquare(half_width) => {
                re.abs() >= *half_width || im.abs() >= *half_width
            }
        }
    }

    pub fn name(&self) -> String {
        match self {
            RegionFunction::All => "all".to_string(),
            RegionFunction::NonNegative(reading) => format!("nonneg({})", reading.name()),
            RegionFunction::OutsideOriginSquare(width) => {
                format!("outside_square({})", format_rat(width))
            }
        }
    }
}

/// The full declared option set for a model face.
///
/// Every field is an option in Wolfram's sense: named, defaulted, and inspectable. None of them may
/// change the object — they say how a receiver reads it. `record()` returns the option set as rows
/// so the emitted artifact carries the assumptions it was produced under, which is the part of
/// Wolfram's convention worth the most and the part most often lost when a plot is exported.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModelOptions {
    /// Height/value reading — Wolfram's implicit `Abs` for `ComplexPlot3D`, made exact.
    pub value_reading: ExactReading,
    /// Phase reading — Wolfram's `Arg`, replaced by the exact quadrant classification.
    pub phase_reading: ExactReading,
    pub scaling: ScalingFunction,
    pub mesh_functions: Vec<MeshFunction>,
    pub region: RegionFunction,
    /// Stations per axis. An aperture, not a quality knob: raising it does not make an undecided
    /// thing decide, it only changes where the receiver looks.
    pub stations: u32,
}

impl Default for ModelOptions {
    fn default() -> Self {
        Self {
            value_reading: ExactReading::SquaredModulus,
            phase_reading: ExactReading::Quadrant,
            scaling: ScalingFunction::Identity,
            mesh_functions: Vec::new(),
            region: RegionFunction::All,
            stations: 16,
        }
    }
}

impl ModelOptions {
    /// The options as inspectable rows, for deposit beside every artifact.
    pub fn record(&self) -> BTreeMap<String, String> {
        let mut rows = BTreeMap::new();
        rows.insert("value_reading".into(), self.value_reading.name().into());
        rows.insert("phase_reading".into(), self.phase_reading.name().into());
        rows.insert("scaling".into(), self.scaling.name().into());
        rows.insert("region".into(), self.region.name());
        rows.insert("stations".into(), self.stations.to_string());
        rows.insert(
            "mesh_functions".into(),
            self.mesh_functions
                .iter()
                .map(|mesh| {
                    format!(
                        "{}@[{}]",
                        mesh.reading.name(),
                        mesh.levels
                            .iter()
                            .map(format_rat)
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                })
                .collect::<Vec<_>>()
                .join(";"),
        );
        rows
    }

    pub fn with_mesh(mut self, mesh: MeshFunction) -> Self {
        self.mesh_functions.push(mesh);
        self
    }

    pub fn with_scaling(mut self, scaling: ScalingFunction) -> Self {
        self.scaling = scaling;
        self
    }

    pub fn with_stations(mut self, stations: u32) -> Result<Self, ModelError> {
        if stations == 0 {
            return Err(ModelError::VacuousAperture);
        }
        self.stations = stations;
        Ok(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ModelError {
    #[error("a receiver must look at least once")]
    VacuousAperture,
    #[error("the declared window is empty or inverted")]
    EmptyWindow,
}

/// A read of an ordered exact walk under a declared option set.
///
/// This is the model face: the turn (exact phase), the certified mesh crossings, the scaled values,
/// and the options that produced them. It carries no colour and no canvas.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModelFace {
    pub schema: String,
    pub options: BTreeMap<String, String>,
    pub turn: TurnReading,
    pub crossings: Vec<MeshCrossing>,
    /// Station values under `value_reading` then `scaling`. `None` where the reading or the scaling
    /// is undefined there — carried as a hole rather than filled in.
    pub scaled_values: Vec<Option<Rat>>,
    /// Stations the region function excluded, by index. Excluded, never silently dropped.
    pub excluded_stations: Vec<usize>,
}

/// Read an ordered exact walk under declared options.
pub fn read_model(points: &[(Rat, Rat)], options: &ModelOptions) -> ModelFace {
    let mut admitted = Vec::new();
    let mut excluded_stations = Vec::new();
    for (index, (re, im)) in points.iter().enumerate() {
        if options.region.admits(re, im) {
            admitted.push((re.clone(), im.clone()));
        } else {
            excluded_stations.push(index);
        }
    }

    let turn = read_turn(&admitted);
    let mut crossings = Vec::new();
    for mesh in &options.mesh_functions {
        crossings.extend(certified_crossings(&admitted, mesh));
    }
    let scaled_values = admitted
        .iter()
        .map(|(re, im)| {
            options
                .value_reading
                .read(re, im)
                .and_then(|value| options.scaling.apply(&value))
        })
        .collect();

    ModelFace {
        schema: "holonic-engine.model-face.v1".to_string(),
        options: options.record(),
        turn,
        crossings,
        scaled_values,
        excluded_stations,
    }
}

#[cfg(test)]
mod tests {
    //! Controls for the modeling surface.
    //!
    //! The load-bearing one is `option_change_never_moves_the_object`: an option is a receiver
    //! coordinate, so changing it may change what is read and must never change what is there.

    use relational_geometry::rat;

    use super::*;

    /// The unit square walked counter-clockwise: exactly one full turn about the origin.
    fn unit_loop() -> Vec<(Rat, Rat)> {
        vec![
            (integer(1), integer(0)),
            (integer(1), integer(1)),
            (integer(0), integer(1)),
            (integer(-1), integer(1)),
            (integer(-1), integer(0)),
            (integer(-1), integer(-1)),
            (integer(0), integer(-1)),
            (integer(1), integer(-1)),
            (integer(1), integer(0)),
        ]
    }

    #[test]
    fn a_counter_clockwise_loop_reads_exactly_one_turn() {
        let turn = read_turn(&unit_loop());
        assert_eq!(turn.quarter_turns, 4, "one full turn is four quarter-turns");
        assert!(turn.is_determined());
    }

    #[test]
    fn reversing_the_walk_reverses_the_turn() {
        let mut reversed = unit_loop();
        reversed.reverse();
        assert_eq!(read_turn(&reversed).quarter_turns, -4);
    }

    #[test]
    fn a_loop_that_misses_the_origin_reads_no_turn() {
        // The control that keeps the winding meaningful: a walk that does not enclose the origin
        // must return zero. Without it, a reading that always returned 4 would pass the test above.
        let points = vec![
            (integer(2), integer(1)),
            (integer(3), integer(1)),
            (integer(3), integer(2)),
            (integer(2), integer(2)),
            (integer(2), integer(1)),
        ];
        assert_eq!(read_turn(&points).quarter_turns, 0);
    }

    #[test]
    fn two_loops_read_two_turns() {
        let mut doubled = unit_loop();
        doubled.extend(unit_loop());
        assert_eq!(read_turn(&doubled).quarter_turns, 8);
    }

    #[test]
    fn a_step_through_the_origin_is_reported_not_guessed() {
        // A diagonal step whose cross product vanishes has no determined turn direction. Guessing
        // one would be manufacturing phase.
        let points = vec![(integer(1), integer(1)), (integer(-1), integer(-1))];
        let turn = read_turn(&points);
        assert_eq!(
            turn.ambiguous_steps,
            vec![0],
            "the undetermined step must be reported"
        );
    }

    #[test]
    fn the_origin_has_no_quadrant_and_no_phase() {
        assert_eq!(quadrant_of(&integer(0), &integer(0)), None);
        assert_eq!(
            ExactReading::Quadrant.read(&integer(0), &integer(0)),
            None,
            "phase at the origin must be a hole, not a value"
        );
    }

    #[test]
    fn every_quadrant_is_reachable_and_distinct() {
        let corners = [
            (integer(1), integer(1), 0u8),
            (integer(-1), integer(1), 1),
            (integer(-1), integer(-1), 2),
            (integer(1), integer(-1), 3),
        ];
        for (re, im, expected) in corners {
            assert_eq!(quadrant_of(&re, &im), Some(expected));
        }
    }

    #[test]
    fn the_integer_decade_is_exact_across_scales() {
        assert_eq!(integer_decade(&integer(1)), Some(0));
        assert_eq!(integer_decade(&integer(9)), Some(0));
        assert_eq!(integer_decade(&integer(10)), Some(1));
        assert_eq!(integer_decade(&integer(999)), Some(2));
        assert_eq!(integer_decade(&integer(1000)), Some(3));
        assert_eq!(integer_decade(&rat(1, 10)), Some(-1));
        assert_eq!(integer_decade(&rat(1, 1000)), Some(-3));
        assert_eq!(integer_decade(&rat(-1, 100)), Some(-2), "sign is ignored");
        assert_eq!(integer_decade(&integer(0)), None, "zero has no decade");
    }

    #[test]
    fn the_decade_brackets_its_own_value() {
        // The defining property, checked rather than assumed: 10^k <= |v| < 10^(k+1).
        for value in [
            rat(1, 7),
            rat(22, 7),
            integer(1234),
            rat(-5, 3),
            rat(1, 999),
        ] {
            let decade = integer_decade(&value).expect("nonzero");
            let ten = Rat::from_integer(10.into());
            let mut lower = Rat::from_integer(1.into());
            for _ in 0..decade.abs() {
                if decade > 0 {
                    lower *= &ten;
                } else {
                    lower /= &ten;
                }
            }
            let upper = &lower * &ten;
            let magnitude = value.abs();
            assert!(
                lower <= magnitude && magnitude < upper,
                "decade {decade} does not bracket {}",
                format_rat(&value)
            );
        }
    }

    #[test]
    fn a_mesh_level_crossing_is_certified_by_a_sign_change() {
        let points = vec![
            (integer(1), integer(0)),
            (integer(2), integer(0)),
            (integer(3), integer(0)),
        ];
        let mesh = MeshFunction::new(ExactReading::SquaredModulus, vec![integer(5)]);
        let crossings = certified_crossings(&points, &mesh);
        assert_eq!(crossings.len(), 1, "|z|^2 crosses 5 exactly once on 1->3");
        assert_eq!(crossings[0].lower_station, 1);
        assert_eq!(crossings[0].value_before, integer(4));
        assert_eq!(crossings[0].value_after, integer(9));
    }

    #[test]
    fn a_level_never_reached_yields_no_crossing() {
        // The control: without it, a crossing finder that always fired would pass the test above.
        let points = vec![(integer(1), integer(0)), (integer(2), integer(0))];
        let mesh = MeshFunction::new(ExactReading::SquaredModulus, vec![integer(1000)]);
        assert!(certified_crossings(&points, &mesh).is_empty());
    }

    /// THE OPTION FALSIFIER. An option is a receiver coordinate: it may change what is read and
    /// must never change what is there.
    #[test]
    fn option_change_never_moves_the_object() {
        let points = unit_loop();
        let plain = ModelOptions::default();
        let elaborate = ModelOptions::default()
            .with_scaling(ScalingFunction::IntegerDecades)
            .with_mesh(MeshFunction::new(ExactReading::RealPart, vec![integer(0)]))
            .with_stations(64)
            .expect("stations");

        let first = read_model(&points, &plain);
        let second = read_model(&points, &elaborate);

        assert_eq!(
            first.turn, second.turn,
            "the winding is a property of the object and must not move with the options"
        );
        assert_ne!(
            first.options, second.options,
            "the two option sets must actually differ, or this control proves nothing"
        );
        assert_ne!(
            first.scaled_values, second.scaled_values,
            "the scaling option must actually change what is read"
        );
    }

    #[test]
    fn the_region_function_excludes_rather_than_drops() {
        let points = unit_loop();
        let options = ModelOptions {
            region: RegionFunction::NonNegative(ExactReading::RealPart),
            ..Default::default()
        };
        let face = read_model(&points, &options);
        assert!(
            !face.excluded_stations.is_empty(),
            "the fixture must exclude something or this proves nothing"
        );
        assert_eq!(
            face.excluded_stations.len() + face.scaled_values.len(),
            points.len(),
            "every station is either read or recorded as excluded"
        );
    }

    #[test]
    fn the_face_records_the_options_it_was_produced_under() {
        let face = read_model(&unit_loop(), &ModelOptions::default());
        for key in [
            "value_reading",
            "phase_reading",
            "scaling",
            "region",
            "stations",
        ] {
            assert!(
                face.options.contains_key(key),
                "the artifact does not record its own {key}"
            );
        }
    }

    #[test]
    fn a_vacuous_aperture_is_refused() {
        assert_eq!(
            ModelOptions::default().with_stations(0).unwrap_err(),
            ModelError::VacuousAperture
        );
    }

    #[test]
    fn the_squared_modulus_is_exact_at_an_irrational_ratio() {
        // |z|^2 stays rational where |z| would not: the reason the squared modulus is the carrier.
        let value = ExactReading::SquaredModulus
            .read(&integer(1), &integer(1))
            .expect("defined");
        assert_eq!(
            value,
            integer(2),
            "|1+i|^2 = 2, exactly; |1+i| is not rational"
        );
    }

    /// THE JOIN. `HarmonicReal` is the exact carrier of the form `crates/holonic-body/src/arrow.rs` gates
    /// the founding on, and this exhibits the correspondence rather than asserting it.
    ///
    /// `crates/holonic-body` has zero dependencies and cannot import this crate, so the arrow's own
    /// `relate` arithmetic is re-derived here over `Rat` from the **same four declared points**
    /// that `arrow.rs`'s `the_founding_band_is_a_cone_and_all_three_classes_are_reachable`
    /// uses. The classes are therefore computed from the material; nothing here hands two
    /// members of one class the same declared value.
    ///
    /// Both arms are required. The correspondence must hold at every point, **and** the material
    /// must actually reach all three classes plus the horizon — a reading that returned one sign
    /// everywhere would agree with anything and would have classified nothing.
    #[test]
    fn the_harmonic_real_is_the_arrows_founding_form() {
        // arrow.rs::relate, over Rat: re-base both boundaries to the pole and read the pair.
        //   aim   = W+ = (a-f) . (b-f)      the cohere that STANDS
        //   cross = W- = (a-f) x (b-f)      the gyration that FLOWS
        fn relate(a: (i64, i64), b: (i64, i64), f: (i64, i64)) -> (Rat, Rat) {
            let (ar, ai) = (integer(a.0 - f.0), integer(a.1 - f.1));
            let (br, bi) = (integer(b.0 - f.0), integer(b.1 - f.1));
            (&ar * &br + &ai * &bi, &ai * &br - &ar * &bi)
        }

        // arrow.rs's own declared material: one inside the cone, one on the wall, one outside,
        // and one at the pole's own horizon.
        let material = [
            ("inside the cone", (1, 0), (0, 1), (0, 0)),
            ("on the wall", (2, 0), (1, 1), (0, 0)),
            ("outside the cone", (2, 0), (3, 0), (0, 0)),
            ("at the horizon", (1, 0), (0, 1), (1, 0)),
        ];

        let mut signs: std::collections::BTreeSet<i8> = std::collections::BTreeSet::new();
        let mut horizons = 0usize;
        for (name, a, b, f) in material {
            let (aim, cross) = relate(a, b, f);
            let harmonic = ExactReading::HarmonicReal
                .read(&aim, &cross)
                .expect("the harmonic reading is total");

            // The identity, exactly: Re(z^2) for z = aim + i*cross.
            assert_eq!(
                harmonic,
                &aim * &aim - &cross * &cross,
                "{name}: the harmonic reading IS aim^2 - cross^2"
            );
            // And it is the negation of the form `founds()` tests, which is why the founding
            // band is `HarmonicReal <= 0` rather than `>= 0`.
            assert_eq!(
                harmonic,
                -(&cross * &cross - &aim * &aim),
                "{name}: founds() tests cross^2 - aim^2, the same form with the hand reversed"
            );
            // The squared modulus deletes what this doubles: |z|^2 = aim^2 + cross^2 differs
            // from Re(z^2) by exactly 2*cross^2, the phase term.
            let modulus = ExactReading::SquaredModulus
                .read(&aim, &cross)
                .expect("the modulus reading is total");
            assert_eq!(
                &modulus - &harmonic,
                integer(2) * &cross * &cross,
                "{name}: the two readings differ by twice the gyration's square"
            );

            signs.insert(match harmonic {
                ref value if value.is_zero() => 0,
                ref value if value.is_negative() => -1,
                _ => 1,
            });
            if aim.is_zero() && cross.is_zero() {
                horizons += 1;
            }
        }

        // THE ANTI-VACUITY ARM. All three signs must appear, or the reading is constant on this
        // material and its agreement with the arrow is not evidence.
        assert_eq!(
            signs,
            std::collections::BTreeSet::from([-1, 0, 1]),
            "the declared material must reach all three causal classes"
        );
        // And the horizon must be present, because it is the one place this reading is strictly
        // coarser than `Arrow::causal_class`: z = 0 returns the same zero the cone wall returns.
        assert_eq!(horizons, 1, "the degenerate case must be in the material");
        let wall = relate((2, 0), (1, 1), (0, 0));
        let horizon = relate((1, 0), (0, 1), (1, 0));
        assert_eq!(
            ExactReading::HarmonicReal.read(&wall.0, &wall.1),
            ExactReading::HarmonicReal.read(&horizon.0, &horizon.1),
            "squaring sends the whole wall to zero, so one scalar cannot separate the horizon \
             from it -- `at_horizon()` reads the PAIR, and that is the whole difference"
        );
        assert_ne!(
            (&wall.0, &wall.1),
            (&horizon.0, &horizon.1),
            "and the pair does separate them"
        );
    }
}
