//! **The native arm's resident laws: the Athena atlas walked and read on the card.**
//!
//! The native Eros/Athena baseline (`crate::athena`) is a suffix automaton over the declared
//! material, emitted as an integer container — classes, compressed-sparse-row transport by germ,
//! standings, suffix links, a vocabulary — and mounted from that container alone. These laws are
//! its hot deed, realized as resident kernels under the same passage as the foreign arm's: one
//! graph, typed admission, lineage-local refusal, a census read once.
//!
//! ```text
//!   walk     (construction, 0 → 1)   several prompts' germs carried through the transport rows
//!                                     from the root; a row with no such germ falls along the
//!                                     suffix link and retries (the ARC); an unseen germ returns to
//!                                     the root. Returns T × 2: the landed class and the mark
//!                                     (1 forward, 0 arc, 2 unseen) per position.
//!   future   (transport, 1 → 1)      for every position and every vocabulary germ, the STANDING of
//!                                     the class reached by that germ from the landed class's suffix
//!                                     chain (0 where no class in the chain offers it). T × V.
//!   depth    (transport, 1 → 1)      the same climb returning how far up the chain the germ was
//!                                     found (−1 where unreached). T × V.
//! ```
//!
//! The words are integers: the laws refuse any grain but `2^0`. Every law is entailed only by the
//! rest's own declarations — the populations it reads must be identified in the rest's header with
//! their shapes and integer carriers (`DeclaredShape`), and the law's statement must be one the rest
//! carries in its metadata (`AuthoritativeDescription`); see [`crate::native_occurrence`].
//!
//! **The geometry travels beside the law, never inside it.** Both laws hold an apparatus geometry
//! the caller declared, exactly as `resident_law::ContractTiled` holds a `TileGeometry`: the
//! returned words are bit-identical under every admitted member of the family, and the family is
//! [`ResidentSurface::athena_future_candidates`], read off the device and the module's measured
//! registers. No block is authored here and none is the maximum the device would admit.

use std::collections::BTreeMap;

use crate::ported_operation::OperationSpecies;
use crate::resident_law::{EntailmentRefusal, LawEntailment, ResidentLaw, ResidentMaterial};
use crate::resident_section::{
    AthenaFutureGeometry, AthenaWalkGeometry, Lane, LawShape, Positions, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface, StagedWords,
};
use crate::source_occurrence::BindingValidation;

/// The statement of the walk law, as the rest must declare it.
pub const WALK_LAW: &str = "walk: carry each prompt germ through the transport row of the current class from the root; when the row has no such germ, fall along the suffix link and retry (the arc); an unseen germ returns to the root";
/// The statement of the future-standing law, as the rest must declare it.
pub const FUTURE_LAW: &str = "future: for every position and every vocabulary germ, the standing of the class reached by that germ from the landed class's suffix chain, zero where no class in the chain offers it";
/// The statement of the future-depth law, as the rest must declare it.
pub const DEPTH_LAW: &str = "depth: for every position and every vocabulary germ, how far up the landed class's suffix chain the germ was found, minus one where unreached";

/// The rest's populations the laws read, by their names in the rest, with the extents the rest's
/// own header declares for them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AthenaArrays {
    pub indptr: String,
    pub germ: String,
    pub target: String,
    pub standing: String,
    pub suffix: String,
    pub classes: usize,
    pub transitions: usize,
    pub vocabulary: usize,
}

impl AthenaArrays {
    fn present(&self, material: &ResidentMaterial<'_>, with_standing: bool) -> Result<(), String> {
        for name in [&self.indptr, &self.germ, &self.target, &self.suffix] {
            if !material.arrays.contains_key(name) {
                return Err(name.clone());
            }
        }
        if with_standing && !material.arrays.contains_key(&self.standing) {
            return Err(self.standing.clone());
        }
        Ok(())
    }

    fn shapes_entailed(&self, validation: &BindingValidation, law: &'static str, with_standing: bool) -> Result<Vec<(String, String, String)>, EntailmentRefusal> {
        let mut parameters = Vec::new();
        let mut need: Vec<(&str, &String, Vec<usize>)> = vec![
            ("indptr", &self.indptr, vec![self.classes + 1, 1]),
            ("germ", &self.germ, vec![self.transitions, 1]),
            ("target", &self.target, vec![self.transitions, 1]),
            ("suffix", &self.suffix, vec![self.classes, 1]),
        ];
        if with_standing {
            need.push(("standing", &self.standing, vec![self.classes, 1]));
        }
        for (parameter, name, shape) in need {
            match validation.shapes.iter().find(|(p, s)| p == name && *s == shape) {
                Some((p, s)) => parameters.push((parameter.to_owned(), format!("{name} {shape:?}"), format!("declared shape {p}: {s:?}"))),
                None => {
                    return Err(EntailmentRefusal::ParameterUnentailed {
                        law,
                        parameter,
                        value: format!("{name} {shape:?}"),
                        testimony: validation.shapes.iter().map(|(p, s)| format!("{p}: {s:?}")).collect(),
                    });
                }
            }
        }
        Ok(parameters)
    }

    fn ranges(&self, material: &ResidentMaterial<'_>, with_standing: bool) -> Vec<(u64, u64)> {
        let mut out = vec![
            material.arrays[&self.indptr].range(),
            material.arrays[&self.germ].range(),
            material.arrays[&self.target].range(),
            material.arrays[&self.suffix].range(),
        ];
        if with_standing {
            out.push(material.arrays[&self.standing].range());
        }
        out
    }
}

/// A law binds only when the rest itself carries the statement. A description is exterior testimony
/// **here** because the rest emitted it; the same testimony on a foreign container is a name.
fn declared(validation: &BindingValidation, law: &'static str, statement: &str) -> Result<(String, String, String), EntailmentRefusal> {
    if validation.descriptions.iter().any(|carried| carried == statement) {
        Ok(("law".to_owned(), law.to_owned(), "the rest's own declaration of this law".to_owned()))
    } else {
        Err(EntailmentRefusal::SliceDoesNotEntail { law, required_any_of: vec![law], offered: validation.descriptions.clone() })
    }
}

fn integer_grain(operation: &'static str, grain: ResidentGrain) -> Result<(), ResidentRefusal> {
    if grain.0 != 0 {
        return Err(ResidentRefusal::Declaration { operation, what: format!("the native atlas words are integers: grain 2^0 is declared, not 2^-{}", grain.0) });
    }
    Ok(())
}

/// **The walk**: several prompts' germs carried from the root, one warp per prompt. Species:
/// construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AthenaWalk {
    pub arrays: AthenaArrays,
    /// The concatenated prompt germ indices, mounted as a `u32` array under this name
    /// (`vocabulary` and above marks an unseen germ).
    pub prompt: String,
    /// The prompt boundaries: `prompts + 1` offsets into `prompt`, mounted as a `u32` array.
    pub offsets: String,
    /// The apparatus geometry: how many warps one block carries, so the grid is
    /// `ceil(prompts / warps)`. Never semantic.
    pub geometry: AthenaWalkGeometry,
}

impl AthenaWalk {
    fn prompts(&self, material: &ResidentMaterial<'_>) -> usize {
        material.arrays.get(&self.offsets).map(|offsets| offsets.rows().saturating_sub(1)).unwrap_or(0)
    }
}

impl ResidentLaw for AthenaWalk {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let mut parameters = self.arrays.shapes_entailed(validation, "athena-walk", false)?;
        parameters.push(declared(validation, "athena-walk", WALK_LAW)?);
        Ok(LawEntailment { law: "athena-walk", parameters, naming_slices: vec![WALK_LAW.to_owned()] })
    }
    fn name(&self) -> &'static str {
        "athena-walk"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Construction
    }
    fn arity(&self) -> (usize, usize) {
        (0, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        self.arrays.present(material, false)?;
        for name in [&self.prompt, &self.offsets] {
            if !material.arrays.contains_key(name) {
                return Err(name.clone());
            }
        }
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, _inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        33 // a class index or a mark, below 2^32, at grain 2^0
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, grain: ResidentGrain, _inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        integer_grain("athena-walk", grain)?;
        let positions = material.arrays[&self.prompt].rows();
        surface.shape_athena_walk(positions, self.prompts(material), self.arrays.classes, self.arrays.transitions, self.geometry)
    }
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        let mut out = self.arrays.ranges(material, false);
        out.push(material.arrays[&self.prompt].range());
        out.push(material.arrays[&self.offsets].range());
        out
    }
    fn record<'chart>(
        &self,
        surface: &ResidentSurface<'chart>,
        lane: &Lane<'_, 'chart>,
        _inputs: &[&ResidentSection<'chart>],
        material: &ResidentMaterial<'chart>,
        _staged: &BTreeMap<String, StagedWords<'chart>>,
        _shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let array = |name: &String| -> &Positions<'chart> { &material.arrays[name] };
        surface.record_athena_walk(
            lane,
            array(&self.arrays.indptr),
            array(&self.arrays.germ),
            array(&self.arrays.target),
            array(&self.arrays.suffix),
            array(&self.prompt),
            array(&self.offsets),
            self.arrays.classes,
            self.arrays.vocabulary,
            self.geometry,
            out,
        )
    }
}

/// **The future section**: the standing (or the depth) of every vocabulary germ from every landed
/// class. Species: transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AthenaFuture {
    pub arrays: AthenaArrays,
    /// `false`: the standing face; `true`: the depth face.
    pub depth: bool,
    /// The apparatus geometry: positions and germ lanes per block, germs per lane, and how much of
    /// each position's suffix chain crosses into shared once. Never semantic.
    pub geometry: AthenaFutureGeometry,
}

impl AthenaFuture {
    fn law(&self) -> &'static str {
        if self.depth {
            "athena-depth"
        } else {
            "athena-future"
        }
    }
}

impl ResidentLaw for AthenaFuture {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let statement = if self.depth { DEPTH_LAW } else { FUTURE_LAW };
        let mut parameters = self.arrays.shapes_entailed(validation, self.law(), !self.depth)?;
        parameters.push(declared(validation, self.law(), statement)?);
        Ok(LawEntailment { law: self.law(), parameters, naming_slices: vec![statement.to_owned()] })
    }
    fn name(&self) -> &'static str {
        self.law()
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Transport
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        self.arrays.present(material, !self.depth)
    }
    fn bound_octaves(&self, _grain: ResidentGrain, _inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        33 // a standing below 2^32, or a depth below the class count, at grain 2^0
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        integer_grain(self.law(), grain)?;
        let (positions, width, _) = inputs.first().copied().unwrap_or((0, 0, 0));
        if width != 2 {
            return Err(ResidentRefusal::WidthDisagrees { operation: self.law(), left: width, right: 2 });
        }
        surface.shape_athena_future(positions, self.arrays.vocabulary, self.arrays.classes, self.arrays.transitions, self.depth, self.geometry)
    }
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        self.arrays.ranges(material, !self.depth)
    }
    fn record<'chart>(
        &self,
        surface: &ResidentSurface<'chart>,
        lane: &Lane<'_, 'chart>,
        inputs: &[&ResidentSection<'chart>],
        material: &ResidentMaterial<'chart>,
        _staged: &BTreeMap<String, StagedWords<'chart>>,
        _shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        // The depth face reads no standing: the value it returns is the height of the arc, so the
        // suffix array stands in for the standing pointer and the kernel never dereferences it.
        let standing = if self.depth { &material.arrays[&self.arrays.suffix] } else { &material.arrays[&self.arrays.standing] };
        surface.record_athena_future(
            lane,
            &material.arrays[&self.arrays.indptr],
            &material.arrays[&self.arrays.germ],
            &material.arrays[&self.arrays.target],
            standing,
            &material.arrays[&self.arrays.suffix],
            inputs[0],
            self.arrays.classes,
            self.arrays.vocabulary,
            self.depth,
            self.geometry,
            out,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ported_operation::OperationSpecies;
    use crate::resident_section::AthenaFutureGeometry;

    fn arrays() -> AthenaArrays {
        AthenaArrays {
            indptr: "athena.transport.indptr".to_owned(),
            germ: "athena.transport.germ".to_owned(),
            target: "athena.transport.target".to_owned(),
            standing: "athena.class.standing".to_owned(),
            suffix: "athena.class.suffix".to_owned(),
            classes: 4,
            transitions: 6,
            vocabulary: 3,
        }
    }

    fn validation(shapes: &[(&str, &[usize])], descriptions: &[&str]) -> BindingValidation {
        BindingValidation {
            operation: "athena walk".to_owned(),
            species: OperationSpecies::Construction,
            symbols: Vec::new(),
            fields: Vec::new(),
            shapes: shapes.iter().map(|(p, s)| ((*p).to_owned(), s.to_vec())).collect(),
            interventions: Vec::new(),
            descriptions: descriptions.iter().map(|d| (*d).to_owned()).collect(),
        }
    }

    fn walk() -> AthenaWalk {
        AthenaWalk {
            arrays: arrays(),
            prompt: "prompt.germs".to_owned(),
            offsets: "prompt.offsets".to_owned(),
            geometry: crate::resident_section::AthenaWalkGeometry { warps: 1 },
        }
    }

    #[test]
    fn a_native_law_binds_only_when_the_rest_declares_it_and_identifies_every_population() {
        let complete: Vec<(&str, &[usize])> = vec![
            ("athena.transport.indptr", &[5, 1]),
            ("athena.transport.germ", &[6, 1]),
            ("athena.transport.target", &[6, 1]),
            ("athena.class.suffix", &[4, 1]),
        ];
        let entailed = walk().entailment(&validation(&complete, &[WALK_LAW])).expect("the rest declares the walk");
        assert_eq!(entailed.law, "athena-walk");
        // four populations plus the rest's own statement of the law
        assert_eq!(entailed.parameters.len(), 5);
        assert_eq!(entailed.naming_slices, vec![WALK_LAW.to_owned()]);

        // **An unrelated statement does not authenticate this law.** This is the native twin of a
        // valid but unrelated implementation slice refusing to authenticate a foreign binding.
        assert!(walk().entailment(&validation(&complete, &[FUTURE_LAW])).is_err());
        assert!(walk().entailment(&validation(&complete, &[])).is_err());
        // and a declared shape that disagrees with the law's own extents refuses by parameter
        let drifted: Vec<(&str, &[usize])> = vec![
            ("athena.transport.indptr", &[4, 1]),
            ("athena.transport.germ", &[6, 1]),
            ("athena.transport.target", &[6, 1]),
            ("athena.class.suffix", &[4, 1]),
        ];
        assert!(walk().entailment(&validation(&drifted, &[WALK_LAW])).is_err());
    }

    #[test]
    fn the_future_face_needs_the_standing_and_the_depth_face_does_not() {
        let geometry = AthenaFutureGeometry { positions_per_block: 1, lanes: 32, germs_per_lane: 1, chain_stage: 0 };
        let without_standing: Vec<(&str, &[usize])> = vec![
            ("athena.transport.indptr", &[5, 1]),
            ("athena.transport.germ", &[6, 1]),
            ("athena.transport.target", &[6, 1]),
            ("athena.class.suffix", &[4, 1]),
        ];
        let mut with_standing = without_standing.clone();
        with_standing.push(("athena.class.standing", &[4, 1]));

        let standing_face = AthenaFuture { arrays: arrays(), depth: false, geometry };
        let depth_face = AthenaFuture { arrays: arrays(), depth: true, geometry };
        assert_eq!(standing_face.name(), "athena-future");
        assert_eq!(depth_face.name(), "athena-depth");
        assert_eq!(standing_face.species(), OperationSpecies::Transport);
        assert_eq!(standing_face.arity(), (1, 1));

        assert!(standing_face.entailment(&validation(&with_standing, &[FUTURE_LAW])).is_ok());
        // the standing face without the standing population is unentailed, by name
        assert!(standing_face.entailment(&validation(&without_standing, &[FUTURE_LAW])).is_err());
        // the depth face returns the height of the arc and reads no standing at all
        assert!(depth_face.entailment(&validation(&without_standing, &[DEPTH_LAW])).is_ok());
        // and neither face is authenticated by the other's statement
        assert!(depth_face.entailment(&validation(&with_standing, &[FUTURE_LAW])).is_err());
        assert!(standing_face.entailment(&validation(&with_standing, &[DEPTH_LAW])).is_err());
    }

    #[test]
    fn the_native_laws_refuse_any_grain_but_the_integer_one() {
        assert!(integer_grain("athena-walk", ResidentGrain(0)).is_ok());
        assert!(integer_grain("athena-walk", ResidentGrain(20)).is_err());
        assert!(integer_grain("athena-future", ResidentGrain(48)).is_err());
    }
}
