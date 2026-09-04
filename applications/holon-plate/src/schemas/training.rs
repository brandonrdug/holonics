//! `HTEC` — the training ecology's form.
//!
//! Owner: `crates/holonic-life/src/holonic_training.rs:443` (`encode_native_bytes`) and `:494`
//! (`decode_native_bytes`). Its own docstring states the boundary this plate inherits: the
//! encoding *"carries only the current recurrent route population and its local receiver faces.
//! It contains no source occurrence, consequence log, prediction cache, hash identity, or
//! wall-clock field."*
//!
//! That is the whole reason this schema is the right first one to hold. The plate cannot leak a
//! source population it was never given, and the sentence above is checkable against the codec
//! rather than asserted here.
//!
//! The further deed for this schema is one **cultivation occurrence** — co-present source faces, a
//! receiver-parameter binding, and the actual consequence. A body that takes one and does not move
//! is refused upstream by `present_and_require_change`.

use std::collections::BTreeMap;

use life::holonic_training::{FaceAddress, SourceFace, TrainingEcology};

use crate::census::Census;
use crate::deed::{deed_head, open_deed, put_bytes, put_u64, Cursor};
use crate::plate::SchemaTag;
use crate::schema::{LitBody, PlateSchema};

/// `HTEC`, the leading octets of the form codec's own wire.
pub const TRAINING_TAG: SchemaTag = match SchemaTag::new(*b"HTEC") {
    Some(tag) => tag,
    None => panic!("HTEC is four octets of [A-Z0-9]"),
};

/// The codec's own layout version, the `\x02` in its `b"HTEC\0\0\0\x02"` prefix.
///
/// Raised from `1` on 2026-08-16 when the training ecology began carrying its two-sided standing —
/// per fiber, the confirmations and refutations that decide admission by quotient closure. A rest
/// sealed at version `1` carries no refutation evidence, and reading it as "never refuted" would
/// admit every fiber it holds, so the codec refuses it by name rather than defaulting.
pub const TRAINING_SCHEMA_VERSION: u32 = 2;

pub struct TrainingSchema;

pub static TRAINING_SCHEMA: TrainingSchema = TrainingSchema;

impl PlateSchema for TrainingSchema {
    fn tag(&self) -> SchemaTag {
        TRAINING_TAG
    }

    fn version(&self) -> u32 {
        TRAINING_SCHEMA_VERSION
    }

    fn shape(&self) -> &'static str {
        "training-ecology form: the recurrent transduction-fiber population with its local \
         receiver axes; no source occurrence, no consequence log, no prediction cache, no \
         wall-clock field"
    }

    fn deed_shape(&self) -> &'static str {
        "one cultivation occurrence:\n    \
         u64 faces, each { u64 axis_octets, axis, u64 ordinal, u64 value_octets, value }\n    \
         u64 parameters, each { u64 name_octets, name, u64 value_octets, value }\n    \
         u64 consequence_octets, consequence"
    }

    fn relight(&self, form: &[u8]) -> Result<Box<dyn LitBody>, String> {
        // The codec's own decode revalidates the whole ecology before returning it; a form that
        // does not close does not become a body.
        let ecology = TrainingEcology::decode_native_bytes(form)?;
        Ok(Box::new(TrainingBody { ecology }))
    }
}

struct TrainingBody {
    ecology: TrainingEcology,
}

impl LitBody for TrainingBody {
    fn form(&self) -> Result<Vec<u8>, String> {
        self.ecology.encode_native_bytes()
    }

    fn census(&self) -> Result<Census, String> {
        Census::found([
            ("generation", self.ecology.generation),
            ("minimum_recurrence", self.ecology.minimum_recurrence),
            (
                "route_aperture",
                self.ecology.maximum_templates_per_occurrence as u64,
            ),
            ("fibers", self.ecology.fibers.len() as u64),
            (
                "active_templates",
                self.ecology.active_template_count() as u64,
            ),
        ])
        .map_err(|refusal| refusal.to_string())
    }

    fn present(&mut self, deed: &[u8]) -> Result<(), String> {
        let occurrence = TrainingDeed::decode(deed)?;
        self.ecology.cultivate(
            &occurrence.faces,
            &occurrence.parameters,
            &occurrence.consequence,
        )?;
        Ok(())
    }
}

/// One further deed for a training ecology, in its exact wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrainingDeed {
    pub faces: Vec<SourceFace>,
    pub parameters: BTreeMap<String, String>,
    pub consequence: Vec<u8>,
}

impl TrainingDeed {
    pub fn encode(&self) -> Vec<u8> {
        let mut octets = deed_head(TRAINING_TAG);
        put_u64(&mut octets, self.faces.len() as u64);
        for face in &self.faces {
            put_bytes(&mut octets, face.address.axis.as_bytes());
            put_u64(&mut octets, face.address.ordinal);
            put_bytes(&mut octets, &face.value);
        }
        put_u64(&mut octets, self.parameters.len() as u64);
        for (name, value) in &self.parameters {
            put_bytes(&mut octets, name.as_bytes());
            put_bytes(&mut octets, value.as_bytes());
        }
        put_bytes(&mut octets, &self.consequence);
        octets
    }

    pub fn decode(deed: &[u8]) -> Result<Self, String> {
        let mut cursor: Cursor<'_> = open_deed(deed, TRAINING_TAG)?;
        let face_count = cursor.usize()?;
        let mut faces = Vec::new();
        for _ in 0..face_count {
            let axis = cursor.utf8("face axis")?;
            let ordinal = cursor.u64()?;
            let value = cursor.bytes()?;
            faces.push(SourceFace::new(FaceAddress::new(axis, ordinal), value));
        }
        let parameter_count = cursor.usize()?;
        let mut parameters = BTreeMap::new();
        for _ in 0..parameter_count {
            let name = cursor.utf8("receiver axis")?;
            let value = cursor.utf8("receiver value")?;
            if parameters.insert(name.clone(), value).is_some() {
                return Err(format!("the deed repeats the receiver axis `{name}`"));
            }
        }
        let consequence = cursor.bytes()?;
        cursor.finish()?;
        Ok(Self {
            faces,
            parameters,
            consequence,
        })
    }
}
