//! `CDER` — one conditioned derivation body at a rest boundary.
//!
//! Owner: `crates/holonic-life/src/conditioned_rest.rs` (`ConditionedRest::encode_native_bytes` /
//! `decode_native_bytes`). Its own docstring states the boundary this plate inherits: the form
//! carries the founded morphology and the deposited standing, and **no query and no derived
//! passage** — there is no field for one.
//!
//! That is what makes this schema worth holding. Every other form the plate carries is a body's
//! organization; this one is a body's organization *plus* the deposited material it conducts over,
//! with its own source corpus deliberately absent. A body re-lit off it derives; it cannot replay,
//! because nothing it could replay was sealed.
//!
//! The further deed is one **further whole of linguistic material** — a named source and its
//! surface. The re-lit body reads it through the engine's own `expose` and witnesses its words into
//! the morphology, so a word never witnessed founds a stem and a word already founded gains a whole
//! in its lineage. A whole that moves nothing is refused upstream by `present_and_require_change`,
//! and re-presenting a whole the body has already received is exactly that case: the recurrence is
//! across **distinct** wholes, so a repeat is not a second witness.

use life::conditioned_rest::{ConditionedRest, CONDITIONED_REST_VERSION};

use crate::census::Census;
use crate::deed::{deed_head, open_deed, put_bytes, Cursor};
use crate::plate::SchemaTag;
use crate::schema::{LitBody, PlateSchema};

/// `CDER`, the leading octets of the form codec's own wire.
pub const CONDITIONED_TAG: SchemaTag = match SchemaTag::new(*b"CDER") {
    Some(tag) => tag,
    None => panic!("CDER is four octets of [A-Z0-9]"),
};

/// The codec's own layout version, **read from the codec** rather than restated here. A copied
/// version is a claim about another crate's wire that stops being true silently.
pub const CONDITIONED_SCHEMA_VERSION: u32 = CONDITIONED_REST_VERSION;

pub struct ConditionedSchema;

pub static CONDITIONED_SCHEMA: ConditionedSchema = ConditionedSchema;

impl PlateSchema for ConditionedSchema {
    fn tag(&self) -> SchemaTag {
        CONDITIONED_TAG
    }

    fn version(&self) -> u32 {
        CONDITIONED_SCHEMA_VERSION
    }

    fn shape(&self) -> &'static str {
        "conditioned-derivation form: the founded morphology -- every stem with its identity, its \
         parent and the named wholes that witnessed it -- and the deposited standing it conducts \
         over; no query, no derived passage, no corpus surface, no wall-clock field"
    }

    fn deed_shape(&self) -> &'static str {
        "one further whole of linguistic material:\n    \
         u64 whole_octets, whole\n    \
         u64 text_octets, text"
    }

    fn relight(&self, form: &[u8]) -> Result<Box<dyn LitBody>, String> {
        // The codec's own decode re-founds the whole morphology through the engine's one public
        // seam and compares it field for field before returning; a form that does not close, and a
        // form whose founding order that seam cannot reproduce, does not become a body.
        let rest =
            ConditionedRest::decode_native_bytes(form).map_err(|refusal| refusal.to_string())?;
        Ok(Box::new(ConditionedRestBody { rest }))
    }
}

struct ConditionedRestBody {
    rest: ConditionedRest,
}

impl LitBody for ConditionedRestBody {
    fn form(&self) -> Result<Vec<u8>, String> {
        self.rest
            .encode_native_bytes()
            .map_err(|refusal| refusal.to_string())
    }

    fn census(&self) -> Result<Census, String> {
        Census::found(
            self.rest
                .census_rows()
                .map_err(|refusal| refusal.to_string())?,
        )
        .map_err(|refusal| refusal.to_string())
    }

    fn present(&mut self, deed: &[u8]) -> Result<(), String> {
        let whole = ConditionedDeed::decode(deed)?;
        self.rest.receive_whole(&whole.whole, &whole.text);
        Ok(())
    }
}

/// One further whole of linguistic material, in its exact wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionedDeed {
    /// What this whole is. It becomes the named witness on every stem the text founds, so it is
    /// lineage rather than a label.
    pub whole: String,
    /// The surface, as written. The engine's `expose` is the only reading applied to it.
    pub text: String,
}

impl ConditionedDeed {
    pub fn encode(&self) -> Vec<u8> {
        let mut octets = deed_head(CONDITIONED_TAG);
        put_bytes(&mut octets, self.whole.as_bytes());
        put_bytes(&mut octets, self.text.as_bytes());
        octets
    }

    pub fn decode(deed: &[u8]) -> Result<Self, String> {
        let mut cursor: Cursor<'_> = open_deed(deed, CONDITIONED_TAG)?;
        let whole = cursor.utf8("whole identity")?;
        let text = cursor.utf8("whole surface")?;
        cursor.finish()?;
        if whole.is_empty() {
            return Err("a further whole with no identity founds nothing nameable".to_owned());
        }
        Ok(Self { whole, text })
    }
}
