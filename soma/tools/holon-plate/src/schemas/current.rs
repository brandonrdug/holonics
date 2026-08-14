//! `ERST` — one direct-production body at a receiving-edge rest.
//!
//! Owner: `soma/membrane/src/live_current.rs:1241` (`encode_native_words`), `:1540`
//! (`encode_native_bytes`), `:1558` (`from_native_bytes`). Its docstring at `:1240` states the
//! boundary in one sentence: *"This is a persistence boundary, never input light."*
//!
//! This schema is the sharpest illustration of what the plate does and does not deposit, because
//! its own codec already draws the line. `LiveCurrentMachine::rest_image` (`:3758`) refuses to
//! close over an **attached seed** — a lineage that has been opened and has not yet crossed its
//! first event — with `UnsettledRest`. An open ingress is a current in flight, and a current in
//! flight is exactly the thing that cannot be deposited. The codec refuses; the plate inherits
//! the refusal rather than restating it.
//!
//! `from_native_bytes` at `:1569` closes by calling `LiveCurrentMachine::from_rest_image(image)?`
//! and re-taking the image from that machine. Reopening this form therefore already goes through a
//! real machine before an image exists; there is no path here that reads a body out of octets
//! without mounting it.
//!
//! The further deed is one **contemporary event** continuing every live lineage against the same
//! standing-before surface — the machine's own whole transition, not a synthetic poke.

use body::num::Cog;
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentEvent, CurrentGeometry, LiveCurrentMachine, LiveCurrentRestImage,
    LIVE_CURRENT_REST_LAYOUT_VERSION,
};

use crate::census::Census;
use crate::deed::{deed_head, open_deed, put_i64, Cursor};
use crate::plate::SchemaTag;
use crate::schema::{LitBody, PlateSchema};

/// `ERST`, the form codec's own native magic read as ASCII (`0x4552_5354`).
pub const CURRENT_TAG: SchemaTag = match SchemaTag::new(*b"ERST") {
    Some(tag) => tag,
    None => panic!("ERST is four octets of [A-Z0-9]"),
};

/// The codec's own layout version, taken from the codec rather than copied. If the membrane bumps
/// its rest layout, this reader stops holding the old plates and says so by version.
pub const CURRENT_SCHEMA_VERSION: u32 = LIVE_CURRENT_REST_LAYOUT_VERSION;

pub struct CurrentSchema;

pub static CURRENT_SCHEMA: CurrentSchema = CurrentSchema;

impl PlateSchema for CurrentSchema {
    fn tag(&self) -> SchemaTag {
        CURRENT_TAG
    }

    fn version(&self) -> u32 {
        CURRENT_SCHEMA_VERSION
    }

    fn shape(&self) -> &'static str {
        "live-current rest form: the standing surface with its constituents, and every settled \
         lineage's canonical carrier wire; no source event, radiation, contact, receipt, or \
         provenance, and no attached seed -- an open ingress cannot rest"
    }

    fn deed_shape(&self) -> &'static str {
        "one contemporary event continuing every settled lineage:\n    \
         i64 relation   (the material relation atom; zero is allowed -- sameness is material)\n    \
         i64 action     (the resolving action current; zero is the ABSENCE of an action \
         and refuses)"
    }

    fn relight(&self, form: &[u8]) -> Result<Box<dyn LitBody>, String> {
        // `from_native_bytes` itself closes by remounting through a real machine, so this is the
        // second of two mounts and neither of them reads a body out of octets directly.
        let image = LiveCurrentRestImage::from_native_bytes(form).map_err(debug)?;
        let machine = LiveCurrentMachine::from_rest_image(image).map_err(debug)?;
        Ok(Box::new(CurrentBody { machine }))
    }
}

struct CurrentBody {
    machine: LiveCurrentMachine,
}

impl LitBody for CurrentBody {
    fn form(&self) -> Result<Vec<u8>, String> {
        self.machine
            .rest_image()
            .map_err(debug)?
            .encode_native_bytes()
            .map_err(debug)
    }

    fn census(&self) -> Result<Census, String> {
        let image = self.machine.rest_image().map_err(debug)?;
        let carrier_words: usize = image
            .lineages()
            .iter()
            .map(|lineage| lineage.native_carrier_words().len())
            .sum();
        // The receiving-edge position of every settled lineage, summed. This is a coordinate of
        // the live carriers -- it is inside the deposited carrier wire and the membrane reads it
        // back out with `lineage_cursor` -- and not a tally the plate keeps for itself. It is here
        // because `carrier_words` does NOT move on an event: a depth-one carrier holds its extent
        // and advances within it, so an extent alone cannot witness that a body received anything.
        let mut carrier_cursors = 0u64;
        for lineage in image.lineages() {
            let cursor = self
                .machine
                .lineage_cursor(lineage.lineage())
                .ok_or_else(|| "a settled lineage has no receiving-edge cursor".to_owned())?;
            carrier_cursors = carrier_cursors
                .checked_add(cursor)
                .ok_or_else(|| "the summed receiving edge does not fit its carrier".to_owned())?;
        }
        Census::found([
            ("standing_rank", image.standing().rank()),
            ("standing_cells", image.standing().cells().len() as u64),
            (
                "standing_constituents",
                image.standing().constituents().len() as u64,
            ),
            ("lineages", image.lineages().len() as u64),
            ("next_lineage", image.next_lineage()),
            ("carrier_words", carrier_words as u64),
            ("carrier_cursors", carrier_cursors),
        ])
        .map_err(|refusal| refusal.to_string())
    }

    fn present(&mut self, deed: &[u8]) -> Result<(), String> {
        let event = CurrentDeed::decode(deed)?;
        // A relation atom may be zero -- sameness is material -- so only a non-canonical packing
        // refuses here. An action current may not: zero is the absence of an event action rather
        // than a second spelling of one, and `ActionCurrent::new` refuses it at the abi.
        let relation = RelationAtom::new(Cog::lit(event.relation))
            .ok_or_else(|| "the deed's relation word is not a canonical cog".to_owned())?;
        let action = ActionCurrent::new(Cog::lit(event.action)).ok_or_else(|| {
            "zero is the absence of an event action, not an action; this deed carries no current"
                .to_owned()
        })?;

        let image = self.machine.rest_image().map_err(debug)?;
        if image.lineages().is_empty() {
            return Err(
                "this body carries no settled lineage, so there is nothing for a contemporary \
                 event to continue"
                    .to_owned(),
            );
        }
        let currents: Vec<CurrentEvent<'static>> = image
            .lineages()
            .iter()
            .map(|lineage| {
                CurrentEvent::continuing(lineage.lineage(), CurrentGeometry::Cell(relation), action)
            })
            .collect();
        self.machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
        Ok(())
    }
}

/// One further deed for a live current body, in its exact wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CurrentDeed {
    pub relation: i64,
    pub action: i64,
}

impl CurrentDeed {
    pub fn encode(&self) -> Vec<u8> {
        let mut octets = deed_head(CURRENT_TAG);
        put_i64(&mut octets, self.relation);
        put_i64(&mut octets, self.action);
        octets
    }

    pub fn decode(deed: &[u8]) -> Result<Self, String> {
        let mut cursor: Cursor<'_> = open_deed(deed, CURRENT_TAG)?;
        let relation = cursor.i64()?;
        let action = cursor.i64()?;
        cursor.finish()?;
        Ok(Self { relation, action })
    }
}

fn debug(error: impl core::fmt::Debug) -> String {
    format!("{error:?}")
}
