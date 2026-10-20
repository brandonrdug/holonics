//! Shared signed physical action at the Word's actual fixed operands (Refs #63 #62).
//!
//! The existing source-completion and charted-center consumers keep their admission and
//! receipt contracts. MaterialTangent also consumes the contact variation owner's exact
//! quadratic admission. This library preparation neither admits an Alpha span nor certifies
//! affine parity, and carries no persistent state.
//!
//! The element, resonator and transit owners still execute the same operations. A future
//! span owner must bind fixed material, actual pump ticks and every domain/prefix check;
//! moving these functions does not establish that contract.

use crate::hnn::HnnError;

/// Signed junction and full tick of the admitted linear relation. The native element,
/// resonator and contact owners supply the images at the actual pump tick. In particular, the
/// rate, displacement, velocity and arriving waves remain correlated with their source label.
pub(crate) fn junctions(
    operands: &crate::hnn::propagation::Operands,
    state: &crate::hnn::word::EndChange,
) -> Result<Vec<crate::hnn::propagation::Junction>, HnnError> {
    (0..operands.rings().len())
        .map(|ring| {
            let incoming: Vec<_> = operands
                .incident(ring)
                .iter()
                .map(|&a| state.arrivals[a][operands.end_slot(a, ring)].as_slice())
                .collect();
            let anchor = crate::hnn::propagation::participation(
                operands.weights(ring),
                &state.storage[ring],
                &incoming,
            )?;
            Ok(crate::hnn::propagation::scattering_about(
                anchor,
                &state.storage[ring],
                &incoming,
            ))
        })
        .collect()
}

pub(crate) fn tick(
    operands: &crate::hnn::propagation::Operands,
    state: &crate::hnn::word::EndChange,
    tick: usize,
) -> Result<crate::hnn::word::EndChange, HnnError> {
    let junctions = junctions(operands, state)?;
    let mut next = state.clone();
    for (ring, junction) in junctions.iter().enumerate() {
        let drive = crate::hnn::propagation::element_step(
            &operands.rings()[ring],
            &junction.storage_wave,
            &junction.contrast,
        )?
        .next;
        if let Some(resonator) = &operands.resonators()[ring] {
            let local = state.resonators[ring]
                .as_ref()
                .ok_or(HnnError::ContinuingState {
                    what: "the affine completion needs the full producing resonator state",
                })?;
            let driven = resonator.step(
                tick,
                &drive,
                [&local[0], &local[1]],
                &crate::hnn::ring::ResonatorRemainders::default(),
                None,
            )?;
            next.storage[ring] = driven.output;
            next.resonators[ring] = Some(driven.state);
            next.resonator_phases[ring] = Some(resonator.phase_at(tick));
        } else {
            next.storage[ring] = drive;
        }
    }
    for (a, contact) in operands.contacts().iter().enumerate() {
        let (from, to) = contact.ends();
        let outgoing = |ring: usize| {
            &junctions[ring].outgoing[operands
                .incident(ring)
                .iter()
                .position(|&index| index == a)
                .unwrap()]
        };
        let passed = crate::hnn::propagation::transit(
            contact,
            operands.step(),
            outgoing(from),
            outgoing(to),
            &state.states[a][0],
            &state.states[a][1],
        )?;
        next.arrivals[a] = [passed.arrive_from, passed.arrive_to];
        next.states[a] = [passed.displacement, passed.rate];
    }
    Ok(next)
}
