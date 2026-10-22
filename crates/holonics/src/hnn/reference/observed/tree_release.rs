//! Executed-tree keyed control of the native aperture-one release (Refs #73 #148 #386).
//!
//! [definition; agent-inferred] The tree control draws the same caller-declared key from the
//! actual trained tree at its producing pending address, using `receiver::release::draw_exact`.
//! Its emitted class is received by that tree before the next face is read. The ordinary native
//! combined release and its authentication guard remain unchanged: no tree decision is presented
//! as a native `ScoredFaceReading`, and no zero wave or replacement receiving map is fabricated.
//!
//! On the caller's private fork only, `observed_epoch_prefix(receiver, tree, &[])` installs the
//! received tree; the empty receiving-step list deliberately leaves the irrelevant two-family
//! mixture population unchanged. A pure-tree control has no mixture Bayesian update. The shared
//! ingress owner then advances the actual source, address, clock, carry and closing crib. This
//! local self-reception is not a material-map deposit and never teaches a retained main resident.
//! The caller owns fork isolation, the shared initial key stream and the declared output length.
//!
//! Current/commit/moment, one producing pending, its kept read, aperture and addressed tree are
//! authenticated before a key is read. All fallible reception/ingress runs on staged copies;
//! any error leaves resident, crib and key stream unchanged. Key exhaustion or an unresolved
//! draw returns its native decision, emits nothing and keeps the pending operand. A consumed
//! unresolved key is reported and advanced exactly once, as in the native draw owner.
//!
//! This consumer reads faces and placement of the helical pair interaction. The helix, pair,
//! cell holonomy, tube and tower thread remain with the pending word and shared ingress. The
//! lessons' authored answer/control substitution is avoided by using the actual tree and its
//! exact draw/receive owners. It supplies no EOS, joint-mode or learned-generation claim.

use super::*;
use crate::compression::landmark::context::LandmarkFace;
use crate::receiver::release::{KeyStream, ReleaseReturn, draw_exact};

/// Exterior receipt of the executed tree's actual draw and optional native ingress. A successful
/// ingress consumed the producing pending operand; no live pending handle is retained here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeReleaseReceipt {
    pub tree: LandmarkFace,
    pub key: Option<(usize, Rat)>,
    pub release: ReleaseReturn,
    pub ingestion: Option<IngestClassReceipt>,
}

impl TreeReleaseReceipt {
    pub fn class(&self) -> Option<usize> {
        self.release.drawn_class()
    }
}

impl Reference {
    /// Draw and locally receive one actual executed-tree control cell, then consume it through
    /// the ordinary observed ingress. This is intentionally separate from the combined-face
    /// `ingest_released_cell_continuing` guard. The caller supplies a private release fork.
    #[allow(clippy::too_many_arguments)]
    pub fn release_tree_cell_continuing(
        &self,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        pending: PendingId,
        keys: &mut KeyStream,
        placement: Option<&OccurrencePlacement>,
    ) -> Result<TreeReleaseReceipt, HnnError> {
        let refuse = |reason| HnnError::Unadmitted { reason };
        resident.admit_exact_current()?;
        if resident.pending.len() != 1 || !resident.staged.is_empty() || resident.moments.len() != 1
        {
            return Err(refuse(
                "a tree release consumes one producing pending and one actual source moment",
            ));
        }
        let slot = resident
            .pending
            .get(&pending)
            .ok_or(HnnError::UnknownHandle {
                handle: Handle::Pending(pending),
            })?;
        let phases = slot.ratio.phases();
        let receiver = phases.ring();
        if phases.aperture() != 1 {
            return Err(refuse(
                "an executed-tree continuation reads one admitted receiving phase",
            ));
        }
        let kept = slot
            .kept
            .as_ref()
            .ok_or_else(|| refuse("a tree release keeps its actual producing native read"))?;
        if kept.commit != resident.constitution.commit()
            || slot.ratio.commit() != resident.constitution.commit()
            || slot.ratio.current(&resident.field)? != resident.current
            || resident.moments.values().next() != Some(slot.ratio.moment())
        {
            return Err(refuse(
                "a tree release continues its producing material, current and source moment",
            ));
        }
        let trees = slot.ratio.tree_faces(&resident.constitution, &[])?;
        let [tree_face] = trees.as_slice() else {
            return Err(refuse(
                "one actual addressed tree face belongs to the pending tree release",
            ));
        };
        let mut next_keys = keys.clone();
        let index = next_keys.keys_read();
        let Some(key) = next_keys.next_key() else {
            return Ok(TreeReleaseReceipt {
                tree: tree_face.clone(),
                key: None,
                release: ReleaseReturn::NoContinuationBridges {
                    reason: "the declared key stream has no key left".to_owned(),
                },
                ingestion: None,
            });
        };
        let release = draw_exact(&tree_face.probabilities, &key).map_err(|_| {
            refuse("the executed tree draw requires its exact normalized face and declared key")
        })?;
        let Some(class) = release.drawn_class() else {
            let receipt = TreeReleaseReceipt {
                tree: tree_face.clone(),
                key: Some((index, key)),
                release,
                ingestion: None,
            };
            *keys = next_keys;
            return Ok(receipt);
        };
        // This includes class/placement/horizon, crib endpoint and source admission. Nothing
        // from the cloned key stream has been published if a declared operand refuses here.
        admit_observed_cell(resident, crib, pairing, class, placement)?;
        let mut tree = resident
            .constitution
            .landmarks(receiver)
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?
            .clone();
        let received = match slot.ratio.observed_addresses(&[])? {
            Some(addresses) => {
                tree.receive_observed_arrivals(&addresses, &[class], phases.grain())?
            }
            None => tree.receive_arrivals(&slot.ratio.addresses(&[])?, &[class], phases.grain())?,
        };
        if received.as_slice() != trees.as_slice() {
            return Err(refuse(
                "the tree draw and local reception share the actual producing address and face",
            ));
        }
        let tree_face = tree_face.clone();
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        // No two-family likelihood is received on a pure executed-tree control.
        next.constitution = next
            .constitution
            .observed_epoch_prefix(receiver, tree, &[])?;
        self.discard(&mut next, Handle::Pending(pending))?;
        let ingestion =
            self.ingest_class_step(&mut next, &mut next_crib, pairing, class, placement)?;
        *resident = next;
        *crib = next_crib;
        *keys = next_keys;
        Ok(TreeReleaseReceipt {
            tree: tree_face,
            key: Some((index, key)),
            release,
            ingestion: Some(ingestion),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::paired::PairedCarrier;
    use crate::hnn::tests::support::{contact, small_field_of};

    fn opening(
        before_carry: bool,
    ) -> (
        Reference,
        Resident,
        ObservedCrib,
        PairingDeclaration,
        Constitution,
    ) {
        let base = small_field_of(
            &[5, 2, 3],
            vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
            2,
            4,
        );
        let mut declaration = base.declaration().clone();
        declaration.receivers[0].aperture = 1;
        declaration.rings[0].lock = (0..4).collect();
        for ring in &mut declaration.rings[1..] {
            ring.lock.clear();
        }
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: (0..4).map(|class| (class, class ^ 1)).collect(),
        };
        let material = PairedCarrier::found(
            &field,
            Constitution::initial(&field, 1 << 40).unwrap(),
            0,
            &pairing,
        )
        .unwrap()
        .0;
        let reference = Reference::new(16, 1 << 40);
        let current = if before_carry {
            Current::at(
                &field,
                field
                    .rings()
                    .iter()
                    .map(|ring| BigInt::from(ring.period() - 1))
                    .collect(),
            )
            .unwrap()
        } else {
            Current::at_rest(&field)
        };
        let mut resident = reference
            .mount_with(&field, &current, material.clone())
            .unwrap();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        (reference, resident, ObservedCrib::new(0), pairing, material)
    }

    fn pending(port: &Reference, resident: &mut Resident) -> PendingId {
        let moment = resident.continuing().unwrap().0;
        let phases = resident.admitted[0].clone();
        port.refine(resident, &moment, &phases).unwrap().0
    }

    fn step(
        port: &Reference,
        resident: &mut Resident,
        crib: &mut ObservedCrib,
        pairing: &PairingDeclaration,
        keys: &mut KeyStream,
    ) -> TreeReleaseReceipt {
        let pending = pending(port, resident);
        port.release_tree_cell_continuing(resident, crib, pairing, pending, keys, None)
            .unwrap()
    }

    #[test]
    fn tree_keyed_control_draws_actual_faces_and_receives_its_own_classes_only() {
        let (port, mut resident, mut crib, pairing, _) = opening(false);
        let trunk = resident.clone();
        let receiver = resident.admitted[0].ring();
        let population = resident.constitution.population(receiver).unwrap().clone();
        let map = resident
            .constitution
            .receiving_map(receiver)
            .unwrap()
            .clone();
        let mut keys = KeyStream::new(vec![0x31, 0x97, 0xe4, 0x02], 1).unwrap();
        for index in 0..4 {
            let id = pending(&port, &mut resident);
            let slot = &resident.pending[&id];
            let actual = slot.ratio.tree_faces(&resident.constitution, &[]).unwrap()[0].clone();
            let address = slot.ratio.addresses(&[]).unwrap();
            let mut expected_tree = resident.constitution.landmarks(receiver).unwrap().clone();
            let mut expected_keys = keys.clone();
            let key = expected_keys.next_key().unwrap();
            let expected_draw = draw_exact(&actual.probabilities, &key).unwrap();
            let class = expected_draw.drawn_class().unwrap();
            expected_tree.receive(&address[0], class).unwrap();
            let result = port
                .release_tree_cell_continuing(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    id,
                    &mut keys,
                    None,
                )
                .unwrap();
            assert_eq!(result.tree, actual);
            assert_eq!(result.key, Some((index, key)));
            assert_eq!(result.release, expected_draw);
            assert!(result.ingestion.is_some());
            assert!(resident.pending.is_empty());
            assert_eq!(
                resident.constitution.landmarks(receiver),
                Some(&expected_tree)
            );
            assert_eq!(
                resident.constitution.population(receiver),
                Some(&population)
            );
            assert_eq!(resident.constitution.receiving_map(receiver), Some(&map));
            assert_eq!(resident.constitution.commit(), trunk.constitution.commit());
            assert_eq!(keys, expected_keys);
        }
        assert_eq!(keys.keys_read(), 4);
        assert_eq!(trunk.constitution.population(receiver), Some(&population));
        assert_eq!(trunk.moments.values().next().unwrap().cells(), 0);
    }

    #[test]
    fn tree_keyed_control_cold_continuation_releases_identically_from_the_saved_key_cursor() {
        let (port, mut warm, mut warm_crib, pairing, material) = opening(false);
        let bytes = vec![0x10, 0xa0, 0xf0, 0x70, 0x30];
        let mut warm_keys = KeyStream::new(bytes.clone(), 1).unwrap();
        step(&port, &mut warm, &mut warm_crib, &pairing, &mut warm_keys);
        step(&port, &mut warm, &mut warm_crib, &pairing, &mut warm_keys);
        let state = warm.continuing_state(0).unwrap();
        let parsed = ContinuingState::from_text(&state.to_text(), 1 << 40).unwrap();
        let field = warm.field.clone();
        let mut cold = port
            .mount_continued(&field, &Current::at_rest(&field), material, &parsed)
            .unwrap();
        let crib_text = warm_crib.unplaced_checkpoint().unwrap();
        let mut cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            cold.current(),
            warm_crib.next_position(),
            &crib_text,
        )
        .unwrap();
        let mut cold_keys = KeyStream::new(bytes, 1).unwrap();
        for _ in 0..warm_keys.keys_read() {
            cold_keys.next_key().unwrap();
        }
        assert_eq!(warm_keys, cold_keys);
        for _ in 0..3 {
            let a = step(&port, &mut warm, &mut warm_crib, &pairing, &mut warm_keys);
            let b = step(&port, &mut cold, &mut cold_crib, &pairing, &mut cold_keys);
            assert_eq!((&a.tree, &a.key, &a.release), (&b.tree, &b.key, &b.release));
            assert_eq!(a.class(), b.class());
            assert_eq!(warm_keys, cold_keys);
            assert_eq!(warm_crib, cold_crib);
            assert_eq!(
                warm.continuing_state(0).unwrap().to_text(),
                cold.continuing_state(0).unwrap().to_text()
            );
        }
    }

    #[test]
    fn tree_keyed_control_key_exhaustion_emits_nothing_and_keeps_the_pending() {
        let (port, mut resident, mut crib, pairing, _) = opening(false);
        let id = pending(&port, &mut resident);
        let before = format!("{resident:?}");
        let old_crib = crib.clone();
        let mut keys = KeyStream::new(Vec::new(), 1).unwrap();
        let old_keys = keys.clone();
        let result = port
            .release_tree_cell_continuing(&mut resident, &mut crib, &pairing, id, &mut keys, None)
            .unwrap();
        assert!(matches!(
            result.release,
            ReleaseReturn::NoContinuationBridges { .. }
        ));
        assert_eq!(result.class(), None);
        assert!(result.ingestion.is_none());
        assert_eq!(format!("{resident:?}"), before);
        assert_eq!(crib, old_crib);
        assert_eq!(keys, old_keys);
    }

    #[test]
    fn tree_keyed_control_authentication_refusals_are_atomic_including_keys() {
        for defect in 0..4 {
            let (port, mut resident, mut crib, pairing, _) = opening(false);
            let id = pending(&port, &mut resident);
            match defect {
                0 => {
                    resident
                        .pending
                        .get_mut(&id)
                        .unwrap()
                        .kept
                        .as_mut()
                        .unwrap()
                        .commit += 1;
                }
                1 => {
                    pending(&port, &mut resident);
                }
                2 => {
                    crib = ObservedCrib::new(1);
                }
                _ => {
                    resident.current.rekey(&resident.field, 0, 1).unwrap();
                }
            }
            let before = format!("{resident:?}");
            let old_crib = crib.clone();
            let mut keys = KeyStream::new(vec![0x45], 1).unwrap();
            let old_keys = keys.clone();
            assert!(
                port.release_tree_cell_continuing(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    id,
                    &mut keys,
                    None
                )
                .is_err()
            );
            assert_eq!(format!("{resident:?}"), before);
            assert_eq!(crib, old_crib);
            assert_eq!(keys, old_keys);
        }
    }

    #[test]
    fn tree_keyed_control_late_close_refusal_rolls_back_tree_clock_crib_and_key() {
        let (port, mut resident, mut crib, pairing, _) = opening(true);
        let id = pending(&port, &mut resident);
        crib.entries.push(ObservedCribCell {
            position: 0,
            class: resident.field.alphabet(),
            placement: None,
        });
        let before = format!("{resident:?}");
        let old_crib = crib.clone();
        let mut keys = KeyStream::new(vec![0x22], 1).unwrap();
        let old_keys = keys.clone();
        assert!(
            port.release_tree_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                id,
                &mut keys,
                None
            )
            .is_err()
        );
        assert_eq!(format!("{resident:?}"), before);
        assert_eq!(crib, old_crib);
        assert_eq!(keys, old_keys);
    }
}
