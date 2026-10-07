//! One declaring coefficient face, bound to its immutable field and actual material inputs.
//!
//! The producer is `ReceivingPhases::declare`: exact rest-basis storage -> receiving anchors,
//! before source E/pair ports and receiving R. Reuse removes only that repeated declaration.
//! Actual source opening, carried state, output reads and comparisons are separate consumers.

use super::ReceivingPhases;
use crate::hnn::HnnError;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration};
use crate::hnn::ring::ResonatorMaterial;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;

#[derive(Clone, Debug, PartialEq, Eq)]
struct RingMaterial {
    standing: Vec<Rat>,
    passive: ExactRatMatrix,
    contrast: ExactRatMatrix,
    slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    resonator: Option<ResonatorMaterial>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ContactMaterial {
    storage: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    signature: Option<Vec<bool>>,
    surface: Option<Rat>,
}

/// Exact inputs read by `Operands::exact_at_cut`, without source/receiving ports or statistics.
/// The fixed Field holds incidence, source-storage basis, steps, widths and receiving distances.
struct DeclaringMaterial {
    rings: Vec<RingMaterial>,
    contacts: Vec<ContactMaterial>,
}

impl DeclaringMaterial {
    fn read(field: &Field, material: &Constitution) -> Self {
        Self {
            rings: (0..field.rings().len())
                .map(|g| RingMaterial {
                    standing: material.standing(g).to_vec(),
                    passive: material.passive_factor(g).clone(),
                    contrast: material.contrast_port(g).clone(),
                    slices: material.slices(g).to_vec(),
                    resonator: material.ring_resonator(g).cloned(),
                })
                .collect(),
            contacts: (0..field.contacts().len())
                .map(|a| ContactMaterial {
                    storage: material.contact_storage(a).clone(),
                    stiffness: material.contact_stiffness(a).clone(),
                    dissipation: material.contact_dissipation(a).clone(),
                    signature: material
                        .contact_stiffness_signature(a)
                        .map(<[bool]>::to_vec),
                    surface: material.contact_surface_storage(a).cloned(),
                })
                .collect(),
        }
    }

    fn matches(&self, material: &Constitution) -> bool {
        self.rings.iter().enumerate().all(|(g, r)| {
            r.standing == material.standing(g)
                && r.passive == *material.passive_factor(g)
                && r.contrast == *material.contrast_port(g)
                && r.slices == material.slices(g)
                && r.resonator.as_ref() == material.ring_resonator(g)
        }) && self.contacts.iter().enumerate().all(|(a, c)| {
            c.storage == *material.contact_storage(a)
                && c.stiffness == *material.contact_stiffness(a)
                && c.dissipation == *material.contact_dissipation(a)
                && c.signature.as_deref() == material.contact_stiffness_signature(a)
                && c.surface.as_ref() == material.contact_surface_storage(a)
        })
    }
}

struct Declared {
    material: DeclaringMaterial,
    current: Current,
    receiver: ReceiverDeclaration,
    phases: ReceivingPhases,
}

/// One successful declaring face. Its field cannot change while it is borrowed; its material,
/// lift and full receiver declaration are compared exactly at each use. No update label or
/// commit counter substitutes for equality. This holds no source, Word, carry, target or covector.
pub(crate) struct DeclaringFace<'f> {
    field: &'f Field,
    declared: Option<Declared>,
}

impl<'f> DeclaringFace<'f> {
    pub(crate) fn new(field: &'f Field) -> Self {
        Self {
            field,
            declared: None,
        }
    }

    /// `O = col_c v_R(e_j; storage=e_c, opened_at=0)` and its rank/scope are unchanged when
    /// these producing inputs agree. E/pair/R are absent from O, but remain actual inputs to
    /// the separate source/receiving law. The bool is this coefficient-read receipt, not a
    /// count of native Words or evidence of faster/useful communication.
    pub(crate) fn declare(
        &mut self,
        material: &Constitution,
        current: &Current,
        receiver: &ReceiverDeclaration,
    ) -> Result<(ReceivingPhases, bool), HnnError> {
        if let Some(saved) = &self.declared {
            if saved.current == *current
                && saved.receiver == *receiver
                && saved.material.matches(material)
            {
                return Ok((saved.phases.clone(), true));
            }
        }
        // Invalidate before the original constructor: a failed new declaration never installs
        // a face, and its typed refusal is exactly the original producer's refusal.
        self.declared = None;
        let phases = ReceivingPhases::declare(self.field, material, current, receiver)?;
        self.declared = Some(Declared {
            material: DeclaringMaterial::read(self.field, material),
            current: current.clone(),
            receiver: receiver.clone(),
            phases: phases.clone(),
        });
        Ok((phases, false))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::Landmarks;
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::moment::PairPort;
    use crate::hnn::receiving::RankScope;
    use crate::hnn::tests::support::{contact, small_field};
    use crate::ratio::{integer, rat};
    use crate::receiver::population::PortPopulation;

    /// The actual declaration must not even access an excluded port/statistic. This is a
    /// producer-dependency falsifier; it supplies no task truth or learned receiver.
    struct InteriorOnly<'a>(&'a Constitution);
    impl ConstitutionRead for InteriorOnly<'_> {
        fn standing(&self, g: usize) -> &[Rat] {
            self.0.standing(g)
        }
        fn passive_factor(&self, g: usize) -> &ExactRatMatrix {
            self.0.passive_factor(g)
        }
        fn contrast_port(&self, g: usize) -> &ExactRatMatrix {
            self.0.contrast_port(g)
        }
        fn slices(&self, g: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
            self.0.slices(g)
        }
        fn contact_storage(&self, a: usize) -> &ExactRatMatrix {
            self.0.contact_storage(a)
        }
        fn contact_stiffness(&self, a: usize) -> &ExactRatMatrix {
            self.0.contact_stiffness(a)
        }
        fn contact_dissipation(&self, a: usize) -> &ExactRatMatrix {
            self.0.contact_dissipation(a)
        }
        fn contact_stiffness_signature(&self, a: usize) -> Option<&[bool]> {
            self.0.contact_stiffness_signature(a)
        }
        fn contact_surface_storage(&self, a: usize) -> Option<&Rat> {
            self.0.contact_surface_storage(a)
        }
        fn ring_resonator(&self, g: usize) -> Option<&ResonatorMaterial> {
            self.0.ring_resonator(g)
        }
        fn source_port(&self, _: usize) -> Option<&ExactRatMatrix> {
            panic!("declaring rank read E")
        }
        fn pair_port(&self, _: usize, _: usize) -> Option<&PairPort> {
            panic!("declaring rank read pair port")
        }
        fn receiving_map(&self, _: usize) -> Option<&ExactRatMatrix> {
            panic!("declaring rank read R")
        }
        fn transport(&self, _: usize) -> Rat {
            panic!("declaring rank read source transport")
        }
        fn landmarks(&self, _: usize) -> Option<&Landmarks> {
            panic!("declaring rank read landmarks")
        }
        fn population(&self, _: usize) -> Option<&PortPopulation> {
            panic!("declaring rank read population")
        }
    }

    #[test]
    fn declaring_face_excludes_source_and_receiving_ports_by_the_actual_producer() {
        let field = small_field(&[2, 3], vec![contact(0, 1, 2, 0)], 0);
        let material = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let receiver = &field.receivers()[0];
        let fresh = ReceivingPhases::declare(&field, &material, &current, receiver).unwrap();
        assert_eq!(
            fresh,
            ReceivingPhases::declare(&field, &InteriorOnly(&material), &current, receiver).unwrap()
        );
        let mut face = DeclaringFace::new(&field);
        assert_eq!(
            face.declare(&material, &current, receiver).unwrap(),
            (fresh.clone(), false)
        );
        assert_eq!(
            face.declare(&material, &current, receiver).unwrap(),
            (fresh.clone(), true)
        );
        let pair = material.pair_port(0, 1).unwrap();
        let zero_pair = PairPort::new(
            pair.outputs()
                .iter()
                .map(|row| vec![integer(0); row.len()])
                .collect(),
            pair.current_reads().to_vec(),
            pair.earlier_reads().to_vec(),
        )
        .unwrap();
        let changed = material
            .clone()
            .with_ports(
                0,
                None,
                Some(material.source_port(0).unwrap().scaled(&integer(0))),
                Some(material.receiving_map(0).unwrap().scaled(&integer(0))),
            )
            .unwrap()
            .with_pair(0, 1, zero_pair)
            .unwrap()
            .with_transport(0, rat(1, 2))
            .unwrap();
        assert_eq!(
            face.declare(&changed, &current, receiver).unwrap(),
            (fresh.clone(), true)
        );
        assert_eq!(
            fresh,
            ReceivingPhases::declare(&field, &InteriorOnly(&changed), &current, receiver).unwrap()
        );
        assert_eq!(
            fresh,
            ReceivingPhases::declare(&field, &changed, &current, receiver).unwrap()
        );
    }

    #[test]
    fn declaring_face_invalidates_changed_material_lift_receiver_scope_and_refusal() {
        let field = small_field(&[2, 3], vec![contact(0, 1, 2, 0)], 0);
        let material = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let receiver = &field.receivers()[0];
        let mut face = DeclaringFace::new(&field);
        face.declare(&material, &current, receiver).unwrap();
        let mut changed = material
            .clone()
            .with_element(
                0,
                material.passive_factor(0).scaled(&integer(2)),
                material.contrast_port(0).clone(),
                material.slices(0).to_vec(),
            )
            .unwrap();
        let (phases, reused) = face.declare(&changed, &current, receiver).unwrap();
        assert!(!reused);
        assert_eq!(
            phases,
            ReceivingPhases::declare(&field, &changed, &current, receiver).unwrap()
        );
        changed = changed
            .with_channel(
                0,
                material.contact_storage(0).scaled(&integer(2)),
                material.contact_stiffness(0).clone(),
                material.contact_dissipation(0).clone(),
            )
            .unwrap();
        assert!(!face.declare(&changed, &current, receiver).unwrap().1);
        let lifted = Current::at(&field, vec![0.into(), 1.into()]).unwrap();
        assert!(!face.declare(&changed, &lifted, receiver).unwrap().1);
        let mut other = receiver.clone();
        other.tolerance = rat(1, 8);
        let (phases, reused) = face.declare(&changed, &lifted, &other).unwrap();
        assert!(!reused);
        assert_eq!(phases.grain(), 8);
        assert_eq!(
            phases,
            ReceivingPhases::declare(&field, &changed, &lifted, &other).unwrap()
        );
        let width = field.ring(0).width();
        let law = ResonatorMaterial::new(
            ExactRatMatrix::identity(width).unwrap(),
            ExactRatMatrix::identity(width).unwrap(),
            ExactRatMatrix::zero(width, width).unwrap(),
            None,
        )
        .unwrap();
        changed = changed.with_ring_resonator(&field, 0, law.clone()).unwrap();
        let (phases, reused) = face.declare(&changed, &lifted, &other).unwrap();
        assert!(!reused);
        assert_eq!(phases.rank_scope(), RankScope::Linear);
        assert_eq!(
            phases,
            ReceivingPhases::declare(&field, &changed, &lifted, &other).unwrap()
        );
        changed = changed
            .with_ring_resonator(&field, 0, law.with_symmetric_saturation(integer(1)).unwrap())
            .unwrap();
        let (phases, reused) = face.declare(&changed, &lifted, &other).unwrap();
        assert!(!reused);
        assert_eq!(phases.rank_scope(), RankScope::TangentAtRest);
        assert_eq!(
            phases,
            ReceivingPhases::declare(&field, &changed, &lifted, &other).unwrap()
        );
        assert_eq!(
            phases,
            ReceivingPhases::declare(&field, &InteriorOnly(&changed), &lifted, &other).unwrap()
        );
        assert_eq!(
            face.declare(&changed, &lifted, &other).unwrap(),
            (phases, true)
        );
        other.ring = field.rings().len();
        assert!(matches!(
            face.declare(&changed, &lifted, &other),
            Err(HnnError::RingOutside { .. })
        ));
        assert!(face.declared.is_none());
        assert!(!face.declare(&changed, &lifted, receiver).unwrap().1);
    }
}
