use super::*;
use crate::current_world::{
    present_native_event, present_native_event_with, present_native_event_with_regional,
    NativeEventCurrent, NativeEventRelation, NativePathChart, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan, NativeRelationOrganImage,
};
use body::incidence::{
    DiscreteEventGerm, EventCell, EventCellId, EventComplex, EventPort, IncidenceHand,
    IncidenceKind, OrientedIncidence,
};
use body::num::Cog;
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, ContemporaryRadiation, CurrentBoundaryPort, CurrentEvent,
    DirectedCurrentRelation, CpuLiveCurrentExecutor, InterfaceCapability, LiveCurrentMachine,
    ParallelCpuLiveCurrentExecutor,
};

fn relation(value: i64) -> RelationAtom {
    RelationAtom::new(Cog::lit(value)).unwrap()
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).unwrap()
}

fn assert_live_equal(
    cpu: &LiveCurrentMachine,
    card: &LiveCurrentMachine,
    lineages: &[(soma_membrane::CurrentLineage, soma_membrane::CurrentLineage)],
) {
    assert_eq!(cpu.standing(), card.standing());
    assert_eq!(cpu.memory(), card.memory());
    for (cpu_lineage, card_lineage) in lineages {
        assert_eq!(
            cpu.lineage_cursor(*cpu_lineage),
            card.lineage_cursor(*card_lineage)
        );
        assert_eq!(
            cpu.lineage_channel(*cpu_lineage),
            card.lineage_channel(*card_lineage)
        );
        assert_eq!(
            cpu.lineage_carrier(*cpu_lineage)
                .map(|body| body.header()),
            card.lineage_carrier(*card_lineage)
                .map(|body| body.header())
        );
        assert_eq!(
            cpu.lineage_carrier(*cpu_lineage)
                .map(|body| body.carrier()),
            card.lineage_carrier(*card_lineage)
                .map(|body| body.carrier())
        );
    }
}

fn primed_native_pair_for_residency(
) -> (LiveCurrentMachine, NativeRelationOrgan, NativeRelationOrgan) {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
    let mut left = NativeRelationOrgan::new();
    let mut right = NativeRelationOrgan::new();
    for value in [13, 29, 17, 31, -63_245, 47] {
        let left_face = [relation(value)];
        let right_face = [relation(value)];
        let mut currents = [
            NativeEventCurrent::continuing(&mut left, &left_face, action()),
            NativeEventCurrent::continuing(&mut right, &right_face, action()),
        ];
        present_native_event(&mut machine, &mut currents, &[]).unwrap();
    }
    let right_ahead = [relation(71)];
    right
        .present(&mut machine, &right_ahead, action(), false)
        .unwrap();
    let left_turn = [relation(71)];
    let right_turn = [relation(-89)];
    let mut currents = [
        NativeEventCurrent::continuing(&mut left, &left_turn, action()),
        NativeEventCurrent::continuing(&mut right, &right_turn, action()),
    ];
    present_native_event(&mut machine, &mut currents, &[]).unwrap();
    (machine, left, right)
}

struct NativeTriangleChart {
    cells: [EventCell; 7],
    incidences: [OrientedIncidence; 9],
    ports: [EventPort; 2],
}

impl NativeTriangleChart {
    fn new(relations: [i64; 7]) -> Self {
        let ids = core::array::from_fn::<_, 7, _>(|at| EventCellId::new(at as u64));
        let cells = [
            EventCell::new(ids[0], 0, 0, relation(relations[0]).cog()),
            EventCell::new(ids[1], 0, 0, relation(relations[1]).cog()),
            EventCell::new(ids[2], 0, 0, relation(relations[2]).cog()),
            EventCell::new(ids[3], 0, 1, relation(relations[3]).cog()),
            EventCell::new(ids[4], 0, 1, relation(relations[4]).cog()),
            EventCell::new(ids[5], 0, 1, relation(relations[5]).cog()),
            EventCell::new(ids[6], 0, 2, relation(relations[6]).cog()),
        ];
        // e01: v0 -> v1, e12: v1 -> v2, e20: v2 -> v0. The face carries all
        // three oriented edges, so every vertex coefficient in partial(partial(face)) is zero.
        let incidences = [
            OrientedIncidence::boundary(ids[0], ids[3], IncidenceHand::Against, 0),
            OrientedIncidence::boundary(ids[1], ids[3], IncidenceHand::With, 1),
            OrientedIncidence::boundary(ids[1], ids[4], IncidenceHand::Against, 0),
            OrientedIncidence::boundary(ids[2], ids[4], IncidenceHand::With, 1),
            OrientedIncidence::boundary(ids[2], ids[5], IncidenceHand::Against, 0),
            OrientedIncidence::boundary(ids[0], ids[5], IncidenceHand::With, 1),
            OrientedIncidence::boundary(ids[3], ids[6], IncidenceHand::With, 0),
            OrientedIncidence::boundary(ids[4], ids[6], IncidenceHand::With, 1),
            OrientedIncidence::boundary(ids[5], ids[6], IncidenceHand::With, 2),
        ];
        let ports = [
            EventPort::ingress(ids[0], IncidenceHand::With, 0),
            EventPort::exposed(ids[6], IncidenceHand::With, 0),
        ];
        let chart = Self {
            cells,
            incidences,
            ports,
        };
        assert!(chart.boundary_squared_is_zero());
        chart
    }

    fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("the oriented triangle is one exact graded source cell")
    }

    fn boundary_squared_is_zero(&self) -> bool {
        for upper in self
            .cells
            .iter()
            .copied()
            .filter(|cell| cell.dimension() != 0)
        {
            if upper.dimension() == 1 {
                let sum = self
                    .incidences
                    .iter()
                    .copied()
                    .filter(|incidence| {
                        incidence.kind() == IncidenceKind::Boundary && incidence.to() == upper.id()
                    })
                    .map(|incidence| incidence.hand().coefficient())
                    .sum::<i64>();
                if sum != 0 {
                    return false;
                }
                continue;
            }
            for lower in self.cells.iter().copied().filter(|cell| {
                cell.dependency_rank() == upper.dependency_rank()
                    && cell.dimension() + 2 == upper.dimension()
            }) {
                let mut sum = 0i64;
                for outer in self.incidences.iter().copied().filter(|incidence| {
                    incidence.kind() == IncidenceKind::Boundary && incidence.to() == upper.id()
                }) {
                    for inner in self.incidences.iter().copied().filter(|incidence| {
                        incidence.kind() == IncidenceKind::Boundary
                            && incidence.from() == lower.id()
                            && incidence.to() == outer.from()
                    }) {
                        sum += outer.hand().coefficient() * inner.hand().coefficient();
                    }
                }
                if sum != 0 {
                    return false;
                }
            }
        }
        true
    }
}

struct NativeRewriteChart {
    cells: [EventCell; 4],
    incidences: [OrientedIncidence; 2],
    ports: [EventPort; 2],
}

impl NativeRewriteChart {
    fn new(relations: [i64; 4]) -> Self {
        let ids = core::array::from_fn::<_, 4, _>(|at| EventCellId::new(at as u64));
        let cells = [
            EventCell::situated(ids[0], 0, 0, 0, relation(relations[0]).cog()),
            EventCell::situated(ids[1], 0, 0, 0, relation(relations[1]).cog()),
            EventCell::situated(ids[2], 1, 0, 2, relation(relations[2]).cog()),
            EventCell::situated(ids[3], 1, 0, 2, relation(relations[3]).cog()),
        ];
        let incidences = [
            OrientedIncidence::rewrite_interface(ids[0], ids[2], IncidenceHand::With, 0),
            OrientedIncidence::dependency(ids[1], ids[3], IncidenceHand::With, 0),
        ];
        let ports = [
            EventPort::ingress(ids[0], IncidenceHand::With, 0),
            EventPort::exposed(ids[2], IncidenceHand::With, 0),
        ];
        let chart = Self {
            cells,
            incidences,
            ports,
        };
        let germ = DiscreteEventGerm::new(chart.complex())
            .expect("the rewrite chart is one actual local map");
        assert_eq!(germ.preserved_interface_count(), 1);
        assert_eq!(germ.dependency_count(), 2);
        chart
    }

    fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("the rewrite chart retains independent rank, dimension, and grain")
    }
}

fn primed_native_triplet_for_junction() -> (
    LiveCurrentMachine,
    NativeRelationOrgan,
    NativeRelationOrgan,
    NativeRelationOrgan,
) {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
    let mut first = NativeRelationOrgan::new();
    let mut second = NativeRelationOrgan::new();
    let mut third = NativeRelationOrgan::new();
    for value in [13, 29, 17, 31, -63_245, 47, 71, -89] {
        let face = [relation(value)];
        let mut currents = [
            NativeEventCurrent::continuing(&mut first, &face, action()),
            NativeEventCurrent::continuing(&mut second, &face, action()),
            NativeEventCurrent::continuing(&mut third, &face, action()),
        ];
        present_native_event(&mut machine, &mut currents, &[]).unwrap();
    }
    (machine, first, second, third)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ResidueChartEvent {
    zero_relative: [RelationAtom; 4],
    numeral_chart: [RelationAtom; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ResidueChartWorldImage {
    extent: u64,
    cursor: u64,
    register: i64,
}

impl ResidueChartWorldImage {
    fn encode_native_bytes(self) -> [u8; 24] {
        let mut bytes = [0u8; 24];
        bytes[..8].copy_from_slice(&self.extent.to_le_bytes());
        bytes[8..16].copy_from_slice(&self.cursor.to_le_bytes());
        bytes[16..].copy_from_slice(&self.register.to_le_bytes());
        bytes
    }

    fn from_native_bytes(bytes: &[u8]) -> Option<Self> {
        (bytes.len() == 24).then(|| Self {
            extent: u64::from_le_bytes(bytes[..8].try_into().unwrap()),
            cursor: u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            register: i64::from_le_bytes(bytes[16..].try_into().unwrap()),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ResidueChartWorld {
    extent: u64,
    cursor: u64,
    register: i64,
}

impl ResidueChartWorld {
    const fn new(extent: u64) -> Self {
        Self {
            extent,
            cursor: 0,
            register: -903,
        }
    }

    fn digit_sum(mut value: u64, radix: u64) -> i64 {
        let mut sum = 0i64;
        while value != 0 {
            sum += (value % radix) as i64;
            value /= radix;
        }
        sum
    }

    fn atom(value: i64) -> RelationAtom {
        relation(
            value
                .checked_mul(2)
                .and_then(|value| value.checked_add(1))
                .expect("the bounded residue chart has one canonical odd lift"),
        )
    }

    fn next(&mut self) -> ResidueChartEvent {
        assert!(self.cursor < self.extent, "the source horizon is exhausted");
        let coordinate = self.cursor + 1;
        self.cursor = coordinate;
        let coordinate_i64 = coordinate as i64;
        ResidueChartEvent {
            zero_relative: [
                Self::atom(coordinate_i64),
                Self::atom((coordinate % 7) as i64 - 3),
                Self::atom((coordinate % 11) as i64 - 5),
                Self::atom(self.register),
            ],
            numeral_chart: [
                Self::atom(coordinate_i64),
                Self::atom(coordinate.count_ones() as i64),
                Self::atom(Self::digit_sum(coordinate, 10)),
                Self::atom(Self::digit_sum(coordinate, 16)),
            ],
        }
    }

    fn receive_change(&mut self, change: i64) {
        self.register = self
            .register
            .checked_add(change)
            .expect("the bounded residue chart register remains exact");
    }

    const fn checkpoint(self) -> ResidueChartWorldImage {
        ResidueChartWorldImage {
            extent: self.extent,
            cursor: self.cursor,
            register: self.register,
        }
    }

    const fn recover(image: ResidueChartWorldImage) -> Self {
        Self {
            extent: image.extent,
            cursor: image.cursor,
            register: image.register,
        }
    }
}

fn present_residue_chart_event(
    machine: &mut LiveCurrentMachine,
    executor: &mut dyn LiveCurrentExecutor,
    zero_relative: &mut NativeRelationOrgan,
    numeral_chart: &mut NativeRelationOrgan,
    event: &ResidueChartEvent,
) -> ContemporaryRadiation {
    let zero_chart = NativePathChart::new(&event.zero_relative).unwrap();
    let numeral_path = NativePathChart::new(&event.numeral_chart).unwrap();
    let mut currents = [
        NativeEventCurrent::continuing_complex(zero_relative, zero_chart.complex(), action()),
        NativeEventCurrent::continuing_complex(numeral_chart, numeral_path.complex(), action()),
    ];
    present_native_event_with(machine, executor, &mut currents, &[]).unwrap()
}

#[test]
#[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
fn one_resident_card_body_sustains_return_rest_departure_and_durable_remount() {
    let (baseline, left, right) = primed_native_pair_for_residency();
    let rest = baseline.rest_image().unwrap();
    let left_image = left.checkpoint();
    let right_image = right.checkpoint();
    let left_lineage = left_image.lineage().unwrap();
    let right_lineage = right_image.lineage().unwrap();

    let mut cpu = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card = LiveCurrentMachine::from_rest_image(rest).unwrap();
    let mut cpu_left = NativeRelationOrgan::recover(left_image, &cpu).unwrap();
    let mut cpu_right = NativeRelationOrgan::recover(right_image, &cpu).unwrap();
    let mut card_left = NativeRelationOrgan::recover(left_image, &card).unwrap();
    let mut card_right = NativeRelationOrgan::recover(right_image, &card).unwrap();
    let mut cpu_executor = CpuLiveCurrentExecutor;
    let mut cuda = CudaLiveCurrentExecutor::new(0).unwrap();

    let left_face = [relation(-89)];
    let right_face = [relation(97)];
    let relation_rows = [NativeEventRelation::new(0, 1)];
    let cpu_contact = {
        let mut currents = [
            NativeEventCurrent::continuing(&mut cpu_left, &left_face, action()),
            NativeEventCurrent::continuing(&mut cpu_right, &right_face, action()),
        ];
        present_native_event_with(&mut cpu, &mut cpu_executor, &mut currents, &relation_rows)
            .unwrap()
    };
    let card_contact = {
        let mut currents = [
            NativeEventCurrent::continuing(&mut card_left, &left_face, action()),
            NativeEventCurrent::continuing(&mut card_right, &right_face, action()),
        ];
        present_native_event_with(&mut card, &mut cuda, &mut currents, &relation_rows).unwrap()
    };
    assert_eq!(cpu_contact, card_contact);
    assert_live_equal(
        &cpu,
        &card,
        &[(left_lineage, left_lineage), (right_lineage, right_lineage)],
    );
    let emission = card_contact.relations()[0]
        .contact()
        .emission
        .expect("the declared forward hand forms one world deed");
    let returned_change = [emission.term.chi.other, emission.term.chi.same]
        .into_iter()
        .find(|arm| arm.mag != 0)
        .expect("the formed world deed carries one nonzero arm")
        .face();
    let mut world_register = -903i64;
    world_register = world_register
        .checked_add(returned_change)
        .expect("the bounded returned world register remains exact");

    let standing_mounts_after_contact = cuda.standing_full_mounts();
    let carrier_mounts_after_contact = cuda.carrier_full_mounts();
    let return_face = [relation(returned_change)];
    let cpu_return = cpu_right
        .present_with(&mut cpu, &mut cpu_executor, &return_face, action(), false)
        .unwrap();
    let card_return = card_right
        .present_with(&mut card, &mut cuda, &return_face, action(), false)
        .unwrap();
    assert_eq!(cpu_return, card_return);

    for (left_value, right_value) in [(101, -103), (107, -109), (127, -131)] {
        let left_wake = [relation(left_value)];
        let right_wake = [relation(right_value)];
        let cpu_wake = {
            let mut currents = [
                NativeEventCurrent::continuing(&mut cpu_left, &left_wake, action()),
                NativeEventCurrent::continuing(&mut cpu_right, &right_wake, action()),
            ];
            present_native_event_with(&mut cpu, &mut cpu_executor, &mut currents, &[]).unwrap()
        };
        let card_wake = {
            let mut currents = [
                NativeEventCurrent::continuing(&mut card_left, &left_wake, action()),
                NativeEventCurrent::continuing(&mut card_right, &right_wake, action()),
            ];
            present_native_event_with(&mut card, &mut cuda, &mut currents, &[]).unwrap()
        };
        assert_eq!(cpu_wake, card_wake);
    }
    assert_eq!(cuda.standing_full_mounts(), standing_mounts_after_contact);
    assert_eq!(cuda.carrier_full_mounts(), carrier_mounts_after_contact);
    assert!(cuda.standing_device_words() > 0);
    assert!(cuda.carrier_device_words() > 0);

    let departing = [relation(137)];
    let cpu_departure = cpu_left
        .present_with(&mut cpu, &mut cpu_executor, &departing, action(), true)
        .unwrap();
    let card_departure = card_left
        .present_with(&mut card, &mut cuda, &departing, action(), true)
        .unwrap();
    assert_eq!(cpu_departure, card_departure);
    assert!(cpu_left.lineage().is_none());
    assert!(card_left.lineage().is_none());
    assert_eq!(cuda.resident_lineages(), 1);
    assert_live_equal(&cpu, &card, &[(right_lineage, right_lineage)]);

    let launches_at_rest = cuda.launches();
    let card_rest_bytes = card.rest_image().unwrap().encode_native_bytes().unwrap();
    let card_right_bytes = card_right.checkpoint().encode_native_bytes();
    assert_eq!(cuda.launches(), launches_at_rest);
    let first_residency = (
        cuda.resource_retries(),
        cuda.standing_full_mounts(),
        cuda.carrier_full_mounts(),
        cuda.standing_cpu_words(),
        cuda.standing_device_words(),
        cuda.carrier_cpu_words(),
        cuda.carrier_device_words(),
    );
    drop(cuda);

    let reopened_image =
        soma_membrane::LiveCurrentRestImage::from_native_bytes(&card_rest_bytes).unwrap();
    let mut reopened = LiveCurrentMachine::from_rest_image(reopened_image).unwrap();
    let reopened_organ_image =
        NativeRelationOrganImage::from_native_bytes(&card_right_bytes, &reopened).unwrap();
    let mut reopened_right = NativeRelationOrgan::recover(reopened_organ_image, &reopened).unwrap();
    let mut reopened_cuda = CudaLiveCurrentExecutor::new(0).unwrap();
    assert_eq!(reopened_cuda.launches(), 0);

    let first_wake = [relation(149)];
    let cpu_wake = cpu_right
        .present_with(&mut cpu, &mut cpu_executor, &first_wake, action(), false)
        .unwrap();
    let card_wake = reopened_right
        .present_with(
            &mut reopened,
            &mut reopened_cuda,
            &first_wake,
            action(),
            false,
        )
        .unwrap();
    assert_eq!(cpu_wake, card_wake);
    let remount_standing_mounts = reopened_cuda.standing_full_mounts();
    let remount_carrier_mounts = reopened_cuda.carrier_full_mounts();

    let later_wake = [relation(151)];
    let cpu_later = cpu_right
        .present_with(&mut cpu, &mut cpu_executor, &later_wake, action(), false)
        .unwrap();
    let card_later = reopened_right
        .present_with(
            &mut reopened,
            &mut reopened_cuda,
            &later_wake,
            action(),
            false,
        )
        .unwrap();
    assert_eq!(cpu_later, card_later);
    assert_eq!(
        reopened_cuda.standing_full_mounts(),
        remount_standing_mounts
    );
    assert_eq!(reopened_cuda.carrier_full_mounts(), remount_carrier_mounts);
    assert!(reopened_cuda.carrier_device_words() > 0);
    assert_live_equal(&cpu, &reopened, &[(right_lineage, right_lineage)]);

    println!(
            "device={:?} world_register={} pre_remount_launches={} pre_remount_retries={} pre_remount_standing_full={} pre_remount_carrier_full={} pre_remount_standing_h2d_words={} pre_remount_standing_d2d_words={} pre_remount_carrier_h2d_words={} pre_remount_carrier_d2d_words={} remount_launches={} remount_retries={} remount_standing_full={} remount_carrier_full={} remount_carrier_d2d_words={} resident_lineages={}",
            reopened_cuda.device_name(),
            world_register,
            launches_at_rest,
            first_residency.0,
            first_residency.1,
            first_residency.2,
            first_residency.3,
            first_residency.4,
            first_residency.5,
            first_residency.6,
            reopened_cuda.launches(),
            reopened_cuda.resource_retries(),
            reopened_cuda.standing_full_mounts(),
            reopened_cuda.carrier_full_mounts(),
            reopened_cuda.carrier_device_words(),
            reopened_cuda.resident_lineages(),
        );
}

#[test]
#[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
fn large_residue_chart_world_streams_only_participating_current_through_resident_body() {
    const STREAM_EVENTS: u64 = 256;
    const SMALL_EXTENT: u64 = STREAM_EVENTS + 2;
    const LARGE_EXTENT: u64 = 1 << 40;

    let (baseline, zero_relative, numeral_chart) = primed_native_pair_for_residency();
    let rest = baseline.rest_image().unwrap();
    let zero_image = zero_relative.checkpoint();
    let numeral_image = numeral_chart.checkpoint();
    let zero_lineage = zero_image.lineage().unwrap();
    let numeral_lineage = numeral_image.lineage().unwrap();

    let mut cpu = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card = LiveCurrentMachine::from_rest_image(rest).unwrap();
    let mut cpu_zero = NativeRelationOrgan::recover(zero_image, &cpu).unwrap();
    let mut cpu_numeral = NativeRelationOrgan::recover(numeral_image, &cpu).unwrap();
    let mut card_zero = NativeRelationOrgan::recover(zero_image, &card).unwrap();
    let mut card_numeral = NativeRelationOrgan::recover(numeral_image, &card).unwrap();
    let mut cpu_executor = CpuLiveCurrentExecutor;
    let mut cuda = CudaLiveCurrentExecutor::new(0).unwrap();
    let mut cpu_world = ResidueChartWorld::new(SMALL_EXTENT);
    let mut card_world = ResidueChartWorld::new(LARGE_EXTENT);
    assert_eq!(core::mem::size_of::<ResidueChartWorld>(), 24);

    let zero_contact = [relation(-89)];
    let numeral_contact = [relation(97)];
    let hand = [NativeEventRelation::new(0, 1)];
    let cpu_contact = {
        let mut currents = [
            NativeEventCurrent::continuing(&mut cpu_zero, &zero_contact, action()),
            NativeEventCurrent::continuing(&mut cpu_numeral, &numeral_contact, action()),
        ];
        present_native_event_with(&mut cpu, &mut cpu_executor, &mut currents, &hand).unwrap()
    };
    let card_contact = {
        let mut currents = [
            NativeEventCurrent::continuing(&mut card_zero, &zero_contact, action()),
            NativeEventCurrent::continuing(&mut card_numeral, &numeral_contact, action()),
        ];
        present_native_event_with(&mut card, &mut cuda, &mut currents, &hand).unwrap()
    };
    assert_eq!(cpu_contact, card_contact);
    let emission = card_contact.relations()[0]
        .contact()
        .emission
        .expect("the scale world's declared hand forms one material deed");
    let returned_change = [emission.term.chi.other, emission.term.chi.same]
        .into_iter()
        .find(|arm| arm.mag != 0)
        .expect("the scale world's formed deed carries one nonzero arm")
        .face();
    cpu_world.receive_change(returned_change);
    card_world.receive_change(returned_change);
    assert_eq!(cpu_world.register, card_world.register);

    let return_face = [relation(returned_change)];
    let cpu_return = cpu_numeral
        .present_with(&mut cpu, &mut cpu_executor, &return_face, action(), false)
        .unwrap();
    let card_return = card_numeral
        .present_with(&mut card, &mut cuda, &return_face, action(), false)
        .unwrap();
    assert_eq!(cpu_return, card_return);
    let standing_mounts_at_stream = cuda.standing_full_mounts();
    let carrier_mounts_at_stream = cuda.carrier_full_mounts();
    let mut checkpoints = Vec::new();
    let mut stream_rank_transitions = 0u64;

    for step in 1..=STREAM_EVENTS {
        let cpu_event = cpu_world.next();
        let card_event = card_world.next();
        assert_eq!(cpu_event, card_event);
        let cpu_radiation = present_residue_chart_event(
            &mut cpu,
            &mut cpu_executor,
            &mut cpu_zero,
            &mut cpu_numeral,
            &cpu_event,
        );
        let card_radiation = present_residue_chart_event(
            &mut card,
            &mut cuda,
            &mut card_zero,
            &mut card_numeral,
            &card_event,
        );
        assert_eq!(cpu_radiation, card_radiation);
        if card_radiation.before_rank() != card_radiation.after_rank() {
            stream_rank_transitions += 1;
        }
        if [1, 64, 128, STREAM_EVENTS].contains(&step) {
            let memory = card.memory();
            assert_eq!(memory.live_lineages, 2);
            checkpoints.push((
                step,
                card.standing().rank(),
                memory.standing_cells,
                memory.carrier_words,
                memory.overflow_nodes,
                cuda.resident_standing_words(),
                cuda.resident_carrier_words(),
                cuda.resource_retries(),
            ));
            assert_live_equal(
                &cpu,
                &card,
                &[
                    (zero_lineage, zero_lineage),
                    (numeral_lineage, numeral_lineage),
                ],
            );
        }
    }
    assert_eq!(cpu_world.cursor, STREAM_EVENTS);
    assert_eq!(card_world.cursor, STREAM_EVENTS);
    assert_eq!(cpu_world.extent, SMALL_EXTENT);
    assert_eq!(card_world.extent, LARGE_EXTENT);
    assert_eq!(
        cuda.standing_full_mounts(),
        standing_mounts_at_stream + stream_rank_transitions
    );
    assert_eq!(cuda.carrier_full_mounts(), carrier_mounts_at_stream);
    assert!(cuda.standing_device_words() > 0);
    assert!(cuda.carrier_device_words() > cuda.carrier_cpu_words());

    let departure_face = [ResidueChartWorld::atom(137)];
    let cpu_departure = cpu_zero
        .present_with(
            &mut cpu,
            &mut cpu_executor,
            &departure_face,
            action(),
            true,
        )
        .unwrap();
    let card_departure = card_zero
        .present_with(&mut card, &mut cuda, &departure_face, action(), true)
        .unwrap();
    assert_eq!(cpu_departure, card_departure);
    assert_eq!(cuda.resident_lineages(), 1);
    assert_live_equal(&cpu, &card, &[(numeral_lineage, numeral_lineage)]);

    let launches_at_rest = cuda.launches();
    let machine_bytes = card.rest_image().unwrap().encode_native_bytes().unwrap();
    let organ_bytes = card_numeral.checkpoint().encode_native_bytes();
    let world_bytes = card_world.checkpoint().encode_native_bytes();
    assert_eq!(world_bytes.len(), 24);
    assert_eq!(cuda.launches(), launches_at_rest);
    let pre_remount = (
        cuda.launches(),
        cuda.resource_retries(),
        cuda.standing_full_mounts(),
        cuda.carrier_full_mounts(),
        cuda.standing_cpu_words(),
        cuda.standing_device_words(),
        cuda.carrier_cpu_words(),
        cuda.carrier_device_words(),
        cuda.resident_standing_words(),
        cuda.resident_carrier_words(),
    );
    drop(cuda);

    let reopened_image =
        soma_membrane::LiveCurrentRestImage::from_native_bytes(&machine_bytes).unwrap();
    let mut reopened = LiveCurrentMachine::from_rest_image(reopened_image).unwrap();
    let reopened_organ_image =
        NativeRelationOrganImage::from_native_bytes(&organ_bytes, &reopened).unwrap();
    let mut reopened_numeral =
        NativeRelationOrgan::recover(reopened_organ_image, &reopened).unwrap();
    let reopened_world_image = ResidueChartWorldImage::from_native_bytes(&world_bytes).unwrap();
    let mut reopened_world = ResidueChartWorld::recover(reopened_world_image);
    let reopened_before_wake = reopened.rest_image().unwrap();
    let mut reopened_cuda = CudaLiveCurrentExecutor::new(0).unwrap();
    assert_eq!(reopened_cuda.launches(), 0);

    for _ in 0..2 {
        let cpu_event = cpu_world.next();
        let card_event = reopened_world.next();
        assert_eq!(cpu_event, card_event);
        let cpu_numeral_path = NativePathChart::new(&cpu_event.numeral_chart).unwrap();
        let card_numeral_path = NativePathChart::new(&card_event.numeral_chart).unwrap();
        let cpu_wake = cpu_numeral
            .present_complex_with(
                &mut cpu,
                &mut cpu_executor,
                cpu_numeral_path.complex(),
                action(),
                false,
            )
            .unwrap();
        let card_wake = reopened_numeral
            .present_complex_with(
                &mut reopened,
                &mut reopened_cuda,
                card_numeral_path.complex(),
                action(),
                false,
            )
            .unwrap();
        assert_eq!(cpu_wake, card_wake);
    }
    assert_eq!(cpu_world.cursor, SMALL_EXTENT);
    assert_eq!(reopened_world.cursor, SMALL_EXTENT);
    assert_eq!(cpu_world.register, reopened_world.register);
    assert_ne!(reopened_before_wake, reopened.rest_image().unwrap());
    assert!(reopened_cuda.carrier_device_words() > 0);
    assert_live_equal(&cpu, &reopened, &[(numeral_lineage, numeral_lineage)]);

    println!(
            "device={:?} source_extent={} visited={} source_rest_bytes={} machine_rest_bytes={} checkpoints={:?} stream_rank_transitions={} pre_remount_launches={} pre_remount_retries={} standing_full={} carrier_full={} standing_h2d_words={} standing_d2d_words={} carrier_h2d_words={} carrier_d2d_words={} resident_standing_words={} resident_carrier_words={} wait_launches=0 remount_launches={} remount_retries={} remount_carrier_d2d_words={} final_lineages={}",
            reopened_cuda.device_name(),
            LARGE_EXTENT,
            reopened_world.cursor,
            world_bytes.len(),
            machine_bytes.len(),
            checkpoints,
            stream_rank_transitions,
            pre_remount.0,
            pre_remount.1,
            pre_remount.2,
            pre_remount.3,
            pre_remount.4,
            pre_remount.5,
            pre_remount.6,
            pre_remount.7,
            pre_remount.8,
            pre_remount.9,
            reopened_cuda.launches(),
            reopened_cuda.resource_retries(),
            reopened_cuda.carrier_device_words(),
            reopened_cuda.resident_lineages(),
        );
}

#[test]
#[ignore = "requires the RTX CUDA device and committed regional_contacts/lineage_event PTX entries"]
fn graded_triangle_junction_is_exact_across_one_core_many_cores_cuda_and_rest() {
    let (baseline, first, second, third) = primed_native_triplet_for_junction();
    let rest = baseline.rest_image().unwrap();
    let images = [first.checkpoint(), second.checkpoint(), third.checkpoint()];
    let lineages = images.map(|image| image.lineage().unwrap());

    let mut one = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut many = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card = LiveCurrentMachine::from_rest_image(rest).unwrap();
    let mut one_organs = [
        NativeRelationOrgan::recover(images[0], &one).unwrap(),
        NativeRelationOrgan::recover(images[1], &one).unwrap(),
        NativeRelationOrgan::recover(images[2], &one).unwrap(),
    ];
    let mut many_organs = [
        NativeRelationOrgan::recover(images[0], &many).unwrap(),
        NativeRelationOrgan::recover(images[1], &many).unwrap(),
        NativeRelationOrgan::recover(images[2], &many).unwrap(),
    ];
    let mut card_organs = [
        NativeRelationOrgan::recover(images[0], &card).unwrap(),
        NativeRelationOrgan::recover(images[1], &card).unwrap(),
        NativeRelationOrgan::recover(images[2], &card).unwrap(),
    ];
    let charts = [
        NativeTriangleChart::new([17, 19, 23, 2, 4, -6, 1]),
        NativeTriangleChart::new([29, 31, 37, 2, 6, -8, 1]),
        NativeTriangleChart::new([41, 43, 47, 2, 4, -6, 1]),
    ];
    for chart in &charts {
        assert!(chart.boundary_squared_is_zero());
        assert_eq!(chart.complex().outer_grain().unwrap(), 3);
    }
    let arcs = [
        NativeRegionalArc::new(
            0,
            CurrentBoundaryPort::Exposed(0),
            1,
            CurrentBoundaryPort::Exposed(0),
            InterfaceCapability::new(0x4355_4441, 0),
            0,
            0,
            IncidenceHand::Against,
        ),
        NativeRegionalArc::new(
            1,
            CurrentBoundaryPort::Exposed(0),
            2,
            CurrentBoundaryPort::Exposed(0),
            InterfaceCapability::new(0x4355_4441, 1),
            1,
            0,
            IncidenceHand::With,
        ),
    ];
    // These are two actual co-present source cells, not one row replayed later. Their shared
    // exposed arms must close as one joint component without cloning the standing successor.
    let regional = [
        NativeRegionalRelation::new(2, &arcs),
        NativeRegionalRelation::new(2, &arcs),
    ];
    let mut one_executor = ParallelCpuLiveCurrentExecutor::new(1);
    let mut many_executor = ParallelCpuLiveCurrentExecutor::new(8);
    let mut cuda = CudaLiveCurrentExecutor::new(0).unwrap();

    let one_radiation = {
        let [first, second, third] = &mut one_organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(first, charts[0].complex(), action()),
            NativeEventCurrent::continuing_complex(second, charts[1].complex(), action()),
            NativeEventCurrent::continuing_complex(third, charts[2].complex(), action()),
        ];
        present_native_event_with_regional(
            &mut one,
            &mut one_executor,
            &mut currents,
            &[],
            &regional,
        )
        .unwrap()
    };
    let many_radiation = {
        let [first, second, third] = &mut many_organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(first, charts[0].complex(), action()),
            NativeEventCurrent::continuing_complex(second, charts[1].complex(), action()),
            NativeEventCurrent::continuing_complex(third, charts[2].complex(), action()),
        ];
        present_native_event_with_regional(
            &mut many,
            &mut many_executor,
            &mut currents,
            &[],
            &regional,
        )
        .unwrap()
    };
    let card_radiation = {
        let [first, second, third] = &mut card_organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(first, charts[0].complex(), action()),
            NativeEventCurrent::continuing_complex(second, charts[1].complex(), action()),
            NativeEventCurrent::continuing_complex(third, charts[2].complex(), action()),
        ];
        present_native_event_with_regional(&mut card, &mut cuda, &mut currents, &[], &regional)
            .unwrap()
    };

    assert_eq!(one_radiation, many_radiation);
    assert_eq!(one_radiation, card_radiation);
    assert_live_equal(&one, &many, &lineages.map(|lineage| (lineage, lineage)));
    assert_live_equal(&one, &card, &lineages.map(|lineage| (lineage, lineage)));
    assert_eq!(one_radiation.regional().len(), 2);
    assert_eq!(
        one_radiation.regional()[0].constituent(),
        one_radiation.regional()[1].constituent()
    );
    let constituent = one_radiation.regional()[0].constituent();
    assert!(!constituent.cells().is_empty());
    assert!(!constituent.incidences().is_empty());
    assert!(!constituent.exposed().is_empty());
    assert!(constituent.pins().iter().any(|pin| pin.is_open()));
    // Compression here is the outgoing joint face: two actual co-present regional cells are
    // represented by one successor constituent while their exposed residual remains live.
    // `LivePath::interior_folded` is the narrower later path-step optimization and is not the
    // definition of this event's compression.
    assert_eq!(one.standing().constituents().len(), 1);
    assert_eq!(one.standing().constituents()[0], *constituent);

    // A second, non-triangular source world uses the same live mouth. Its boundary degree is
    // zero throughout while dependency rank and constituent grain change independently; one
    // dependency is explicitly the interface preserved by the local rewrite.
    let rewrites = [
        NativeRewriteChart::new([101, 103, 107, 109]),
        NativeRewriteChart::new([113, 127, 131, 137]),
        NativeRewriteChart::new([139, 149, 151, 157]),
    ];
    for rewrite in &rewrites {
        assert_eq!(rewrite.complex().outer_grain().unwrap(), 3);
        assert!(rewrite
            .complex()
            .cells()
            .iter()
            .all(|cell| cell.dimension() == 0));
    }
    let rewrite_arcs = [
        NativeRegionalArc::new(
            0,
            CurrentBoundaryPort::Exposed(0),
            1,
            CurrentBoundaryPort::Exposed(0),
            InterfaceCapability::new(0x5245_5752_4954_45, 0),
            0,
            0,
            IncidenceHand::Against,
        ),
        NativeRegionalArc::new(
            1,
            CurrentBoundaryPort::Exposed(0),
            2,
            CurrentBoundaryPort::Exposed(0),
            InterfaceCapability::new(0x5245_5752_4954_45, 1),
            1,
            0,
            IncidenceHand::With,
        ),
    ];
    let rewrite_regional = [
        NativeRegionalRelation::new(2, &rewrite_arcs),
        NativeRegionalRelation::new(2, &rewrite_arcs),
    ];
    let one_rewrite = {
        let [first, second, third] = &mut one_organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(first, rewrites[0].complex(), action()),
            NativeEventCurrent::continuing_complex(second, rewrites[1].complex(), action()),
            NativeEventCurrent::continuing_complex(third, rewrites[2].complex(), action()),
        ];
        present_native_event_with_regional(
            &mut one,
            &mut one_executor,
            &mut currents,
            &[],
            &rewrite_regional,
        )
        .unwrap()
    };
    let many_rewrite = {
        let [first, second, third] = &mut many_organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(first, rewrites[0].complex(), action()),
            NativeEventCurrent::continuing_complex(second, rewrites[1].complex(), action()),
            NativeEventCurrent::continuing_complex(third, rewrites[2].complex(), action()),
        ];
        present_native_event_with_regional(
            &mut many,
            &mut many_executor,
            &mut currents,
            &[],
            &rewrite_regional,
        )
        .unwrap()
    };
    let card_rewrite = {
        let [first, second, third] = &mut card_organs;
        let mut currents = [
            NativeEventCurrent::continuing_complex(first, rewrites[0].complex(), action()),
            NativeEventCurrent::continuing_complex(second, rewrites[1].complex(), action()),
            NativeEventCurrent::continuing_complex(third, rewrites[2].complex(), action()),
        ];
        present_native_event_with_regional(
            &mut card,
            &mut cuda,
            &mut currents,
            &[],
            &rewrite_regional,
        )
        .unwrap()
    };
    assert_eq!(one_rewrite, many_rewrite);
    assert_eq!(one_rewrite, card_rewrite);
    assert_live_equal(&one, &many, &lineages.map(|lineage| (lineage, lineage)));
    assert_live_equal(&one, &card, &lineages.map(|lineage| (lineage, lineage)));
    assert!(one_rewrite.currents()[0]
        .incidences()
        .iter()
        .any(|row| row.incidence().kind() == IncidenceKind::RewriteInterface));
    let rewrite_constituent = one_rewrite.regional()[0].constituent();
    let rewrite_behavior = rewrite_constituent.boundary_behavior().unwrap();
    let (recompressed, certificate) = rewrite_constituent.clone().compress_certified().unwrap();
    assert_eq!(recompressed.boundary_behavior().unwrap(), rewrite_behavior);
    assert_eq!(certificate.behavior(), &rewrite_behavior);
    assert_eq!(one.standing().constituents().len(), 2);

    let one_rest = one.rest_image().unwrap();
    let many_rest = many.rest_image().unwrap();
    let card_rest = card.rest_image().unwrap();
    assert_eq!(one_rest, many_rest);
    assert_eq!(one_rest, card_rest);
    let rest_words = card_rest.encode_native_words().unwrap();
    let reopened_image = soma_membrane::LiveCurrentRestImage::from_native_words(&rest_words)
        .expect("the joint cellular successor crosses one exact durable rest boundary");
    let reopened = LiveCurrentMachine::from_rest_image(reopened_image).unwrap();
    assert_eq!(reopened.standing(), card.standing());
    assert_eq!(reopened.memory(), card.memory());
    assert_eq!(cuda.contact_launches(), 6);
    assert!(cuda.parallel_contact_lanes() >= 29);
    assert!(cuda.stack_growths() > 0);
    assert!(cuda.stack_limit_bytes() >= LIVE_COMPLEX_STACK_MIN_BYTES);

    println!(
            "device={:?} triangle_cells=21 triangle_incidences=27 rewrite_cells=12 rewrite_incidences=6 source_grain=3 boundary_squared=0 regional_cells=4 standing_constituents={} triangle_exposed_pins={} rewrite_exposed_pins={} contact_launches={} parallel_contact_lanes={} lineage_launches={} retries={} stack_growths={} stack_bytes={} rest_words={}",
            cuda.device_name(),
            card.standing().constituents().len(),
            constituent.exposed().len(),
            rewrite_constituent.exposed().len(),
            cuda.contact_launches(),
            cuda.parallel_contact_lanes(),
            cuda.launches() - cuda.contact_launches(),
            cuda.resource_retries(),
            cuda.stack_growths(),
            cuda.stack_limit_bytes(),
            rest_words.len(),
        );
}

#[test]
#[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
fn one_cuda_mouth_matches_cpu_through_found_departure_and_later_ride() {
    let standing = SparseStandingSurface::empty_rank(6).unwrap();
    let mut cpu = LiveCurrentMachine::new(standing.clone());
    let mut card = LiveCurrentMachine::new(standing);
    let first = [relation(13)];
    let cpu_main = cpu.attach(&first).unwrap();
    let card_main = card.attach(&first).unwrap();
    let mut cuda = CudaLiveCurrentExecutor::new(0).unwrap();
    // A second exact owner may lawfully mount the same card and become current between
    // construction and enactment. The retained live-current owner must reactivate its own
    // context before touching its module or allocations.
    let device = Device::get(0).unwrap();
    let foreign_context = Context::create(&device).unwrap();

    for value in [13, 29, 17, 31, -63_245, 47, 71, -89] {
        let event = [relation(value)];
        let cpu_return = cpu
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                cpu_main,
                &event,
                action(),
            )]))
            .unwrap();
        let card_return = card
            .receive_with(
                ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                    card_main,
                    &event,
                    action(),
                )]),
                &mut cuda,
            )
            .unwrap();
        assert_eq!(cpu_return, card_return);
        assert_live_equal(&cpu, &card, &[(cpu_main, card_main)]);
        foreign_context.make_current().unwrap();
    }

    let constituent_first = [relation(101)];
    let cpu_constituent = cpu.attach(&constituent_first).unwrap();
    let card_constituent = card.attach(&constituent_first).unwrap();
    let cpu_return = cpu
        .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
            cpu_constituent,
            &constituent_first,
            action(),
        )]))
        .unwrap();
    let card_return = card
        .receive_with(
            ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                card_constituent,
                &constituent_first,
                action(),
            )]),
            &mut cuda,
        )
        .unwrap();
    assert_eq!(cpu_return, card_return);

    let constituent_end = [relation(103)];
    let cpu_return = cpu
        .receive(ContemporaryEvent::unrelated(&[CurrentEvent::ending(
            cpu_constituent,
            &constituent_end,
            action(),
        )]))
        .unwrap();
    let card_return = card
        .receive_with(
            ContemporaryEvent::unrelated(&[CurrentEvent::ending(
                card_constituent,
                &constituent_end,
                action(),
            )]),
            &mut cuda,
        )
        .unwrap();
    assert_eq!(cpu_return, card_return);
    assert!(!cpu.contains(cpu_constituent));
    assert!(!card.contains(card_constituent));

    let later = [relation(-253)];
    let cpu_return = cpu
        .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
            cpu_main,
            &later,
            action(),
        )]))
        .unwrap();
    let card_return = card
        .receive_with(
            ContemporaryEvent::unrelated(&[CurrentEvent::continuing(card_main, &later, action())]),
            &mut cuda,
        )
        .unwrap();
    assert_eq!(cpu_return, card_return);
    assert_live_equal(&cpu, &card, &[(cpu_main, card_main)]);
    assert!(cuda.device_name().contains("NVIDIA"));
    assert_eq!(cuda.launches(), 11 + cuda.resource_retries());
}

#[test]
#[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
fn directed_current_hand_is_formed_on_card_and_matches_cpu() {
    fn primed_pair() -> (
        LiveCurrentMachine,
        soma_membrane::CurrentLineage,
        soma_membrane::CurrentLineage,
    ) {
        let first = [relation(13)];
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let left = machine.attach(&first).unwrap();
        let right = machine.attach(&first).unwrap();
        for value in [13, 29, 17, 31, -63_245, 47] {
            let face = [relation(value)];
            machine
                .receive(ContemporaryEvent::unrelated(&[
                    CurrentEvent::continuing(left, &face, action()),
                    CurrentEvent::continuing(right, &face, action()),
                ]))
                .unwrap();
        }
        let right_ahead = [relation(71)];
        machine
            .receive(ContemporaryEvent::unrelated(&[CurrentEvent::continuing(
                right,
                &right_ahead,
                action(),
            )]))
            .unwrap();
        let left_turn = [relation(71)];
        let right_turn = [relation(-89)];
        machine
            .receive(ContemporaryEvent::unrelated(&[
                CurrentEvent::continuing(left, &left_turn, action()),
                CurrentEvent::continuing(right, &right_turn, action()),
            ]))
            .unwrap();
        (machine, left, right)
    }

    let (baseline, left, right) = primed_pair();
    let before_rank = baseline.standing().rank();
    let before_cells = baseline.standing().cells().len();
    let rest = baseline.rest_image().unwrap();
    let mut cpu_forward = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card_forward = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut cpu_reverse = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card_reverse = LiveCurrentMachine::from_rest_image(rest).unwrap();
    let mut cuda = CudaLiveCurrentExecutor::new(0).unwrap();

    let left_face = [relation(-89)];
    let right_face = [relation(97)];
    let forward_currents = [
        CurrentEvent::continuing(left, &left_face, action()),
        CurrentEvent::continuing(right, &right_face, action()),
    ];
    let reverse_currents = [
        CurrentEvent::continuing(left, &left_face, action()),
        CurrentEvent::continuing(right, &right_face, action()),
    ];
    let forward_relation = [DirectedCurrentRelation::new(left, right)];
    let reverse_relation = [DirectedCurrentRelation::new(right, left)];

    let cpu_forward_return = cpu_forward
        .receive(ContemporaryEvent::new(&forward_currents, &forward_relation))
        .unwrap();
    let card_forward_return = card_forward
        .receive_with(
            ContemporaryEvent::new(&forward_currents, &forward_relation),
            &mut cuda,
        )
        .unwrap();
    assert_eq!(cpu_forward_return, card_forward_return);
    assert_live_equal(
        &cpu_forward,
        &card_forward,
        &[(left, left), (right, right)],
    );

    let cpu_reverse_return = cpu_reverse
        .receive(ContemporaryEvent::new(&reverse_currents, &reverse_relation))
        .unwrap();
    let card_reverse_return = card_reverse
        .receive_with(
            ContemporaryEvent::new(&reverse_currents, &reverse_relation),
            &mut cuda,
        )
        .unwrap();
    assert_eq!(cpu_reverse_return, card_reverse_return);
    assert_live_equal(
        &cpu_reverse,
        &card_reverse,
        &[(left, left), (right, right)],
    );

    assert_eq!(
        cpu_forward_return.currents(),
        cpu_reverse_return.currents()
    );
    assert_ne!(
        cpu_forward_return.relations()[0].contact(),
        cpu_reverse_return.relations()[0].contact()
    );
    assert_ne!(cpu_forward.standing(), cpu_reverse.standing());
    assert_eq!(cuda.directed_contacts(), 2);
    assert_eq!(cuda.launches(), 4 + cuda.resource_retries());
    println!(
            "device={:?} stack={} launches={} retries={} directed_contacts={} before_rank={} before_cells={} forward_after_rank={} forward_after_cells={} reverse_after_rank={} reverse_after_cells={}",
            cuda.device_name(),
            cuda.stack_limit_bytes(),
            cuda.launches(),
            cuda.resource_retries(),
            cuda.directed_contacts(),
            before_rank,
            before_cells,
            cpu_forward.standing().rank(),
            cpu_forward.standing().cells().len(),
            cpu_reverse.standing().rank(),
            cpu_reverse.standing().cells().len(),
        );
}

#[test]
#[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
fn program_world_hand_crosses_the_native_cuda_mouth() {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum ProgramLaw {
        Independent,
        LeftWritesRight,
        RightWritesLeft,
    }

    struct ProgramEvent {
        left: [RelationAtom; 1],
        right: [RelationAtom; 1],
        relations: Vec<NativeEventRelation>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct ProgramReturn {
        changes: [Option<RelationAtom>; 2],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct ProgramWorldImage {
        state: [i64; 2],
        law: ProgramLaw,
    }

    struct ProgramWorld {
        state: [i64; 2],
        law: ProgramLaw,
        received_contacts: usize,
        pending: Option<ProgramReturn>,
    }

    impl ProgramWorld {
        fn new(law: ProgramLaw) -> Self {
            Self {
                state: [1_000, -1_000],
                law,
                received_contacts: 0,
                pending: None,
            }
        }

        fn change(&mut self, next: [i64; 2]) -> ProgramEvent {
            let left = next[0] - self.state[0];
            let right = next[1] - self.state[1];
            self.state = next;
            let relations = match self.law {
                ProgramLaw::Independent => Vec::new(),
                ProgramLaw::LeftWritesRight => vec![NativeEventRelation::new(0, 1)],
                ProgramLaw::RightWritesLeft => vec![NativeEventRelation::new(1, 0)],
            };
            ProgramEvent {
                left: [relation(left)],
                right: [relation(right)],
                relations,
            }
        }

        fn observe_by(&mut self, difference: [i64; 2]) -> ProgramEvent {
            self.state = [
                self.state[0]
                    .checked_add(difference[0])
                    .expect("the bounded program register remains exact"),
                self.state[1]
                    .checked_add(difference[1])
                    .expect("the bounded program register remains exact"),
            ];
            ProgramEvent {
                left: [relation(difference[0])],
                right: [relation(difference[1])],
                relations: Vec::new(),
            }
        }

        fn receive(
            &mut self,
            relations: &[NativeEventRelation],
            radiation: &ContemporaryRadiation,
        ) {
            assert!(
                self.pending.is_none(),
                "an actual world return is still open"
            );
            assert_eq!(relations.len(), radiation.relations().len());
            let mut changes = [0i64; 2];
            for (relation, row) in relations.iter().zip(radiation.relations()) {
                self.received_contacts += 1;
                let Some(emission) = row.contact().emission else {
                    continue;
                };
                let change = [emission.term.chi.other, emission.term.chi.same]
                    .into_iter()
                    .find(|arm| arm.mag != 0)
                    .expect("a formed program deed carries a nonzero arm")
                    .face();
                changes[relation.to()] = changes[relation.to()]
                    .checked_add(change)
                    .expect("co-present program deeds remain inside the bounded register");
            }

            let mut returned = [None, None];
            for member in 0..2 {
                if changes[member] != 0 {
                    self.state[member] = self.state[member]
                        .checked_add(changes[member])
                        .expect("the bounded program register remains exact");
                    returned[member] = Some(relation(changes[member]));
                }
            }
            if returned.iter().any(Option::is_some) {
                self.pending = Some(ProgramReturn { changes: returned });
            }
        }

        fn take_return(&mut self) -> Option<ProgramReturn> {
            self.pending.take()
        }

        fn checkpoint(&self) -> Option<ProgramWorldImage> {
            self.pending.is_none().then_some(ProgramWorldImage {
                state: self.state,
                law: self.law,
            })
        }

        fn recover(image: ProgramWorldImage) -> Self {
            Self {
                state: image.state,
                law: image.law,
                received_contacts: 0,
                pending: None,
            }
        }
    }

    fn primed_native_pair() -> (LiveCurrentMachine, NativeRelationOrgan, NativeRelationOrgan) {
        let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).unwrap());
        let mut left = NativeRelationOrgan::new();
        let mut right = NativeRelationOrgan::new();
        for value in [13, 29, 17, 31, -63_245, 47] {
            let left_face = [relation(value)];
            let right_face = [relation(value)];
            let mut currents = [
                NativeEventCurrent::continuing(&mut left, &left_face, action()),
                NativeEventCurrent::continuing(&mut right, &right_face, action()),
            ];
            present_native_event(&mut machine, &mut currents, &[]).unwrap();
        }
        let right_ahead = [relation(71)];
        right
            .present(&mut machine, &right_ahead, action(), false)
            .unwrap();
        let left_turn = [relation(71)];
        let right_turn = [relation(-89)];
        let mut currents = [
            NativeEventCurrent::continuing(&mut left, &left_turn, action()),
            NativeEventCurrent::continuing(&mut right, &right_turn, action()),
        ];
        present_native_event(&mut machine, &mut currents, &[]).unwrap();
        (machine, left, right)
    }

    fn enact_program_world(
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
        left: &mut NativeRelationOrgan,
        right: &mut NativeRelationOrgan,
        world: &mut ProgramWorld,
    ) -> ContemporaryRadiation {
        let event = world.change([911, -903]);
        let radiation = {
            let mut currents = [
                NativeEventCurrent::continuing(left, &event.left, action()),
                NativeEventCurrent::continuing(right, &event.right, action()),
            ];
            present_native_event_with(machine, executor, &mut currents, &event.relations).unwrap()
        };
        world.receive(&event.relations, &radiation);
        radiation
    }

    fn return_program_consequence(
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
        left: &mut NativeRelationOrgan,
        right: &mut NativeRelationOrgan,
        world: &mut ProgramWorld,
    ) -> ContemporaryRadiation {
        let returned = world
            .take_return()
            .expect("the formed world deed supplies one genuinely later event");
        let radiation = match returned.changes {
            [Some(left_change), Some(right_change)] => {
                let left_face = [left_change];
                let right_face = [right_change];
                let mut currents = [
                    NativeEventCurrent::continuing(left, &left_face, action()),
                    NativeEventCurrent::continuing(right, &right_face, action()),
                ];
                present_native_event_with(machine, executor, &mut currents, &[]).unwrap()
            }
            [Some(left_change), None] => {
                let left_face = [left_change];
                left.present_with(machine, executor, &left_face, action(), false)
                    .unwrap()
            }
            [None, Some(right_change)] => {
                let right_face = [right_change];
                right
                    .present_with(machine, executor, &right_face, action(), false)
                    .unwrap()
            }
            [None, None] => unreachable!("an empty world return is natural rest"),
        };
        world.receive(&[], &radiation);
        radiation
    }

    let (baseline, left, right) = primed_native_pair();
    let before_rank = baseline.standing().rank();
    let before_cells = baseline.standing().cells().len();
    let rest = baseline.rest_image().unwrap();
    let left_image = left.checkpoint();
    let right_image = right.checkpoint();

    let mut cpu_forward = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card_forward = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut cpu_reverse = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card_reverse = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut cpu_independent = LiveCurrentMachine::from_rest_image(rest.clone()).unwrap();
    let mut card_independent = LiveCurrentMachine::from_rest_image(rest).unwrap();

    let mut cpu_forward_left = NativeRelationOrgan::recover(left_image, &cpu_forward).unwrap();
    let mut cpu_forward_right = NativeRelationOrgan::recover(right_image, &cpu_forward).unwrap();
    let mut card_forward_left = NativeRelationOrgan::recover(left_image, &card_forward).unwrap();
    let mut card_forward_right = NativeRelationOrgan::recover(right_image, &card_forward).unwrap();
    let mut cpu_reverse_left = NativeRelationOrgan::recover(left_image, &cpu_reverse).unwrap();
    let mut cpu_reverse_right = NativeRelationOrgan::recover(right_image, &cpu_reverse).unwrap();
    let mut card_reverse_left = NativeRelationOrgan::recover(left_image, &card_reverse).unwrap();
    let mut card_reverse_right = NativeRelationOrgan::recover(right_image, &card_reverse).unwrap();
    let mut cpu_independent_left =
        NativeRelationOrgan::recover(left_image, &cpu_independent).unwrap();
    let mut cpu_independent_right =
        NativeRelationOrgan::recover(right_image, &cpu_independent).unwrap();
    let mut card_independent_left =
        NativeRelationOrgan::recover(left_image, &card_independent).unwrap();
    let mut card_independent_right =
        NativeRelationOrgan::recover(right_image, &card_independent).unwrap();

    let mut cuda = CudaLiveCurrentExecutor::new(0).unwrap();
    let mut cpu_executor = CpuLiveCurrentExecutor;
    let mut cpu_forward_world = ProgramWorld::new(ProgramLaw::LeftWritesRight);
    let mut card_forward_world = ProgramWorld::new(ProgramLaw::LeftWritesRight);
    let cpu_forward_return = enact_program_world(
        &mut cpu_forward,
        &mut cpu_executor,
        &mut cpu_forward_left,
        &mut cpu_forward_right,
        &mut cpu_forward_world,
    );
    let card_forward_return = enact_program_world(
        &mut card_forward,
        &mut cuda,
        &mut card_forward_left,
        &mut card_forward_right,
        &mut card_forward_world,
    );

    let mut cpu_reverse_world = ProgramWorld::new(ProgramLaw::RightWritesLeft);
    let mut card_reverse_world = ProgramWorld::new(ProgramLaw::RightWritesLeft);
    let cpu_reverse_return = enact_program_world(
        &mut cpu_reverse,
        &mut cpu_executor,
        &mut cpu_reverse_left,
        &mut cpu_reverse_right,
        &mut cpu_reverse_world,
    );
    let card_reverse_return = enact_program_world(
        &mut card_reverse,
        &mut cuda,
        &mut card_reverse_left,
        &mut card_reverse_right,
        &mut card_reverse_world,
    );

    let mut cpu_independent_world = ProgramWorld::new(ProgramLaw::Independent);
    let mut card_independent_world = ProgramWorld::new(ProgramLaw::Independent);
    let cpu_independent_return = enact_program_world(
        &mut cpu_independent,
        &mut cpu_executor,
        &mut cpu_independent_left,
        &mut cpu_independent_right,
        &mut cpu_independent_world,
    );
    let card_independent_return = enact_program_world(
        &mut card_independent,
        &mut cuda,
        &mut card_independent_left,
        &mut card_independent_right,
        &mut card_independent_world,
    );

    assert_eq!(cpu_forward_return, card_forward_return);
    assert_eq!(cpu_reverse_return, card_reverse_return);
    assert_eq!(cpu_independent_return, card_independent_return);
    assert_live_equal(
        &cpu_forward,
        &card_forward,
        &[
            (left_image.lineage().unwrap(), left_image.lineage().unwrap()),
            (
                right_image.lineage().unwrap(),
                right_image.lineage().unwrap(),
            ),
        ],
    );
    assert_live_equal(
        &cpu_reverse,
        &card_reverse,
        &[
            (left_image.lineage().unwrap(), left_image.lineage().unwrap()),
            (
                right_image.lineage().unwrap(),
                right_image.lineage().unwrap(),
            ),
        ],
    );
    assert_live_equal(
        &cpu_independent,
        &card_independent,
        &[
            (left_image.lineage().unwrap(), left_image.lineage().unwrap()),
            (
                right_image.lineage().unwrap(),
                right_image.lineage().unwrap(),
            ),
        ],
    );

    assert_eq!(
        cpu_forward_return.currents(),
        cpu_reverse_return.currents()
    );
    assert_eq!(
        cpu_forward_return.currents(),
        cpu_independent_return.currents()
    );
    assert_eq!(cpu_forward_return.relations().len(), 1);
    assert_eq!(cpu_reverse_return.relations().len(), 1);
    assert!(cpu_independent_return.relations().is_empty());
    assert!(cpu_forward_return.relations()[0]
        .contact()
        .emission
        .is_some());
    assert!(cpu_reverse_return.relations()[0]
        .contact()
        .emission
        .is_none());
    assert_ne!(cpu_forward.standing(), cpu_reverse.standing());
    assert_ne!(cpu_forward.standing(), cpu_independent.standing());
    assert_eq!(cpu_forward_world.received_contacts, 1);
    assert_eq!(card_forward_world.received_contacts, 1);
    assert_eq!(cpu_reverse_world.received_contacts, 1);
    assert_eq!(card_reverse_world.received_contacts, 1);
    assert_eq!(cpu_independent_world.received_contacts, 0);
    assert_eq!(card_independent_world.received_contacts, 0);
    assert_eq!(cpu_forward_world.pending, card_forward_world.pending);
    assert!(card_forward_world.pending.is_some());
    assert!(cpu_forward_world.checkpoint().is_none());
    assert!(card_forward_world.checkpoint().is_none());
    assert!(card_reverse_world.pending.is_none());
    assert!(card_independent_world.pending.is_none());
    assert!(card_reverse_world.checkpoint().is_some());
    assert!(card_independent_world.checkpoint().is_some());
    assert_eq!(cuda.directed_contacts(), 2);
    // **The population crosses once per contemporary EVENT, not once per current.**
    //
    // This read `6 + resource_retries` until 2026-08-10, when `lineage_event` was launched
    // `Dim3::x(1)` and `enact` iterated currents serially — six currents, six crossings. The
    // population mouth enacts a whole contemporary event in one crossing, one lane per current, so
    // the same six currents now cross five times: one of these events carries two currents and they
    // are co-present. The strict inequality is the load-bearing half — it fails if the population
    // path ever degenerates back to one current per crossing.
    assert!(
        cuda.launches() < 6 + cuda.resource_retries(),
        "six currents must cross fewer than six times: {} launches, {} retries",
        cuda.launches(),
        cuda.resource_retries()
    );
    assert_eq!(cuda.launches(), 5 + cuda.resource_retries());

    let forward_contact_cells = card_forward.standing().cells().len();
    let reverse_contact_cells = card_reverse.standing().cells().len();
    let independent_contact_cells = card_independent.standing().cells().len();
    let cpu_before_world_return = cpu_forward.rest_image().unwrap();
    let card_before_world_return = card_forward.rest_image().unwrap();
    assert_eq!(cpu_before_world_return, card_before_world_return);

    let cpu_world_return = return_program_consequence(
        &mut cpu_forward,
        &mut cpu_executor,
        &mut cpu_forward_left,
        &mut cpu_forward_right,
        &mut cpu_forward_world,
    );
    let card_world_return = return_program_consequence(
        &mut card_forward,
        &mut cuda,
        &mut card_forward_left,
        &mut card_forward_right,
        &mut card_forward_world,
    );
    assert_eq!(cpu_world_return, card_world_return);
    assert_eq!(card_world_return.currents().len(), 1);
    assert!(card_world_return.relations().is_empty());
    assert!(cpu_forward_world.pending.is_none());
    assert!(card_forward_world.pending.is_none());
    assert_ne!(card_forward.rest_image().unwrap(), card_before_world_return);
    assert_live_equal(
        &cpu_forward,
        &card_forward,
        &[
            (left_image.lineage().unwrap(), left_image.lineage().unwrap()),
            (
                right_image.lineage().unwrap(),
                right_image.lineage().unwrap(),
            ),
        ],
    );
    assert_eq!(
        cpu_forward_world.checkpoint(),
        card_forward_world.checkpoint()
    );

    let card_rest = card_forward.rest_image().unwrap();
    let card_left_rest = card_forward_left.checkpoint();
    let card_right_rest = card_forward_right.checkpoint();
    let card_world_rest = card_forward_world
        .checkpoint()
        .expect("every available card consequence returned before rest");
    let resting_cells = card_forward.standing().cells().len();
    let launches_at_rest = cuda.launches();

    // Waiting is not an event. It neither launches the card nor changes the joint rest face.
    assert!(card_forward_world.take_return().is_none());
    assert_eq!(cuda.launches(), launches_at_rest);
    assert_eq!(card_forward.rest_image().unwrap(), card_rest);
    assert_eq!(card_forward_left.checkpoint(), card_left_rest);
    assert_eq!(card_forward_right.checkpoint(), card_right_rest);
    assert_eq!(card_forward_world.checkpoint().unwrap(), card_world_rest);
    let wait_launches = cuda.launches() - launches_at_rest;

    let mut card_woken = LiveCurrentMachine::from_rest_image(card_rest).unwrap();
    let mut card_woken_left = NativeRelationOrgan::recover(card_left_rest, &card_woken).unwrap();
    let mut card_woken_right = NativeRelationOrgan::recover(card_right_rest, &card_woken).unwrap();
    let mut card_woken_world = ProgramWorld::recover(card_world_rest);

    let cpu_probe = cpu_forward_world.observe_by([-253, 257]);
    let card_probe = card_woken_world.observe_by([-253, 257]);
    assert_eq!(cpu_probe.left, card_probe.left);
    assert_eq!(cpu_probe.right, card_probe.right);
    let cpu_probe_return = {
        let mut currents = [
            NativeEventCurrent::continuing(&mut cpu_forward_left, &cpu_probe.left, action()),
            NativeEventCurrent::continuing(&mut cpu_forward_right, &cpu_probe.right, action()),
        ];
        present_native_event_with(&mut cpu_forward, &mut cpu_executor, &mut currents, &[])
            .unwrap()
    };
    cpu_forward_world.receive(&[], &cpu_probe_return);
    let card_probe_return = {
        let mut currents = [
            NativeEventCurrent::continuing(&mut card_woken_left, &card_probe.left, action()),
            NativeEventCurrent::continuing(&mut card_woken_right, &card_probe.right, action()),
        ];
        present_native_event_with(&mut card_woken, &mut cuda, &mut currents, &[]).unwrap()
    };
    card_woken_world.receive(&[], &card_probe_return);

    assert_eq!(cpu_probe_return, card_probe_return);
    assert_live_equal(
        &cpu_forward,
        &card_woken,
        &[
            (left_image.lineage().unwrap(), left_image.lineage().unwrap()),
            (
                right_image.lineage().unwrap(),
                right_image.lineage().unwrap(),
            ),
        ],
    );
    assert_eq!(
        cpu_forward_world.checkpoint(),
        card_woken_world.checkpoint()
    );
    assert_eq!(cuda.directed_contacts(), 2);
    // The same correction as above, further along this world: nine currents, and the two that share
    // a contemporary event now cross together.
    assert!(
        cuda.launches() < 9 + cuda.resource_retries(),
        "nine currents must cross fewer than nine times: {} launches, {} retries",
        cuda.launches(),
        cuda.resource_retries()
    );
    assert_eq!(cuda.launches(), 7 + cuda.resource_retries());

    println!(
            "device={:?} stack={} launches={} retries={} directed_contacts={} before_rank={} before_cells={} forward_contact_cells={} reverse_contact_cells={} independent_contact_cells={} return_currents={} resting_cells={} wait_launches={} wake_cells={} reverse_open={} independent_relations={}",
            cuda.device_name(),
            cuda.stack_limit_bytes(),
            cuda.launches(),
            cuda.resource_retries(),
            cuda.directed_contacts(),
            before_rank,
            before_cells,
            forward_contact_cells,
            reverse_contact_cells,
            independent_contact_cells,
            card_world_return.currents().len(),
            resting_cells,
            wait_launches,
            card_woken.standing().cells().len(),
            card_reverse_world.pending.is_none(),
            card_independent_return.relations().len(),
        );
}
