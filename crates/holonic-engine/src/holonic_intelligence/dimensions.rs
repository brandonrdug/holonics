/// A situated dimension whose species is carried by its Rust type.
macro_rules! dimension {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $name(pub usize);
    };
}

dimension!(TopologicalDegree);
dimension!(IncidenceRank);
dimension!(IncidenceNullity);
dimension!(CycleRank);
dimension!(CarrierRank);
dimension!(ExteriorDegree);
dimension!(RepresentationRank);
dimension!(GeneratorExtent);
dimension!(ReceiverExtent);
dimension!(ReconstructionExtent);
dimension!(ScaleExtent);
dimension!(ApparatusWork);

/// Why one dimension cannot yet be returned from the native structural owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DimensionObstruction {
    ScaleChartOutsideNativeThread,
    ApparatusWorkOutsideNativeRest,
}

/// An exact dimension or its typed open obligation. Unknown is never encoded as zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DimensionFace<Dimension> {
    Exact(Dimension),
    Open(DimensionObstruction),
}

/// Non-conflated dimension faces of one intrinsic native holon profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntrinsicHolonDimensions {
    pub topological_degree: DimensionFace<TopologicalDegree>,
    pub incidence_rank: DimensionFace<IncidenceRank>,
    pub incidence_nullity: DimensionFace<IncidenceNullity>,
    pub cycle_rank: DimensionFace<CycleRank>,
    pub carrier_rank: DimensionFace<CarrierRank>,
    pub exterior_degree: DimensionFace<ExteriorDegree>,
    pub representation_rank: DimensionFace<RepresentationRank>,
    pub generator_extent: DimensionFace<GeneratorExtent>,
    pub receiver_extent: DimensionFace<ReceiverExtent>,
    pub reconstruction_extent: DimensionFace<ReconstructionExtent>,
    pub scale_extent: DimensionFace<ScaleExtent>,
    pub apparatus_work: DimensionFace<ApparatusWork>,
}
