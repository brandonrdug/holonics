use holonic_engine::{
    native_ecology::holonic_intelligence::{IntoDismantlingBoundaryReturn, NativeInferenceRequest},
    native_spool::NativeTransportScaffold,
};
use life::native_intelligence::{
    consume_dismantling_return, ApparatusRealization, DepartedDismantlingLanes, MorphologyLineage,
    NativeCirculationBoundary, NativeCirculationConfiguration, NativeCirculationEvent,
    NativeCirculationSession, NativeCirculationSnapshot, NativeCultivationCandidate,
    NativeDeclineReceipt, NativeDiffusionIngress, NativeDiffusionLaw, NativeDiffusionStanding,
    NativeMorphologyCommit, NativeMorphologyPackage, NativeOwnedInferenceAddress,
    NativeSessionError, ReturnedScaffoldInteraction,
};
use thiserror::Error;

/// One admitted Athena application and the physically separate cold/insufficiency lanes which do
/// not enter its runtime dependency closure.
#[derive(Debug)]
pub struct AthenaAlphaAdmission<ColdWitness, Insufficiency> {
    pub application: AthenaAlphaApplication,
    pub departed: DepartedDismantlingLanes<ColdWitness, Insufficiency>,
}

/// Product-named exterior application over exactly one neutral session owner.
#[derive(Debug)]
pub struct AthenaAlphaApplication {
    session: NativeCirculationSession,
}

#[derive(Debug, Error)]
pub enum AthenaAlphaError {
    #[error("the neutral circulation refused the Athena application: {0}")]
    Circulation(String),
    #[error("the source-neutral application admission refused: {0}")]
    Admission(String),
}

impl From<NativeSessionError> for AthenaAlphaError {
    fn from(error: NativeSessionError) -> Self {
        Self::Circulation(error.to_string())
    }
}

impl AthenaAlphaApplication {
    pub fn mount(
        package: NativeMorphologyPackage,
        configuration: NativeCirculationConfiguration,
    ) -> Result<Self, AthenaAlphaError> {
        Ok(Self {
            session: NativeCirculationSession::mount(package, configuration)?,
        })
    }

    pub fn from_dismantling_return<Returned>(
        returned: Returned,
        configuration: NativeCirculationConfiguration,
    ) -> Result<
        AthenaAlphaAdmission<Returned::ColdWitness, Returned::Insufficiency>,
        AthenaAlphaError,
    >
    where
        Returned: IntoDismantlingBoundaryReturn<Productive = NativeTransportScaffold>,
    {
        let (hot, departed) = consume_dismantling_return(returned)
            .map_err(|error| AthenaAlphaError::Admission(error.to_string()))?;
        let package = NativeMorphologyPackage::found(
            hot,
            MorphologyLineage::origin(),
            Vec::new(),
            vec![ApparatusRealization {
                apparatus_family: "athena-alpha-application".to_owned(),
                realization_version: "v1".to_owned(),
            }],
            Vec::new(),
        )
        .map_err(|error| AthenaAlphaError::Admission(error.to_string()))?;
        Ok(AthenaAlphaAdmission {
            application: Self::mount(package, configuration)?,
            departed,
        })
    }

    pub fn generation(&self) -> u64 {
        self.session.generation()
    }

    pub fn package(&self) -> &NativeMorphologyPackage {
        self.session.package()
    }

    pub fn conduct(
        &self,
        request: NativeInferenceRequest,
    ) -> Result<NativeCirculationBoundary, AthenaAlphaError> {
        Ok(self.session.conduct(request)?)
    }

    pub fn continue_from(
        &self,
        boundary: &NativeCirculationBoundary,
        successor: &NativeOwnedInferenceAddress,
    ) -> Result<NativeCirculationBoundary, AthenaAlphaError> {
        Ok(self.session.continue_from(boundary, successor)?)
    }

    pub fn stage_return(
        &self,
        boundary: &NativeCirculationBoundary,
        returned: ReturnedScaffoldInteraction,
    ) -> Result<NativeCultivationCandidate, AthenaAlphaError> {
        Ok(self.session.stage_return(boundary, returned)?)
    }

    pub fn commit(
        self,
        candidate: NativeCultivationCandidate,
    ) -> Result<(Self, NativeMorphologyCommit), AthenaAlphaError> {
        let (session, commit) = self.session.commit(candidate)?;
        Ok((Self { session }, commit))
    }

    pub fn decline(
        self,
        boundary: &NativeCirculationBoundary,
    ) -> Result<(Self, NativeDeclineReceipt), AthenaAlphaError> {
        let (session, receipt) = self.session.decline(boundary)?;
        Ok((Self { session }, receipt))
    }

    pub fn diffuse(
        &self,
        law: &NativeDiffusionLaw,
        standing: &NativeDiffusionStanding,
        ingress: NativeDiffusionIngress,
    ) -> Result<NativeCirculationEvent, AthenaAlphaError> {
        Ok(self.session.diffuse(law, standing, ingress)?)
    }

    pub fn snapshot(&self) -> Result<NativeCirculationSnapshot, AthenaAlphaError> {
        Ok(self.session.snapshot()?)
    }

    pub fn remount(snapshot: NativeCirculationSnapshot) -> Result<Self, AthenaAlphaError> {
        Ok(Self {
            session: NativeCirculationSession::remount(snapshot)?,
        })
    }
}
