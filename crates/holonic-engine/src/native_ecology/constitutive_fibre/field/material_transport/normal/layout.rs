//! Serialized charts of the normal relation. Extents follow the carried objects; these are
//! not semantic capacities. The device counterpart is `field_normal_material.cuh`.
use std::mem::size_of;

pub(super) struct MomentWire;
impl MomentWire {
    pub const LIMB_BITS: usize = u32::BITS as usize;
    // History pairs multiply two wide components. Adding the homogeneous reference carries
    // one bit, its moment multiplies two such values, and doubled division remainder carries.
    const HISTORY_BITS: usize = 2 * i128::BITS as usize;
    const REQUIRED_BITS: usize = 2 * (Self::HISTORY_BITS + 1) + 1;
    pub const LIMBS: usize = Self::REQUIRED_BITS.div_ceil(Self::LIMB_BITS);
    pub const WORDS: usize = Self::LIMBS + 1; // magnitude limbs followed by sign
    pub const COMPLEX_WORDS: usize = 2 * Self::WORDS;
}

const WIDE_WORDS: usize = size_of::<i128>() / size_of::<i64>();
const QUADRATURES: usize = ["real", "imaginary"].len();
const SOURCE_PORTS: usize = ["outgoing", "held", "target"].len();
const MATRIX_METADATA: usize = ["coefficient radius", "normal residual", "coefficient norm"].len();
const REPORT_METADATA: usize = [
    "coefficient radius",
    "normal residual",
    "coefficient norm",
    "source normal error",
    "cross source error",
]
.len();
pub(super) const STATISTIC_SCALARS: usize = [
    "source normal error",
    "cross source error",
    "target energy",
    "target energy error",
]
.len();

#[derive(Clone, Copy)]
pub(super) enum ReportBall {
    Forward,
    ContemporarySource,
    Observed,
    ReturnedDifference,
    Chronological,
    ContemporaryDifference,
}
impl ReportBall {
    pub const ALL: &'static [Self] = &[
        Self::Forward,
        Self::ContemporarySource,
        Self::Observed,
        Self::ReturnedDifference,
        Self::Chronological,
        Self::ContemporaryDifference,
    ];
}

pub(super) struct NormalLayout {
    pub sources: usize,
    pub source_components: usize,
    pub target_components: usize,
    pub gram_values: usize,
    pub cross_values: usize,
    pub matrix_words: usize,
    pub state_words: usize,
    pub ball_stride: usize,
    pub source_at: usize,
    pub metadata_at: usize,
    pub report_moments_at: usize,
    pub report_words: usize,
    pub workspace_words: usize,
}
impl NormalLayout {
    pub fn new(roots: usize, targets: usize) -> Option<Self> {
        let sources = roots.checked_mul(SOURCE_PORTS)?;
        let source_components = sources.checked_mul(QUADRATURES)?;
        let target_components = targets.checked_mul(QUADRATURES)?;
        let gram_values = sources.checked_mul(source_components)?;
        let cross_values = targets.checked_mul(source_components)?;
        let matrix_words = cross_values
            .checked_add(MATRIX_METADATA)?
            .checked_mul(WIDE_WORDS)?;
        let state_words = gram_values
            .checked_add(cross_values)?
            .checked_add(STATISTIC_SCALARS)?
            .checked_mul(MomentWire::WORDS)?
            .checked_add(matrix_words)?;
        let ball_stride = target_components.checked_add(1)?; // complex centre and one joint radius
        let source_at = ReportBall::ALL.len().checked_mul(ball_stride)?;
        let metadata_at = source_at.checked_add(source_components)?.checked_add(1)?;
        let report_moments_at = metadata_at
            .checked_add(REPORT_METADATA)?
            .checked_mul(WIDE_WORDS)?;
        let report_words = STATISTIC_SCALARS
            .checked_mul(MomentWire::WORDS)?
            .checked_add(report_moments_at)?;
        // LDL square, diagonal, target right-hand sides, then each row's exact residual and norm.
        let factor_words = source_components
            .checked_add(targets)?
            .checked_add(1)?
            .checked_mul(source_components)?
            .checked_mul(WIDE_WORDS)?;
        let row_words = targets.checked_mul(MomentWire::WORDS.checked_add(WIDE_WORDS)?)?;
        let workspace_words = factor_words.checked_add(row_words)?;
        Some(Self {
            sources,
            source_components,
            target_components,
            gram_values,
            cross_values,
            matrix_words,
            state_words,
            ball_stride,
            source_at,
            metadata_at,
            report_moments_at,
            report_words,
            workspace_words,
        })
    }
    pub fn ball_at(&self, ball: ReportBall) -> usize {
        ball as usize * self.ball_stride
    }
    pub fn ball_radius_at(&self, ball: ReportBall) -> usize {
        self.ball_at(ball) + self.target_components
    }
    pub fn cross_words_at(&self) -> usize {
        self.matrix_words + self.gram_values * MomentWire::WORDS
    }
    pub fn scalar_words_at(&self) -> usize {
        self.cross_words_at() + self.cross_values * MomentWire::WORDS
    }
}
