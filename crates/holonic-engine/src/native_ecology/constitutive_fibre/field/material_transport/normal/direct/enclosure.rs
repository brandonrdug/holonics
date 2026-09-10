use super::*;

/// A declared joint Euclidean enclosure. The encoded centre and radius are one input family;
/// there is no point-current conversion. The producing return keeps its finer operand relation.
#[derive(Clone, Copy)]
pub struct ResidentNormalEnclosureView<'a, 'c> {
    pub(super) surface: &'c ResidentSurface<'c>,
    pub(crate) section: &'a ResidentSection<'c>,
    pub(crate) offset: usize,
    pub(crate) width: usize,
    pub(crate) grain: ResidentGrain,
}
pub struct ResidentNormalEnclosure<'c> {
    pub(super) surface: &'c ResidentSurface<'c>,
    section: ResidentSection<'c>,
    width: usize,
    grain: ResidentGrain,
}
impl<'c> ResidentNormalEnclosure<'c> {
    pub fn view(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.surface,
            section: &self.section,
            offset: 0,
            width: self.width,
            grain: self.grain,
        }
    }
    pub fn inspect(&self) -> Result<NativeFieldCurrentBall, ConstitutiveFibreError> {
        self.view().inspect()
    }
}
impl ResidentNormalEnclosureView<'_, '_> {
    pub fn components(&self) -> usize {
        self.width
    }
    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }
    pub fn inspect(&self) -> Result<NativeFieldCurrentBall, ConstitutiveFibreError> {
        let words = self.surface.read_out(self.section)?;
        let v = wides(&words[self.offset..self.offset + 2 * (self.width + 1)])?;
        let scale = BigInt::one() << self.grain.0;
        if v[self.width] < 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(NativeFieldCurrentBall {
            center: v[..self.width]
                .chunks_exact(2)
                .map(|v| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(v[0].into(), scale.clone()),
                        Rat::new(v[1].into(), scale.clone()),
                    )
                })
                .collect(),
            radius: Rat::new(v[self.width].into(), scale),
        })
    }
}

#[derive(Clone, Copy)]
pub enum ResidentNormalInput<'a, 'c> {
    Point(ResidentConstitutiveCurrent<'a, 'c>),
    Enclosed(ResidentNormalEnclosureView<'a, 'c>),
}
impl ResidentNormalInput<'_, '_> {
    pub fn width(&self) -> usize {
        match self {
            Self::Point(v) => v.width,
            Self::Enclosed(v) => v.width,
        }
    }
}
impl<'a, 'c> From<ResidentConstitutiveCurrent<'a, 'c>> for ResidentNormalInput<'a, 'c> {
    fn from(v: ResidentConstitutiveCurrent<'a, 'c>) -> Self {
        Self::Point(v)
    }
}
impl<'a, 'c> From<ResidentNormalEnclosureView<'a, 'c>> for ResidentNormalInput<'a, 'c> {
    fn from(v: ResidentNormalEnclosureView<'a, 'c>) -> Self {
        Self::Enclosed(v)
    }
}
impl<'a, 'c> ResidentNormalReturn<'a, 'c> {
    pub fn before(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.surface,
            section: &self.before,
            offset: 0,
            width: 2 * self.targets,
            grain: self.grain,
        }
    }
    pub fn forward(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        ResidentNormalEnclosureView {
            surface: self.surface,
            section: self.after.as_ref().unwrap_or(&self.before),
            offset: 0,
            width: 2 * self.targets,
            grain: self.grain,
        }
    }
    /// Transfer the completed forward enclosure into continuing use without keeping a chain
    /// of source returns. This carries the stated outer family, not an assertion that it is the
    /// exact joint source/output fibre. Keep the original return when that finer relation is needed.
    pub fn into_forward(self) -> ResidentNormalEnclosure<'c> {
        ResidentNormalEnclosure {
            surface: self.surface,
            section: self.after.unwrap_or(self.before),
            width: 2 * self.targets,
            grain: self.grain,
        }
    }
}
