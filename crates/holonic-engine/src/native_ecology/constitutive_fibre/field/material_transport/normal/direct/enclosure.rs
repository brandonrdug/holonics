use super::*;

/// A declared joint Euclidean enclosure. The encoded centre and radius are one input family;
/// there is no point-current conversion. The producing return keeps its finer operand relation.
#[derive(Clone, Copy)]
pub struct ResidentNormalEnclosureView<'a, 'c> {
    pub(crate) surface: &'c ResidentSurface<'c>,
    pub(crate) section: &'a ResidentSection<'c>,
    pub(crate) offset: usize,
    pub(crate) width: usize,
    pub(crate) grain: ResidentGrain,
}
pub struct ResidentNormalEnclosure<'c> {
    pub(super) surface: &'c ResidentSurface<'c>,
    pub(super) section: ResidentSection<'c>,
    pub(super) width: usize,
    pub(super) grain: ResidentGrain,
}
impl<'c> ResidentNormalEnclosure<'c> {
    pub(crate) fn from_resident(
        surface: &'c ResidentSurface<'c>,
        section: ResidentSection<'c>,
        width: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if width == 0
            || width % 2 != 0
            || section.rows() != 1
            || section.width() != 2 * (width + 1)
            || section.grain().0 != 0
            || !std::ptr::eq(section.surface(), surface)
            || !(1..=120).contains(&grain.0)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(Self {
            surface,
            section,
            width,
            grain,
        })
    }

    /// Restore the declared complete ball from an exterior point-word chart.
    pub fn remount(
        surface: &'c ResidentSurface<'c>,
        rest: ResidentSectionRest,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if rest.rows != 1 || rest.width < 6 || rest.width % 2 != 0 || !(1..=120).contains(&grain.0)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = rest.width / 2 - 1;
        if width % 2 != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        crate::native_ecology::constitutive_fibre::circulation::rest::point_section(
            &rest,
            1,
            2 * (width + 1),
        )?;
        if wides(&rest.intervals)?[width] < 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(Self {
            surface,
            section: surface.mount_section_rest(&rest)?,
            width,
            grain,
        })
    }
    pub fn rest(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.section, 64)?)
    }
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
    pub(crate) fn surface(&self) -> &ResidentSurface<'_> {
        self.surface
    }
    pub(crate) fn section(&self) -> &ResidentSection<'_> {
        self.section
    }
    pub(crate) fn offset(&self) -> usize {
        self.offset
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
impl<'a, 'c> ResidentNormalEnclosureView<'a, 'c> {
    /// Read the exact point only when the entire declared ball has radius zero.
    /// A nonzero radius or an unrepresentable reduced rational returns an obstruction.
    pub fn read_exact_point(self) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
        let width = self
            .width
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let out = self.surface.fresh_section(1, width, ResidentGrain(0))?;
        let work = self.surface.fresh_section(
            1,
            self.width
                .checked_mul(2)
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let mut p = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            self.surface
                .record_normal_exact_point(&lane, self, &work, &out)?;
        }
        p.close(0, &out, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "exact point of declared ball: {:?}",
                r.obstruction
            )));
        }
        Ok(out)
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
impl<'a, 'c> ResidentNormalInput<'a, 'c> {
    /// Use the common normal-input conversion, retaining its full radius and any
    /// rational-to-dyadic rounding. An existing enclosure must have the requested grain.
    pub fn enclosure(
        self,
        surface: &'c ResidentSurface<'c>,
        grain: ResidentGrain,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let width = self.width();
        let words = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = surface.fresh_section(1, words, ResidentGrain(0))?;
        let mut p = surface.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            surface.record_normal_enclose_input(&lane, self, grain, &section)?;
        }
        p.close(0, &section, 64)?;
        let r = p.finish()?.launch()?;
        if !r.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normal input enclosure: {:?}",
                r.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface,
            section,
            width,
            grain,
        })
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
