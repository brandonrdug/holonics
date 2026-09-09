//! The local native return retains sparse overlap factors and its actual producing map.
//! It is not a publication API: the field's joined journal must carry these dependencies.
use super::*;

pub(in super::super) struct NativeCausalContactReturn<'c> {
    surface: &'c ResidentSurface<'c>,
    _owner: Rc<()>,
    _origin: Rc<()>,
    producing: Rc<OperativeSections<'c>>,
    forward: Rc<ResidentSection<'c>>,
    pub(super) incoming: Rc<ResidentSection<'c>>,
    pub(in super::super) overlaps: Rc<ResidentSection<'c>>,
    pub(in super::super) errors: Rc<ResidentSection<'c>>,
    pub(in super::super) bounds: Rc<ResidentSection<'c>>,
    count: usize,
    d: usize,
    grain: u32,
}

#[derive(Debug, Serialize)]
pub(in super::super) struct CausalContactReturnReading {
    pub incoming_internal: NativeFieldCurrentBall,
    pub contact_covector: Vec<Vec<ExactComplexWaveCurrent>>,
    pub contact_covector_radius: Rat,
    pub overlaps: Vec<ExactComplexWaveCurrent>,
    pub overlap_radii: Vec<Rat>,
}

impl<'f, 'c> NativeCausalContactPropagation<'f, 'c> {
    /// A native ball covector supplied by the enclosing producer. No authored learning delta
    /// or selected face enters here. The source field remains borrowed by the forward owner.
    pub(in super::super) fn pull_back(
        &self,
        covector: &ResidentSection<'c>,
    ) -> Result<NativeCausalContactReturn<'c>, Error> {
        let surface = self.field.relation.surface;
        let count = self.births.len();
        let d = 6 * self.field.nodes();
        let incoming = Rc::new(surface.fresh_section(count.max(1), 4, ResidentGrain(0))?);
        let overlaps = Rc::new(surface.fresh_section(count.max(1), 4, ResidentGrain(0))?);
        let errors = Rc::new(surface.fresh_section(count.max(1), 2, ResidentGrain(0))?);
        let bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_causal_contact_pullback(
                &lane,
                [
                    &self._producing.map,
                    &self._producing.bounds,
                    &self.trace,
                    covector,
                ],
                d,
                count,
                self.grain,
                [&incoming, &overlaps, &errors, &bounds],
            )?;
        }
        passage.close(0, &bounds, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "causal contact return: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeCausalContactReturn {
            surface,
            _owner: Rc::clone(&self.field.owner),
            _origin: Rc::clone(&self._origin),
            producing: Rc::clone(&self._producing),
            forward: Rc::clone(&self.trace),
            incoming,
            overlaps,
            errors,
            bounds,
            count,
            d,
            grain: self.grain,
        })
    }
}

impl NativeCausalContactReturn<'_> {
    /// Cold dense projection of D_source H; resident factors remain sparse and source-qualified.
    pub(in super::super) fn inspect(&self) -> Result<CausalContactReturnReading, Error> {
        let read = |s: &ResidentSection<'_>| -> Result<Vec<i128>, Error> {
            wides(&self.surface.detach_section(s, 64)?.intervals)
        };
        let input = read(&self.incoming)?;
        let overlaps = read(&self.overlaps)?;
        let errors = read(&self.errors)?;
        let bounds = read(&self.bounds)?;
        let map = read(&self.producing.map)?;
        let trace = self.surface.detach_section(&self.forward, 64)?;
        let scale = BigInt::one() << self.grain;
        let rat = |value: i128| Rat::new(value.into(), scale.clone());
        let waves = |values: &[i128]| {
            values
                .chunks_exact(2)
                .map(|v| ExactComplexWaveCurrent::new(rat(v[0]), rat(v[1])))
                .collect::<Vec<_>>()
        };
        let overlaps = waves(&overlaps[..2 * self.count]);
        let contacts = map
            .chunks_exact(self.d)
            .take(self.count)
            .map(waves)
            .collect::<Vec<_>>();
        let mut covector = vec![vec![ExactComplexWaveCurrent::zero(); self.d / 2]; self.count];
        for (after, row) in trace
            .intervals
            .chunks_exact(Layout::WORDS)
            .take(self.count)
            .enumerate()
        {
            if row[0].0 == -1 {
                continue;
            }
            let before = usize::try_from(row[0].0).map_err(invalid)?;
            if before >= after {
                return Err(Error::Shape);
            }
            for j in 0..self.d / 2 {
                covector[before][j] = covector[before][j]
                    .add(&contacts[after][j].multiply(&overlaps[after].conjugate()));
                covector[after][j] =
                    covector[after][j].add(&contacts[before][j].multiply(&overlaps[after]));
            }
        }
        Ok(CausalContactReturnReading {
            incoming_internal: NativeFieldCurrentBall {
                center: waves(&input[..2 * self.count]),
                radius: rat(bounds[0]),
            },
            contact_covector: covector,
            contact_covector_radius: rat(bounds[1]),
            overlaps,
            overlap_radii: errors[..self.count].iter().copied().map(rat).collect(),
        })
    }
}
