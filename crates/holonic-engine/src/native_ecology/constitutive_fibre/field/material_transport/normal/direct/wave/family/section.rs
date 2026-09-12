//! Conditional source sections used to evaluate an entire dependent return generator.
use super::*;
/// Constructive coordinates of the declared family receiver, retaining all coordinate aliases.
/// The kernel of this coordinate map decodes to zero source difference.
pub struct NormalReceiverCoordinates<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    coordinates: ResidentSection<'c>,
    fibre: ResidentConstitutiveReturn<'c>,
}
/// Exact resident face `(lambda, anchor, p, c; denominator)` returned by a declared family
/// receiver.  It is a bounded face witness, never the whole source family.
pub struct NormalWaveFacePacket<'a, 'c> {
    source: &'a NormalWaveFamily<'c>,
    packet: ResidentSection<'c>,
}
impl<'a, 'c> NormalWaveFacePacket<'a, 'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> { self.source }
    pub fn resident(&self) -> &ResidentSection<'c> { &self.packet }
    pub fn into_resident(self) -> ResidentSection<'c> { self.packet }
}
impl<'a, 'c> NormalReceiverCoordinates<'a, 'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        self.source
    }
    pub fn coordinates(&self) -> &ResidentSection<'c> {
        &self.coordinates
    }
    pub fn coordinate_fibre(&self) -> &ResidentConstitutiveReturn<'c> {
        &self.fibre
    }
    /// The original source decoder retains the full coordinate kernel. This packet merely
    /// encodes its declared receiver face; it does not replace the source or the generator.
    pub fn into_coordinates(self) -> ResidentSection<'c> {
        self.coordinates
    }
    /// Evaluate the original affine source at this witnessed face. The original anchor owner
    /// is supplied to the resident section kernel, so an out-of-domain face is refused.
    pub fn bound_section(&self) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        let s=self.source.origin.fibre().surface;
        let n=self.source.origin.fibre().roots;
        let t=self.source.relation.target_width();
        let anchor=s.fresh_section(1,t+2,ResidentGrain(0))?;
        let mut p=s.begin_passage(&[vec![]])?;
        {let lane=p.open(0,&[])?;
            s.record_coupled_joint_anchor(&lane,self.source.relation.report(),self.source.relation.source_width(),
                self.source.anchor(),n,t,&self.coordinates,&anchor)?;
        }
        p.close(0,&anchor,64)?;
        let result=p.finish()?.launch()?;
        if !result.obstruction.is_empty(){return Err(ConstitutiveFibreError::Arithmetic(format!("source face anchor: {:?}",result.obstruction)));}
        self.source.parameter_section(&self.coordinates,&anchor)
    }
    pub fn section(&self) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.bound_section()
    }
    pub fn into_section(self) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.bound_section()
    }
}
impl<'c> NormalWaveFamily<'c> {
    /// Return the exact supported receiver face while keeping all values on the resident device.
    pub fn receiver_face(&self) -> Result<NormalWaveFacePacket<'_, 'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let n = self.origin.fibre().roots;
        let a = n.checked_mul(4).ok_or(ConstitutiveFibreError::Shape)?;
        let t = a.checked_mul(2).and_then(|v| v.checked_add(2)).ok_or(ConstitutiveFibreError::Shape)?;
        let receiver = self.read_receiver()?;
        receiver.require_supported()?;
        let report = receiver.into_report();
        let packet = s.fresh_section(1, t + 1, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        { let lane = p.open(0, &[])?;
          s.record_coupled_receiver_face_packet(&lane, &report, n, &packet)?; }
        p.close(0, &packet, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() { return Err(ConstitutiveFibreError::Arithmetic(format!("receiver face packet: {:?}", result.obstruction))); }
        Ok(NormalWaveFacePacket { source: self, packet })
    }

    pub fn receiver_coordinates(
        &self,
    ) -> Result<NormalReceiverCoordinates<'_, 'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let t = self.relation.target_width();
        let receiver = self.read_receiver()?.into_report();
        let graph = s.fresh_section(2 * t, 2 * t, ResidentGrain(0))?;
        let coordinates = s.fresh_section(1, t + 1, ResidentGrain(0))?;
        let fibre = ResidentConstitutiveReturn::allocate(
            s,
            t,
            t,
            self.relation.occurrence(),
            ConstitutiveSourceChart::Linear,
        )?;
        let workspace = s.fresh_section(1, 8 * t, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_coupled_receiver_coordinates(
                &lane,
                self.relation.report(),
                self.relation.source_width(),
                t,
                &receiver,
                &graph,
                &coordinates,
                fibre.report(),
                &workspace,
            )?;
        }
        p.close(0, &coordinates, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "source receiver coordinates: {:?}",
                result.obstruction
            )));
        }
        Ok(NormalReceiverCoordinates {
            source: self,
            coordinates,
            fibre,
        })
    }
    pub(in super::super) fn parameter_section(
        &self,
        parameters: &ResidentSection<'c>,
        anchor: &ResidentSection<'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        let s = self.origin.fibre().surface;
        let t = self.relation.target_width();
        let returned = ResidentConstitutiveReturn::allocate(
            s,
            1,
            t,
            self.relation.occurrence(),
            ConstitutiveSourceChart::Linear,
        )?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_coupled_family_section(
                &lane,
                self.relation.report(),
                self.relation.source_width(),
                t,
                parameters,
                anchor,
                returned.report(),
            )?;
        }
        passage.close(0, returned.report(), 64)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "dependent source section: {:?}",
                result.obstruction
            )));
        }
        Ok(returned)
    }
    /// The image and final map come from the actual retained word; source restriction has not
    /// changed its clock. The caller retains the parameter assignment and complete original domain.
    pub(in super::super) fn parameter_image(
        &self,
        relation: ResidentConstitutiveReturn<'c>,
        last: Rc<ResidentWaveRelation<'c>>,
        coverage: ResidentSection<'c>,
        passages: u64,
    ) -> Self {
        Self {
            origin: Rc::clone(&self.origin),
            relation,
            last_relation: Some(last),
            affine_coverage: Some(coverage),
            passages,
        }
    }

    /// Decode a face packet in its original anchor frame. The returned coordinates retain the
    /// complete affine kernel; no unrelated receiver or singleton source is selected.
    pub fn coordinates_of_face(
        &self, face: &NormalWaveFacePacket<'_, 'c>,
    ) -> Result<NormalReceiverCoordinates<'_, 'c>, ConstitutiveFibreError> {
        if !std::ptr::eq(self.origin.fibre().surface, face.source.origin.fibre().surface)
            || !std::ptr::eq(self.anchor().section, face.source.anchor().section) {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.coordinates_of_resident_face(&face.packet)
    }
    /// Decode a resident/serialized face in this explicitly supplied source frame. The caller
    /// retains its source-cut descriptor; numeric coordinates alone are not a global identity.
    pub fn coordinates_of_resident_face(&self,packet:&ResidentSection<'c>)
        ->Result<NormalReceiverCoordinates<'_, 'c>,ConstitutiveFibreError>{
        let s = self.origin.fibre().surface;
        let n = self.origin.fibre().roots;
        let a = n.checked_mul(4).ok_or(ConstitutiveFibreError::Shape)?;
        let t = a.checked_mul(2).and_then(|v| v.checked_add(2)).ok_or(ConstitutiveFibreError::Shape)?;
        let receiver = s.fresh_section(1, 8 + 8 * a, ResidentGrain(0))?;
        let graph = s.fresh_section(2 * t, 2 * t, ResidentGrain(0))?;
        let coordinates = s.fresh_section(1, t + 1, ResidentGrain(0))?;
        let fibre = ResidentConstitutiveReturn::allocate(s, t, t, self.relation.occurrence(), ConstitutiveSourceChart::Linear)?;
        let workspace = s.fresh_section(1, 8 * t, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        { let lane = p.open(0, &[])?;
          s.record_coupled_face_packet_receiver(&lane, packet, n, &receiver)?;
          s.record_coupled_receiver_coordinates(&lane, self.relation.report(), self.relation.source_width(), t, &receiver, &graph, &coordinates, fibre.report(), &workspace)?;
        }
        p.close(0, &coordinates, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() { return Err(ConstitutiveFibreError::Arithmetic(format!("face coordinates: {:?}", result.obstruction))); }
        Ok(NormalReceiverCoordinates { source: self, coordinates, fibre })
    }
}
