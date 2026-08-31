use super::*;

/// One sparse exact complex term presented to the resident target/port/factor junction. The
/// occurrence address maps back to the caller's complete response/source/target fibre; only the
/// coordinates needed by this apparatus chart are repeated here.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentAddressedComplexJunctionTerm {
    pub occurrence: u32,
    pub target_site: u32,
    pub exterior_port: u32,
    pub factor: u32,
    pub current: ExactComplexWaveCurrent,
}

/// One linearly joined dependent complex section and its later positive constitutive face.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentAddressedComplexJunctionGroup {
    pub exterior_port: u32,
    pub factor: u32,
    pub occurrences: Vec<u32>,
    /// Exact target-site subjunctions retained behind the final port/factor sum.
    pub target_sections: Vec<(u32, Vec<u32>)>,
    pub joined_current: ExactComplexWaveCurrent,
    /// Numerator of `|joined_current|²`; the common denominator is returned once by the word.
    pub positive_numerator: BigUint,
}

/// Terminal return from the resident addressed complex junction.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentAddressedComplexJunctionReturn {
    pub groups: Vec<ResidentAddressedComplexJunctionGroup>,
    pub common_denominator: BigInt,
    pub positive_denominator: BigUint,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub terminal_host_egress_octets: u64,
    pub intermediate_semantic_egress_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

impl ResidentAddressedComplexJunctionReturn {
    /// Telemetry hook for any apparatus path which performs a semantic step after this device
    /// return but still claims to be part of the resident-to-terminal word.
    pub fn record_post_device_cpu_semantic_step(&mut self) {
        self.cpu_semantic_replay_after_device = true;
    }
}

impl ResidentMembraneInteriorWord {
    /// Join every sparse response/source/target current on the existing resident CUDA context.
    /// The host derives only a common exact apparatus chart and group offsets. The card performs
    /// signed linear aggregation and then the positive norm, with no intermediate readback.
    pub fn conduct_addressed_complex_junction(
        &mut self,
        terms: &[ResidentAddressedComplexJunctionTerm],
    ) -> Result<ResidentAddressedComplexJunctionReturn, CudaRefineError> {
        if terms.is_empty()
            || terms.len() > u32::MAX as usize
            || terms.iter().any(|term| {
                term.exterior_port == 0 || term.current.is_zero()
            })
        {
            return Err(CudaRefineError::ComplexCurrentShape);
        }
        let mut ordered = terms.to_vec();
        ordered.sort_by_key(|term| {
            (
                term.exterior_port,
                term.factor,
                term.target_site,
                term.occurrence,
            )
        });
        if ordered
            .windows(2)
            .any(|pair| pair[0].occurrence == pair[1].occurrence)
        {
            return Err(CudaRefineError::ComplexCurrentShape);
        }

        let currents = ordered
            .iter()
            .map(|term| term.current.clone())
            .collect::<Vec<_>>();
        let common_denominator = common_complex_denominator(&currents)?;
        let mut greatest_input = BigInt::zero();
        let mut group_offsets = vec![0_u64];
        let mut group_keys = Vec::<(u32, u32)>::new();
        let mut group_occurrences = Vec::<Vec<u32>>::new();
        let mut group_target_sections = Vec::<Vec<(u32, Vec<u32>)>>::new();
        let mut greatest_group_mass = BigInt::zero();
        let mut current_key = None;
        for (at, term) in ordered.iter().enumerate() {
            let key = (term.exterior_port, term.factor);
            if current_key != Some(key) {
                if current_key.is_some() {
                    group_offsets.push(
                        u64::try_from(at).map_err(|_| CudaRefineError::ComplexCurrentShape)?,
                    );
                }
                current_key = Some(key);
                group_keys.push(key);
                group_occurrences.push(Vec::new());
                group_target_sections.push(Vec::new());
            }
            group_occurrences
                .last_mut()
                .ok_or(CudaRefineError::ComplexCurrentShape)?
                .push(term.occurrence);
            let targets = group_target_sections
                .last_mut()
                .ok_or(CudaRefineError::ComplexCurrentShape)?;
            if targets.last().is_none_or(|(target, _)| *target != term.target_site) {
                targets.push((term.target_site, Vec::new()));
            }
            targets
                .last_mut()
                .ok_or(CudaRefineError::ComplexCurrentShape)?
                .1
                .push(term.occurrence);
            for component in [&term.current.real, &term.current.imaginary] {
                let magnitude =
                    (component.numer() * (&common_denominator / component.denom())).abs();
                greatest_input = greatest_input.max(magnitude.clone());
                greatest_group_mass += magnitude;
            }
        }
        group_offsets.push(
            u64::try_from(ordered.len()).map_err(|_| CudaRefineError::ComplexCurrentShape)?,
        );
        if group_keys.is_empty() || group_keys.len() > u32::MAX as usize {
            return Err(CudaRefineError::ComplexCurrentShape);
        }
        let (_, input_words) = greatest_input.to_u32_digits();
        let (_, joined_words) = greatest_group_mass.to_u32_digits();
        let input_limbs = input_words.len().max(1);
        let joined_limbs = joined_words.len().max(input_limbs).max(1);
        let norm_limbs = joined_limbs
            .checked_mul(2)
            .and_then(|extent| extent.checked_add(1))
            .ok_or(CudaRefineError::ComplexCurrentShape)?;
        if input_limbs > u32::MAX as usize
            || joined_limbs > u32::MAX as usize
            || norm_limbs > u32::MAX as usize
        {
            return Err(CudaRefineError::ComplexCurrentShape);
        }

        let mut real_signs = Vec::with_capacity(ordered.len());
        let mut real_limbs = Vec::with_capacity(ordered.len() * input_limbs);
        let mut imaginary_signs = Vec::with_capacity(ordered.len());
        let mut imaginary_limbs = Vec::with_capacity(ordered.len() * input_limbs);
        for term in &ordered {
            let (sign, limbs) =
                encode_component(&term.current.real, &common_denominator, input_limbs)?;
            real_signs.push(sign);
            real_limbs.extend(limbs);
            let (sign, limbs) =
                encode_component(&term.current.imaginary, &common_denominator, input_limbs)?;
            imaginary_signs.push(sign);
            imaginary_limbs.extend(limbs);
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let offsets = Buffer::of(&group_offsets)?;
        let real_sign = Buffer::of(&real_signs)?;
        let real = Buffer::of(&real_limbs)?;
        let imaginary_sign = Buffer::of(&imaginary_signs)?;
        let imaginary = Buffer::of(&imaginary_limbs)?;
        let group_count = group_keys.len();
        let joined_real_sign = Buffer::alloc(group_count)?;
        let joined_real = Buffer::alloc(
            group_count * joined_limbs * std::mem::size_of::<u32>(),
        )?;
        let joined_imaginary_sign = Buffer::alloc(group_count)?;
        let joined_imaginary = Buffer::alloc(
            group_count * joined_limbs * std::mem::size_of::<u32>(),
        )?;
        let positive = Buffer::alloc(group_count * norm_limbs * std::mem::size_of::<u32>())?;
        let positive_scratch =
            Buffer::alloc(group_count * norm_limbs * std::mem::size_of::<u32>())?;
        let mut pointers = [
            offsets.pointer,
            real_sign.pointer,
            real.pointer,
            imaginary_sign.pointer,
            imaginary.pointer,
            joined_real_sign.pointer,
            joined_real.pointer,
            joined_imaginary_sign.pointer,
            joined_imaginary.pointer,
            positive.pointer,
            positive_scratch.pointer,
        ];
        let mut group_count_wire = group_count as u32;
        let mut input_limbs_wire = input_limbs as u32;
        let mut joined_limbs_wire = joined_limbs as u32;
        let mut norm_limbs_wire = norm_limbs as u32;
        let mut arguments = pointers
            .iter_mut()
            .map(|pointer| pointer as *mut u64 as *mut std::ffi::c_void)
            .collect::<Vec<_>>();
        arguments.extend([
            &mut group_count_wire as *mut u32 as *mut std::ffi::c_void,
            &mut input_limbs_wire as *mut u32 as *mut std::ffi::c_void,
            &mut joined_limbs_wire as *mut u32 as *mut std::ffi::c_void,
            &mut norm_limbs_wire as *mut u32 as *mut std::ffi::c_void,
        ]);
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.addressed_complex_junction,
                    self.card.grid_for(group_count as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_addressed_complex_junction)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 1;

        let mut returned_real_signs = vec![0_u8; group_count];
        let mut returned_real = vec![0_u32; group_count * joined_limbs];
        let mut returned_imaginary_signs = vec![0_u8; group_count];
        let mut returned_imaginary = vec![0_u32; group_count * joined_limbs];
        let mut returned_positive = vec![0_u32; group_count * norm_limbs];
        joined_real_sign.read(&mut returned_real_signs)?;
        joined_real.read(&mut returned_real)?;
        joined_imaginary_sign.read(&mut returned_imaginary_signs)?;
        joined_imaginary.read(&mut returned_imaginary)?;
        positive.read(&mut returned_positive)?;
        let groups = group_keys
            .into_iter()
            .enumerate()
            .map(|(group, (exterior_port, factor))| {
                let joined_begin = group * joined_limbs;
                let joined_end = joined_begin + joined_limbs;
                let positive_begin = group * norm_limbs;
                let positive_end = positive_begin + norm_limbs;
                Ok(ResidentAddressedComplexJunctionGroup {
                    exterior_port,
                    factor,
                    occurrences: group_occurrences[group].clone(),
                    target_sections: group_target_sections[group].clone(),
                    joined_current: ExactComplexWaveCurrent::new(
                        decode_component(
                            returned_real_signs[group],
                            &returned_real[joined_begin..joined_end],
                            &common_denominator,
                        )?,
                        decode_component(
                            returned_imaginary_signs[group],
                            &returned_imaginary[joined_begin..joined_end],
                            &common_denominator,
                        )?,
                    ),
                    positive_numerator: BigUint::new(
                        returned_positive[positive_begin..positive_end].to_vec(),
                    ),
                })
            })
            .collect::<Result<Vec<_>, CudaRefineError>>()?;
        let positive_denominator = common_denominator
            .magnitude()
            .pow(2_u32);
        let host_ingress_octets = [
            std::mem::size_of_val(group_offsets.as_slice()),
            std::mem::size_of_val(real_signs.as_slice()),
            std::mem::size_of_val(real_limbs.as_slice()),
            std::mem::size_of_val(imaginary_signs.as_slice()),
            std::mem::size_of_val(imaginary_limbs.as_slice()),
        ]
        .into_iter()
        .sum::<usize>() as u64;
        let terminal_host_egress_octets = [
            std::mem::size_of_val(returned_real_signs.as_slice()),
            std::mem::size_of_val(returned_real.as_slice()),
            std::mem::size_of_val(returned_imaginary_signs.as_slice()),
            std::mem::size_of_val(returned_imaginary.as_slice()),
            std::mem::size_of_val(returned_positive.as_slice()),
        ]
        .into_iter()
        .sum::<usize>() as u64;
        Ok(ResidentAddressedComplexJunctionReturn {
            groups,
            common_denominator,
            positive_denominator,
            device: self.card.device_name().to_owned(),
            launches: 1,
            synchronizations: 1,
            host_ingress_octets,
            terminal_host_egress_octets,
            intermediate_semantic_egress_octets: 0,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }
}
