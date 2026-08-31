use super::*;

impl CudaRefineExecutor {
    /// Classify exact coordinate-box contacts and compare matched presentations without returning
    /// to the host between the two laws.
    ///
    /// Every coordinate is an integer numerator over one caller-declared common denominator; the
    /// aperture has already been multiplied by that denominator squared. The host verifies only
    /// that the wire arithmetic cannot overflow. The classifications and their ordered
    /// cross-presentation pairs are enacted on the card under one terminal synchronization.
    pub fn contact_passage_on_device(
        &mut self,
        lower_xyz: &[i64],
        upper_xyz: &[i64],
        task_left: &[u32],
        task_right: &[u32],
        comparison_left: &[u32],
        comparison_right: &[u32],
        aperture_squared: u64,
    ) -> Result<DeviceContactPassage, CudaRefineError> {
        if lower_xyz.len() != upper_xyz.len() || lower_xyz.len() % 3 != 0 {
            return Err(CudaRefineError::ContactCoordinateShape {
                lower: lower_xyz.len(),
                upper: upper_xyz.len(),
            });
        }
        if task_left.len() != task_right.len() || comparison_left.len() != comparison_right.len() {
            return Err(CudaRefineError::ContactIndexShape);
        }
        let vertices = lower_xyz.len() / 3;
        if task_left.len() > u32::MAX as usize
            || comparison_left.len() > u32::MAX as usize
            || vertices > u32::MAX as usize
        {
            return Err(CudaRefineError::ContactPassageTooWide);
        }
        for (at, (lower, upper)) in lower_xyz.iter().zip(upper_xyz).enumerate() {
            if lower > upper {
                return Err(CudaRefineError::ReversedContactCoordinate {
                    at,
                    lower: *lower,
                    upper: *upper,
                });
            }
        }
        for (task, (left, right)) in task_left.iter().zip(task_right).enumerate() {
            for vertex in [*left, *right] {
                if vertex as usize >= vertices {
                    return Err(CudaRefineError::ContactVertexOutsidePopulation {
                        task,
                        vertex,
                        vertices,
                    });
                }
            }
            let mut greatest_squared = 0_u128;
            for axis in 0..3 {
                let left_at = *left as usize * 3 + axis;
                let right_at = *right as usize * 3 + axis;
                let low = i128::from(lower_xyz[left_at]) - i128::from(upper_xyz[right_at]);
                let high = i128::from(upper_xyz[left_at]) - i128::from(lower_xyz[right_at]);
                if low < i128::from(i64::MIN)
                    || low > i128::from(i64::MAX)
                    || high < i128::from(i64::MIN)
                    || high > i128::from(i64::MAX)
                {
                    return Err(CudaRefineError::ContactDistanceOverflow { task });
                }
                let far = low.unsigned_abs().max(high.unsigned_abs());
                greatest_squared = greatest_squared
                    .checked_add(
                        far.checked_mul(far)
                            .ok_or(CudaRefineError::ContactDistanceOverflow { task })?,
                    )
                    .ok_or(CudaRefineError::ContactDistanceOverflow { task })?;
            }
            if greatest_squared > u128::from(u64::MAX) {
                return Err(CudaRefineError::ContactDistanceOverflow { task });
            }
        }
        for (comparison, (left, right)) in comparison_left.iter().zip(comparison_right).enumerate()
        {
            for reading in [*left, *right] {
                if reading as usize >= task_left.len() {
                    return Err(CudaRefineError::ContactReadingOutsidePopulation {
                        comparison,
                        reading,
                        readings: task_left.len(),
                    });
                }
            }
        }

        let pair_count = task_left.len();
        let comparison_count = comparison_left.len();
        if pair_count == 0 {
            return Ok(DeviceContactPassage {
                contact_classes: Vec::new(),
                paired_classes: Vec::new(),
                launches: 0,
                synchronizations: 0,
                host_ingress_octets: 0,
                host_egress_octets: 0,
                resident_octets: 0,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let lower = Buffer::of(lower_xyz)?;
        let upper = Buffer::of(upper_xyz)?;
        let left = Buffer::of(task_left)?;
        let right = Buffer::of(task_right)?;
        let classes = Buffer::alloc(pair_count * std::mem::size_of::<u8>())?;
        let comparison_left_device = Buffer::of(comparison_left)?;
        let comparison_right_device = Buffer::of(comparison_right)?;
        let paired = Buffer::alloc(comparison_count * std::mem::size_of::<u8>())?;

        let mut lower_pointer = lower.pointer;
        let mut upper_pointer = upper.pointer;
        let mut left_pointer = left.pointer;
        let mut right_pointer = right.pointer;
        let mut class_pointer = classes.pointer;
        let mut pair_count_wire = pair_count as u32;
        let mut aperture_wire = aperture_squared;
        let mut classify_arguments: Vec<*mut c_void> = vec![
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut left_pointer as *mut u64 as *mut c_void,
            &mut right_pointer as *mut u64 as *mut c_void,
            &mut class_pointer as *mut u64 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut aperture_wire as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.contact_pairs,
                    self.grid_for(pair_count as u64)?,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    classify_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(classify_contact_pairs)",
        )?;
        let mut launches = 1_u64;

        if comparison_count > 0 {
            let mut comparison_left_pointer = comparison_left_device.pointer;
            let mut comparison_right_pointer = comparison_right_device.pointer;
            let mut paired_pointer = paired.pointer;
            let mut comparison_count_wire = comparison_count as u32;
            let mut compare_arguments: Vec<*mut c_void> = vec![
                &mut class_pointer as *mut u64 as *mut c_void,
                &mut comparison_left_pointer as *mut u64 as *mut c_void,
                &mut comparison_right_pointer as *mut u64 as *mut c_void,
                &mut paired_pointer as *mut u64 as *mut c_void,
                &mut comparison_count_wire as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.contact_compare,
                        self.grid_for(comparison_count as u64)?,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        compare_arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(compare_contact_presentations)",
            )?;
            launches += 1;
        }
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += launches;

        let mut contact_classes = vec![0_u8; pair_count];
        classes.read(&mut contact_classes)?;
        let mut paired_classes = vec![0_u8; comparison_count];
        if comparison_count > 0 {
            paired.read(&mut paired_classes)?;
        }
        let ingress = std::mem::size_of_val(lower_xyz)
            + std::mem::size_of_val(upper_xyz)
            + std::mem::size_of_val(task_left)
            + std::mem::size_of_val(task_right)
            + std::mem::size_of_val(comparison_left)
            + std::mem::size_of_val(comparison_right);
        let egress = contact_classes.len() + paired_classes.len();
        Ok(DeviceContactPassage {
            contact_classes,
            paired_classes,
            launches,
            synchronizations: 1,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Return exact contact and every simultaneous local optical role without crossing a host
    /// boundary between the two laws. The caller supplies scale apertures read from the material;
    /// they are geometry receivers, not authored capacity bounds.
    pub fn optical_incidence_on_device(
        &mut self,
        lower_xyz: &[i64],
        upper_xyz: &[i64],
        task_left: &[u32],
        task_right: &[u32],
        aperture_squared: u64,
        term_gap: u64,
        line_gap: u64,
    ) -> Result<DeviceOpticalIncidencePassage, CudaRefineError> {
        if lower_xyz.len() != upper_xyz.len() || lower_xyz.len() % 3 != 0 {
            return Err(CudaRefineError::ContactCoordinateShape {
                lower: lower_xyz.len(),
                upper: upper_xyz.len(),
            });
        }
        if task_left.len() != task_right.len() {
            return Err(CudaRefineError::ContactIndexShape);
        }
        if term_gap > line_gap {
            return Err(CudaRefineError::OpticalIncidenceAperture { term_gap, line_gap });
        }
        let vertices = lower_xyz.len() / 3;
        if task_left.len() > u32::MAX as usize || vertices > u32::MAX as usize {
            return Err(CudaRefineError::ContactPassageTooWide);
        }
        for (at, (lower, upper)) in lower_xyz.iter().zip(upper_xyz).enumerate() {
            if lower > upper {
                return Err(CudaRefineError::ReversedContactCoordinate {
                    at,
                    lower: *lower,
                    upper: *upper,
                });
            }
        }
        for (task, (left, right)) in task_left.iter().zip(task_right).enumerate() {
            for vertex in [*left, *right] {
                if vertex as usize >= vertices {
                    return Err(CudaRefineError::ContactVertexOutsidePopulation {
                        task,
                        vertex,
                        vertices,
                    });
                }
            }
            let mut greatest_squared = 0_u128;
            for axis in 0..3 {
                let left_at = *left as usize * 3 + axis;
                let right_at = *right as usize * 3 + axis;
                let low = i128::from(lower_xyz[left_at]) - i128::from(upper_xyz[right_at]);
                let high = i128::from(upper_xyz[left_at]) - i128::from(lower_xyz[right_at]);
                if low < i128::from(i64::MIN)
                    || low > i128::from(i64::MAX)
                    || high < i128::from(i64::MIN)
                    || high > i128::from(i64::MAX)
                {
                    return Err(CudaRefineError::ContactDistanceOverflow { task });
                }
                let far = low.unsigned_abs().max(high.unsigned_abs());
                greatest_squared = greatest_squared
                    .checked_add(
                        far.checked_mul(far)
                            .ok_or(CudaRefineError::ContactDistanceOverflow { task })?,
                    )
                    .ok_or(CudaRefineError::ContactDistanceOverflow { task })?;
            }
            if greatest_squared > u128::from(u64::MAX) {
                return Err(CudaRefineError::ContactDistanceOverflow { task });
            }
        }

        let pair_count = task_left.len();
        if pair_count == 0 {
            return Ok(DeviceOpticalIncidencePassage {
                contact_classes: Vec::new(),
                incidence_words: Vec::new(),
                launches: 0,
                synchronizations: 0,
                host_ingress_octets: 0,
                host_egress_octets: 0,
                resident_octets: 0,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let lower = Buffer::of(lower_xyz)?;
        let upper = Buffer::of(upper_xyz)?;
        let left = Buffer::of(task_left)?;
        let right = Buffer::of(task_right)?;
        let classes = Buffer::alloc(pair_count * std::mem::size_of::<u8>())?;
        let incidences = Buffer::alloc(pair_count * std::mem::size_of::<u32>())?;

        let mut lower_pointer = lower.pointer;
        let mut upper_pointer = upper.pointer;
        let mut left_pointer = left.pointer;
        let mut right_pointer = right.pointer;
        let mut class_pointer = classes.pointer;
        let mut pair_count_wire = pair_count as u32;
        let mut aperture_wire = aperture_squared;
        let mut classify_arguments: Vec<*mut c_void> = vec![
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut left_pointer as *mut u64 as *mut c_void,
            &mut right_pointer as *mut u64 as *mut c_void,
            &mut class_pointer as *mut u64 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut aperture_wire as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.contact_pairs,
                    self.grid_for(pair_count as u64)?,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    classify_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(classify_contact_pairs)",
        )?;

        let mut incidence_pointer = incidences.pointer;
        let mut term_gap_wire = term_gap;
        let mut line_gap_wire = line_gap;
        let mut incidence_arguments: Vec<*mut c_void> = vec![
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut left_pointer as *mut u64 as *mut c_void,
            &mut right_pointer as *mut u64 as *mut c_void,
            &mut class_pointer as *mut u64 as *mut c_void,
            &mut incidence_pointer as *mut u64 as *mut c_void,
            &mut pair_count_wire as *mut u32 as *mut c_void,
            &mut term_gap_wire as *mut u64 as *mut c_void,
            &mut line_gap_wire as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.optical_incidence,
                    self.grid_for(pair_count as u64)?,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    incidence_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(classify_optical_incidence)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 2;

        let mut contact_classes = vec![0_u8; pair_count];
        classes.read(&mut contact_classes)?;
        let mut incidence_words = vec![0_u32; pair_count];
        incidences.read(&mut incidence_words)?;
        let ingress = std::mem::size_of_val(lower_xyz)
            + std::mem::size_of_val(upper_xyz)
            + std::mem::size_of_val(task_left)
            + std::mem::size_of_val(task_right)
            + std::mem::size_of::<u64>() * 3;
        let egress = std::mem::size_of_val(contact_classes.as_slice())
            + std::mem::size_of_val(incidence_words.as_slice());
        Ok(DeviceOpticalIncidencePassage {
            contact_classes,
            incidence_words,
            launches: 2,
            synchronizations: 1,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }
}
