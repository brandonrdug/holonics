use super::*;

/// **Every distinct reading in the corpus, given a dense identity.**
pub struct ReadingIdentities {
    /// Indexed by `SurfaceId.0`.
    pub per_surface: Vec<u32>,
    /// How many distinct readings the corpus carries, excluding the terminus.
    pub distinct: usize,
}

impl ReadingIdentities {
    pub fn of(census: &CorpusCensus, atlas: &ConductAtlas) -> Self {
        let widest = census
            .wholes()
            .iter()
            .flat_map(|whole| whole.stream.iter())
            .map(|surface| surface.0 as usize)
            .max()
            .unwrap_or(0);
        let mut per_surface = vec![ABSENT; widest + 1];
        let mut seen: BTreeMap<[u64; 4], u32> = BTreeMap::new();
        for whole in census.wholes() {
            for surface in &whole.stream {
                let slot = surface.0 as usize;
                if per_surface[slot] != ABSENT {
                    continue;
                }
                let (kind, weight, density) = census.signature(*surface);
                let reading = [kind, weight, density, atlas.token(*surface)];
                let next = seen.len() as u32 + 1;
                let identity = *seen.entry(reading).or_insert(next);
                per_surface[slot] = identity;
            }
        }
        Self {
            per_surface,
            distinct: seen.len(),
        }
    }
}

/// The whole corpus, laid out once for the device.
pub struct DeviceCorpus {
    pub(super) whole_offset: Vec<u32>,
    pub(super) whole_length: Vec<u32>,
    pub(super) stream: Vec<u32>,
}

impl DeviceCorpus {
    pub fn of(census: &CorpusCensus) -> Result<Self, CudaRefineError> {
        let occurrences: usize = census.wholes().iter().map(|whole| whole.stream.len()).sum();
        if occurrences > u32::MAX as usize {
            return Err(CudaRefineError::CorpusTooWide { occurrences });
        }
        let mut whole_offset = Vec::with_capacity(census.wholes().len());
        let mut whole_length = Vec::with_capacity(census.wholes().len());
        let mut stream = Vec::with_capacity(occurrences);
        for whole in census.wholes() {
            whole_offset.push(stream.len() as u32);
            whole_length.push(whole.stream.len() as u32);
            stream.extend(whole.stream.iter().map(|surface| surface.0));
        }
        Ok(Self {
            whole_offset,
            whole_length,
            stream,
        })
    }
}

impl CudaRefineExecutor {
    /// **Refine one surface's occurrence population to saturation, on the card.**
    ///
    /// One crossing per shell, one lane per occurrence. Returns the class of every site at every
    /// shell walked, and the shell at which the partition last split — which is the horizon.
    pub fn saturate(
        &mut self,
        corpus: &DeviceCorpus,
        identities: &ReadingIdentities,
        sites: &[(u32, u32)],
        ceiling: usize,
    ) -> Result<DeviceSaturation, CudaRefineError> {
        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let count = sites.len();
        if count == 0 {
            return Ok(DeviceSaturation {
                // No occurrence, so no shell ever split: the least final radius is 0. This was `1`,
                // the same authored floor the cpu law carried at `last_split.max(1)`.
                horizon: 0,
                classes: 0,
                shells: 0,
                classes_at_one: 0,
                site_class: Vec::new(),
            });
        }

        // The table can never fill: distinct pairs are at most the site count, so the next power of
        // two ABOVE it always leaves an empty slot. Derived; no load factor.
        let capacity = (count + 1).next_power_of_two();
        let mask = (capacity - 1) as u32;

        let whole: Vec<u32> = sites.iter().map(|(whole, _)| *whole).collect();
        let position: Vec<u32> = sites.iter().map(|(_, position)| *position).collect();

        let device_whole = Buffer::of(&whole)?;
        let device_position = Buffer::of(&position)?;
        let device_offset = Buffer::of(&corpus.whole_offset)?;
        let device_length = Buffer::of(&corpus.whole_length)?;
        let device_stream = Buffer::of(&corpus.stream)?;
        let device_reading = Buffer::of(&identities.per_surface)?;
        let table_pair = Buffer::alloc(capacity * std::mem::size_of::<u64>())?;
        let table_key = Buffer::alloc(capacity * std::mem::size_of::<u64>())?;
        // Every site opens in one class. Class identities begin at one so they can never equal the
        // empty marker, which is all ones.
        let mut cpu_class = vec![1u32; count];
        let device_class = Buffer::of(&cpu_class)?;
        let device_next = Buffer::alloc(count * std::mem::size_of::<u32>())?;

        let mut previous_classes = 1usize;
        let mut classes_at_one = 1usize;
        let mut last_split = 0usize;
        let mut shells = 0usize;
        let grid = self.grid_for(count as u64)?;

        for depth in 1..=ceiling {
            table_pair.fill(0xff, capacity * std::mem::size_of::<u64>())?;
            table_key.fill(0xff, capacity * std::mem::size_of::<u64>())?;
            shells += 1;

            let mut site_count = count as u32;
            let mut shell_depth = depth as u32;
            let mut capacity_mask = mask;
            let arguments: [*mut c_void; 12] = [
                &mut { device_whole.pointer } as *mut u64 as *mut c_void,
                &mut { device_position.pointer } as *mut u64 as *mut c_void,
                &mut { device_class.pointer } as *mut u64 as *mut c_void,
                &mut { device_offset.pointer } as *mut u64 as *mut c_void,
                &mut { device_length.pointer } as *mut u64 as *mut c_void,
                &mut { device_stream.pointer } as *mut u64 as *mut c_void,
                &mut { device_reading.pointer } as *mut u64 as *mut c_void,
                &mut { table_pair.pointer } as *mut u64 as *mut c_void,
                &mut { table_key.pointer } as *mut u64 as *mut c_void,
                &mut { device_next.pointer } as *mut u64 as *mut c_void,
                &mut site_count as *mut u32 as *mut c_void,
                &mut shell_depth as *mut u32 as *mut c_void,
            ];
            // `capacity_mask` is the thirteenth; the array above is fixed so it is appended here.
            let mut full: Vec<*mut c_void> = arguments.to_vec();
            full.push(&mut capacity_mask as *mut u32 as *mut c_void);

            driver(
                unsafe {
                    cuLaunchKernel(
                        self.refine,
                        grid,
                        1,
                        1,
                        self.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        full.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(refine_shell)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;

            // The claimed slots are the new classes. Read them back and renumber densely, which
            // keeps the class identity small and keeps the table's next round exact.
            let mut next = vec![0u32; count];
            device_next.read(&mut next)?;
            let mut dense: BTreeMap<u32, u32> = BTreeMap::new();
            for slot in &next {
                let assigned = dense.len() as u32 + 1;
                dense.entry(*slot).or_insert(assigned);
            }
            for (at, slot) in next.iter().enumerate() {
                cpu_class[at] = dense[slot];
            }
            let classes = dense.len();
            if depth == 1 {
                classes_at_one = classes;
            }
            if classes > previous_classes {
                last_split = depth;
                previous_classes = classes;
            }
            driver(
                unsafe {
                    cuMemcpyHtoD_v2(
                        device_class.pointer,
                        cpu_class.as_ptr().cast(),
                        count * std::mem::size_of::<u32>(),
                    )
                },
                "cuMemcpyHtoD_v2",
            )?;
            if classes == count {
                // Every class is a singleton; no deeper shell can split anything. This is the
                // theorem the cpu law stops on, and it holds here for the same reason.
                break;
            }
        }

        Ok(DeviceSaturation {
            // `0` when no shell ever split, which is the reading and not a floor. The cpu law's
            // `SaturationHorizon::horizon` carries the same convention and the two are compared
            // directly by `the_card_refines_the_front`.
            horizon: last_split,
            classes: previous_classes,
            shells,
            classes_at_one,
            site_class: cpu_class,
        })
    }
}
