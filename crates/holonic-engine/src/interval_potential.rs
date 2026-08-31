//! Resident interval-potential receiver owner.
use super::*;
/// apparatus owner mounts only the rows through which the declared exterior receiver factors.
pub struct ResidentIntervalPotentialReceiver {
    lower_incidence: Buffer,
    upper_incidence: Buffer,
    row_addresses: Buffer,
    card: CudaRefineExecutor,
    address: String,
    rows: u32,
    nodes: u32,
    greatest_row_mass: u128,
    mount_host_ingress_octets: u64,
}

/// One exact receiver projection from an already-resident interval potential complex.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ResidentIntervalPotentialReturn {
    pub address: String,
    pub selected_native_addresses: Vec<u32>,
    pub selected_lower: Vec<String>,
    pub selected_upper: Vec<String>,
    pub plural_population: Vec<u32>,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

impl ResidentIntervalPotentialReceiver {
    pub fn mount(
        card: CudaRefineExecutor,
        address: impl Into<String>,
        rows: usize,
        nodes: usize,
        row_addresses: &[u32],
        lower_incidence: &[i64],
        upper_incidence: &[i64],
    ) -> Result<Self, CudaRefineError> {
        let expected = rows
            .checked_mul(nodes)
            .ok_or(CudaRefineError::IntervalPotentialShape)?;
        let unique_addresses = row_addresses.iter().copied().collect::<BTreeSet<_>>();
        if rows == 0
            || nodes == 0
            || rows > u32::MAX as usize
            || nodes > u32::MAX as usize
            || row_addresses.len() != rows
            || unique_addresses.len() != rows
            || lower_incidence.len() != expected
            || upper_incidence.len() != expected
            || lower_incidence
                .iter()
                .zip(upper_incidence)
                .any(|(lower, upper)| lower > upper)
        {
            return Err(CudaRefineError::IntervalPotentialShape);
        }
        let greatest_row_mass = lower_incidence
            .chunks_exact(nodes)
            .zip(upper_incidence.chunks_exact(nodes))
            .map(|(lower, upper)| {
                lower.iter().zip(upper).fold(0u128, |mass, (from, until)| {
                    mass.saturating_add(
                        u128::from(from.unsigned_abs()).max(u128::from(until.unsigned_abs())),
                    )
                })
            })
            .max()
            .unwrap_or(0);
        let mount_host_ingress_octets = std::mem::size_of_val(lower_incidence)
            .checked_add(std::mem::size_of_val(upper_incidence))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(row_addresses)))
            .and_then(|octets| u64::try_from(octets).ok())
            .ok_or(CudaRefineError::IntervalPotentialShape)?;
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        Ok(Self {
            lower_incidence: Buffer::of(lower_incidence)?,
            upper_incidence: Buffer::of(upper_incidence)?,
            row_addresses: Buffer::of(row_addresses)?,
            card,
            address: address.into(),
            rows: rows as u32,
            nodes: nodes as u32,
            greatest_row_mass,
            mount_host_ingress_octets,
        })
    }

    /// Cross exact real coefficient currents and take the declared interval-order receiver on the
    /// card. A plural return remains explicit; this method never lets the host break a tie.
    pub fn conduct(
        &mut self,
        fronts: &[Vec<Rat>],
    ) -> Result<ResidentIntervalPotentialReturn, CudaRefineError> {
        let nodes = self.nodes as usize;
        if fronts.is_empty()
            || fronts.len() > u32::MAX as usize
            || fronts.iter().any(|front| front.len() != nodes)
        {
            return Err(CudaRefineError::IntervalPotentialShape);
        }
        let mut coefficients = Vec::with_capacity(fronts.len() * nodes);
        let mut denominators = Vec::with_capacity(fronts.len());
        let mut greatest_numerator = 0u128;
        for front in fronts {
            let denominator = common_real_denominator(front)?;
            for coefficient in front {
                let numerator = coefficient.numer() * (&denominator / coefficient.denom());
                let numerator = numerator
                    .to_i64()
                    .ok_or(CudaRefineError::IntervalPotentialCurrentOutsideApparatus)?;
                greatest_numerator = greatest_numerator.max(u128::from(numerator.unsigned_abs()));
                coefficients.push(numerator);
            }
            denominators.push(
                denominator
                    .to_u64()
                    .ok_or(CudaRefineError::IntervalPotentialCurrentOutsideApparatus)?,
            );
        }
        if self
            .greatest_row_mass
            .checked_mul(greatest_numerator)
            .filter(|bound| *bound <= i64::MAX as u128)
            .is_none()
        {
            return Err(CudaRefineError::IntervalPotentialAccumulationOverflow);
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let coefficient = Buffer::of(&coefficients)?;
        let front_count = fronts.len();
        let selected_address = Buffer::alloc(front_count * std::mem::size_of::<u32>())?;
        let selected_lower = Buffer::alloc(front_count * std::mem::size_of::<i64>())?;
        let selected_upper = Buffer::alloc(front_count * std::mem::size_of::<i64>())?;
        let plural_count = Buffer::alloc(front_count * std::mem::size_of::<u32>())?;
        let mut lower_pointer = self.lower_incidence.pointer;
        let mut upper_pointer = self.upper_incidence.pointer;
        let mut address_pointer = self.row_addresses.pointer;
        let mut coefficient_pointer = coefficient.pointer;
        let mut selected_address_pointer = selected_address.pointer;
        let mut selected_lower_pointer = selected_lower.pointer;
        let mut selected_upper_pointer = selected_upper.pointer;
        let mut plural_pointer = plural_count.pointer;
        let mut rows = self.rows;
        let mut nodes = self.nodes;
        let mut arguments: [*mut c_void; 10] = [
            &mut lower_pointer as *mut u64 as *mut c_void,
            &mut upper_pointer as *mut u64 as *mut c_void,
            &mut address_pointer as *mut u64 as *mut c_void,
            &mut coefficient_pointer as *mut u64 as *mut c_void,
            &mut selected_address_pointer as *mut u64 as *mut c_void,
            &mut selected_lower_pointer as *mut u64 as *mut c_void,
            &mut selected_upper_pointer as *mut u64 as *mut c_void,
            &mut plural_pointer as *mut u64 as *mut c_void,
            &mut rows as *mut u32 as *mut c_void,
            &mut nodes as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.interval_potential_receiver,
                    front_count as u32,
                    1,
                    1,
                    self.card.warp,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(receive_interval_potential_incidence)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 1;
        let mut returned_address = vec![0u32; front_count];
        let mut returned_lower = vec![0i64; front_count];
        let mut returned_upper = vec![0i64; front_count];
        let mut returned_plural = vec![0u32; front_count];
        selected_address.read(&mut returned_address)?;
        selected_lower.read(&mut returned_lower)?;
        selected_upper.read(&mut returned_upper)?;
        plural_count.read(&mut returned_plural)?;
        if returned_plural.iter().any(|plural| *plural == 0)
            || returned_lower
                .iter()
                .zip(&returned_upper)
                .any(|(lower, upper)| lower > upper)
        {
            return Err(CudaRefineError::IntervalPotentialShape);
        }
        let lower = returned_lower
            .into_iter()
            .zip(&denominators)
            .map(|(numerator, denominator)| {
                Rat::new(BigInt::from(numerator), BigInt::from(*denominator)).to_string()
            })
            .collect();
        let upper = returned_upper
            .into_iter()
            .zip(&denominators)
            .map(|(numerator, denominator)| {
                Rat::new(BigInt::from(numerator), BigInt::from(*denominator)).to_string()
            })
            .collect();
        let ingress = std::mem::size_of_val(coefficients.as_slice()) as u64;
        let egress = front_count
            .checked_mul(2 * std::mem::size_of::<u32>() + 2 * std::mem::size_of::<i64>())
            .ok_or(CudaRefineError::IntervalPotentialShape)? as u64;
        Ok(ResidentIntervalPotentialReturn {
            address: self.address.clone(),
            selected_native_addresses: returned_address,
            selected_lower: lower,
            selected_upper: upper,
            plural_population: returned_plural,
            device: self.card.device_name().to_owned(),
            launches: 1,
            synchronizations: 1,
            block_threads: self.card.warp,
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets: ingress,
            successor_host_egress_octets: egress,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets: ingress + egress,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }
}
