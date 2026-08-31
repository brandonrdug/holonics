//! Owner-local CUDA refinement surface.

use super::*;

pub struct ResidentNativeWord {
    // Device allocations must be released before the context which owns them. Rust drops fields
    // in declaration order, so these precede `card` deliberately.
    generator_table: Buffer,
    word: Buffer,
    card: CudaRefineExecutor,
    states: u32,
    word_length: u32,
    resident_invariant_octets: u64,
    mount_host_ingress_octets: u64,
}

/// One terminal return from an already-resident native word.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentNativeWordReturn {
    pub native_end: Vec<u32>,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub invariant_transport_reuploaded: bool,
}

/// One real incidence section retained on the card while exact complex coefficient currents cross
/// it.  In the Complex Parametron reading, rows are oriented carrier branches, columns are the
/// addressed coefficient nodes, and the two current coordinates retain relative phase before any
/// binary receiver is taken.  The owner is singular and deliberately not `Clone`.
pub struct ResidentComplexIncidence {
    // Released before the context which owns it.
    incidence: Buffer,
    card: CudaRefineExecutor,
    address: String,
    grain: u32,
    branches: u32,
    nodes: u32,
    greatest_row_mass: u128,
    mount_host_ingress_octets: u64,
}

/// One terminal exact complex section returned from the resident incidence map.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentComplexIncidenceReturn {
    pub address: String,
    /// Physical values are these exact coordinates multiplied by `2^-grain`.
    pub grain: u32,
    pub sections: Vec<Vec<ExactComplexWaveCurrent>>,
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
    pub binary_receiver_taken: bool,
}

impl ResidentComplexIncidence {
    /// Mount one exact oriented incidence map. Its extents and row-mass aperture are read from the
    /// material; no hidden width or phase population is authored.
    pub fn mount(
        card: CudaRefineExecutor,
        address: impl Into<String>,
        grain: u32,
        branches: usize,
        nodes: usize,
        incidence: &[i64],
    ) -> Result<Self, CudaRefineError> {
        let expected = branches
            .checked_mul(nodes)
            .ok_or(CudaRefineError::ComplexIncidenceShape)?;
        if branches == 0
            || nodes == 0
            || incidence.len() != expected
            || branches > u32::MAX as usize
            || nodes > u32::MAX as usize
        {
            return Err(CudaRefineError::ComplexIncidenceShape);
        }
        let greatest_row_mass = incidence
            .chunks_exact(nodes)
            .map(|row| {
                row.iter().fold(0u128, |mass, entry| {
                    mass.saturating_add(u128::from(entry.unsigned_abs()))
                })
            })
            .max()
            .unwrap_or(0);
        let mount_host_ingress_octets = u64::try_from(std::mem::size_of_val(incidence))
            .map_err(|_| CudaRefineError::ComplexIncidenceShape)?;
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        let incidence = Buffer::of(incidence)?;
        Ok(Self {
            incidence,
            card,
            address: address.into(),
            grain,
            branches: branches as u32,
            nodes: nodes as u32,
            greatest_row_mass,
            mount_host_ingress_octets,
        })
    }

    pub fn device_name(&self) -> &str {
        self.card.device_name()
    }

    pub fn address(&self) -> &str {
        &self.address
    }

    pub fn grain(&self) -> u32 {
        self.grain
    }

    /// Carry arbitrary exact rational phase pairs through the already-mounted real incidence map.
    /// Each front is rebased to its own common positive denominator at the apparatus mouth and
    /// reconstructed exactly after the terminal read. The card performs both contractions; the
    /// host neither selects a phase nor replays the product.
    pub fn conduct(
        &mut self,
        fronts: &[Vec<ExactComplexWaveCurrent>],
    ) -> Result<ResidentComplexIncidenceReturn, CudaRefineError> {
        let nodes = self.nodes as usize;
        if fronts.is_empty() || fronts.iter().any(|front| front.len() != nodes) {
            return Err(CudaRefineError::ComplexCurrentShape);
        }
        if fronts.len() > u32::MAX as usize {
            return Err(CudaRefineError::ComplexCurrentShape);
        }

        let mut real = Vec::with_capacity(fronts.len() * nodes);
        let mut imaginary = Vec::with_capacity(fronts.len() * nodes);
        let mut denominators = Vec::with_capacity(fronts.len());
        let mut greatest_numerator = 0u128;
        for front in fronts {
            let denominator = common_complex_denominator(front)?;
            for current in front {
                let re = current.real.numer() * (&denominator / current.real.denom());
                let im = current.imaginary.numer() * (&denominator / current.imaginary.denom());
                let re = re
                    .to_i64()
                    .ok_or(CudaRefineError::ComplexCurrentOutsideApparatus)?;
                let im = im
                    .to_i64()
                    .ok_or(CudaRefineError::ComplexCurrentOutsideApparatus)?;
                greatest_numerator = greatest_numerator
                    .max(u128::from(re.unsigned_abs()))
                    .max(u128::from(im.unsigned_abs()));
                real.push(re);
                imaginary.push(im);
            }
            denominators.push(
                denominator
                    .to_u64()
                    .ok_or(CudaRefineError::ComplexCurrentOutsideApparatus)?,
            );
        }
        if self
            .greatest_row_mass
            .checked_mul(greatest_numerator)
            .filter(|bound| *bound <= i64::MAX as u128)
            .is_none()
        {
            return Err(CudaRefineError::ComplexIncidenceAccumulationOverflow);
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let coefficient_real = Buffer::of(&real)?;
        let coefficient_imaginary = Buffer::of(&imaginary)?;
        let output_count = fronts
            .len()
            .checked_mul(self.branches as usize)
            .ok_or(CudaRefineError::ComplexIncidenceShape)?;
        let section_real = Buffer::alloc(output_count * std::mem::size_of::<i64>())?;
        let section_imaginary = Buffer::alloc(output_count * std::mem::size_of::<i64>())?;
        if output_count > 0 {
            let grid = self.card.grid_for(output_count as u64)?;
            let mut incidence_pointer = self.incidence.pointer;
            let mut real_pointer = coefficient_real.pointer;
            let mut imaginary_pointer = coefficient_imaginary.pointer;
            let mut section_real_pointer = section_real.pointer;
            let mut section_imaginary_pointer = section_imaginary.pointer;
            let mut branch_count = self.branches;
            let mut node_count = self.nodes;
            let mut front_count = fronts.len() as u32;
            let mut arguments: [*mut c_void; 8] = [
                &mut incidence_pointer as *mut u64 as *mut c_void,
                &mut real_pointer as *mut u64 as *mut c_void,
                &mut imaginary_pointer as *mut u64 as *mut c_void,
                &mut section_real_pointer as *mut u64 as *mut c_void,
                &mut section_imaginary_pointer as *mut u64 as *mut c_void,
                &mut branch_count as *mut u32 as *mut c_void,
                &mut node_count as *mut u32 as *mut c_void,
                &mut front_count as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.complex_incidence,
                        grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(conduct_complex_incidence)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.card.launches += 1;
        }
        let mut returned_real = vec![0i64; output_count];
        let mut returned_imaginary = vec![0i64; output_count];
        section_real.read(&mut returned_real)?;
        section_imaginary.read(&mut returned_imaginary)?;
        let branches = self.branches as usize;
        let sections = denominators
            .iter()
            .enumerate()
            .map(|(front, denominator)| {
                (0..branches)
                    .map(|branch| {
                        let at = front * branches + branch;
                        ExactComplexWaveCurrent::new(
                            Rat::new(BigInt::from(returned_real[at]), BigInt::from(*denominator)),
                            Rat::new(
                                BigInt::from(returned_imaginary[at]),
                                BigInt::from(*denominator),
                            ),
                        )
                    })
                    .collect()
            })
            .collect();
        let coefficient_octets = std::mem::size_of_val(real.as_slice())
            .checked_add(std::mem::size_of_val(imaginary.as_slice()))
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(denominators.as_slice())))
            .ok_or(CudaRefineError::ComplexIncidenceShape)? as u64;
        let output_octets = output_count
            .checked_mul(2 * std::mem::size_of::<i64>())
            .ok_or(CudaRefineError::ComplexIncidenceShape)? as u64;
        Ok(ResidentComplexIncidenceReturn {
            address: self.address.clone(),
            grain: self.grain,
            sections,
            device: self.card.device_name().to_owned(),
            launches: u64::from(output_count > 0),
            synchronizations: u64::from(output_count > 0),
            block_threads: self.card.block_threads(),
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets: coefficient_octets,
            successor_host_egress_octets: output_octets,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets: coefficient_octets + output_octets,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            binary_receiver_taken: false,
        })
    }
}

/// The source-neutral incidence returned after a complete receiver constitutive form has already
/// acted through its reverse causal word.  `rows[f]` is therefore the exact effective covector
/// seen by factor `f`; it is not an invitation for the apparatus to reconstruct a foreign metric
/// or to replay a host-side `M` phase.  The equality of these rows with the mounted incidence is
/// the local naturality receipt for the resident contraction.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CausalAdjointPulledIncidence {
    pub schema: String,
    pub rows: Vec<Vec<i64>>,
}

pub const CAUSAL_ADJOINT_PULLED_INCIDENCE_SCHEMA: &str =
    "holonic-engine.causal-adjoint-pulled-incidence.v1";

impl CausalAdjointPulledIncidence {
    /// The factor and coefficient populations are read from returned local covectors.  There is
    /// no caller-selected width, rank, or source coordinate in this constructor.
    pub fn found(rows: Vec<Vec<i64>>) -> Result<Self, CudaRefineError> {
        let incidence = Self {
            schema: CAUSAL_ADJOINT_PULLED_INCIDENCE_SCHEMA.to_owned(),
            rows,
        };
        incidence.validate()?;
        Ok(incidence)
    }

    pub fn validate(&self) -> Result<(), CudaRefineError> {
        let Some(nodes) = self.rows.first().map(Vec::len) else {
            return Err(CudaRefineError::CoupledComplexParametronShape);
        };
        if self.schema != CAUSAL_ADJOINT_PULLED_INCIDENCE_SCHEMA
            || nodes == 0
            || self.rows.len() > u32::MAX as usize
            || nodes > u32::MAX as usize
            || self.rows.iter().any(|row| row.len() != nodes)
        {
            return Err(CudaRefineError::CoupledComplexParametronShape);
        }
        Ok(())
    }

    pub fn factors(&self) -> usize {
        self.rows.len()
    }

    pub fn nodes(&self) -> usize {
        self.rows.first().map_or(0, Vec::len)
    }
}

/// One compact, already-derived exact mixed finite-Leibniz remainder.  `contribution` is the
/// complete returned complex mixed term of an admitted L1 family; it is not a caller coefficient
/// to be multiplied against a replacement current.  Every factor address is an index into a
/// population derived at mount from the returned causal-adjoint incidence, never a semantic label
/// or foreign coordinate.  The three incidences are retained separately because withdrawing any
/// one factor removes the whole mixed contact.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CoupledComplexInteraction {
    pub output_factor: u32,
    pub left_factor: u32,
    pub right_factor: u32,
    pub contribution: ExactComplexWaveCurrent,
}

/// One terminal receipt from the resident causal-adjoint-pulled Complex-Parametron body.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ResidentCoupledComplexParametronReturn {
    pub address: String,
    pub sections: Vec<ExactComplexWaveCurrent>,
    /// The exact effective covectors whose equality with the mounted rows is the factorization
    /// receipt.  A constitutive form has already acted upstream in the causal adjoint.
    pub causal_adjoint_pulled_incidence: CausalAdjointPulledIncidence,
    pub active_factors: Vec<bool>,
    pub common_denominator: BigInt,
    pub dyadic_exponent: Option<u32>,
    pub limb_count: usize,
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub block_threads: u32,
    pub mount_host_ingress_octets: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub resident_working_octets: u64,
    pub mixed_interaction_count: usize,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub binary_receiver_taken: bool,
}

pub(super) struct PendingCoupledComplexParametron {
    active_factors: Vec<bool>,
    active: Buffer,
    output_real_sign: Buffer,
    output_real_limbs: Buffer,
    output_imaginary_sign: Buffer,
    output_imaginary_limbs: Buffer,
}

/// One singular resident body coupling causal-adjoint-pulled incidence and its finite-Leibniz
/// interaction graph.  It deliberately owns no metric phase: the complete receiver constitution
/// has already been pulled through the retained reverse word before this native rest is mounted.
///
/// The active population is a recoverable withdrawal aperture, not a binary Parametron reading.
/// It removes a primary factor and every mixed term incident to that factor inside the one device
/// kernel, without a host semantic replay or invariant re-upload.
pub struct ResidentCoupledComplexParametron {
    primary_real_sign: Buffer,
    primary_real_limbs: Buffer,
    primary_imaginary_sign: Buffer,
    primary_imaginary_limbs: Buffer,
    output_factors: Buffer,
    left_factors: Buffer,
    right_factors: Buffer,
    mixed_real_sign: Buffer,
    mixed_real_limbs: Buffer,
    mixed_imaginary_sign: Buffer,
    mixed_imaginary_limbs: Buffer,
    card: CudaRefineExecutor,
    address: String,
    factors: u32,
    interactions: u32,
    limb_count: u32,
    common_denominator: BigInt,
    causal_adjoint_pulled_incidence: CausalAdjointPulledIncidence,
    mount_host_ingress_octets: u64,
}

pub(super) struct CoupledLimbChart {
    pub(super) denominator: BigInt,
    pub(super) limb_count: usize,
    primary_real_sign: Vec<u8>,
    primary_real_limbs: Vec<u32>,
    primary_imaginary_sign: Vec<u8>,
    primary_imaginary_limbs: Vec<u32>,
    mixed_real_sign: Vec<u8>,
    pub(super) mixed_real_limbs: Vec<u32>,
    mixed_imaginary_sign: Vec<u8>,
    pub(super) mixed_imaginary_limbs: Vec<u32>,
}

pub(super) fn lcm_positive(left: BigInt, right: &BigInt) -> BigInt {
    let divisor = integer_gcd(left.clone(), right.clone());
    (left / divisor) * right
}

fn is_word_prime(candidate: u32) -> bool {
    if candidate < 2 {
        return false;
    }
    if candidate == 2 {
        return true;
    }
    if candidate & 1 == 0 {
        return false;
    }
    let mut divisor = 3_u32;
    while u64::from(divisor) * u64::from(divisor) <= u64::from(candidate) {
        if candidate % divisor == 0 {
            return false;
        }
        divisor += 2;
    }
    true
}

/// Derive a deterministic family of distinct word-prime receiver charts whose product strictly
/// exceeds the exact requested bound. The family population is a consequence of the bound; this
/// function owns no fixed chart count or semantic rank aperture.
pub(super) fn derive_word_prime_family(
    bound: &BigUint,
) -> Result<(Vec<u32>, BigUint), CudaRefineError> {
    let mut primes = Vec::new();
    let mut product = BigUint::one();
    let mut candidate = u32::MAX >> 1;
    while &product <= bound {
        if is_word_prime(candidate) {
            product *= candidate;
            primes.push(candidate);
        }
        candidate = candidate
            .checked_sub(2)
            .filter(|next| *next >= 3)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    }
    if primes.is_empty() {
        // Even the smallest nonzero image needs one chart so its rank is actually witnessed.
        while !is_word_prime(candidate) {
            candidate = candidate
                .checked_sub(2)
                .filter(|next| *next >= 3)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        }
        primes.push(candidate);
        product = BigUint::from(candidate);
    }
    Ok((primes, product))
}

/// Derive one deterministic finite-chart occurrence which can witness a nonzero minor.  This is
/// deliberately not an exact-rank oracle: its modular rank is only the lower leg of the later
/// rank sandwich.  The reconstructed identity `D X = J B`, with `D != 0`, supplies the upper leg
/// by proving that every row of `X` lies in the selected-row span.  A rank-lowering chart therefore
/// obstructs at the exact square instead of being mistaken for an admitted rational rank.
pub(super) fn derive_word_prime_rank_witness() -> Result<(Vec<u32>, BigUint), CudaRefineError> {
    derive_word_prime_family(&BigUint::zero())
}

fn exact_primary_contributions(
    incidence: &CausalAdjointPulledIncidence,
    standing_front: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    incidence
        .rows
        .iter()
        .map(|row| {
            row.iter().zip(standing_front).fold(
                ExactComplexWaveCurrent::zero(),
                |total, (coefficient, current)| {
                    total.add(&current.scaled(&Rat::from_integer(BigInt::from(*coefficient))))
                },
            )
        })
        .collect()
}

fn dyadic_exponent(denominator: &BigInt) -> Option<u32> {
    if denominator <= &BigInt::zero() {
        return None;
    }
    let mut residual = denominator.clone();
    let mut exponent = 0u32;
    while (&residual & BigInt::one()).is_zero() {
        residual >>= 1usize;
        exponent = exponent.checked_add(1)?;
    }
    (residual == BigInt::one()).then_some(exponent)
}

pub(super) fn encode_component(
    value: &Rat,
    denominator: &BigInt,
    limb_count: usize,
) -> Result<(u8, Vec<u32>), CudaRefineError> {
    let numerator = value.numer() * (denominator / value.denom());
    let sign = if numerator.is_zero() {
        0
    } else if numerator.is_negative() {
        2
    } else {
        1
    };
    let (_, mut limbs) = numerator.abs().to_u32_digits();
    if limbs.len() > limb_count {
        return Err(CudaRefineError::CoupledComplexParametronAccumulationOverflow);
    }
    limbs.resize(limb_count, 0);
    Ok((sign, limbs))
}

impl ResidentExactRationalMatrix {
    pub(super) fn mount(matrix: &ExactRatMatrix) -> Result<Self, CudaRefineError> {
        if matrix.rows() == 0
            || matrix.columns() == 0
            || matrix.rows() > u32::MAX as usize
            || matrix.columns() > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let common_denominator = matrix.entries().iter().fold(BigInt::one(), |held, entry| {
            lcm_positive(held, entry.denom())
        });
        if common_denominator <= BigInt::zero() {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_numerator = matrix
            .entries()
            .iter()
            .map(|entry| (entry.numer() * (&common_denominator / entry.denom())).abs())
            .max()
            .unwrap_or_else(BigInt::zero);
        let numerator_limb_count = maximal_numerator.to_u32_digits().1.len().max(1);
        let denominator_limb_count = common_denominator.to_u32_digits().1.len().max(1);
        if numerator_limb_count > u32::MAX as usize || denominator_limb_count > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let mut numerator_signs = Vec::with_capacity(matrix.entries().len());
        let mut numerator_limbs = Vec::with_capacity(
            matrix
                .entries()
                .len()
                .checked_mul(numerator_limb_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        );
        for entry in matrix.entries() {
            let (sign, limbs) = encode_component(entry, &common_denominator, numerator_limb_count)?;
            numerator_signs.push(sign);
            numerator_limbs.extend(limbs);
        }
        let mut denominator_limbs = common_denominator.to_u32_digits().1;
        denominator_limbs.resize(denominator_limb_count, 0);
        let resident_octets = [
            std::mem::size_of_val(&numerator_signs[..]),
            std::mem::size_of_val(&numerator_limbs[..]),
            std::mem::size_of_val(&denominator_limbs[..]),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let mounted = Self {
            rows: matrix.rows() as u32,
            columns: matrix.columns() as u32,
            numerator_limb_count: numerator_limb_count as u32,
            denominator_limb_count: denominator_limb_count as u32,
            common_denominator,
            maximal_numerator,
            numerator_signs: Buffer::of(&numerator_signs)?,
            numerator_limbs: Buffer::of(&numerator_limbs)?,
            denominator_limbs: Buffer::of(&denominator_limbs)?,
            resident_octets,
        };
        mounted.validate_layout()?;
        Ok(mounted)
    }

    pub(super) fn validate_layout(&self) -> Result<(), CudaRefineError> {
        if self.rows == 0
            || self.columns == 0
            || self.numerator_limb_count == 0
            || self.denominator_limb_count == 0
            || self.common_denominator <= BigInt::zero()
            || self.maximal_numerator.is_negative()
            || self.resident_octets == 0
            || self.numerator_signs.pointer == 0
            || self.numerator_limbs.pointer == 0
            || self.denominator_limbs.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }
}

impl ResidentIntegralMatrix {
    pub(super) fn validate_layout(&self) -> Result<(), CudaRefineError> {
        if self.rows == 0
            || self.columns == 0
            || self.numerator_limb_count == 0
            || self.maximal_numerator.is_negative()
            || self.resident_octets == 0
            || self.signs.pointer == 0
            || self.limbs.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }
}

impl ResidentFactoredConstitutiveSpine {
    pub(super) fn validate_layout(&self, factors: u32) -> Result<(), CudaRefineError> {
        self.root_constitutive.validate_layout()?;
        self.effective_incidence.validate_layout()?;
        if self.root_rank == 0
            || self.history_population == 0
            || self.root_constitutive.rows != self.root_rank
            || self.root_constitutive.columns != self.root_rank
            || self.effective_incidence.columns != factors
            || self.effective_incidence.rows
                != self
                    .root_rank
                    .checked_mul(self.history_population)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            || self.history_weight_limb_count == 0
            || self.maximal_history_weight.is_zero()
            || self.history_weights.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }
}

impl ResidentTransportedConstitutiveSpine {
    pub(super) fn validate_layout(&self, factors: u32) -> Result<(), CudaRefineError> {
        self.effective_incidence.validate_layout()?;
        if self.root_rank == 0
            || self.history_population == 0
            || self.effective_incidence.columns != factors
            || self.effective_incidence.rows
                != self
                    .root_rank
                    .checked_mul(self.history_population)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            || self.history_weight_limb_count == 0
            || self.maximal_history_weight.is_zero()
            || self.history_weights.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }
}

impl ResidentTransportedFactoredHistory {
    pub(super) fn validate_layout(&self, effective_rows: u32) -> Result<(), CudaRefineError> {
        if self.root_rank == 0
            || self.history_population == 0
            || effective_rows
                != self
                    .root_rank
                    .checked_mul(self.history_population)
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            || self.history_weight_limb_count == 0
            || self.maximal_history_weight.is_zero()
            || self.history_weights.pointer == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }
}

pub(super) fn factored_moment_section_identity(section: &FactoredMomentSection) -> String {
    let mut identity = Sha256::new();
    identity.update(b"holonic-engine.factored-moment-section.resident-address.v2");
    identity.update(section.factor_population.to_le_bytes());
    identity.update(section.image_rank.to_le_bytes());
    for factor in &section.basis_factors {
        identity.update(factor.to_le_bytes());
    }
    for matrix in [&section.incidence, &section.constitutive] {
        identity.update(matrix.rows().to_le_bytes());
        identity.update(matrix.columns().to_le_bytes());
        for entry in matrix.entries() {
            let numerator = entry.numer().to_signed_bytes_le();
            let denominator = entry.denom().to_signed_bytes_le();
            identity.update(numerator.len().to_le_bytes());
            identity.update(numerator);
            identity.update(denominator.len().to_le_bytes());
            identity.update(denominator);
        }
    }
    identity
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

pub(super) fn encode_integer(
    value: &BigInt,
    limb_count: usize,
) -> Result<(u8, Vec<u32>), CudaRefineError> {
    encode_component(
        &Rat::from_integer(value.clone()),
        &BigInt::one(),
        limb_count,
    )
}

pub(super) fn encode_integral_form_factors(
    factors: &[IntegralFormFrameFactor],
    limb_count: usize,
) -> Result<(Vec<u32>, Vec<u8>, Vec<u32>), CudaRefineError> {
    let mut sources = Vec::with_capacity(factors.len());
    let mut signs = Vec::with_capacity(factors.len());
    let mut limbs = Vec::with_capacity(factors.len().saturating_mul(limb_count));
    for factor in factors {
        match factor.coordinate {
            None if factor.scale.is_zero() => sources.push(u32::MAX),
            Some(source) if !factor.scale.is_zero() => sources.push(source),
            _ => return Err(CudaRefineError::MembraneInteriorWordShape),
        }
        let (sign, encoded) = encode_integer(&factor.scale, limb_count)?;
        signs.push(sign);
        limbs.extend(encoded);
    }
    Ok((sources, signs, limbs))
}

pub(super) fn decode_component(
    sign: u8,
    limbs: &[u32],
    denominator: &BigInt,
) -> Result<Rat, CudaRefineError> {
    let mut value = BigInt::zero();
    for limb in limbs.iter().rev() {
        value <<= 32usize;
        value += *limb;
    }
    match sign {
        0 if value.is_zero() => Ok(Rat::new(value, denominator.clone())),
        1 if !value.is_zero() => Ok(Rat::new(value, denominator.clone())),
        2 if !value.is_zero() => Ok(Rat::new(-value, denominator.clone())),
        _ => Err(CudaRefineError::CoupledComplexParametronShape),
    }
}

pub(super) fn decode_signed_magnitude(sign: u8, limbs: &[u32]) -> Result<BigInt, CudaRefineError> {
    let mut value = BigInt::zero();
    for limb in limbs.iter().rev() {
        value <<= 32usize;
        value += *limb;
    }
    match sign {
        0 if value.is_zero() => Ok(value),
        1 if !value.is_zero() => Ok(value),
        2 if !value.is_zero() => Ok(-value),
        _ => Err(CudaRefineError::MembraneInteriorWordShape),
    }
}

pub(super) fn derive_coupled_limb_chart(
    incidence: &CausalAdjointPulledIncidence,
    standing_front: &[ExactComplexWaveCurrent],
    interactions: &[CoupledComplexInteraction],
) -> Result<CoupledLimbChart, CudaRefineError> {
    if standing_front.len() != incidence.nodes() || interactions.is_empty() {
        return Err(CudaRefineError::CoupledComplexParametronShape);
    }
    let primary = exact_primary_contributions(incidence, standing_front);
    let mut denominator = BigInt::one();
    for current in primary
        .iter()
        .chain(interactions.iter().map(|term| &term.contribution))
    {
        for component in [&current.real, &current.imaginary] {
            if component.denom().is_zero() {
                return Err(CudaRefineError::CoupledComplexParametronShape);
            }
            denominator = lcm_positive(denominator, component.denom());
        }
    }
    let mut maximal = BigInt::zero();
    for factor in 0..incidence.factors() {
        for (axis, component) in [&primary[factor].real, &primary[factor].imaginary]
            .into_iter()
            .enumerate()
        {
            let mut magnitude = (component.numer() * (&denominator / component.denom())).abs();
            for interaction in interactions
                .iter()
                .filter(|term| term.output_factor as usize == factor)
            {
                let mixed = if axis == 0 {
                    &interaction.contribution.real
                } else {
                    &interaction.contribution.imaginary
                };
                magnitude += (mixed.numer() * (&denominator / mixed.denom())).abs();
            }
            maximal = maximal.max(magnitude);
        }
    }
    let (_, digits) = maximal.to_u32_digits();
    let limb_count = digits.len().max(1);
    let mut chart = CoupledLimbChart {
        denominator: denominator.clone(),
        limb_count,
        primary_real_sign: Vec::with_capacity(incidence.factors()),
        primary_real_limbs: Vec::with_capacity(incidence.factors() * limb_count),
        primary_imaginary_sign: Vec::with_capacity(incidence.factors()),
        primary_imaginary_limbs: Vec::with_capacity(incidence.factors() * limb_count),
        mixed_real_sign: Vec::with_capacity(interactions.len()),
        mixed_real_limbs: Vec::with_capacity(interactions.len() * limb_count),
        mixed_imaginary_sign: Vec::with_capacity(interactions.len()),
        mixed_imaginary_limbs: Vec::with_capacity(interactions.len() * limb_count),
    };
    for current in &primary {
        let (sign, limbs) = encode_component(&current.real, &denominator, limb_count)?;
        chart.primary_real_sign.push(sign);
        chart.primary_real_limbs.extend(limbs);
        let (sign, limbs) = encode_component(&current.imaginary, &denominator, limb_count)?;
        chart.primary_imaginary_sign.push(sign);
        chart.primary_imaginary_limbs.extend(limbs);
    }
    for interaction in interactions {
        let (sign, limbs) =
            encode_component(&interaction.contribution.real, &denominator, limb_count)?;
        chart.mixed_real_sign.push(sign);
        chart.mixed_real_limbs.extend(limbs);
        let (sign, limbs) = encode_component(
            &interaction.contribution.imaginary,
            &denominator,
            limb_count,
        )?;
        chart.mixed_imaginary_sign.push(sign);
        chart.mixed_imaginary_limbs.extend(limbs);
    }
    Ok(chart)
}

impl ResidentCoupledComplexParametron {
    /// Mounting is the only chart conversion: exact primary adjoint contributions and the exact
    /// mixed remainders are rebased to one derived denominator before reaching the device.
    pub fn mount(
        card: CudaRefineExecutor,
        address: impl Into<String>,
        causal_adjoint_pulled_incidence: CausalAdjointPulledIncidence,
        standing_front: Vec<ExactComplexWaveCurrent>,
        interactions: Vec<CoupledComplexInteraction>,
    ) -> Result<Self, CudaRefineError> {
        causal_adjoint_pulled_incidence.validate()?;
        let factors = causal_adjoint_pulled_incidence.factors();
        if interactions.len() > u32::MAX as usize {
            return Err(CudaRefineError::CoupledComplexParametronShape);
        }
        for interaction in &interactions {
            if interaction.contribution.is_zero()
                || interaction.output_factor as usize >= factors
                || interaction.left_factor as usize >= factors
                || interaction.right_factor as usize >= factors
            {
                return Err(CudaRefineError::CoupledComplexParametronShape);
            }
        }
        let chart = derive_coupled_limb_chart(
            &causal_adjoint_pulled_incidence,
            &standing_front,
            &interactions,
        )?;
        if chart.limb_count > u32::MAX as usize {
            return Err(CudaRefineError::CoupledComplexParametronShape);
        }
        let output_factors = interactions
            .iter()
            .map(|term| term.output_factor)
            .collect::<Vec<_>>();
        let left_factors = interactions
            .iter()
            .map(|term| term.left_factor)
            .collect::<Vec<_>>();
        let right_factors = interactions
            .iter()
            .map(|term| term.right_factor)
            .collect::<Vec<_>>();
        let mount_host_ingress_octets = [
            std::mem::size_of_val(chart.primary_real_sign.as_slice()),
            std::mem::size_of_val(chart.primary_real_limbs.as_slice()),
            std::mem::size_of_val(chart.primary_imaginary_sign.as_slice()),
            std::mem::size_of_val(chart.primary_imaginary_limbs.as_slice()),
            std::mem::size_of_val(output_factors.as_slice()),
            std::mem::size_of_val(left_factors.as_slice()),
            std::mem::size_of_val(right_factors.as_slice()),
            std::mem::size_of_val(chart.mixed_real_sign.as_slice()),
            std::mem::size_of_val(chart.mixed_real_limbs.as_slice()),
            std::mem::size_of_val(chart.mixed_imaginary_sign.as_slice()),
            std::mem::size_of_val(chart.mixed_imaginary_limbs.as_slice()),
        ]
        .into_iter()
        .try_fold(0usize, usize::checked_add)
        .ok_or(CudaRefineError::CoupledComplexParametronShape)?
            as u64;
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        Ok(Self {
            primary_real_sign: Buffer::of(&chart.primary_real_sign)?,
            primary_real_limbs: Buffer::of(&chart.primary_real_limbs)?,
            primary_imaginary_sign: Buffer::of(&chart.primary_imaginary_sign)?,
            primary_imaginary_limbs: Buffer::of(&chart.primary_imaginary_limbs)?,
            output_factors: Buffer::of(&output_factors)?,
            left_factors: Buffer::of(&left_factors)?,
            right_factors: Buffer::of(&right_factors)?,
            mixed_real_sign: Buffer::of(&chart.mixed_real_sign)?,
            mixed_real_limbs: Buffer::of(&chart.mixed_real_limbs)?,
            mixed_imaginary_sign: Buffer::of(&chart.mixed_imaginary_sign)?,
            mixed_imaginary_limbs: Buffer::of(&chart.mixed_imaginary_limbs)?,
            card,
            address: address.into(),
            factors: factors as u32,
            interactions: interactions.len() as u32,
            limb_count: chart.limb_count as u32,
            common_denominator: chart.denominator,
            causal_adjoint_pulled_incidence,
            mount_host_ingress_octets,
        })
    }

    pub fn causal_adjoint_pulled_incidence(&self) -> &CausalAdjointPulledIncidence {
        &self.causal_adjoint_pulled_incidence
    }

    pub fn conduct(
        &mut self,
        active_factors: &[bool],
    ) -> Result<ResidentCoupledComplexParametronReturn, CudaRefineError> {
        let pending = self.enqueue(active_factors)?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.finalize(pending, 1)
    }

    pub(super) fn enqueue(
        &mut self,
        active_factors: &[bool],
    ) -> Result<PendingCoupledComplexParametron, CudaRefineError> {
        if active_factors.len() != self.factors as usize {
            return Err(CudaRefineError::CoupledComplexParametronShape);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let active = Buffer::of(
            &active_factors
                .iter()
                .map(|value| u8::from(*value))
                .collect::<Vec<_>>(),
        )?;
        let output_real_sign = Buffer::alloc(self.factors as usize)?;
        let output_real_limbs = Buffer::alloc(
            self.factors as usize * self.limb_count as usize * std::mem::size_of::<u32>(),
        )?;
        let output_imaginary_sign = Buffer::alloc(self.factors as usize)?;
        let output_imaginary_limbs = Buffer::alloc(
            self.factors as usize * self.limb_count as usize * std::mem::size_of::<u32>(),
        )?;
        let mut pointers = [
            self.primary_real_sign.pointer,
            self.primary_real_limbs.pointer,
            self.primary_imaginary_sign.pointer,
            self.primary_imaginary_limbs.pointer,
            active.pointer,
            self.output_factors.pointer,
            self.left_factors.pointer,
            self.right_factors.pointer,
            self.mixed_real_sign.pointer,
            self.mixed_real_limbs.pointer,
            self.mixed_imaginary_sign.pointer,
            self.mixed_imaginary_limbs.pointer,
            output_real_sign.pointer,
            output_real_limbs.pointer,
            output_imaginary_sign.pointer,
            output_imaginary_limbs.pointer,
        ];
        let mut factor_count = self.factors;
        let mut interaction_count = self.interactions;
        let mut limb_count = self.limb_count;
        let mut arguments = pointers
            .iter_mut()
            .map(|pointer| pointer as *mut u64 as *mut c_void)
            .collect::<Vec<_>>();
        arguments.extend([
            &mut factor_count as *mut u32 as *mut c_void,
            &mut interaction_count as *mut u32 as *mut c_void,
            &mut limb_count as *mut u32 as *mut c_void,
        ]);
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.coupled_complex_parametron,
                    self.card.grid_for(u64::from(self.factors))?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_coupled_complex_parametron)",
        )?;
        self.card.launches += 1;
        Ok(PendingCoupledComplexParametron {
            active_factors: active_factors.to_vec(),
            active,
            output_real_sign,
            output_real_limbs,
            output_imaginary_sign,
            output_imaginary_limbs,
        })
    }

    pub(super) fn finalize(
        &mut self,
        pending: PendingCoupledComplexParametron,
        synchronizations: u64,
    ) -> Result<ResidentCoupledComplexParametronReturn, CudaRefineError> {
        let PendingCoupledComplexParametron {
            active_factors,
            active,
            output_real_sign,
            output_real_limbs,
            output_imaginary_sign,
            output_imaginary_limbs,
        } = pending;
        let _active_lifetime = active;
        let mut real_sign = vec![0u8; self.factors as usize];
        let mut real_limbs = vec![0u32; self.factors as usize * self.limb_count as usize];
        let mut imaginary_sign = vec![0u8; self.factors as usize];
        let mut imaginary_limbs = vec![0u32; self.factors as usize * self.limb_count as usize];
        output_real_sign.read(&mut real_sign)?;
        output_real_limbs.read(&mut real_limbs)?;
        output_imaginary_sign.read(&mut imaginary_sign)?;
        output_imaginary_limbs.read(&mut imaginary_limbs)?;
        let sections = (0..self.factors as usize)
            .map(|factor| {
                let start = factor * self.limb_count as usize;
                let end = start + self.limb_count as usize;
                Ok(ExactComplexWaveCurrent::new(
                    decode_component(
                        real_sign[factor],
                        &real_limbs[start..end],
                        &self.common_denominator,
                    )?,
                    decode_component(
                        imaginary_sign[factor],
                        &imaginary_limbs[start..end],
                        &self.common_denominator,
                    )?,
                ))
            })
            .collect::<Result<Vec<_>, CudaRefineError>>()?;
        let successor_host_ingress_octets = active_factors.len() as u64;
        let successor_host_egress_octets = (self.factors as usize)
            .checked_mul(
                2 * std::mem::size_of::<u8>()
                    + 2 * self.limb_count as usize * std::mem::size_of::<u32>(),
            )
            .ok_or(CudaRefineError::CoupledComplexParametronShape)?
            as u64;
        Ok(ResidentCoupledComplexParametronReturn {
            address: self.address.clone(),
            sections,
            causal_adjoint_pulled_incidence: self.causal_adjoint_pulled_incidence.clone(),
            active_factors,
            common_denominator: self.common_denominator.clone(),
            dyadic_exponent: dyadic_exponent(&self.common_denominator),
            limb_count: self.limb_count as usize,
            device: self.card.device_name().to_owned(),
            launches: 1,
            synchronizations,
            block_threads: self.card.block_threads(),
            mount_host_ingress_octets: self.mount_host_ingress_octets,
            successor_host_ingress_octets,
            successor_host_egress_octets,
            resident_invariant_octets: self.mount_host_ingress_octets,
            resident_working_octets: successor_host_ingress_octets + successor_host_egress_octets,
            mixed_interaction_count: self.interactions as usize,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
            binary_receiver_taken: false,
        })
    }
}

/// One singular-card composition of the existing L2 coupled current, participant causal atlas,
/// and L5 affine transport laws.  Its primary executor is declared last so every forked leaf and
/// its buffers depart before the one underlying CUDA context/module is released.

pub(super) fn common_real_denominator(front: &[Rat]) -> Result<BigInt, CudaRefineError> {
    let mut common = BigInt::one();
    for denominator in front.iter().map(Rat::denom) {
        if denominator.is_zero() {
            return Err(CudaRefineError::IntervalPotentialCurrentOutsideApparatus);
        }
        let gcd = integer_gcd(common.clone(), denominator.clone());
        common = (common / gcd) * denominator;
    }
    Ok(common)
}

fn common_complex_denominator(
    front: &[ExactComplexWaveCurrent],
) -> Result<BigInt, CudaRefineError> {
    let mut common = BigInt::one();
    for denominator in front
        .iter()
        .flat_map(|current| [current.real.denom(), current.imaginary.denom()])
    {
        if denominator.is_zero() {
            return Err(CudaRefineError::ComplexCurrentShape);
        }
        let divisor = integer_gcd(common.clone(), denominator.clone());
        common = (common / divisor) * denominator;
    }
    Ok(common.abs())
}

fn integer_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    if left.is_zero() { BigInt::one() } else { left }
}

impl ResidentNativeWord {
    /// Mount one finite native action and its complete ordered word as continuing device standing.
    pub fn mount(
        card: CudaRefineExecutor,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        word: &[u32],
    ) -> Result<Self, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
            || word.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if let Some(generator) = word
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }
        driver(unsafe { cuCtxSetCurrent(card.context) }, "cuCtxSetCurrent")?;
        let word_length = word.len();
        let generator_table = Buffer::of(generator_table)?;
        let word = Buffer::of(word)?;
        let resident_invariant_octets = expected
            .checked_mul(std::mem::size_of::<u32>())
            .and_then(|octets| octets.checked_add(word_length * std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::NativeActionTooWide)?
            as u64;
        Ok(Self {
            generator_table,
            word,
            card,
            states: states as u32,
            word_length: word_length as u32,
            resident_invariant_octets,
            mount_host_ingress_octets: resident_invariant_octets,
        })
    }

    pub fn device_name(&self) -> &str {
        self.card.device_name()
    }

    pub fn block_threads(&self) -> u32 {
        self.card.block_threads()
    }

    pub fn mount_host_ingress_octets(&self) -> u64 {
        self.mount_host_ingress_octets
    }

    pub fn resident_invariant_octets(&self) -> u64 {
        self.resident_invariant_octets
    }

    /// Carry a later addressed population through the already-resident action and word.
    pub fn conduct(
        &mut self,
        native_start: &[u32],
    ) -> Result<ResidentNativeWordReturn, CudaRefineError> {
        if native_start.len() > u32::MAX as usize {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = native_start
            .iter()
            .copied()
            .find(|state| *state >= self.states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: self.states as usize,
            });
        }

        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let start = Buffer::of(native_start)?;
        let end = Buffer::alloc(std::mem::size_of_val(native_start))?;
        let count = native_start.len();
        if count > 0 {
            let grid = self.card.grid_for(count as u64)?;
            let mut table_pointer = self.generator_table.pointer;
            let mut word_pointer = self.word.pointer;
            let mut start_pointer = start.pointer;
            let mut end_pointer = end.pointer;
            let mut cell_count = count as u32;
            let mut state_count = self.states;
            let mut word_length = self.word_length;
            let mut arguments: Vec<*mut c_void> = vec![
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut word_pointer as *mut u64 as *mut c_void,
                &mut start_pointer as *mut u64 as *mut c_void,
                &mut end_pointer as *mut u64 as *mut c_void,
                &mut cell_count as *mut u32 as *mut c_void,
                &mut state_count as *mut u32 as *mut c_void,
                &mut word_length as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.card.native_word,
                        grid,
                        1,
                        1,
                        self.card.block_x,
                        1,
                        1,
                        0,
                        ptr::null_mut(),
                        arguments.as_mut_ptr(),
                        ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(conduct_native_word)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.card.launches += 1;
        }
        let mut native_end = vec![0u32; count];
        if count > 0 {
            end.read(&mut native_end)?;
        }
        let state_octets = std::mem::size_of_val(native_start) as u64;
        Ok(ResidentNativeWordReturn {
            native_end,
            launches: u64::from(count > 0),
            synchronizations: u64::from(count > 0),
            host_ingress_octets: state_octets,
            host_egress_octets: state_octets,
            resident_invariant_octets: self.resident_invariant_octets,
            resident_working_octets: state_octets * 2,
            invariant_transport_reuploaded: false,
        })
    }
}
