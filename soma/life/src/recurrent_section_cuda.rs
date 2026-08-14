//! Record: research/records/2026-08-12_THE_RECURRENT_LAW_CROSSES_THE_CORPUS_DEPARTURE_THE_UNSEEN_SECTION_RIDES_ITS_DEPOSIT.md
//! Mandatory CUDA owner for exact local transformation-law founding and later evaluation.

use core::ffi::c_void;

use mount::{Context, Device, DeviceBuffer, Module, Stream, SOMA_PTX};
use serde::Serialize;
use soma_abi::recurrent_law_cuda as wire;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BiaffineSampleGrid {
    pub x0: i64,
    pub x1: i64,
    pub y0: i64,
    pub y1: i64,
    /// `(x0,y0), (x1,y0), (x0,y1), (x1,y1)`.
    pub values: [i64; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BiaffineLaw {
    pub origin: [i64; 2],
    pub step: [i64; 2],
    /// Newton coefficients `c0, cx, cy, cxy`.
    pub coefficients: [i64; 4],
}

impl BiaffineLaw {
    pub const fn words(self) -> [i64; wire::LAW_VALUES] {
        [
            self.origin[0],
            self.origin[1],
            self.step[0],
            self.step[1],
            self.coefficients[0],
            self.coefficients[1],
            self.coefficients[2],
            self.coefficients[3],
        ]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BiaffineQuery {
    pub law: BiaffineLaw,
    pub point: [i64; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum BiaffineEvaluation {
    Value(i64),
    OutsideLattice,
    FiniteCarrierOverflow,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecurrentFoldQuery {
    pub law: BiaffineLaw,
    pub initial: i64,
    pub currents: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum RecurrentFoldEvaluation {
    Complete { trace: Vec<i64>, terminus: i64 },
    OutsideLattice,
    FiniteCarrierOverflow,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RecurrentLawCudaReceipt {
    pub schema: String,
    pub operation: String,
    pub device: String,
    pub rows: usize,
    pub launch_ordinal: u64,
    pub grid: [u32; 3],
    pub block: [u32; 3],
    pub host_semantic_replay: bool,
}

pub struct CudaRecurrentLawExecutor {
    module: Module,
    device_name: String,
    census: mount::cuda::LaunchCensus,
    launches: u64,
    stream: Stream,
    context: Context,
}

impl CudaRecurrentLawExecutor {
    pub fn new(device_ordinal: i32) -> Result<Self, String> {
        mount::cuda::init().map_err(|error| error.to_string())?;
        let device = Device::get(device_ordinal).map_err(|error| error.to_string())?;
        let census = device.launch_census().map_err(|error| error.to_string())?;
        let context = Context::create(&device).map_err(|error| error.to_string())?;
        let module = Module::load_ptx(SOMA_PTX).map_err(|error| error.to_string())?;
        module
            .function(wire::FOUND_ENTRY_SYMBOL)
            .map_err(|error| error.to_string())?;
        module
            .function(wire::EVALUATE_ENTRY_SYMBOL)
            .map_err(|error| error.to_string())?;
        module
            .function(wire::FOLD_ENTRY_SYMBOL)
            .map_err(|error| error.to_string())?;
        let stream = Stream::create().map_err(|error| error.to_string())?;
        Ok(Self {
            module,
            device_name: device.name,
            census,
            launches: 0,
            stream,
            context,
        })
    }

    pub fn device_name(&self) -> &str {
        &self.device_name
    }

    pub const fn launches(&self) -> u64 {
        self.launches
    }

    pub fn found(
        &mut self,
        grids: &[BiaffineSampleGrid],
    ) -> Result<(Vec<BiaffineLaw>, RecurrentLawCudaReceipt), String> {
        if grids.is_empty() {
            return Err("no transformation-law founding face reached the card".to_owned());
        }
        let mut input = Vec::with_capacity(grids.len() * wire::FOUND_INPUT_WORDS);
        for grid in grids {
            for value in [
                grid.x0,
                grid.x1,
                grid.y0,
                grid.y1,
                grid.values[0],
                grid.values[1],
                grid.values[2],
                grid.values[3],
            ] {
                input.extend_from_slice(&wire::encode_i64(value));
            }
        }
        let output_words = grids
            .len()
            .checked_mul(wire::FOUND_OUTPUT_WORDS)
            .ok_or_else(|| "the transformation-law founding output overflowed".to_owned())?;
        let (returned, receipt) = self.launch(
            wire::FOUND_ENTRY_SYMBOL,
            "found",
            input,
            output_words,
            grids.len(),
        )?;
        let mut laws = Vec::with_capacity(grids.len());
        for row in 0..grids.len() {
            let at = row * wire::FOUND_OUTPUT_WORDS;
            if returned[at + wire::FOUND_OUTPUT_VERSION] != wire::LAYOUT_VERSION
                || returned[at + wire::FOUND_OUTPUT_STATUS] != wire::STATUS_COMPLETE
            {
                return Err(format!(
                    "the card refused transformation-law founding row {row} with status {}",
                    returned[at + wire::FOUND_OUTPUT_STATUS]
                ));
            }
            let mut values = [0i64; wire::LAW_VALUES];
            for (coordinate, value) in values.iter_mut().enumerate() {
                *value = wire::decode_i64(
                    &returned,
                    at + wire::FOUND_OUTPUT_LAW_AT + coordinate * wire::I64_WORDS,
                )
                .ok_or_else(|| "the card truncated a founded transformation law".to_owned())?;
            }
            laws.push(BiaffineLaw {
                origin: [values[0], values[1]],
                step: [values[2], values[3]],
                coefficients: [values[4], values[5], values[6], values[7]],
            });
        }
        Ok((laws, receipt))
    }

    pub fn evaluate(
        &mut self,
        queries: &[BiaffineQuery],
    ) -> Result<(Vec<BiaffineEvaluation>, RecurrentLawCudaReceipt), String> {
        if queries.is_empty() {
            return Err("no remounted transformation-law query reached the card".to_owned());
        }
        let mut input = Vec::with_capacity(queries.len() * wire::EVALUATE_INPUT_WORDS);
        for query in queries {
            for value in query.law.words().into_iter().chain(query.point.into_iter()) {
                input.extend_from_slice(&wire::encode_i64(value));
            }
        }
        let output_words = queries
            .len()
            .checked_mul(wire::EVALUATE_OUTPUT_WORDS)
            .ok_or_else(|| "the transformation-law evaluation output overflowed".to_owned())?;
        let (returned, receipt) = self.launch(
            wire::EVALUATE_ENTRY_SYMBOL,
            "evaluate",
            input,
            output_words,
            queries.len(),
        )?;
        let mut evaluations = Vec::with_capacity(queries.len());
        for row in 0..queries.len() {
            let at = row * wire::EVALUATE_OUTPUT_WORDS;
            if returned[at + wire::EVALUATE_OUTPUT_VERSION] != wire::LAYOUT_VERSION {
                return Err(format!(
                    "the card omitted transformation-law query row {row}"
                ));
            }
            evaluations.push(match returned[at + wire::EVALUATE_OUTPUT_STATUS] {
                wire::STATUS_COMPLETE => BiaffineEvaluation::Value(
                    wire::decode_i64(&returned, at + wire::EVALUATE_OUTPUT_VALUE_AT).ok_or_else(
                        || "the card truncated a transformation-law value".to_owned(),
                    )?,
                ),
                wire::STATUS_OUTSIDE_LATTICE => BiaffineEvaluation::OutsideLattice,
                wire::STATUS_OVERFLOW => BiaffineEvaluation::FiniteCarrierOverflow,
                status => {
                    return Err(format!(
                        "the card refused transformation-law query row {row} with status {status}"
                    ))
                }
            });
        }
        Ok((evaluations, receipt))
    }

    /// Enact complete recurrent passages on the card. Every intermediate standing returns; the
    /// host has no per-event callback and cannot replay or repair the fold.
    pub fn fold(
        &mut self,
        queries: &[RecurrentFoldQuery],
    ) -> Result<(Vec<RecurrentFoldEvaluation>, RecurrentLawCudaReceipt), String> {
        if queries.is_empty() || queries.iter().any(|query| query.currents.is_empty()) {
            return Err("a recurrent fold requires nonempty later currents".to_owned());
        }
        self.context
            .make_current()
            .map_err(|error| error.to_string())?;
        let current_values = queries.iter().try_fold(0usize, |total, query| {
            total
                .checked_add(query.currents.len())
                .ok_or_else(|| "the recurrent-fold current sheet overflowed".to_owned())
        })?;
        let trace_values = queries.iter().try_fold(0usize, |total, query| {
            total
                .checked_add(query.currents.len() + 1)
                .ok_or_else(|| "the recurrent-fold trace sheet overflowed".to_owned())
        })?;
        let mut rows = Vec::with_capacity(queries.len() * wire::FOLD_INPUT_WORDS);
        let mut currents = Vec::with_capacity(current_values * wire::I64_WORDS);
        let mut current_offset = 0usize;
        let mut trace_offset = 0usize;
        for query in queries {
            for value in query.law.words() {
                rows.extend_from_slice(&wire::encode_i64(value));
            }
            rows.extend_from_slice(&wire::encode_i64(query.initial));
            rows.push(
                u32::try_from(current_offset)
                    .map_err(|_| "the recurrent-fold current offset exceeds u32".to_owned())?,
            );
            rows.push(
                u32::try_from(query.currents.len())
                    .map_err(|_| "a recurrent-fold current exceeds u32".to_owned())?,
            );
            rows.push(
                u32::try_from(trace_offset)
                    .map_err(|_| "the recurrent-fold trace offset exceeds u32".to_owned())?,
            );
            for value in &query.currents {
                currents.extend_from_slice(&wire::encode_i64(*value));
            }
            current_offset = current_offset
                .checked_add(query.currents.len())
                .ok_or_else(|| "the recurrent-fold current cursor overflowed".to_owned())?;
            trace_offset = trace_offset
                .checked_add(query.currents.len() + 1)
                .ok_or_else(|| "the recurrent-fold trace cursor overflowed".to_owned())?;
        }
        let output_words = queries
            .len()
            .checked_mul(wire::FOLD_OUTPUT_WORDS)
            .ok_or_else(|| "the recurrent-fold output overflowed".to_owned())?;
        let trace_words = trace_values
            .checked_mul(wire::I64_WORDS)
            .ok_or_else(|| "the recurrent-fold trace output overflowed".to_owned())?;
        let row_device = DeviceBuffer::alloc(rows.len()).map_err(|error| error.to_string())?;
        row_device
            .copy_from_slice(&rows)
            .map_err(|error| error.to_string())?;
        let current_device =
            DeviceBuffer::alloc(currents.len()).map_err(|error| error.to_string())?;
        current_device
            .copy_from_slice(&currents)
            .map_err(|error| error.to_string())?;
        let output_device =
            DeviceBuffer::<u32>::alloc_zeroed(output_words).map_err(|error| error.to_string())?;
        let trace_device =
            DeviceBuffer::<u32>::alloc_zeroed(trace_words).map_err(|error| error.to_string())?;
        self.context
            .synchronize()
            .map_err(|error| error.to_string())?;
        let function = self
            .module
            .function(wire::FOLD_ENTRY_SYMBOL)
            .map_err(|error| error.to_string())?;
        let work = u64::try_from(queries.len())
            .map_err(|_| "the recurrent-fold row population exceeds u64".to_owned())?;
        let launch = function
            .linear_launch(self.census, work)
            .map_err(|error| error.to_string())?;
        let mut row_pointer = row_device.device_ptr();
        let mut row_len = rows.len();
        let mut current_pointer = current_device.device_ptr();
        let mut current_len = currents.len();
        let mut output_pointer = output_device.device_ptr();
        let mut output_len = output_words;
        let mut trace_pointer = trace_device.device_ptr();
        let mut trace_len = trace_words;
        let mut x_stride = launch.x_stride;
        let mut parameters = [
            &mut row_pointer as *mut u64 as *mut c_void,
            &mut row_len as *mut usize as *mut c_void,
            &mut current_pointer as *mut u64 as *mut c_void,
            &mut current_len as *mut usize as *mut c_void,
            &mut output_pointer as *mut u64 as *mut c_void,
            &mut output_len as *mut usize as *mut c_void,
            &mut trace_pointer as *mut u64 as *mut c_void,
            &mut trace_len as *mut usize as *mut c_void,
            &mut x_stride as *mut u32 as *mut c_void,
        ];
        function
            .launch_on(&self.stream, launch.grid, launch.block, &mut parameters)
            .map_err(|error| error.to_string())?;
        self.stream
            .synchronize()
            .map_err(|error| error.to_string())?;
        let mut returned = vec![0u32; output_words];
        output_device
            .copy_to_slice(&mut returned)
            .map_err(|error| error.to_string())?;
        let mut traces = vec![0u32; trace_words];
        trace_device
            .copy_to_slice(&mut traces)
            .map_err(|error| error.to_string())?;
        let mut evaluations = Vec::with_capacity(queries.len());
        for row in 0..queries.len() {
            let at = row * wire::FOLD_OUTPUT_WORDS;
            if returned[at + wire::FOLD_OUTPUT_VERSION] != wire::LAYOUT_VERSION {
                return Err(format!("the card omitted recurrent-fold row {row}"));
            }
            evaluations.push(match returned[at + wire::FOLD_OUTPUT_STATUS] {
                wire::STATUS_COMPLETE => {
                    let offset = returned[at + wire::FOLD_OUTPUT_TRACE_OFFSET] as usize;
                    let extent = returned[at + wire::FOLD_OUTPUT_TRACE_EXTENT] as usize;
                    let end = offset
                        .checked_add(extent)
                        .ok_or_else(|| "the recurrent-fold returned trace overflowed".to_owned())?;
                    if end > trace_values {
                        return Err("the recurrent-fold returned trace left its sheet".to_owned());
                    }
                    let trace = (offset..end)
                        .map(|position| {
                            wire::decode_i64(&traces, position * wire::I64_WORDS).ok_or_else(|| {
                                "the recurrent-fold returned a truncated trace".to_owned()
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let terminus = wire::decode_i64(&returned, at + wire::FOLD_OUTPUT_VALUE_AT)
                        .ok_or_else(|| "the recurrent-fold omitted its terminus".to_owned())?;
                    if trace.last().copied() != Some(terminus) {
                        return Err("the recurrent-fold trace and terminus disagree".to_owned());
                    }
                    RecurrentFoldEvaluation::Complete { trace, terminus }
                }
                wire::STATUS_OUTSIDE_LATTICE => RecurrentFoldEvaluation::OutsideLattice,
                wire::STATUS_OVERFLOW => RecurrentFoldEvaluation::FiniteCarrierOverflow,
                status => {
                    return Err(format!(
                        "the card refused recurrent-fold row {row} with status {status}"
                    ))
                }
            });
        }
        self.launches = self
            .launches
            .checked_add(1)
            .ok_or_else(|| "the recurrent-law launch ordinal overflowed".to_owned())?;
        Ok((
            evaluations,
            RecurrentLawCudaReceipt {
                schema: "soma-life.recurrent-law-cuda-receipt.v1".to_owned(),
                operation: "fold".to_owned(),
                device: self.device_name.clone(),
                rows: queries.len(),
                launch_ordinal: self.launches,
                grid: [launch.grid.x, launch.grid.y, launch.grid.z],
                block: [launch.block.x, launch.block.y, launch.block.z],
                host_semantic_replay: false,
            },
        ))
    }

    fn launch(
        &mut self,
        symbol: &str,
        operation: &str,
        input: Vec<u32>,
        output_words: usize,
        rows: usize,
    ) -> Result<(Vec<u32>, RecurrentLawCudaReceipt), String> {
        self.context
            .make_current()
            .map_err(|error| error.to_string())?;
        let input_device = DeviceBuffer::alloc(input.len()).map_err(|error| error.to_string())?;
        input_device
            .copy_from_slice(&input)
            .map_err(|error| error.to_string())?;
        let output_device =
            DeviceBuffer::<u32>::alloc_zeroed(output_words).map_err(|error| error.to_string())?;
        self.context
            .synchronize()
            .map_err(|error| error.to_string())?;
        let function = self
            .module
            .function(symbol)
            .map_err(|error| error.to_string())?;
        let work = u64::try_from(rows)
            .map_err(|_| "the recurrent-law row population exceeds u64".to_owned())?;
        let launch = function
            .linear_launch(self.census, work)
            .map_err(|error| error.to_string())?;
        let mut input_pointer = input_device.device_ptr();
        let mut input_len = input.len();
        let mut output_pointer = output_device.device_ptr();
        let mut output_len = output_words;
        let mut x_stride = launch.x_stride;
        let mut parameters = [
            &mut input_pointer as *mut u64 as *mut c_void,
            &mut input_len as *mut usize as *mut c_void,
            &mut output_pointer as *mut u64 as *mut c_void,
            &mut output_len as *mut usize as *mut c_void,
            &mut x_stride as *mut u32 as *mut c_void,
        ];
        function
            .launch_on(&self.stream, launch.grid, launch.block, &mut parameters)
            .map_err(|error| error.to_string())?;
        self.stream
            .synchronize()
            .map_err(|error| error.to_string())?;
        let mut returned = vec![0u32; output_words];
        output_device
            .copy_to_slice(&mut returned)
            .map_err(|error| error.to_string())?;
        self.launches = self
            .launches
            .checked_add(1)
            .ok_or_else(|| "the recurrent-law launch ordinal overflowed".to_owned())?;
        Ok((
            returned,
            RecurrentLawCudaReceipt {
                schema: "soma-life.recurrent-law-cuda-receipt.v1".to_owned(),
                operation: operation.to_owned(),
                device: self.device_name.clone(),
                rows,
                launch_ordinal: self.launches,
                grid: [launch.grid.x, launch.grid.y, launch.grid.z],
                block: [launch.block.x, launch.block.y, launch.block.z],
                host_semantic_replay: false,
            },
        ))
    }
}

impl Drop for CudaRecurrentLawExecutor {
    fn drop(&mut self) {
        let _ = self.context.make_current();
    }
}
