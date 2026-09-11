//! Exterior JSONL delivery over one continuing native session. Packet boundaries do not create
//! native occurrences. Output must drain before another request is read or executed.

use crate::{HnaOccurrence, HnaSession};
use holonic_engine::native_ecology::holonic_intelligence::face_of_last_row;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    io::{self, BufRead, Write},
    path::{Path, PathBuf},
};
use thiserror::Error;

pub const HNA_STREAM_REQUEST_SCHEMA: &str = "org.holonics.hna.stream-request.v1";
pub const HNA_STREAM_EVENT_SCHEMA: &str = "org.holonics.hna.stream-event.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaStreamRequest {
    pub schema: String,
    pub command: HnaStreamCommand,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "kebab-case", deny_unknown_fields)]
pub enum HnaStreamCommand {
    ActuateText { text:String },
    ProjectSymbol { #[serde(default)] full_emission:bool },
    EmitSymbol { #[serde(default)] full_emission:bool, #[serde(default)] retain_comparison:bool },
    ObserveSymbol { source:u64, text:String },
    CompareSymbol {source:u64,text:String,#[serde(default)] coefficient_row:Option<usize>},
    ReleaseSymbolComparison {source:u64},
    ReceiveNextSymbol { text:String },
    ReceiveCurrent {
        current: crate::native::CurrentWire,
        #[serde(default)]
        source: Option<u64>,
    },
    Rechart {
        gauges: Vec<crate::native::CurrentWire>,
    },
    ReplaceIncidence {
        node: usize,
        transport: crate::native::CurrentWire,
    },
    InspectRelation,
    Advance {
        occurrence: HnaOccurrence,
        #[serde(default)]
        full_emission: bool,
    },
    /// Explicit native material domain; the original inherited-family command is unchanged.
    AdvanceNative {
        occurrence: HnaOccurrence,
        #[serde(default)]
        full_emission: bool,
    },
    Inspect,
    Checkpoint {
        path: PathBuf,
    },
    SupplyInputMaterial {
        path: PathBuf,
    },
    Close,
}

/// Durable transport state, separate from the native ecology. A pending output is a result
/// already obtained, never an instruction to repeat its native operation after a write failure.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaStreamState {
    pub sequence: u64,
    pub input: Vec<u8>,
    pub input_complete: bool,
    pub output: Option<Vec<u8>>,
    /// Bytes accepted by this Writer, not proof of delivery to an exterior peer.
    pub output_accepted: usize,
    pub closed: bool,
}

impl HnaStreamState {
    pub fn validate(&self) -> Result<(), HnaStreamError> {
        if self.output_accepted > self.output.as_ref().map_or(0, Vec::len) {
            return Err(HnaStreamError::State(
                "output cursor exceeds retained frame",
            ));
        }
        if self.input_complete && self.input.is_empty() {
            return Err(HnaStreamError::State("empty completed input frame"));
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
pub enum HnaStreamError {
    #[error("stream input failed; partial input remains owned: {0}")]
    Input(io::Error),
    #[error("stream output failed; do not repeat the native request: {0}")]
    Output(io::Error),
    #[error("stream input frame is incomplete; its bytes remain owned")]
    IncompleteInput,
    #[error("stream input frame is malformed; its bytes remain owned: {0}")]
    Malformed(String),
    #[error("invalid stream state: {0}")]
    State(&'static str),
    #[error("stream encoding: {0}")]
    Encoding(#[from] serde_json::Error),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HnaStreamDisposition {
    InputExhausted,
    Closed,
}

pub struct HnaStream {
    state: HnaStreamState,
}

impl HnaStream {
    pub fn from_state(state: HnaStreamState) -> Result<Self, HnaStreamError> {
        state.validate()?;
        Ok(Self { state })
    }
    pub fn new() -> Self {
        Self {
            state: HnaStreamState::default(),
        }
    }
    pub fn state(&self) -> &HnaStreamState {
        &self.state
    }

    /// An explicit new connection replays a retained response from its beginning, with the same
    /// event sequence. Its old peer may already have received a prefix or the complete event;
    /// deduplication/acknowledgment is the exterior peer's job. No native operation repeats.
    pub fn open_new_connection(&mut self) {
        self.state.output_accepted = 0;
        self.state.closed = false;
    }

    /// Explicit transfer of a rejected/incomplete frame to its operator; never silently drop it.
    pub fn take_input(&mut self) -> Vec<u8> {
        self.state.input_complete = false;
        std::mem::take(&mut self.state.input)
    }

    pub fn pump(
        &mut self,
        session: &mut HnaSession<'_, '_>,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<HnaStreamDisposition, HnaStreamError> {
        self.pump_target(session, input, output)
    }

    pub fn pump_native(
        &mut self,
        session: &mut crate::native::NativeSession<'_>,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<HnaStreamDisposition, HnaStreamError> {
        self.pump_target(session, input, output)
    }

    pub fn pump_wave(&mut self,session:&mut crate::native::NativeWaveSession<'_>,
        input:&mut impl BufRead,output:&mut impl Write)->Result<HnaStreamDisposition,HnaStreamError> {
        self.pump_target(session,input,output)
    }

    pub fn pump_coupled_wave(&mut self,session:&mut crate::native::NativeCoupledWaveSession<'_>,input:&mut impl BufRead,output:&mut impl Write)->Result<HnaStreamDisposition,HnaStreamError>{self.pump_target(session,input,output)}

    fn emit(&mut self, event: &str, value: Value) -> Result<(), HnaStreamError> {
        let mut bytes = serde_json::to_vec(&json!({"schema":HNA_STREAM_EVENT_SCHEMA,
            "sequence":self.state.sequence,"event":event,"value":value}))?;
        bytes.push(b'\n');
        self.state.output = Some(bytes);
        self.state.output_accepted = 0;
        Ok(())
    }

    fn drain(&mut self, output: &mut impl Write) -> Result<(), HnaStreamError> {
        if let Some(frame) = &self.state.output {
            while self.state.output_accepted < frame.len() {
                match output.write(&frame[self.state.output_accepted..]) {
                    Ok(0) => {
                        return Err(HnaStreamError::Output(io::Error::new(
                            io::ErrorKind::WriteZero,
                            "writer accepted no bytes",
                        )))
                    }
                    Ok(n) => self.state.output_accepted += n,
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(HnaStreamError::Output(error)),
                }
            }
            output.flush().map_err(HnaStreamError::Output)?;
            self.state.output = None;
            self.state.output_accepted = 0;
        }
        Ok(())
    }

    /// Drain an already-produced frame without reading or executing any request. This is the
    /// same delivery boundary used by the session pumps, also available to other native clients.
    pub fn drain_pending(&mut self, output: &mut impl Write) -> Result<(), HnaStreamError> {
        self.state.validate()?;
        self.drain(output)
    }

    fn pump_target(
        &mut self,
        target: &mut impl StreamTarget,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<HnaStreamDisposition, HnaStreamError> {
        self.state.validate()?;
        loop {
            self.drain(output)?;
            if self.state.closed {
                return Ok(HnaStreamDisposition::Closed);
            }
            // read_until appends partial bytes before reporting an error. Preserve those bytes
            // and append the next fragment on a later pump call rather than inventing an event.
            let read = if self.state.input_complete {
                0
            } else {
                match input.read_until(b'\n', &mut self.state.input) {
                    Ok(n) => n,
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(HnaStreamError::Input(error)),
                }
            };
            self.state.input_complete |= self.state.input.ends_with(b"\n");
            if read == 0 && self.state.input.is_empty() {
                return Ok(HnaStreamDisposition::InputExhausted);
            }
            if self.state.input.iter().all(u8::is_ascii_whitespace) {
                self.state.input.clear();
                self.state.input_complete = false;
                if read == 0 {
                    return Ok(HnaStreamDisposition::InputExhausted);
                }
                continue;
            }
            let request: HnaStreamRequest = match serde_json::from_slice(&self.state.input) {
                Ok(request) => request,
                Err(error) if error.is_eof() && !self.state.input.ends_with(b"\n") => {
                    return Err(HnaStreamError::IncompleteInput)
                }
                Err(error) => {
                    self.state.input_complete = true;
                    return Err(HnaStreamError::Malformed(error.to_string()));
                }
            };
            self.state.input_complete = true;
            if request.schema != HNA_STREAM_REQUEST_SCHEMA {
                return Err(HnaStreamError::Malformed("request schema/version".into()));
            }
            self.state.sequence = self
                .state
                .sequence
                .checked_add(1)
                .ok_or(HnaStreamError::State("sequence exhausted"))?;
            self.state.input.clear();
            self.state.input_complete = false;
            match request.command {
                HnaStreamCommand::CompareSymbol{source,text,coefficient_row}=>match target.compare_symbol(source,&text,coefficient_row){
                    Ok(value)=>self.emit("symbol-comparison",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::ReleaseSymbolComparison{source}=>match target.release_symbol_comparison(source){
                    Ok(value)=>self.emit("symbol-comparison-released",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::ReceiveNextSymbol{text}=>match target.receive_next_symbol(&text){
                    Ok(value)=>self.emit("next-symbol-received",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::ProjectSymbol{full_emission}=>match target.project_symbol(full_emission){
                    Ok(value)=>self.emit("symbol-projection",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::ActuateText {text}=>match target.actuate_text(&text) {
                    Ok(value)=>self.emit("source-actuated",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::EmitSymbol {full_emission,retain_comparison}=>match target.emit_symbol(full_emission,retain_comparison) {
                    Ok(value)=>self.emit("symbol-emitted",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::ObserveSymbol {source,text}=>match target.observe_symbol(source,&text) {
                    Ok(value)=>self.emit("prediction-received",value)?,
                    Err(error)=>self.emit("refused",json!({"error":error,"anatomy":target.inspect()}))?,
                },
                HnaStreamCommand::ReceiveCurrent { current, source } => {
                    match target.receive_current(&current, source) {
                        Ok(value) => self.emit("current-received", value)?,
                        Err(error) => {
                            self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                        }
                    }
                }
                HnaStreamCommand::Rechart { gauges } => match target.rechart(&gauges) {
                    Ok(value) => self.emit("recharted", value)?,
                    Err(error) => {
                        self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                    }
                },
                HnaStreamCommand::ReplaceIncidence { node, transport } => {
                    match target.replace_incidence(node, &transport) {
                        Ok(value) => self.emit("incidence-replaced", value)?,
                        Err(error) => {
                            self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                        }
                    }
                }
                HnaStreamCommand::InspectRelation => match target.inspect_relation() {
                    Ok(value) => self.emit("relation", value)?,
                    Err(error) => {
                        self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                    }
                },
                HnaStreamCommand::Advance {
                    occurrence,
                    full_emission,
                } => match target.advance(&occurrence, full_emission) {
                    Ok(value) => self.emit("advanced", value)?,
                    Err(error) => {
                        self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                    }
                },
                HnaStreamCommand::Inspect => self.emit("state", target.inspect())?,
                HnaStreamCommand::SupplyInputMaterial { path } => {
                    match target.supply_input_material(&path) {
                        Ok(()) => self.emit(
                            "input-material-supplied",
                            json!({"path":path,"anatomy":target.inspect()}),
                        )?,
                        Err(error) => {
                            self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                        }
                    }
                }
                HnaStreamCommand::AdvanceNative {
                    occurrence,
                    full_emission,
                } => match target.advance_native(&occurrence, full_emission) {
                    Ok(value) => self.emit("native-advanced", value)?,
                    Err(error) => {
                        self.emit("refused", json!({"error":error,"anatomy":target.inspect()}))?
                    }
                },
                HnaStreamCommand::Checkpoint { path } => {
                    // The artifact contains this pending reply. Restoring it can deliver the
                    // publication result without repeating any earlier native operation.
                    self.emit(
                        "checkpoint-published",
                        json!({"path":path,"anatomy":target.inspect()}),
                    )?;
                    if let Err(error) = target.checkpoint(&path, &self.state) {
                        self.emit(
                            "checkpoint-refused-or-unconfirmed",
                            json!({"path":path,"error":error,"anatomy":target.inspect()}),
                        )?;
                    }
                }
                HnaStreamCommand::Close => {
                    self.state.closed = true;
                    self.emit("connection-closed", target.inspect())?;
                }
            }
        }
    }
}

impl Default for HnaStream {
    fn default() -> Self {
        Self::new()
    }
}

/// Only an exterior effect seam for I/O tests. Native current and learning are never callbacks
/// supplied through the public stream protocol; actual adapters use HnaSession or NativeSession.
trait StreamTarget {
    fn compare_symbol(&self,_:u64,_:&str,_:Option<usize>)->Result<Value,String>{Err("joint producing-family comparison unsupported by this model".into())}
    fn release_symbol_comparison(&mut self,_:u64)->Result<Value,String>{Err("coupled comparison release unsupported by this model".into())}
    fn receive_next_symbol(&mut self,_:&str)->Result<Value,String>{Err("actual next-symbol receiver unsupported by this model".into())}
    fn project_symbol(&self,_:bool)->Result<Value,String>{Err("projected family receiver unsupported by this model".into())}
    fn actuate_text(&mut self,_:&str)->Result<Value,String>{Err("text source chart unsupported by this model".into())}
    fn emit_symbol(&mut self,_:bool,_:bool)->Result<Value,String>{Err("symbol receiver unsupported by this model".into())}
    fn observe_symbol(&mut self,_:u64,_:&str)->Result<Value,String>{Err("symbol observation chart unsupported by this model".into())}
    fn receive_current(
        &mut self,
        _: &crate::native::CurrentWire,
        _: Option<u64>,
    ) -> Result<Value, String> {
        Err("current reception is not supported by this model kind".into())
    }
    fn rechart(&mut self, _: &[crate::native::CurrentWire]) -> Result<Value, String> {
        Err("live phase recharting is not supported by this model kind".into())
    }
    fn replace_incidence(
        &mut self,
        _: usize,
        _: &crate::native::CurrentWire,
    ) -> Result<Value, String> {
        Err("phase incidence replacement is not supported by this model kind".into())
    }
    fn inspect_relation(&self) -> Result<Value, String> {
        Err("local relation inspection is not supported by this model kind".into())
    }
    fn advance(&mut self, occurrence: &HnaOccurrence, full: bool) -> Result<Value, String>;
    fn advance_native(&mut self, occurrence: &HnaOccurrence, full: bool) -> Result<Value, String>;
    fn inspect(&self) -> Value;
    fn checkpoint(&self, path: &Path, transport: &HnaStreamState) -> Result<(), String>;
    fn supply_input_material(&mut self, path: &Path) -> Result<(), String>;
}

impl StreamTarget for crate::native::NativeSession<'_> {
    fn receive_current(
        &mut self,
        current: &crate::native::CurrentWire,
        source: Option<u64>,
    ) -> Result<Value, String> {
        self.receive(current, source)
            .map(|v| json!(v))
            .map_err(|e| e.to_string())
    }
    fn rechart(&mut self, gauges: &[crate::native::CurrentWire]) -> Result<Value, String> {
        crate::native::NativeSession::rechart(self, gauges)
            .map(|v| json!(v))
            .map_err(|e| e.to_string())
    }
    fn replace_incidence(
        &mut self,
        node: usize,
        transport: &crate::native::CurrentWire,
    ) -> Result<Value, String> {
        crate::native::NativeSession::replace_incidence(self, node, transport)
            .map(|_| json!(self.inspect()))
            .map_err(|e| e.to_string())
    }
    fn inspect_relation(&self) -> Result<Value, String> {
        self.relation_snapshot()
            .map(|v| json!(v))
            .map_err(|e| e.to_string())
    }
    fn inspect(&self) -> Value {
        json!(crate::native::NativeSession::inspect(self))
    }
    fn advance(&mut self, _: &HnaOccurrence, _: bool) -> Result<Value, String> {
        Err("address/token occurrences do not define native phase currents".into())
    }
    fn advance_native(&mut self, _: &HnaOccurrence, _: bool) -> Result<Value, String> {
        Err("address/token occurrences do not define native phase currents".into())
    }
    fn checkpoint(&self, path: &Path, transport: &HnaStreamState) -> Result<(), String> {
        self.checkpoint_stream(path, transport)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
    fn supply_input_material(&mut self, _: &Path) -> Result<(), String> {
        Err("inherited lookup rows do not define native phase material".into())
    }
}

impl StreamTarget for HnaSession<'_, '_> {
    fn supply_input_material(&mut self, path: &Path) -> Result<(), String> {
        HnaSession::supply_input_material(self, path).map_err(|error| error.to_string())
    }
    fn advance(&mut self, occurrence: &HnaOccurrence, full: bool) -> Result<Value, String> {
        let cycle = HnaSession::advance(self, occurrence).map_err(|e| e.to_string())?;
        Ok(cycle_value(cycle, full, self.anatomy()))
    }
    fn advance_native(&mut self, occurrence: &HnaOccurrence, full: bool) -> Result<Value, String> {
        let cycle = HnaSession::advance_native(self, occurrence).map_err(|e| e.to_string())?;
        let mut value = cycle_value(cycle.output, full, self.anatomy());
        value["admission"] = json!(cycle.admission);
        Ok(value)
    }
    fn inspect(&self) -> Value {
        json!(self.anatomy())
    }
    fn checkpoint(&self, path: &Path, transport: &HnaStreamState) -> Result<(), String> {
        self.checkpoint_stream(path, transport)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

fn cycle_value(
    cycle: holonic_engine::native_ecology::holonic_intelligence::NativeFullCycleOutput,
    full: bool,
    anatomy: crate::HnaSessionAnatomy,
) -> Value {
    let face = face_of_last_row(
        &cycle.final_emission.intervals,
        cycle.final_emission.rows,
        cycle.final_emission.width,
    );
    let mut emission = cycle.final_emission;
    if !full {
        emission.intervals.clear();
    }
    json!({"emission":emission,"selected_face":face,"full_intervals":full,
            "local_returns":cycle.passage_returns,"anatomy":anatomy})
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        cell::RefCell,
        io::{BufReader, Cursor, Read},
    };

    #[derive(Default)]
    struct Target {
        advances: usize,
        saved: RefCell<Option<HnaStreamState>>,
    }
    impl StreamTarget for Target {
        fn supply_input_material(&mut self, _: &Path) -> Result<(), String> {
            Ok(())
        }
        fn advance_native(
            &mut self,
            occurrence: &HnaOccurrence,
            full: bool,
        ) -> Result<Value, String> {
            self.advance(occurrence, full)
        }
        fn advance(&mut self, _: &HnaOccurrence, _: bool) -> Result<Value, String> {
            self.advances += 1;
            Ok(json!({"effects":self.advances}))
        }
        fn inspect(&self) -> Value {
            json!({"effects":self.advances})
        }
        fn checkpoint(&self, _: &Path, state: &HnaStreamState) -> Result<(), String> {
            *self.saved.borrow_mut() = Some(state.clone());
            Ok(())
        }
    }
    fn request(command: HnaStreamCommand) -> Vec<u8> {
        let mut bytes = serde_json::to_vec(&HnaStreamRequest {
            schema: HNA_STREAM_REQUEST_SCHEMA.into(),
            command,
        })
        .unwrap();
        bytes.push(b'\n');
        bytes
    }
    fn advance() -> Vec<u8> {
        request(HnaStreamCommand::Advance {
            occurrence: HnaOccurrence {
                row_addresses: vec![1, 2],
                history: vec![],
            },
            full_emission: false,
        })
    }

    #[test]
    fn native_domain_is_an_explicit_stream_request_and_event() {
        let bytes = request(HnaStreamCommand::AdvanceNative {
            occurrence: HnaOccurrence {
                row_addresses: vec![4, 9],
                history: vec![],
            },
            full_emission: false,
        });
        let mut stream = HnaStream::new();
        let mut target = Target::default();
        let mut output = Vec::new();
        assert_eq!(
            stream
                .pump_target(&mut target, &mut Cursor::new(bytes), &mut output)
                .unwrap(),
            HnaStreamDisposition::InputExhausted
        );
        let event: Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(event["event"], "native-advanced");
        assert_eq!(target.advances, 1);
    }

    #[test]
    fn supplied_material_is_receipted_without_manufacturing_a_native_occurrence() {
        let bytes = request(HnaStreamCommand::SupplyInputMaterial {
            path: PathBuf::from("input.safetensors"),
        });
        let mut stream = HnaStream::new();
        let mut target = Target::default();
        let mut output = Vec::new();
        stream
            .pump_target(&mut target, &mut Cursor::new(bytes), &mut output)
            .unwrap();
        assert_eq!(target.advances, 0);
        let event: Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(event["event"], "input-material-supplied");
    }

    struct PartialInput {
        bytes: Vec<u8>,
        at: usize,
    }
    impl Read for PartialInput {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            let bytes = self.fill_buf()?;
            let n = bytes.len().min(out.len());
            out[..n].copy_from_slice(&bytes[..n]);
            self.consume(n);
            Ok(n)
        }
    }
    impl BufRead for PartialInput {
        fn fill_buf(&mut self) -> io::Result<&[u8]> {
            if self.at == self.bytes.len() {
                Err(io::Error::other("input fault"))
            } else {
                Ok(&self.bytes[self.at..])
            }
        }
        fn consume(&mut self, n: usize) {
            self.at += n;
        }
    }
    struct PartialOutput {
        bytes: Vec<u8>,
        limit: usize,
        fail_flush: bool,
    }
    impl Write for PartialOutput {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if self.bytes.len() >= self.limit {
                return Err(io::Error::new(io::ErrorKind::BrokenPipe, "output fault"));
            }
            let n = bytes.len().min(self.limit - self.bytes.len()).min(3);
            self.bytes.extend_from_slice(&bytes[..n]);
            Ok(n)
        }
        fn flush(&mut self) -> io::Result<()> {
            if self.fail_flush {
                Err(io::Error::other("flush fault"))
            } else {
                Ok(())
            }
        }
    }

    #[test]
    fn fragmented_input_retains_one_occurrence_until_its_whole_frame_arrives() {
        let bytes = advance();
        let cut = 17;
        let mut stream = HnaStream::new();
        let mut target = Target::default();
        let mut out = Vec::new();
        let mut first = PartialInput {
            bytes: bytes[..cut].to_vec(),
            at: 0,
        };
        assert!(matches!(
            stream.pump_target(&mut target, &mut first, &mut out),
            Err(HnaStreamError::Input(_))
        ));
        assert_eq!(target.advances, 0);
        assert_eq!(stream.state.input, bytes[..cut]);
        let state = serde_json::from_slice(&serde_json::to_vec(stream.state()).unwrap()).unwrap();
        let mut resumed = HnaStream::from_state(state).unwrap();
        let mut tail = BufReader::with_capacity(1, Cursor::new(&bytes[cut..]));
        assert_eq!(
            resumed
                .pump_target(&mut target, &mut tail, &mut out)
                .unwrap(),
            HnaStreamDisposition::InputExhausted
        );
        assert_eq!(target.advances, 1);
        assert_eq!(resumed.state.sequence, 1);
    }

    #[test]
    fn output_backpressure_prevents_reading_or_executing_the_next_request() {
        let first = advance();
        let all = [first.clone(), advance()].concat();
        let mut input = Cursor::new(all);
        let mut target = Target::default();
        let mut stream = HnaStream::new();
        let mut output = PartialOutput {
            bytes: Vec::new(),
            limit: 7,
            fail_flush: false,
        };
        assert!(matches!(
            stream.pump_target(&mut target, &mut input, &mut output),
            Err(HnaStreamError::Output(_))
        ));
        assert_eq!(target.advances, 1);
        assert_eq!(input.position(), first.len() as u64);
        assert_eq!(stream.state.output_accepted, 7);
        output.limit = usize::MAX;
        stream
            .pump_target(&mut target, &mut input, &mut output)
            .unwrap();
        assert_eq!(target.advances, 2);
        assert_eq!(
            output
                .bytes
                .split(|b| *b == b'\n')
                .filter(|b| !b.is_empty())
                .count(),
            2
        );
    }

    #[test]
    fn flush_failure_and_new_connection_replay_do_not_repeat_the_effect() {
        let mut input = Cursor::new(advance());
        let mut target = Target::default();
        let mut stream = HnaStream::new();
        let mut output = PartialOutput {
            bytes: Vec::new(),
            limit: usize::MAX,
            fail_flush: true,
        };
        assert!(stream
            .pump_target(&mut target, &mut input, &mut output)
            .is_err());
        let full = output.bytes.clone();
        assert_eq!(target.advances, 1);
        let mut resumed = HnaStream::from_state(stream.state.clone()).unwrap();
        resumed.open_new_connection();
        let mut delivered = Vec::new();
        resumed
            .pump_target(&mut target, &mut Cursor::new([]), &mut delivered)
            .unwrap();
        assert_eq!(target.advances, 1);
        assert_eq!(delivered, full);
    }

    #[test]
    fn checkpoint_retains_its_pending_reply_and_close_is_a_transport_boundary() {
        let mut target = Target::default();
        let mut stream = HnaStream::new();
        let bytes = [
            request(HnaStreamCommand::Checkpoint {
                path: "saved.hna".into(),
            }),
            request(HnaStreamCommand::Close),
            advance(),
        ]
        .concat();
        let mut input = Cursor::new(bytes);
        let mut output = Vec::new();
        assert_eq!(
            stream
                .pump_target(&mut target, &mut input, &mut output)
                .unwrap(),
            HnaStreamDisposition::Closed
        );
        assert_eq!(target.advances, 0);
        let saved = target.saved.borrow();
        let saved = saved.as_ref().unwrap();
        assert_eq!(saved.sequence, 1);
        assert!(saved.output.is_some());
        assert_eq!(saved.output_accepted, 0);
    }

    #[test]
    fn incomplete_and_malformed_frames_remain_owned_without_effects() {
        let mut target = Target::default();
        let mut stream = HnaStream::new();
        let mut output = Vec::new();
        let partial = b"{\"schema\":";
        assert!(matches!(
            stream.pump_target(&mut target, &mut Cursor::new(partial), &mut output),
            Err(HnaStreamError::IncompleteInput)
        ));
        assert_eq!(stream.take_input(), partial);
        assert_eq!(target.advances, 0);
        assert!(matches!(
            stream.pump_target(&mut target, &mut Cursor::new(b"{\n"), &mut output),
            Err(HnaStreamError::Malformed(_))
        ));
        assert_eq!(stream.state.input, b"{\n");
        assert_eq!(target.advances, 0);
        let mut next = Cursor::new(advance());
        assert!(matches!(
            stream.pump_target(&mut target, &mut next, &mut output),
            Err(HnaStreamError::Malformed(_))
        ));
        assert_eq!(
            next.position(),
            0,
            "a malformed completed frame requires explicit disposition, not implicit concatenation"
        );
    }
}

impl StreamTarget for crate::native::NativeWaveSession<'_> {
    fn actuate_text(&mut self,text:&str)->Result<Value,String>{self.actuate_text(text).map_err(|e|e.to_string())}
    fn emit_symbol(&mut self,full:bool,retain:bool)->Result<Value,String>{
        (if retain {self.predict_symbol(full)} else {self.next_symbol(full)}).map_err(|e|e.to_string())
    }
    fn observe_symbol(&mut self,source:u64,text:&str)->Result<Value,String>{self.receive_symbol(source,text).map_err(|e|e.to_string())}
    fn advance(&mut self,_:&HnaOccurrence,_:bool)->Result<Value,String>{Err("use the wave's declared source/receiver commands".into())}
    fn advance_native(&mut self,_:&HnaOccurrence,_:bool)->Result<Value,String>{Err("use the wave's declared source/receiver commands".into())}
    fn inspect(&self)->Value{crate::native::NativeWaveSession::inspect(self)}
    fn checkpoint(&self,path:&Path,transport:&HnaStreamState)->Result<(),String>{self.checkpoint_stream(path,transport).map(|_|()).map_err(|e|e.to_string())}
    fn supply_input_material(&mut self,_:&Path)->Result<(),String>{Err("a file path is not a native wave source conversion".into())}
}

impl StreamTarget for crate::native::NativeCoupledWaveSession<'_>{
    fn compare_symbol(&self,id:u64,text:&str,row:Option<usize>)->Result<Value,String>{self.compare_symbol(id,text,row).map_err(|e|e.to_string())}
    fn release_symbol_comparison(&mut self,id:u64)->Result<Value,String>{self.release_symbol_comparison(id).map_err(|e|e.to_string())}
    fn receive_next_symbol(&mut self,text:&str)->Result<Value,String>{self.receive_next_symbol(text).map_err(|e|e.to_string())}
    fn inspect_relation(&self)->Result<Value,String>{self.inspect_relation().map_err(|e|e.to_string())}
    fn project_symbol(&self,full:bool)->Result<Value,String>{self.project_current(full).map_err(|e|e.to_string())}
    fn actuate_text(&mut self,text:&str)->Result<Value,String>{self.actuate_text(text).map_err(|e|e.to_string())}
    fn emit_symbol(&mut self,full:bool,retain:bool)->Result<Value,String>{
        if retain{self.predict_symbol(full)}else{self.next_symbol(full)}.map_err(|e|e.to_string())
    }
    fn observe_symbol(&mut self,_:u64,_:&str)->Result<Value,String>{Err("joint comparison is available through compare-symbol; its material-development return is not yet bound".into())}
    fn advance(&mut self,_:&HnaOccurrence,_:bool)->Result<Value,String>{Err("use the coupled wave's declared source/receiver commands".into())}
    fn advance_native(&mut self,_:&HnaOccurrence,_:bool)->Result<Value,String>{Err("use the coupled wave's declared source/receiver commands".into())}
    fn inspect(&self)->Value{crate::native::NativeCoupledWaveSession::inspect(self)}
    fn checkpoint(&self,path:&Path,transport:&HnaStreamState)->Result<(),String>{self.checkpoint_stream(path,transport).map(|_|()).map_err(|e|e.to_string())}
    fn supply_input_material(&mut self,_:&Path)->Result<(),String>{Err("a file path is not a coupled wave source conversion".into())}
}
