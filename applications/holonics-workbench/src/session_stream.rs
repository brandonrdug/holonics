//! The process boundary for the continuing HNA stream. It deliberately bypasses the batch
//! Workbench response collector so responses are flushed while the native owner remains live.
use crate::HnaCommand;
use holonics_hna::{
    native::{
        with_native_session, NativeModelSpec, NativeSavedSession, NativeSessionAnatomy,
        with_mathematical_session, NativeSessionError, NativeWaveSavedSession, NativeCoupledWaveSavedSession,
        with_field_session, FieldSessionSpec, NativeFieldSavedSession, NativeFieldSession,
    },
    HnaStream,
    HnaStreamDisposition,
};
use serde::Serialize;
use std::{
    fs::{self, File},
    io::{self, BufRead, BufReader},
    path::PathBuf,
};

#[derive(Debug, Serialize)]
pub struct NativeHnaStreamProcessReceipt {
    pub schema: &'static str,
    pub disposition: Option<HnaStreamDisposition>,
    pub stream_error: Option<String>,
    pub transport_sequence: u64,
    pub anatomy: NativeSessionAnatomy,
    pub checkpoint: PathBuf,
    pub checkpoint_octets: Option<u64>,
    pub checkpoint_error: Option<String>,
    pub persistent: bool,
}

#[derive(Debug, Serialize)]
pub struct MathematicalHnaStreamProcessReceipt {
    pub schema: &'static str,
    pub disposition: Option<HnaStreamDisposition>,
    pub stream_error: Option<String>,
    pub transport_sequence: u64,
    pub inspect: serde_json::Value,
    /// Input opening, native setup, JSONL processing/egress and native teardown. Excludes the
    /// CLI parser and writing this final receipt. Per-request timings are nested within this.
    pub elapsed_microseconds: u128,
}

#[derive(Debug, Serialize)]
pub struct FieldHnaStreamProcessReceipt {
    pub schema: &'static str,
    pub disposition: Option<HnaStreamDisposition>,
    pub stream_error: Option<String>,
    pub checkpoint: PathBuf,
    pub checkpoint_octets: Option<u64>,
    pub checkpoint_error: Option<String>,
    pub transport_sequence: u64,
    pub inspect: serde_json::Value,
}

pub fn run_field_session_stream(command: HnaCommand) -> Result<FieldHnaStreamProcessReceipt, NativeSessionError> {
    let HnaCommand::FieldSession { source, resume, input, checkpoint } = command else {
        return Err(NativeSessionError::Application("expected a field streaming session command".into()));
    };
    if checkpoint.exists() { return Err(NativeSessionError::Application(format!("field checkpoint already exists: {:?}", checkpoint))); }
    if let Some(parent) = checkpoint.parent().filter(|p| !p.as_os_str().is_empty()) { fs::create_dir_all(parent).map_err(|e| NativeSessionError::Application(format!("cannot create field checkpoint directory {:?}: {e}", parent)))?; }
    let mut input: Box<dyn BufRead> = if input.as_os_str() == "-" { Box::new(io::stdin().lock()) } else { Box::new(BufReader::new(File::open(&input).map_err(|e| NativeSessionError::Application(format!("cannot read field input {:?}: {e}", input)))?)) };
    let mut output = io::stdout().lock();
    fn finish(session: &NativeFieldSession<'_>, stream: &HnaStream, pump: Result<HnaStreamDisposition, holonics_hna::HnaStreamError>, checkpoint: &PathBuf) -> FieldHnaStreamProcessReceipt {
        let (disposition, stream_error) = match pump { Ok(v) => (Some(v), None), Err(e) => (None, Some(e.to_string())) };
        let saved = session.checkpoint(checkpoint, stream.state());
        let (checkpoint_octets, checkpoint_error) = match saved { Ok(r) => (Some(r.bytes), None), Err(e) => (None, Some(e.to_string())) };
        FieldHnaStreamProcessReceipt { schema: "org.holonics.hna.field-stream-process.v1", disposition, stream_error, checkpoint: checkpoint.clone(), checkpoint_octets, checkpoint_error, transport_sequence: stream.state().sequence, inspect: session.inspect() }
    }
    if resume {
        return NativeFieldSavedSession::open(&source)?.with_session(|session, stream| { stream.open_new_connection(); let pump = stream.pump_field(session, &mut input, &mut output); Ok(finish(session, stream, pump, &checkpoint)) });
    }
    let bytes = fs::read(&source).map_err(|e| NativeSessionError::Application(format!("cannot read field source {:?}: {e}", source)))?;
    let spec: FieldSessionSpec = serde_json::from_slice(&bytes)?;
    with_field_session(&spec, |session| { let mut stream = HnaStream::new(); stream.open_new_connection(); let pump = stream.pump_field(session, &mut input, &mut output); Ok(finish(session, &stream, pump, &checkpoint)) })
}

pub fn run_mathematical_session_stream(
    command: HnaCommand,
) -> Result<MathematicalHnaStreamProcessReceipt, NativeSessionError> {
    let HnaCommand::MathematicalSession { input } = command else {
        return Err(NativeSessionError::Application(
            "expected a mathematical streaming session command".into(),
        ));
    };
    let start = std::time::Instant::now();
    let mut input: Box<dyn BufRead> = if input.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(BufReader::new(File::open(&input).map_err(|error| {
            NativeSessionError::Application(format!("cannot read mathematical input {:?}: {error}", input))
        })?))
    };
    let mut output = io::stdout().lock();
    let mut receipt = with_mathematical_session(|session| {
        let mut stream = HnaStream::new();
        stream.open_new_connection();
        let pump = stream.pump_mathematical(session, &mut input, &mut output);
        let (disposition, stream_error) = match pump {
            Ok(disposition) => (Some(disposition), None),
            Err(error) => (None, Some(error.to_string())),
        };
        Ok(MathematicalHnaStreamProcessReceipt {
            schema: "org.holonics.hna.mathematical-stream-process.v1",
            disposition,
            stream_error,
            transport_sequence: stream.state().sequence,
            inspect: session.inspect(),
            elapsed_microseconds: 0,
        })
    })?;
    receipt.elapsed_microseconds = start.elapsed().as_micros();
    Ok(receipt)
}

#[derive(Debug, Serialize)]
pub struct WaveHnaStreamProcessReceipt {
    pub schema: &'static str,
    pub disposition: Option<HnaStreamDisposition>,
    pub stream_error: Option<String>,
    pub checkpoint: PathBuf,
    pub checkpoint_octets: Option<u64>,
    pub checkpoint_error: Option<String>,
    pub transport_sequence: u64,
    pub epochs: WaveEpochReceipt,
    pub inspect: serde_json::Value,
}

#[derive(Debug, Serialize)]
pub struct WaveEpochReceipt {
    pub before: u64,
    pub after: u64,
}

pub fn run_native_session_stream(
    command: HnaCommand,
) -> Result<NativeHnaStreamProcessReceipt, NativeSessionError> {
    let HnaCommand::NativeSession {
        source,
        resume,
        input,
        checkpoint,
    } = command
    else {
        return Err(NativeSessionError::Application(
            "expected a native streaming session command".into(),
        ));
    };
    if checkpoint.exists() {
        return Err(NativeSessionError::Application(format!(
            "native checkpoint already exists: {:?}",
            checkpoint
        )));
    }
    if let Some(parent) = checkpoint.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|error| {
            NativeSessionError::Application(format!(
                "cannot create native checkpoint directory {:?}: {error}",
                parent
            ))
        })?;
    }
    let mut input: Box<dyn BufRead> = if input.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(BufReader::new(File::open(&input).map_err(|error| {
            NativeSessionError::Application(format!(
                "cannot read native input {:?}: {error}",
                input
            ))
        })?))
    };
    let mut output = io::stdout().lock();

    fn finish_native_stream(
        session: &mut holonics_hna::native::NativeSession<'_>,
        stream: &HnaStream,
        pump: Result<HnaStreamDisposition, holonics_hna::HnaStreamError>,
        checkpoint: &PathBuf,
    ) -> NativeHnaStreamProcessReceipt {
        let (disposition, stream_error) = match pump {
            Ok(disposition) => (Some(disposition), None),
            Err(error) => (None, Some(error.to_string())),
        };
        let publication = session.checkpoint_stream(checkpoint, stream.state());
        let (checkpoint_octets, checkpoint_error, persistent) = match publication {
            Ok(receipt) => (Some(receipt.bytes), None, true),
            Err(error) => (None, Some(error.to_string()), false),
        };
        NativeHnaStreamProcessReceipt {
            schema: "org.holonics.hna.native-stream-process.v2",
            disposition,
            stream_error,
            transport_sequence: stream.state().sequence,
            anatomy: session.inspect(),
            checkpoint: checkpoint.clone(),
            checkpoint_octets,
            checkpoint_error,
            persistent,
        }
    }

    if resume {
        let saved = NativeSavedSession::read(&source)?;
        return saved.with_session(|session, stream| {
            stream.open_new_connection();
            let pump = stream.pump_native(session, &mut input, &mut output);
            Ok(finish_native_stream(session, stream, pump, &checkpoint))
        });
    }

    let seed = fs::read(&source).map_err(|error| {
        NativeSessionError::Application(format!("cannot read native seed {:?}: {error}", source))
    })?;
    let spec = NativeModelSpec::read(&seed)?;
    with_native_session(&spec, |session| {
        let mut stream = HnaStream::new();
        stream.open_new_connection();
        let result = stream.pump_native(session, &mut input, &mut output);
        Ok(finish_native_stream(session, &stream, result, &checkpoint))
    })
}

pub fn run_wave_session_stream(
    command: HnaCommand,
) -> Result<WaveHnaStreamProcessReceipt, NativeSessionError> {
    let HnaCommand::WaveSession {
        source,
        resume,
        seed,
        input,
        checkpoint,
    } = command
    else {
        return Err(NativeSessionError::Application(
            "expected a wave streaming session command".into(),
        ));
    };
    if seed && resume {
        return Err(NativeSessionError::Application(
            "seeded wave sessions cannot resume an existing checkpoint".into(),
        ));
    }
    if checkpoint.exists() {
        return Err(NativeSessionError::Application(format!(
            "wave checkpoint already exists: {:?}",
            checkpoint
        )));
    }
    if let Some(parent) = checkpoint.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|error| {
            NativeSessionError::Application(format!(
                "cannot create wave checkpoint directory {:?}: {error}",
                parent
            ))
        })?;
    }
    let mut input: Box<dyn BufRead> = if input.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(BufReader::new(File::open(&input).map_err(|error| {
            NativeSessionError::Application(format!("cannot read wave input {:?}: {error}", input))
        })?))
    };
    let mut output = io::stdout().lock();

    fn finish_wave_stream(
        session: &mut holonics_hna::native::NativeWaveSession<'_>,
        stream: &HnaStream,
        pump: Result<HnaStreamDisposition, holonics_hna::HnaStreamError>,
        checkpoint: &PathBuf,
        before: u64,
    ) -> WaveHnaStreamProcessReceipt {
        let (disposition, stream_error) = match pump {
            Ok(disposition) => (Some(disposition), None),
            Err(error) => (None, Some(error.to_string())),
        };
        let publication = session.checkpoint_stream(checkpoint, stream.state());
        let (checkpoint_octets, checkpoint_error) = match publication {
            Ok(receipt) => (Some(receipt.bytes), None),
            Err(error) => (None, Some(error.to_string())),
        };
        let inspect = session.inspect();
        let after = session.wave().epoch();
        WaveHnaStreamProcessReceipt {
            schema: "org.holonics.hna.wave-stream-process.v1",
            disposition,
            stream_error,
            checkpoint: checkpoint.clone(),
            checkpoint_octets,
            checkpoint_error,
            transport_sequence: stream.state().sequence,
            epochs: WaveEpochReceipt { before, after },
            inspect,
        }
    }

    if seed {
        let bytes = fs::read(&source).map_err(|error| {
            NativeSessionError::Application(format!("cannot read wave seed {:?}: {error}", source))
        })?;
        let spec: holonics_hna::native::NativeWaveSeedSpec = serde_json::from_slice(&bytes)?;
        return holonics_hna::native::with_seeded_wave_session(&spec, |session| {
            let mut stream = HnaStream::new();
            stream.open_new_connection();
            let before = session.wave().epoch();
            let pump = stream.pump_wave(session, &mut input, &mut output);
            Ok(finish_wave_stream(session, &stream, pump, &checkpoint, before))
        });
    }

    let saved = if resume {
        NativeWaveSavedSession::read(&source)?
    } else {
        NativeWaveSavedSession::from_model_directory(&source)?
    };
    saved.with_session(|session, stream| {
        stream.open_new_connection();
        let before = session.wave().epoch();
        let pump = stream.pump_wave(session, &mut input, &mut output);
        Ok(finish_wave_stream(
            session,
            stream,
            pump,
            &checkpoint,
            before,
        ))
    })
}

pub fn run_coupled_wave_session_stream(
    command: HnaCommand,
) -> Result<WaveHnaStreamProcessReceipt, NativeSessionError> {
    let HnaCommand::CoupledWaveSession {
        source,
        resume,
        input,
        checkpoint,
        member,receiver,
    } = command
    else {
        return Err(NativeSessionError::Application(
            "expected a wave streaming session command".into(),
        ));
    };
    if checkpoint.exists() {
        return Err(NativeSessionError::Application(format!(
            "wave checkpoint already exists: {:?}",
            checkpoint
        )));
    }
    if let Some(parent) = checkpoint.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|error| {
            NativeSessionError::Application(format!(
                "cannot create wave checkpoint directory {:?}: {error}",
                parent
            ))
        })?;
    }
    let mut input: Box<dyn BufRead> = if input.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(BufReader::new(File::open(&input).map_err(|error| {
            NativeSessionError::Application(format!("cannot read wave input {:?}: {error}", input))
        })?))
    };
    let mut output = io::stdout().lock();

    fn finish_wave_stream(
        session: &mut holonics_hna::native::NativeCoupledWaveSession<'_>,
        stream: &HnaStream,
        pump: Result<HnaStreamDisposition, holonics_hna::HnaStreamError>,
        checkpoint: &PathBuf,
        before: u64,
    ) -> WaveHnaStreamProcessReceipt {
        let (disposition, stream_error) = match pump {
            Ok(disposition) => (Some(disposition), None),
            Err(error) => (None, Some(error.to_string())),
        };
        let publication = session.checkpoint_stream(checkpoint, stream.state());
        let (checkpoint_octets, checkpoint_error) = match publication {
            Ok(receipt) => (Some(receipt.bytes), None),
            Err(error) => (None, Some(error.to_string())),
        };
        let inspect = session.inspect();
        let after = session.wave().epoch();
        WaveHnaStreamProcessReceipt {
            schema: "org.holonics.hna.coupled-wave-stream-process.v1",
            disposition,
            stream_error,
            checkpoint: checkpoint.clone(),
            checkpoint_octets,
            checkpoint_error,
            transport_sequence: stream.state().sequence,
            epochs: WaveEpochReceipt { before, after },
            inspect,
        }
    }

    let saved=if resume {
        if member.is_some()||receiver.is_some(){return Err(NativeSessionError::Application("resume uses its stored member and receiver chart".into()));}
        NativeCoupledWaveSavedSession::read(&source)?
    }else{
        use holonic_engine::native_ecology::constitutive_fibre::WaveSourceReceiver;
        let receiver=match receiver.as_deref().unwrap_or("direct"){
            "direct"=>WaveSourceReceiver::Direct,"unit-real-sum"=>WaveSourceReceiver::UnitRealSum,
            _=>return Err(NativeSessionError::Application("unsupported coupled source receiver".into())),
        };
        NativeCoupledWaveSavedSession::from_model_directory(&source,member.unwrap_or(0),receiver)?
    };
    saved.with_session(|session, stream| {
        stream.open_new_connection();
        let before = session.wave().epoch();
        let pump = stream.pump_coupled_wave(session, &mut input, &mut output);
        Ok(finish_wave_stream(
            session,
            stream,
            pump,
            &checkpoint,
            before,
        ))
    })
}

