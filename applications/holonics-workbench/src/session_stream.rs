//! The process boundary for the continuing HNA stream. It deliberately bypasses the batch
//! Workbench response collector so responses are flushed while the native owner remains live.
use crate::HnaCommand;
use holonics::hna::{
    native::{
        with_native_session, NativeModelSpec, NativeSavedSession, NativeSessionAnatomy,
        NativeSessionError, NativeWaveSavedSession, NativeCoupledWaveSavedSession,
    },
    HnaCultivationAperture, HnaModel, HnaSessionAnatomy, HnaSessionError, HnaStream,
    HnaStreamDisposition,
};
use serde::Serialize;
use std::{
    fs::{self, File},
    io::{self, BufRead, BufReader, Write},
    path::PathBuf,
};

#[derive(Debug, Serialize)]
pub struct HnaStreamProcessReceipt {
    pub schema: &'static str,
    pub disposition: Option<HnaStreamDisposition>,
    pub stream_error: Option<String>,
    pub checkpoint: PathBuf,
    pub checkpoint_octets: u64,
    pub transport_sequence: u64,
    pub anatomy: HnaSessionAnatomy,
}

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
        session: &mut holonics::hna::native::NativeSession<'_>,
        stream: &HnaStream,
        pump: Result<HnaStreamDisposition, holonics::hna::HnaStreamError>,
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
        input,
        checkpoint,
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
        session: &mut holonics::hna::native::NativeWaveSession<'_>,
        stream: &HnaStream,
        pump: Result<HnaStreamDisposition, holonics::hna::HnaStreamError>,
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
        session: &mut holonics::hna::native::NativeCoupledWaveSession<'_>,
        stream: &HnaStream,
        pump: Result<HnaStreamDisposition, holonics::hna::HnaStreamError>,
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
        use holonics::engine::native_ecology::constitutive_fibre::WaveSourceReceiver;
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

pub fn run_hna_session_stream(
    command: HnaCommand,
) -> Result<HnaStreamProcessReceipt, HnaSessionError> {
    let HnaCommand::Session {
        source,
        resume,
        base_override,
        input_material,
        class,
        input,
        checkpoint,
        learning_shift,
        series_terms,
    } = command
    else {
        return Err(HnaSessionError::Base(
            "expected a streaming session command".into(),
        ));
    };
    if checkpoint.exists() {
        return Err(HnaSessionError::Base(
            "final checkpoint already exists; use a new output path".into(),
        ));
    }
    if let Some(parent) = checkpoint.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent).map_err(|e| HnaSessionError::Base(e.to_string()))?;
    }
    // Open a declared input file before mounting expensive native material. Standard input
    // remains streamed; it is never collected into a complete job before execution.
    let mut input: Box<dyn BufRead> = if input.as_os_str() == "-" {
        Box::new(io::stdin().lock())
    } else {
        Box::new(BufReader::new(
            File::open(input).map_err(|e| HnaSessionError::Base(e.to_string()))?,
        ))
    };
    let mut model = if resume {
        HnaModel::from_checkpoint(source, base_override.as_deref())?
    } else {
        if base_override.is_some() {
            return Err(HnaSessionError::Base(
                "base override requires checkpoint resume".into(),
            ));
        }
        HnaModel::from_native_rest(
            source,
            class,
            HnaCultivationAperture {
                learning_shift,
                series_terms,
            },
        )?
    };
    for material in input_material {
        model = model.with_input_material(material)?;
    }
    let mut output = io::stdout().lock();
    serve(&model, &mut input, &mut output, checkpoint)
}

fn serve(
    model: &HnaModel,
    input: &mut impl BufRead,
    output: &mut impl Write,
    checkpoint: PathBuf,
) -> Result<HnaStreamProcessReceipt, HnaSessionError> {
    model.with_stream_session(|session, stream| {
        // This process is a new connection. Retained replies are replayed with their old
        // event sequence; an unacknowledged peer may need to deduplicate them.
        stream.open_new_connection();
        let result = stream.pump(session, input, output);
        // Always attempt the declared final checkpoint, including input/output failure. It
        // contains partial input or the already-produced pending reply, never a request replay.
        let saved = session.checkpoint_stream(&checkpoint, stream.state()).map_err(|error|
            HnaSessionError::Base(format!("checkpoint failed at native generation {}; unsaved live changes cannot survive this process exiting: {error}", session.anatomy().generation)))?;
        let (disposition, stream_error) = match result {
            Ok(disposition) => (Some(disposition), None),
            Err(error) => (None, Some(error.to_string())),
        };
        Ok(HnaStreamProcessReceipt { schema:"org.holonics.hna.stream-process.v1", disposition,
            stream_error, checkpoint, checkpoint_octets:saved.publication.bytes,
            transport_sequence:stream.state().sequence, anatomy:session.anatomy() })
    })
}
