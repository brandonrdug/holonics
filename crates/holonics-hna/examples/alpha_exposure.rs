//! Inspect the cold Athena conversation exposure and save/resume its source position.
//! This executes no native model and prints no private message text.
use holonics_hna::{
    alpha::exposure::{ExposureCursor, ExposurePartition, ExposureReader},
    publish_new,
};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, io, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let source = PathBuf::from(
        args.next()
            .ok_or("usage: alpha_exposure SOURCE [--resume] [--frames N] [--cursor NEW.json]")?,
    );
    let mut resume = false;
    let mut frames = None;
    let mut output = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--resume" => resume = true,
            "--frames" => {
                frames = Some(
                    args.next()
                        .ok_or("missing frame aperture")?
                        .parse::<u64>()?,
                )
            }
            "--cursor" => output = Some(PathBuf::from(args.next().ok_or("missing cursor path")?)),
            _ => return Err(format!("unknown option {arg}").into()),
        }
    }
    let mut reader = if resume {
        let cursor: ExposureCursor = serde_json::from_reader(File::open(source)?)?;
        ExposureReader::resume(cursor)?
    } else {
        ExposureReader::open(source)?
    };
    let first_sequence = reader.cursor().next_sequence;
    let mut consumed = 0_u64;
    let mut partitions = BTreeMap::<&str, u64>::new();
    let mut roles = BTreeMap::<String, u64>::new();
    let mut development_octets = 0_u64;
    let mut views = 0_u64;
    let mut end = false;
    while frames.is_none_or(|limit| consumed < limit) {
        let Some(frame) = reader.peek()? else {
            end = true;
            break;
        };
        let kind = match frame.partition {
            ExposurePartition::Development => "development",
            ExposurePartition::Evaluation => "evaluation",
            ExposurePartition::Deferred => "deferred",
        };
        *partitions.entry(kind).or_default() += 1;
        views += frame.views.len() as u64;
        for view in &frame.views {
            *roles.entry(view.author_class.clone()).or_default() += 1;
        }
        if frame.partition == ExposurePartition::Development {
            for part in frame.development_parts()? {
                development_octets += part.text.as_ref().map_or(0, |text| text.len() as u64);
            }
        }
        let sequence = frame.sequence;
        reader.acknowledge(sequence)?;
        consumed += 1;
    }
    let cursor = reader.cursor();
    if let Some(path) = output {
        publish_new(path, |file| {
            // A private data-source cursor retains its private source pathname.
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
            }
            serde_json::to_writer(file, &cursor).map_err(io::Error::other)
        })?;
    }
    println!(
        "{}",
        json!({
            "schema":"holonics.conversation-exposure-inspection.v1",
            "native_model_executed":false,
            "first_sequence":first_sequence,"next_sequence":cursor.next_sequence,
            "consumed_frames":consumed,"views":views,"partitions":partitions,
            "captured_view_roles":roles,"development_visible_octets":development_octets,
            "byte_offset":cursor.byte_offset,"source_octets":cursor.source.octets,
            "input_exhausted":end
        })
    );
    Ok(())
}
