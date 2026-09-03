//! Actual exterior worlds for native material artifacts.

use std::{fs, path::PathBuf, process::Command};

use life::native_intelligence::{NativeCirculationBoundary, NativeSessionError, NativeWorldFace};
use serde::{Deserialize, Serialize};
use tempfile::tempdir;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApplicationWorldReturn {
    pub admitted: bool,
    pub carried_octets: u64,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub apparatus: String,
    pub status_code: Option<i32>,
}

impl ApplicationWorldReturn {
    pub fn diagnostic_octets(&self) -> Vec<u8> {
        let mut diagnostic = Vec::with_capacity(16 + self.stdout.len() + self.stderr.len());
        diagnostic.extend_from_slice(&(self.stdout.len() as u64).to_le_bytes());
        diagnostic.extend_from_slice(&self.stdout);
        diagnostic.extend_from_slice(&(self.stderr.len() as u64).to_le_bytes());
        diagnostic.extend_from_slice(&self.stderr);
        diagnostic
    }

    pub fn faces_for(
        &self,
        boundary: &NativeCirculationBoundary,
    ) -> Result<Vec<NativeWorldFace>, NativeSessionError> {
        if self.carried_octets == 0 {
            return Err(NativeSessionError::WorldFace);
        }
        let diagnostic = self.diagnostic_octets();
        boundary
            .issued_world_faces()
            .into_iter()
            .map(|issued| {
                NativeWorldFace::report(
                    issued.clone(),
                    self.admitted,
                    issued.support().clone(),
                    diagnostic.clone(),
                )
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProcessArtifactWorld {
    pub program: PathBuf,
    pub arguments: Vec<String>,
    pub artifact_name: String,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExactReadbackWorld;

#[derive(Debug, Error)]
pub enum ApplicationWorldError {
    #[error("the exterior artifact is empty")]
    EmptyArtifact,
    #[error("the exterior world path or argument is malformed")]
    Configuration,
    #[error("the exterior world apparatus refused: {0}")]
    Apparatus(String),
}

impl ProcessArtifactWorld {
    pub fn act(&self, artifact: &[u8]) -> Result<ApplicationWorldReturn, ApplicationWorldError> {
        validate(
            self.program.as_os_str().is_empty(),
            &self.artifact_name,
            artifact,
        )?;
        let scratch = tempdir().map_err(apparatus)?;
        let artifact_path = scratch.path().join(&self.artifact_name);
        fs::write(&artifact_path, artifact).map_err(apparatus)?;
        let artifact_argument = artifact_path.to_string_lossy();
        let output = Command::new(&self.program)
            .args(
                self.arguments
                    .iter()
                    .map(|argument| argument.replace("{artifact}", &artifact_argument)),
            )
            .output()
            .map_err(apparatus)?;
        Ok(ApplicationWorldReturn {
            admitted: output.status.success(),
            carried_octets: artifact.len() as u64,
            stdout: output.stdout,
            stderr: output.stderr,
            apparatus: format!("process:{}", self.program.display()),
            status_code: output.status.code(),
        })
    }
}

impl ExactReadbackWorld {
    pub fn act(&self, artifact: &[u8]) -> Result<ApplicationWorldReturn, ApplicationWorldError> {
        if artifact.is_empty() {
            return Err(ApplicationWorldError::EmptyArtifact);
        }
        let scratch = tempdir().map_err(apparatus)?;
        let path = scratch.path().join("emission.bin");
        fs::write(&path, artifact).map_err(apparatus)?;
        let returned = fs::read(&path).map_err(apparatus)?;
        Ok(ApplicationWorldReturn {
            admitted: returned == artifact,
            carried_octets: artifact.len() as u64,
            stdout: returned,
            stderr: Vec::new(),
            apparatus: "filesystem-exact-readback".to_owned(),
            status_code: None,
        })
    }
}

fn validate(
    empty_program: bool,
    artifact_name: &str,
    artifact: &[u8],
) -> Result<(), ApplicationWorldError> {
    if artifact.is_empty() {
        return Err(ApplicationWorldError::EmptyArtifact);
    }
    if empty_program
        || artifact_name.is_empty()
        || artifact_name.contains('/')
        || artifact_name.contains("..")
    {
        return Err(ApplicationWorldError::Configuration);
    }
    Ok(())
}

fn apparatus(error: std::io::Error) -> ApplicationWorldError {
    ApplicationWorldError::Apparatus(error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn readback_and_process_return_distinct_actual_consequences() {
        let readback = ExactReadbackWorld.act(b"eee").expect("readback");
        assert!(readback.admitted);
        let process = ProcessArtifactWorld {
            program: PathBuf::from("/bin/sh"),
            arguments: vec![
                "-c".to_owned(),
                "printf process-refused >&2; exit 9".to_owned(),
            ],
            artifact_name: "emission.bin".to_owned(),
        }
        .act(b"eee")
        .expect("process");
        assert!(!process.admitted);
        assert_eq!(process.status_code, Some(9));
        assert_ne!(readback.diagnostic_octets(), process.diagnostic_octets());
    }

    #[test]
    fn absent_apparatus_returns_an_obstruction_without_fallback() {
        assert!(matches!(
            ProcessArtifactWorld {
                program: PathBuf::from("/definitely-absent-holonics-world"),
                arguments: Vec::new(),
                artifact_name: "emission.bin".to_owned(),
            }
            .act(b"eee"),
            Err(ApplicationWorldError::Apparatus(_))
        ));
    }
}
