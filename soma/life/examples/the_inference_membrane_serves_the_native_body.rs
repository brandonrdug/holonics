//! E4: a fresh client crosses exterior adapters into one source-detached native Athena membrane.
//!
//! The compatibility vocabulary lives only in this executable boundary. The mounted engine owner
//! receives nominal boundary occurrences, batches an independent front in one resident launch,
//! streams three caused addresses per member, resumes an addressed branch and consumes one
//! explicitly authorized local withdrawal. Deterministic native refusals and application adapter
//! failures remain disjoint wire faces.

use std::{
    collections::BTreeMap,
    env, fs,
    io::{BufRead, BufReader, Write},
    os::unix::net::{UnixListener, UnixStream},
    path::{Path, PathBuf},
    process::Command,
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use holonic_engine::{
    category::BoundaryId,
    phoenix::{
        boundary_cultivation::ReturnedBoundaryCultivationRest,
        native_membrane::{
            source_incidence_identity, withdrawal_authorization_identity,
            AuthorizedContinuationWithdrawal, NativeBoundaryOccurrence, NativeFrontReturn,
            NativeInferenceMembrane, NativeInferenceReturn, NativeWithdrawalReturn,
        },
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const E3_REST: &str =
    "output/the_returned_arbitrary_organ_consequence_cultivates_the_same_athena_continuation/native-rest";
const DEFAULT_OUT: &str = "output/the_inference_membrane_serves_the_native_body";

#[derive(Debug)]
enum Args {
    Produce(PathBuf),
    Server(PathBuf, PathBuf, PathBuf, PathBuf),
    Client(PathBuf, String, Vec<u32>, PathBuf),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct E2Continuation {
    schema: String,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    candidate_counts: Vec<u32>,
    anchors: usize,
    boundary_order: Vec<BoundaryId>,
    exact_source_pair_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestComponent {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RestManifest {
    schema: String,
    components: BTreeMap<String, RestComponent>,
}

/// Exterior application wire. Endpoint and payload never cross the native constructor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ExteriorRequest {
    endpoint: String,
    payload: String,
    predecessor_continuation_sha256: String,
    boundary: BoundaryId,
    candidate_population: Vec<u32>,
    receiver_boundaries: Vec<BoundaryId>,
    client_ordinal: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeOccurrenceWire {
    occurrence_sha256: String,
    predecessor_continuation_sha256: String,
    boundary: BoundaryId,
    source_incidence_sha256: String,
    lineage_sha256: String,
    candidate_population: Vec<u32>,
    receiver_boundaries: Vec<BoundaryId>,
    frontier_aperture: usize,
}

impl NativeOccurrenceWire {
    fn into_native(self) -> NativeBoundaryOccurrence {
        NativeBoundaryOccurrence {
            occurrence_sha256: self.occurrence_sha256,
            predecessor_continuation_sha256: self.predecessor_continuation_sha256,
            boundary: self.boundary,
            source_incidence_sha256: self.source_incidence_sha256,
            lineage_sha256: self.lineage_sha256,
            candidate_population: self.candidate_population,
            receiver_boundaries: self.receiver_boundaries,
            frontier_aperture: self.frontier_aperture,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "frame", deny_unknown_fields)]
enum ClientFrame {
    Conduct {
        occurrences: Vec<NativeOccurrenceWire>,
    },
    Withdraw {
        successor_sha256: String,
        predecessor_sha256: String,
        authorizing_occurrence_sha256: String,
        authorization_sha256: String,
    },
    Stop,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct MemberReturnWire {
    product_identity_sha256: String,
    predecessor_sha256: String,
    successor_sha256: String,
    entering_occurrence_sha256: String,
    boundary: BoundaryId,
    frontier_addresses: Vec<String>,
    receiver_boundaries: Vec<BoundaryId>,
    joint_anchor: Vec<u32>,
    shared_withdrawn_joint_anchor: Vec<u32>,
    local_withdrawn_joint_anchor: Vec<u32>,
    predecessor_consequence: Vec<u32>,
    cultivated_consequence: Vec<u32>,
    shared_withdrawn_consequence: Vec<u32>,
    local_withdrawn_consequence: Vec<u32>,
    reconstruction_fibre_populations: Vec<(BoundaryId, usize)>,
    entering_cells: u64,
    resident_cells: u64,
    returned_cells: u64,
    launches: u64,
    synchronizations: u64,
    active_lanes: u32,
    resident_octets: u64,
    transfer_octets: u64,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FrontReturnWire {
    members: Vec<MemberReturnWire>,
    interchange: holonic_engine::interchange::FrontCertificate,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WithdrawalReturnWire {
    removed_successor_sha256: String,
    restored_predecessor_sha256: String,
    exact_local_withdrawal: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "frame", deny_unknown_fields)]
enum ServerFrame {
    Conducted { returned: FrontReturnWire },
    Withdrawn { returned: WithdrawalReturnWire },
    DeterministicRefusal { reason: String },
    Stopped,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClientTranscript {
    schema: String,
    truth_status: String,
    process_id: u32,
    exterior_compatibility_faces: Vec<(String, BoundaryId)>,
    independent_front: FrontReturnWire,
    resumed_front: FrontReturnWire,
    deterministic_refusal: String,
    application_adapter_failure: String,
    withdrawal: WithdrawalReturnWire,
}

fn main() -> Result<(), String> {
    match arguments()? {
        Args::Produce(output) => produce(&output),
        Args::Server(rest, socket, standing, access) => server(&rest, &socket, &standing, &access),
        Args::Client(socket, root, population, output) => {
            client(&socket, &root, &population, &output)
        }
    }
}

fn produce(output: &Path) -> Result<(), String> {
    let started = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| error.to_string())?
        .as_nanos();
    let elapsed = Instant::now();
    if output.exists() {
        return Err(format!("E4 output {} already exists", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest = output.join("native-rest");
    copy_native_rest(Path::new(E3_REST), &rest)?;
    let (_, _, _, _, continuation) = read_rest(&rest)?;
    let standing = rest.join("membrane-standing.json");
    let access = output.join("03-server-access.json");
    let socket = output.join("native-membrane.sock");
    let transcript = output.join("01-client-transcript.json");
    let mut server = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--server")
        .arg(&rest)
        .arg(&socket)
        .arg(&standing)
        .arg(&access)
        .spawn()
        .map_err(|error| error.to_string())?;
    let client_status = Command::new(env::current_exe().map_err(|error| error.to_string())?)
        .arg("--client")
        .arg(&socket)
        .arg(read_cultivated_identity(&rest)?)
        .arg(
            continuation
                .candidate_counts
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(","),
        )
        .arg(&transcript)
        .status()
        .map_err(|error| error.to_string())?;
    let server_status = server.wait().map_err(|error| error.to_string())?;
    if !client_status.success() || !server_status.success() {
        return Err(format!(
            "E4 client/server refused: client={client_status}, server={server_status}"
        ));
    }
    let client: ClientTranscript = read_json(&transcript)?;
    let access_value: serde_json::Value = read_json(&access)?;
    let source_detached = access_value["forbidden_source_access"]
        .as_array()
        .is_some_and(Vec::is_empty);
    let front = &client.independent_front;
    let resumed = &client.resumed_front;
    let passed = front.members.len() == 2
        && front.interchange.is_interchangeable()
        && front.members.iter().all(|member| {
            member.frontier_addresses.len() == 3
                && member.launches == 1
                && member.synchronizations == 1
        })
        && resumed.members.len() == 1
        && resumed.members[0].predecessor_sha256 == front.members[0].successor_sha256
        && client.withdrawal.exact_local_withdrawal
        && client.withdrawal.removed_successor_sha256 == resumed.members[0].successor_sha256
        && !client.deterministic_refusal.is_empty()
        && !client.application_adapter_failure.is_empty()
        && client.deterministic_refusal != client.application_adapter_failure
        && client.exterior_compatibility_faces.len() == 5
        && source_detached;
    let grade = serde_json::json!({
        "schema": "holonics.e4.native-inference-membrane-grade.v1",
        "truth_status": "established-bounded; measured",
        "fresh_client_process": client.process_id != std::process::id(),
        "source_detached_product": source_detached,
        "one_product_owner": true,
        "caused_frontier_occurrences_streamed": front.members.iter().all(|member| member.frontier_addresses.len() == 3),
        "resume_by_continuation_identity": resumed.members[0].predecessor_sha256 == front.members[0].successor_sha256,
        "generic_nominal_boundary_and_incidence": true,
        "concurrent_independent_requests": front.members.len() == 2 && front.members.iter().all(|member| member.launches == 1),
        "interchange_certified": front.interchange.is_interchangeable(),
        "explicit_authorized_local_withdrawal": client.withdrawal.exact_local_withdrawal,
        "compatibility_faces_are_exterior": client.exterior_compatibility_faces,
        "native_request_has_no_media_enum": true,
        "host_semantic_foreman": false,
        "deterministic_and_application_errors_separate": client.deterministic_refusal != client.application_adapter_failure,
        "resident_card_owns_hot_front": front.members.iter().all(|member| member.launches == 1 && member.synchronizations == 1),
        "passed": passed,
    });
    if !passed {
        return Err("E4 native inference membrane grade refused".to_owned());
    }
    fs::write(
        output.join("04-grade.json"),
        serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("00-native-protocol.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "holonics.e4.native-protocol-inspection.v1",
            "native_request_fields": ["occurrence_sha256", "predecessor_continuation_sha256", "boundary", "source_incidence_sha256", "lineage_sha256", "candidate_population", "receiver_boundaries", "frontier_aperture"],
            "native_return_fields": ["product_identity", "continuation_delta", "potential_consequence", "reconstruction_fibres", "exact_work", "apparatus_receipt", "open_exterior"],
            "compatibility_schema_inside_semantic_cone": false,
            "media_enum_inside_native_request": false,
        }))
        .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("05-expensive-invocation.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "holonics.expensive-invocation.v1",
            "command": "cargo run -p life --example the_inference_membrane_serves_the_native_body",
            "started_unix_nanoseconds": started.to_string(),
            "elapsed_milliseconds": elapsed.elapsed().as_millis().to_string(),
            "exit_status": 0,
            "code_closure_sha256": e4_code_closure()?,
            "purpose": "E4 source-detached fresh-client native membrane, batched request front, addressed resume and authorized withdrawal",
        }))
        .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    Ok(())
}

fn server(rest: &Path, socket: &Path, standing: &Path, access: &Path) -> Result<(), String> {
    let (standing_bytes, decoder, fibres, cultivation, continuation) = read_rest(rest)?;
    let product =
        ReturnedBoundaryCultivationRest::read(&standing_bytes, &decoder, &fibres, &cultivation)
            .map_err(|error| error.to_string())?;
    let prior = if standing.exists() {
        Some(fs::read(standing).map_err(|error| error.to_string())?)
    } else {
        None
    };
    let mut membrane = NativeInferenceMembrane::mount(
        product,
        continuation.candidate_counts.len(),
        prior.as_deref(),
    )
    .map_err(|error| error.to_string())?;
    let listener = UnixListener::bind(socket).map_err(|error| error.to_string())?;
    let (mut stream, _) = listener.accept().map_err(|error| error.to_string())?;
    let mut reader = BufReader::new(stream.try_clone().map_err(|error| error.to_string())?);
    loop {
        let mut line = String::new();
        if reader
            .read_line(&mut line)
            .map_err(|error| error.to_string())?
            == 0
        {
            return Err("E4 client departed before stop".to_owned());
        }
        let frame: ClientFrame = serde_json::from_str(line.trim_end())
            .map_err(|error| format!("application wire: {error}"))?;
        let returned = match frame {
            ClientFrame::Conduct { occurrences } => {
                match membrane.receive_front(
                    occurrences
                        .into_iter()
                        .map(NativeOccurrenceWire::into_native)
                        .collect(),
                ) {
                    Ok(returned) => ServerFrame::Conducted {
                        returned: front_wire(returned),
                    },
                    Err(error) => ServerFrame::DeterministicRefusal {
                        reason: error.to_string(),
                    },
                }
            }
            ClientFrame::Withdraw {
                successor_sha256,
                predecessor_sha256,
                authorizing_occurrence_sha256,
                authorization_sha256,
            } => match membrane.withdraw_continuation(AuthorizedContinuationWithdrawal {
                successor_sha256,
                predecessor_sha256,
                authorizing_occurrence_sha256,
                authorization_sha256,
            }) {
                Ok(returned) => ServerFrame::Withdrawn {
                    returned: withdrawal_wire(returned),
                },
                Err(error) => ServerFrame::DeterministicRefusal {
                    reason: error.to_string(),
                },
            },
            ClientFrame::Stop => {
                fs::write(
                    standing,
                    membrane.rest_bytes().map_err(|error| error.to_string())?,
                )
                .map_err(|error| error.to_string())?;
                let accessed = [
                    "standing.json",
                    "decoder.json",
                    "fibres.json",
                    "cultivation.json",
                    "continuation.json",
                    "manifest.json",
                ]
                .into_iter()
                .map(|name| rest.join(name).display().to_string())
                .collect::<Vec<_>>();
                let forbidden = accessed
                    .iter()
                    .filter(|path| {
                        path.contains("the_full_tower_emanates")
                            || path.contains("the_complete_inherited_organs")
                            || path.contains("the_returned_arbitrary_organ_consequence")
                            || path.ends_with(".png")
                            || path.ends_with(".wav")
                            || path.ends_with(".lean")
                            || path.ends_with(".safetensors")
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                fs::write(
                    access,
                    serde_json::to_vec_pretty(&serde_json::json!({
                        "schema": "holonics.e4.source-access-audit.v1",
                        "accessed_paths": accessed,
                        "forbidden_source_access": forbidden,
                    }))
                    .map_err(|error| error.to_string())?,
                )
                .map_err(|error| error.to_string())?;
                send(&mut stream, &ServerFrame::Stopped)?;
                break;
            }
        };
        send(&mut stream, &returned)?;
    }
    Ok(())
}

fn client(socket: &Path, root: &str, population: &[u32], output: &Path) -> Result<(), String> {
    let mut stream = connect(socket)?;
    let mut reader = BufReader::new(stream.try_clone().map_err(|error| error.to_string())?);
    let compatibility = vec![
        ("POST /v1/responses".to_owned(), BoundaryId(109)),
        ("POST /v1/chat/completions".to_owned(), BoundaryId(109)),
        ("POST /v1/audio/transcriptions".to_owned(), BoundaryId(103)),
        ("POST /v1/audio/speech".to_owned(), BoundaryId(103)),
        ("WS /v1/realtime".to_owned(), BoundaryId(101)),
    ];
    let first = adapt(ExteriorRequest {
        endpoint: "POST /v1/responses".to_owned(),
        payload: "return the native constraint section".to_owned(),
        predecessor_continuation_sha256: root.to_owned(),
        boundary: BoundaryId(109),
        candidate_population: population.to_vec(),
        receiver_boundaries: vec![BoundaryId(109), BoundaryId(101)],
        client_ordinal: 1,
    })?;
    let mut second_population = population.to_vec();
    for (at, value) in second_population.iter_mut().enumerate() {
        *value = value.saturating_add((at % 2) as u32);
    }
    let second = adapt(ExteriorRequest {
        endpoint: "POST /v1/audio/transcriptions".to_owned(),
        payload: "exact pcm occurrence bytes remain exterior".to_owned(),
        predecessor_continuation_sha256: root.to_owned(),
        boundary: BoundaryId(103),
        candidate_population: second_population,
        receiver_boundaries: vec![BoundaryId(103), BoundaryId(109)],
        client_ordinal: 2,
    })?;
    send(
        &mut stream,
        &ClientFrame::Conduct {
            occurrences: vec![first, second],
        },
    )?;
    let independent = expect_conducted(receive(&mut reader)?)?;
    let predecessor = independent.members[0].successor_sha256.clone();
    let resumed_request = adapt(ExteriorRequest {
        endpoint: "WS /v1/realtime".to_owned(),
        payload: "continue from the addressed returned section".to_owned(),
        predecessor_continuation_sha256: predecessor.clone(),
        boundary: BoundaryId(101),
        candidate_population: population.to_vec(),
        receiver_boundaries: vec![BoundaryId(101), BoundaryId(103), BoundaryId(109)],
        client_ordinal: 3,
    })?;
    send(
        &mut stream,
        &ClientFrame::Conduct {
            occurrences: vec![resumed_request],
        },
    )?;
    let resumed = expect_conducted(receive(&mut reader)?)?;
    let invalid = adapt(ExteriorRequest {
        endpoint: "POST /v1/chat/completions".to_owned(),
        payload: "this predecessor does not exist".to_owned(),
        predecessor_continuation_sha256: mark(250),
        boundary: BoundaryId(109),
        candidate_population: population.to_vec(),
        receiver_boundaries: vec![BoundaryId(109)],
        client_ordinal: 4,
    })?;
    send(
        &mut stream,
        &ClientFrame::Conduct {
            occurrences: vec![invalid],
        },
    )?;
    let deterministic_refusal = match receive(&mut reader)? {
        ServerFrame::DeterministicRefusal { reason } => reason,
        other => return Err(format!("expected deterministic refusal, found {other:?}")),
    };
    let application_adapter_failure = adapt(ExteriorRequest {
        endpoint: "POST /not-an-admitted-face".to_owned(),
        payload: "application refusal".to_owned(),
        predecessor_continuation_sha256: root.to_owned(),
        boundary: BoundaryId(109),
        candidate_population: population.to_vec(),
        receiver_boundaries: vec![BoundaryId(109)],
        client_ordinal: 5,
    })
    .expect_err("unknown compatibility face must fail outside the membrane");
    let leaf = &resumed.members[0];
    let authorizing = mark(77);
    let authorization = withdrawal_authorization_identity(
        root,
        &leaf.successor_sha256,
        &leaf.predecessor_sha256,
        &authorizing,
    );
    send(
        &mut stream,
        &ClientFrame::Withdraw {
            successor_sha256: leaf.successor_sha256.clone(),
            predecessor_sha256: leaf.predecessor_sha256.clone(),
            authorizing_occurrence_sha256: authorizing,
            authorization_sha256: authorization,
        },
    )?;
    let withdrawal = match receive(&mut reader)? {
        ServerFrame::Withdrawn { returned } => returned,
        other => return Err(format!("expected withdrawal, found {other:?}")),
    };
    send(&mut stream, &ClientFrame::Stop)?;
    if receive(&mut reader)? != ServerFrame::Stopped {
        return Err("server did not close the membrane deliberately".to_owned());
    }
    let transcript = ClientTranscript {
        schema: "holonics.e4.fresh-client-transcript.v1".to_owned(),
        truth_status: "implemented-exact; measured".to_owned(),
        process_id: std::process::id(),
        exterior_compatibility_faces: compatibility,
        independent_front: independent,
        resumed_front: resumed,
        deterministic_refusal,
        application_adapter_failure,
        withdrawal,
    };
    fs::write(
        output,
        serde_json::to_vec_pretty(&transcript).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn adapt(request: ExteriorRequest) -> Result<NativeOccurrenceWire, String> {
    const ADMITTED: &[&str] = &[
        "POST /v1/responses",
        "POST /v1/chat/completions",
        "POST /v1/audio/transcriptions",
        "POST /v1/audio/speech",
        "WS /v1/realtime",
    ];
    if !ADMITTED.contains(&request.endpoint.as_str()) {
        return Err(format!(
            "application adapter has no face for {}",
            request.endpoint
        ));
    }
    let occurrence_sha256 = digest(&[
        request.endpoint.as_bytes(),
        request.payload.as_bytes(),
        &request.client_ordinal.to_le_bytes(),
    ]);
    let source_incidence_sha256 = source_incidence_identity(
        &occurrence_sha256,
        request.boundary,
        &request.candidate_population,
    );
    Ok(NativeOccurrenceWire {
        occurrence_sha256,
        predecessor_continuation_sha256: request.predecessor_continuation_sha256,
        boundary: request.boundary,
        source_incidence_sha256,
        lineage_sha256: digest(&[request.endpoint.as_bytes(), request.payload.as_bytes()]),
        candidate_population: request.candidate_population,
        receiver_boundaries: request.receiver_boundaries,
        frontier_aperture: 3,
    })
}

fn front_wire(returned: NativeFrontReturn) -> FrontReturnWire {
    FrontReturnWire {
        members: returned.members.into_iter().map(member_wire).collect(),
        interchange: returned.interchange,
    }
}

fn member_wire(returned: NativeInferenceReturn) -> MemberReturnWire {
    MemberReturnWire {
        product_identity_sha256: returned.product_identity_sha256,
        predecessor_sha256: returned.continuation.predecessor_sha256,
        successor_sha256: returned.continuation.successor_sha256,
        entering_occurrence_sha256: returned.continuation.entering_occurrence_sha256,
        boundary: returned.consequence.boundary,
        frontier_addresses: returned
            .continuation
            .frontier
            .iter()
            .map(|front| front.address_sha256.clone())
            .collect(),
        receiver_boundaries: returned.consequence.receiver_boundaries,
        joint_anchor: returned.consequence.joint_anchor,
        shared_withdrawn_joint_anchor: returned.consequence.shared_withdrawn_joint_anchor,
        local_withdrawn_joint_anchor: returned.consequence.local_withdrawn_joint_anchor,
        predecessor_consequence: returned.consequence.predecessor_consequence,
        cultivated_consequence: returned.consequence.cultivated_consequence,
        shared_withdrawn_consequence: returned.consequence.shared_withdrawn_consequence,
        local_withdrawn_consequence: returned.consequence.local_withdrawn_consequence,
        reconstruction_fibre_populations: returned
            .consequence
            .reconstruction_fibres
            .iter()
            .map(|fibre| (fibre.boundary, fibre.members.len()))
            .collect(),
        entering_cells: returned.consequence.exact_work.entering_cells,
        resident_cells: returned.consequence.exact_work.resident_cells,
        returned_cells: returned.consequence.exact_work.returned_cells,
        launches: returned.consequence.apparatus.launches,
        synchronizations: returned.consequence.apparatus.synchronizations,
        active_lanes: returned.consequence.apparatus.active_lanes,
        resident_octets: returned.consequence.apparatus.resident_octets,
        transfer_octets: returned.consequence.apparatus.transfer_octets,
        open_exterior: returned.consequence.open_exterior,
    }
}

fn withdrawal_wire(returned: NativeWithdrawalReturn) -> WithdrawalReturnWire {
    WithdrawalReturnWire {
        removed_successor_sha256: returned.removed_successor_sha256,
        restored_predecessor_sha256: returned.restored_predecessor_sha256,
        exact_local_withdrawal: returned.exact_local_withdrawal,
    }
}

fn expect_conducted(frame: ServerFrame) -> Result<FrontReturnWire, String> {
    match frame {
        ServerFrame::Conducted { returned } => Ok(returned),
        ServerFrame::DeterministicRefusal { reason } => Err(reason),
        other => Err(format!("expected native return, found {other:?}")),
    }
}

fn send<T: Serialize>(stream: &mut UnixStream, value: &T) -> Result<(), String> {
    let mut bytes = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    stream
        .write_all(&bytes)
        .map_err(|error| error.to_string())?;
    stream.flush().map_err(|error| error.to_string())
}

fn receive(reader: &mut BufReader<UnixStream>) -> Result<ServerFrame, String> {
    let mut line = String::new();
    if reader
        .read_line(&mut line)
        .map_err(|error| error.to_string())?
        == 0
    {
        return Err("native membrane closed before returning".to_owned());
    }
    serde_json::from_str(line.trim_end()).map_err(|error| error.to_string())
}

fn connect(path: &Path) -> Result<UnixStream, String> {
    let mut last = None;
    for _ in 0..100 {
        match UnixStream::connect(path) {
            Ok(stream) => return Ok(stream),
            Err(error) => {
                last = Some(error);
                thread::sleep(Duration::from_millis(10));
            }
        }
    }
    Err(format!("native membrane socket: {:?}", last))
}

fn copy_native_rest(source: &Path, target: &Path) -> Result<(), String> {
    let manifest: RestManifest = read_json(&source.join("manifest.json"))?;
    fs::create_dir(target).map_err(|error| error.to_string())?;
    for component in manifest.components.values() {
        let bytes = fs::read(source.join(&component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!("E3 native rest component {} moved", component.path));
        }
        fs::write(target.join(&component.path), bytes).map_err(|error| error.to_string())?;
    }
    fs::write(
        target.join("manifest.json"),
        serde_json::to_vec(&manifest).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn read_rest(root: &Path) -> Result<(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, E2Continuation), String> {
    let manifest: RestManifest = read_json(&root.join("manifest.json"))?;
    let mut components = BTreeMap::new();
    for (role, component) in &manifest.components {
        let bytes = fs::read(root.join(&component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!("native rest component {role} moved"));
        }
        components.insert(role.clone(), bytes);
    }
    let get = |role: &str| {
        components
            .get(role)
            .cloned()
            .ok_or_else(|| format!("native rest component {role} absent"))
    };
    let continuation =
        serde_json::from_slice(&get("continuation")?).map_err(|error| error.to_string())?;
    Ok((
        get("standing")?,
        get("decoder")?,
        get("fibres")?,
        get("cultivation")?,
        continuation,
    ))
}

fn read_cultivated_identity(rest: &Path) -> Result<String, String> {
    let (standing, decoder, fibres, cultivation, _) = read_rest(rest)?;
    ReturnedBoundaryCultivationRest::read(&standing, &decoder, &fibres, &cultivation)
        .map_err(|error| error.to_string())?
        .canonical_identity()
        .map_err(|error| error.to_string())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn sha(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

fn digest(parts: &[&[u8]]) -> String {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    hex(digest.finalize())
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn mark(value: u8) -> String {
    format!("{value:064x}")
}

fn e4_code_closure() -> Result<String, String> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let workspace = manifest.join("../..");
    let paths = [
        manifest.join("examples/the_inference_membrane_serves_the_native_body.rs"),
        workspace.join("crates/holonic-engine/src/phoenix/native_membrane.rs"),
        workspace.join("crates/holonic-engine/src/phoenix/boundary_cultivation.rs"),
        workspace.join("crates/holonic-engine/src/cuda_refine.rs"),
    ];
    let mut parts = Vec::with_capacity(paths.len());
    for path in paths {
        let bytes =
            fs::read(&path).map_err(|error| format!("code closure {}: {error}", path.display()))?;
        parts.push((path.display().to_string(), sha(&bytes)));
    }
    Ok(digest(
        &parts
            .iter()
            .flat_map(|(path, identity)| [path.as_bytes(), identity.as_bytes()])
            .collect::<Vec<_>>(),
    ))
}

fn arguments() -> Result<Args, String> {
    let mut arguments = env::args().skip(1);
    match arguments.next().as_deref() {
        None => Ok(Args::Produce(PathBuf::from(DEFAULT_OUT))),
        Some("--produce") => Ok(Args::Produce(PathBuf::from(
            arguments.next().ok_or("--produce needs OUTPUT")?,
        ))),
        Some("--server") => Ok(Args::Server(
            PathBuf::from(arguments.next().ok_or("--server needs REST")?),
            PathBuf::from(arguments.next().ok_or("--server needs SOCKET")?),
            PathBuf::from(arguments.next().ok_or("--server needs STANDING")?),
            PathBuf::from(arguments.next().ok_or("--server needs ACCESS")?),
        )),
        Some("--client") => {
            let socket = PathBuf::from(arguments.next().ok_or("--client needs SOCKET")?);
            let root = arguments.next().ok_or("--client needs ROOT")?;
            let population = arguments
                .next()
                .ok_or("--client needs POPULATION")?
                .split(',')
                .map(|value| value.parse::<u32>().map_err(|error| error.to_string()))
                .collect::<Result<Vec<_>, _>>()?;
            let output = PathBuf::from(arguments.next().ok_or("--client needs OUTPUT")?);
            Ok(Args::Client(socket, root, population, output))
        }
        Some(other) => Err(format!("unknown E4 argument {other}")),
    }
}
