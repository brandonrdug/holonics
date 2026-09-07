#!/usr/bin/env python3
"""Acquire an original AMI meeting subset with synchronized audio and turn metadata.

The downloader uses the official AMI Edinburgh endpoints and stores the original mixed WAVs and
manual NXT annotation files. Generated JSON is a convenience index over the original segments;
it is not a replacement transcript or a semantic labeler.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import ssl
import urllib.request
import zipfile
from decimal import Decimal, InvalidOperation
from pathlib import Path
from shutil import copyfile
import wave
from xml.etree import ElementTree


BASE = "https://groups.inf.ed.ac.uk/ami"
ANNOTATION_URL = f"{BASE}/AMICorpusAnnotations/ami_public_manual_1.6.2.zip"


def download(url: str, path: Path) -> None:
    if path.exists():
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    partial = path.with_name(path.name + ".partial")
    if partial.exists():
        raise RuntimeError(f"refusing pre-existing partial download; inspect and recover it first: {partial}")
    try:
        import certifi

        context = ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        context = ssl.create_default_context()
    try:
        with urllib.request.urlopen(url, context=context) as response, partial.open("wb") as output:
            received = 0
            while chunk := response.read(1024 * 1024):
                output.write(chunk)
                received += len(chunk)
            expected = response.headers.get("Content-Length")
            if expected is not None and received != int(expected):
                raise RuntimeError(f"incomplete download: {received} of {expected} bytes from {url}")
        partial.replace(path)
    except Exception:
        raise


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def attr(element: ElementTree.Element, name: str) -> str | None:
    return element.attrib.get(name) or element.attrib.get(f"{{http://nite.sourceforge.net/}}{name}")


def words_for_segment(href: str, words: dict[str, dict]) -> list[dict]:
    match = re.fullmatch(r"[^#]+#id\(([^)]+)\)(?:\.\.id\(([^)]+)\))?", href)
    if not match:
        raise ValueError(f"unresolved or malformed NXT word href: {href!r}")
    first, last = match.group(1), match.group(2) or match.group(1)
    keys = list(words)
    try:
        start, end = keys.index(first), keys.index(last)
    except ValueError:
        raise ValueError(f"NXT word href references an absent word: {href!r}")
    if end < start:
        raise ValueError(f"NXT word href reverses source order: {href!r}")
    selected = [words[key] for key in keys[start : end + 1]]
    filename = Path(href.split("#", 1)[0]).name
    if any(Path(word["source_file"]).name != filename for word in selected):
        raise ValueError(f"NXT word href crosses its declared source file: {href!r}")
    return selected


def href_parts(href: str) -> tuple[str, str]:
    match = re.fullmatch(r"([^#]+)#id\(([^)]+)\)", href)
    if not match:
        raise ValueError(f"malformed NXT pointer href: {href!r}")
    return match.group(1), match.group(2)


def pointer_records(element: ElementTree.Element) -> list[dict]:
    return [
        {"role": pointer.attrib.get("role"), "href": attr(pointer, "href"), "source_attributes": dict(pointer.attrib)}
        for pointer in element
        if pointer.tag.rsplit("}", 1)[-1] == "pointer"
    ]


def exact_clock(value: str, label: str) -> str:
    try:
        parsed = Decimal(value)
    except InvalidOperation as error:
        raise ValueError(f"invalid {label} clock value: {value!r}") from error
    if not parsed.is_finite() or parsed < 0:
        raise ValueError(f"invalid {label} clock value: {value!r}")
    return value


def extract_turns(annotation_root: Path, sessions: list[str], audio_durations: dict[str, Decimal]) -> tuple[list[dict], dict, dict[str, dict]]:
    meetings = ElementTree.parse(annotation_root / "corpusResources/meetings.xml").getroot()
    speakers: dict[str, dict[str, dict]] = {}
    meeting_metadata: dict[str, dict] = {}
    for meeting in meetings.findall("meeting"):
        observation = meeting.attrib.get("observation")
        if observation not in sessions:
            continue
        meeting_metadata[observation] = dict(meeting.attrib)
        speakers[observation] = {
            speaker.attrib["nxt_agent"]: {
                "agent": speaker.attrib["nxt_agent"],
                "channel": int(speaker.attrib["channel"]),
                "global_name": speaker.attrib.get("global_name"),
                "role": speaker.attrib.get("role"),
                "source_attributes": dict(speaker.attrib),
            }
            for speaker in meeting.findall("speaker")
        }

    turns: list[dict] = []
    all_words: dict[str, dict] = {}
    for session in sessions:
        for segment_path in sorted((annotation_root / "segments").glob(f"{session}.*.segments.xml")):
            agent = segment_path.name.split(".")[1]
            word_path = annotation_root / "words" / f"{session}.{agent}.words.xml"
            words: dict[str, dict] = {}
            for element in ElementTree.parse(word_path).getroot():
                identifier = attr(element, "id")
                if not identifier:
                    continue
                if identifier in all_words:
                    raise ValueError(f"duplicate source word ID: {identifier}")
                words[identifier] = {
                    "id": identifier,
                    "kind": element.tag.rsplit("}", 1)[-1],
                    "text": element.text or "",
                    "start": exact_clock(element.attrib["starttime"], "word start"),
                    "end": exact_clock(element.attrib["endtime"], "word end"),
                    "punctuation": element.attrib.get("punc") == "true",
                    "source_attributes": dict(element.attrib),
                    "source_file": str(word_path.relative_to(annotation_root)),
                    **({"vocal_type": element.attrib["type"]} if "type" in element.attrib else {}),
                }
                all_words[identifier] = words[identifier]
                word = words[identifier]
                word["clock_refusal"] = (
                    "source word interval is reversed" if Decimal(word["end"]) < Decimal(word["start"])
                    else "source word interval is outside WAV" if max(Decimal(word["start"]), Decimal(word["end"])) > audio_durations[session]
                    else None
                )
            for segment in ElementTree.parse(segment_path).getroot().findall("segment"):
                children = list(segment)
                href = attr(children[0], "href") if children else ""
                if not href:
                    raise ValueError(f"segment has no NXT child word href: {segment_path}:{attr(segment, 'id')}")
                segment_words = words_for_segment(href, words)
                start = exact_clock(segment.attrib["transcriber_start"], "segment start")
                end = exact_clock(segment.attrib["transcriber_end"], "segment end")
                if Decimal(end) < Decimal(start) or Decimal(end) > audio_durations[session]:
                    raise ValueError(f"segment clock is outside its WAV extent: {session} {start}..{end} > {audio_durations[session]}")
                turns.append(
                    {
                        "session": session,
                        "audio_file": f"audio/{session}.Mix-Headset.wav",
                        "speaker_agent": agent,
                        "speaker": speakers.get(session, {}).get(agent),
                        "start": start,
                        "end": end,
                        "transcript": " ".join(word["text"] for word in segment_words),
                        "words": segment_words,
                        "clock_refusals": [{"word": word["id"], "refusal": word["clock_refusal"]} for word in segment_words if word["clock_refusal"]],
                        "source_segment_id": attr(segment, "id"),
                        "source_segment_file": str(segment_path.relative_to(annotation_root)),
                        "source_segment_attributes": dict(segment.attrib),
                        "source_word_file": str(word_path.relative_to(annotation_root)),
                        "source_word_href": href,
                    }
                )
    return sorted(turns, key=lambda row: (row["session"], Decimal(row["start"]), row["speaker_agent"])), {"meetings": meeting_metadata}, all_words


def extract_dialogue_graph(annotation_root: Path, sessions: list[str], words: dict[str, dict], audio_durations: dict[str, Decimal]) -> tuple[list[dict], dict]:
    acts: dict[tuple[str, str], dict] = {}
    type_records: dict[str, dict] = {}
    for ontology_name in ("ontologies/ap-types.xml", "ontologies/da-types.xml"):
        root = ElementTree.parse(annotation_root / ontology_name).getroot()
        for element in root.iter():
            identifier = attr(element, "id")
            if identifier:
                type_records[identifier] = {"id": identifier, "name": element.attrib.get("name"), "gloss": element.attrib.get("gloss"), "source_attributes": dict(element.attrib), "source_file": ontology_name}
    for session in sessions:
        for path in sorted((annotation_root / "dialogueActs").glob(f"{session}.*.dialog-act.xml")):
            filename = path.name
            agent = filename.split(".")[1]
            for element in ElementTree.parse(path).getroot().findall("dact"):
                identifier = attr(element, "id")
                if not identifier:
                    raise ValueError(f"dialogue act has no source ID: {path}")
                children = [child for child in element if child.tag.rsplit("}", 1)[-1] == "child"]
                href = attr(children[0], "href") if len(children) == 1 else None
                if not href:
                    raise ValueError(f"dialogue act must have exactly one word span: {path}:{identifier}")
                act_words = words_for_segment(href, words)
                if not act_words:
                    raise ValueError(f"dialogue act word span did not resolve: {path}:{identifier}")
                start = min((act_word["start"] for act_word in act_words), key=Decimal)
                end = max((act_word["end"] for act_word in act_words), key=Decimal)
                if Decimal(end) > audio_durations[session]:
                    raise ValueError(f"dialogue act lies outside WAV: {session}:{identifier}")
                aspects = [pointer for pointer in pointer_records(element) if pointer["role"] == "da-aspect"]
                if len(aspects) > 1:
                    raise ValueError(f"dialogue act has multiple da-aspect pointers: {path}:{identifier}")
                annotation_type = None
                if aspects:
                    ontology_file, ontology_id = href_parts(aspects[0]["href"] or "")
                    annotation_type = type_records.get(ontology_id, {"id": ontology_id, "source_file": ontology_file})
                acts[(filename, identifier)] = {
                    "dialog_act_id": identifier,
                    "speaker_agent": agent,
                    "speaker": speakers_for_graph(session, agent, annotation_root),
                    "start": start,
                    "end": end,
                    "transcript": " ".join(word["text"] for word in act_words),
                    "word_ids": [word["id"] for word in act_words],
                    "clock_refusals": [{"word": word["id"], "refusal": word["clock_refusal"]} for word in act_words if word["clock_refusal"]],
                    "source_file": str(path.relative_to(annotation_root)),
                    "source_attributes": dict(element.attrib),
                    "source_word_href": href,
                    "source_pointers": pointer_records(element),
                    "annotation_type": annotation_type,
                }
    links: list[dict] = []
    for session in sessions:
        for path in sorted((annotation_root / "dialogueActs").glob(f"{session}.adjacency-pairs.xml")):
            for pair in ElementTree.parse(path).getroot().findall("adjacency-pair"):
                pair_id = attr(pair, "id")
                pointers = pointer_records(pair)
                role_map = {pointer["role"]: pointer for pointer in pointers}
                if not pair_id:
                    raise ValueError(f"adjacency pair has no source ID: {path}")
                if len(role_map) != len(pointers):
                    links.append({"session": session, "adjacency_pair_id": pair_id, "source_file": str(path.relative_to(annotation_root)), "source_attributes": dict(pair.attrib), "source_pointers": pointers, "resolution_status": "refused-repeated-pointer-role", "refusal": "repeated role cannot select one pointer"})
                    continue
                missing_roles = [role for role in ("source", "target", "type") if role not in role_map]
                if missing_roles:
                    links.append({"session": session, "adjacency_pair_id": pair_id, "source_file": str(path.relative_to(annotation_root)), "source_attributes": dict(pair.attrib), "source_pointers": pointers, "resolution_status": "refused-incomplete-pointers", "refusal": f"missing roles: {missing_roles}"})
                    continue
                endpoints = {}
                refusal = None
                for role in ("source", "target"):
                    try:
                        filename, identifier = href_parts(role_map[role]["href"] or "")
                    except ValueError as error:
                        refusal = str(error)
                        break
                    endpoint = acts.get((filename, identifier))
                    if endpoint is None:
                        refusal = f"adjacency pair endpoint did not resolve: {path}:{pair_id}:{role}"
                        break
                    endpoints[role] = endpoint
                if refusal:
                    links.append({"session": session, "adjacency_pair_id": pair_id, "source_file": str(path.relative_to(annotation_root)), "source_attributes": dict(pair.attrib), "source_pointers": pointers, "resolution_status": "refused-unresolved-endpoint", "refusal": refusal})
                    continue
                try:
                    type_file, type_id = href_parts(role_map["type"]["href"] or "")
                except ValueError as error:
                    links.append({"session": session, "adjacency_pair_id": pair_id, "source_file": str(path.relative_to(annotation_root)), "source_attributes": dict(pair.attrib), "source_pointers": pointers, "resolution_status": "refused-malformed-type", "refusal": str(error)})
                    continue
                links.append({
                    "session": session,
                    "adjacency_pair_id": pair_id,
                    "source": endpoints["source"],
                    "target": endpoints["target"],
                    "link_type": type_records.get(type_id, {"id": type_id, "source_file": type_file}),
                    "source_file": str(path.relative_to(annotation_root)),
                    "source_attributes": dict(pair.attrib),
                    "source_pointers": pointers,
                    "resolution_status": "refused-invalid-source-clock" if any(endpoint["clock_refusals"] for endpoint in endpoints.values()) else "resolved-direct-source-pointer",
                })
    return links, {"dialogue_act_count": len(acts), "adjacency_pair_count": len(links), "resolved_count": sum(link["resolution_status"] == "resolved-direct-source-pointer" for link in links), "refused_count": sum(link["resolution_status"].startswith("refused-") for link in links), "type_records": len(type_records)}


def speakers_for_graph(session: str, agent: str, annotation_root: Path) -> dict | None:
    root = ElementTree.parse(annotation_root / "corpusResources/meetings.xml").getroot()
    for meeting in root.findall("meeting"):
        if meeting.attrib.get("observation") == session:
            for speaker in meeting.findall("speaker"):
                if speaker.attrib.get("nxt_agent") == agent:
                    return {"agent": agent, "channel": int(speaker.attrib["channel"]), "global_name": speaker.attrib.get("global_name"), "role": speaker.attrib.get("role"), "source_attributes": dict(speaker.attrib)}
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(".local/datasets/ami-conversation-es2002"))
    parser.add_argument("--sessions", nargs="+", default=["ES2002a", "ES2002b", "ES2002c", "ES2002d"])
    parser.add_argument("--rebuild-existing", action="store_true", help="preserve v1 indexes and write the revised exact-clock index")
    args = parser.parse_args()
    if any(not re.fullmatch(r"ES2002[abcd]", session) for session in args.sessions):
        parser.error("this bounded acquisition only admits ES2002a-d")
    if args.output.exists() and (args.output / "provenance.json").exists() and not args.rebuild_existing:
        raise SystemExit(f"refusing an existing completed dataset: {args.output}")
    args.output.mkdir(parents=True, exist_ok=True)
    archive = args.output / "source" / "ami_public_manual_1.6.2.zip"
    download(ANNOTATION_URL, archive)
    annotation_root = args.output / "annotations"
    annotation_root.mkdir(exist_ok=True)
    with zipfile.ZipFile(archive) as bundle:
        if bundle.testzip() is not None:
            raise RuntimeError(f"annotation archive failed CRC validation: {archive}")
        wanted = [name for name in bundle.namelist() if name in {"LICENCE.txt", "00README_MANUAL.txt", "corpusResources/meetings.xml", "ontologies/ap-types.xml", "ontologies/da-types.xml"}]
        wanted += [name for name in bundle.namelist() if any(name.startswith(f"{kind}/{session}.") for kind in ("segments", "words", "dialogueActs") for session in args.sessions)]
        for name in sorted(set(wanted)):
            destination = annotation_root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(bundle.read(name))
    audio_records = []
    audio_durations: dict[str, Decimal] = {}
    for session in args.sessions:
        url = f"{BASE}/AMICorpusMirror//amicorpus/{session}/audio/{session}.Mix-Headset.wav"
        path = args.output / "audio" / f"{session}.Mix-Headset.wav"
        download(url, path)
        with wave.open(str(path), "rb") as source:
            if (source.getnchannels(), source.getsampwidth(), source.getframerate()) != (1, 2, 16000):
                raise ValueError(f"unexpected AMI Mix-Headset WAV format: {path}")
            frames = source.getnframes()
            duration = Decimal(frames) / Decimal(source.getframerate())
            payload_bytes = 0
            while block := source.readframes(524288):
                payload_bytes += len(block)
            if payload_bytes != frames * source.getsampwidth() * source.getnchannels():
                raise ValueError(f"truncated WAV payload: {path}")
        audio_durations[session] = duration
        audio_records.append({"session": session, "url": url, "path": str(path), "sha256": sha256(path), "bytes": path.stat().st_size, "channels": 1, "sample_width_bytes": 2, "sample_rate": 16000, "frames": frames, "duration_seconds_exact": str(duration)})
    turns, source_metadata, all_words = extract_turns(annotation_root, args.sessions, audio_durations)
    response_links, graph_stats = extract_dialogue_graph(annotation_root, args.sessions, all_words, audio_durations)
    index_name = "turns.exact.jsonl"
    old_index = args.output / "turns.jsonl"
    if args.rebuild_existing and old_index.exists() and not (args.output / "turns.v1.float.jsonl").exists():
        copyfile(old_index, args.output / "turns.v1.float.jsonl")
    exact_index = args.output / "turns.exact.jsonl"
    if args.rebuild_existing and exact_index.exists() and not (args.output / "turns.exact.v2.jsonl").exists():
        copyfile(exact_index, args.output / "turns.exact.v2.jsonl")
    with (args.output / index_name).open("w", encoding="utf-8") as stream:
        for turn in turns:
            stream.write(json.dumps(turn, ensure_ascii=False) + "\n")
    links_index = args.output / "response-links.exact.jsonl"
    if args.rebuild_existing and links_index.exists() and not (args.output / "response-links.exact.v3.jsonl").exists():
        copyfile(links_index, args.output / "response-links.exact.v3.jsonl")
    with links_index.open("w", encoding="utf-8") as stream:
        for link in response_links:
            stream.write(json.dumps(link, ensure_ascii=False) + "\n")
    old_provenance = args.output / "provenance.json"
    if args.rebuild_existing and old_provenance.exists() and not (args.output / "provenance.v2.json").exists():
        copyfile(old_provenance, args.output / "provenance.v2.json")
    provenance = {
        "schema": "holonics.apple.ami-conversation-subset.v3",
        "source": "AMI Meeting Corpus official Edinburgh distribution",
        "source_word_clock_refusals": [{"word": word["id"], "refusal": word["clock_refusal"]} for word in all_words.values() if word["clock_refusal"]],
        "source_url": "https://groups.inf.ed.ac.uk/ami/corpus/",
        "download_url": "https://groups.inf.ed.ac.uk/ami/download/",
        "license": "Creative Commons Attribution 4.0 International (CC BY 4.0)",
        "manual_annotation_release": "ami_public_manual_1.6.2 (10-Apr-2017)",
        "manual_annotation_sha256": sha256(archive),
        "sessions": args.sessions,
        "audio": audio_records,
        "audio_stream": "Mix-Headset single WAV per meeting; original source file retained",
        "turn_index": {"path": str(args.output / index_name), "count": len(turns), "speaker_agents": sorted({turn["speaker_agent"] for turn in turns}), "clock_representation": "exact source decimal strings"},
        "response_links": {"path": str(links_index), **graph_stats, "link_semantics": "direct source/target pointers from original adjacency-pairs XML; no adjacency inference"},
        "meeting_source_metadata": source_metadata["meetings"],
        "audio_bounds_validation": {"segments_and_words_checked_against_audio_duration": True, "out_of_audio_range_count": 0},
        "partition": "official meetings.xml marks ES2002a-d seen_type=training; no external evaluation split claim is made",
        "synthetic_labels_or_audio": False,
        "models_or_repository_code_executed": False,
    }
    (args.output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "sessions": len(args.sessions), "turns": len(turns), "response_links": len(response_links), "audio_bytes": sum(item["bytes"] for item in audio_records)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
