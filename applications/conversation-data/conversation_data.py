#!/usr/bin/env python3
"""Private, source-preserving Claude Code/Codex material. No learner or evaluator lives here."""
from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import os
from pathlib import Path
import sqlite3
import sys
import tempfile
import zlib

from providers import decode

SCHEMA = "holonics.conversation-data.v1"

DDL = """
PRAGMA foreign_keys=ON;
CREATE TABLE metadata(key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE sources(
 id INTEGER PRIMARY KEY, provider TEXT NOT NULL, path TEXT NOT NULL,
 captured_octets INTEGER NOT NULL, mtime_ns INTEGER NOT NULL,
 records INTEGER NOT NULL DEFAULT 0, context TEXT NOT NULL DEFAULT '{}');
CREATE TABLE events(
 id INTEGER PRIMARY KEY, source INTEGER NOT NULL REFERENCES sources(id),
 record_number INTEGER NOT NULL, byte_start INTEGER NOT NULL, byte_end INTEGER NOT NULL,
 timestamp TEXT, native_id TEXT, parent_id TEXT, session_id TEXT, branch_id TEXT,
 workspace TEXT, phase TEXT, turn_id TEXT, model TEXT, author_class TEXT NOT NULL,
 record_kind TEXT NOT NULL, flags TEXT NOT NULL, provider_metadata TEXT NOT NULL,
 previous_record INTEGER REFERENCES events(id),
 raw_zlib BLOB NOT NULL, UNIQUE(source,record_number));
CREATE TABLE parts(
 event INTEGER NOT NULL REFERENCES events(id), ordinal INTEGER NOT NULL,
 pointer TEXT NOT NULL, kind TEXT NOT NULL, text TEXT,
 PRIMARY KEY(event,ordinal));
CREATE TABLE tool_ports(
 event INTEGER NOT NULL REFERENCES events(id), direction TEXT NOT NULL,
 call_id TEXT NOT NULL, name TEXT, pointer TEXT NOT NULL);
CREATE TABLE links(
 source_event INTEGER NOT NULL REFERENCES events(id), target_event INTEGER REFERENCES events(id),
 kind TEXT NOT NULL, reference TEXT, evidence TEXT NOT NULL,
 UNIQUE(source_event,target_event,kind,reference));
CREATE TABLE comparisons(
 user_event INTEGER NOT NULL REFERENCES events(id), agent_event INTEGER NOT NULL REFERENCES events(id),
 evidence TEXT NOT NULL, PRIMARY KEY(user_event,agent_event));
CREATE TABLE annotations(
 id INTEGER PRIMARY KEY, author TEXT NOT NULL, truth_status TEXT NOT NULL,
 kind TEXT NOT NULL, label TEXT NOT NULL, event INTEGER NOT NULL REFERENCES events(id),
 target_event INTEGER REFERENCES events(id), pointer TEXT, rationale TEXT NOT NULL,
 created_at TEXT NOT NULL);
CREATE INDEX event_native ON events(source,native_id);
CREATE INDEX event_native_global ON events(native_id,source);
CREATE INDEX event_author ON events(author_class);
CREATE INDEX event_scope ON events(session_id,branch_id);
CREATE INDEX part_kind ON parts(kind,event);
CREATE INDEX port_key ON tool_ports(call_id,direction,event);
CREATE VIEW group_characteristics AS
 SELECT s.provider,e.session_id,e.branch_id,e.workspace,e.model,e.phase,e.author_class,
        COUNT(*) AS occurrences
 FROM events e JOIN sources s ON s.id=e.source
 GROUP BY s.provider,e.session_id,e.branch_id,e.workspace,e.model,e.phase,e.author_class;
CREATE VIEW declared_record_views AS
 SELECT s.provider,e.native_id,COUNT(*) AS representations
 FROM events e JOIN sources s ON s.id=e.source WHERE e.native_id IS NOT NULL
 GROUP BY s.provider,e.native_id;
CREATE VIEW comparison_groups AS
 SELECT s.provider,
        CASE WHEN u.native_id IS NULL THEN 'capture:' || u.id ELSE 'declared:' || u.native_id END AS user_group,
        CASE WHEN a.native_id IS NULL THEN 'capture:' || a.id ELSE 'declared:' || a.native_id END AS agent_group,
        COUNT(*) AS observed_views
 FROM comparisons c JOIN events u ON u.id=c.user_event JOIN events a ON a.id=c.agent_event
 JOIN sources s ON s.id=u.source GROUP BY s.provider,user_group,agent_group;
CREATE VIEW agent_generations AS
 SELECT s.provider,e.session_id,e.branch_id,json_extract(e.provider_metadata,'$.api_message_id') AS generation,
        COUNT(*) AS captured_records
 FROM events e JOIN sources s ON s.id=e.source
 WHERE json_extract(e.provider_metadata,'$.api_message_id') IS NOT NULL
 GROUP BY s.provider,e.session_id,e.branch_id,generation;
CREATE VIEW declared_branch_origins AS
 SELECT DISTINCT s.id AS source,s.provider,e.session_id,e.branch_id,
        json_extract(e.provider_metadata,'$.parent_session') AS parent_session,
        json_extract(e.provider_metadata,'$.agent_path') AS agent_path
 FROM events e JOIN sources s ON s.id=e.source
 WHERE json_extract(e.provider_metadata,'$.parent_session') IS NOT NULL;
"""


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def dump(value) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def connect(path: Path, writable=False) -> sqlite3.Connection:
    if writable:
        db = sqlite3.connect(path)
    else:
        db = sqlite3.connect(f"{path.resolve().as_uri()}?mode=ro", uri=True)
    db.row_factory = sqlite3.Row
    return db


def discover(inputs: list[tuple[str, Path]]) -> list[tuple[str, Path, os.stat_result]]:
    captured = {}
    for provider, root in inputs:
        paths = sorted(root.rglob("*.jsonl")) if root.is_dir() else [root]
        for path in paths:
            path = path.resolve()
            stat = path.stat()
            if not path.is_file():
                raise ValueError(f"not a regular source: {path}")
            if path in captured and captured[path][0] != provider:
                raise ValueError(f"two provider declarations for {path}")
            captured[path] = (provider, path, stat)
    return [captured[p] for p in sorted(captured)]


def private_output(path: Path):
    """Create a new private artifact; no existing destination is replaced."""
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    return os.fdopen(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600), "w", encoding="utf-8")


def package(inputs: list[tuple[str, Path]], output: Path) -> dict:
    if output.exists():
        raise FileExistsError(output)
    captured = discover(inputs)  # Every prefix boundary precedes processing/output activity.
    if not captured:
        raise ValueError("no JSONL source files")
    output.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    fd, temporary = tempfile.mkstemp(prefix=f".{output.name}.partial-", dir=output.parent)
    os.close(fd)
    db = sqlite3.connect(temporary)
    db.execute("PRAGMA cache_size=-32768")
    db.execute("PRAGMA temp_store=FILE")
    db.executescript(DDL)
    db.executemany("INSERT INTO metadata VALUES (?,?)", [
        ("schema", dump(SCHEMA)), ("created_at", dump(now())),
        ("privacy", dump("private local material; raw records may contain sensitive data")),
        ("comparison", dump("actual human request and responding agent; no default scalar/gold/preference")),
        ("source_capture", dump("bounded prefixes of append-only logs; raw consumed bytes retained")),
    ])
    try:
        for number, (provider, path, stat) in enumerate(captured, 1):
            source = db.execute("INSERT INTO sources(provider,path,captured_octets,mtime_ns) VALUES (?,?,?,?)",
                                (provider, str(path), stat.st_size, stat.st_mtime_ns)).lastrowid
            context = {"source_key": f"source:{source}",
                       "file_branch_hint": path.name.startswith("agent-") or "subagents" in path.parts}
            _import_source(db, source, provider, path, stat, context)
            db.commit()
            if number == 1 or number % 25 == 0 or number == len(captured):
                print(dump({"prepared_sources": number, "total_sources": len(captured)}), file=sys.stderr, flush=True)
        _normalize_part_roles(db)
        _link_tool_returns(db)
        _link_cross_source_parents(db)
        db.execute("INSERT INTO metadata VALUES (?,?)", ("completed_at", dump(now())))
        db.commit()
        if db.execute("PRAGMA foreign_key_check").fetchone() is not None:
            raise ValueError("dataset reference reconstruction failed")
        db.close()
        with open(temporary, "rb") as handle:
            os.fsync(handle.fileno())
        os.link(temporary, output)  # atomic no-overwrite publication
        os.unlink(temporary)       # only our newly created staging file
        directory = os.open(output.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
        return summary(output)
    except BaseException:
        db.close()
        print(f"Unpublished/recoverable preparation retained at {temporary}", file=sys.stderr)
        raise


def _prefix_records(path, stat):
    with path.open("rb") as handle:
        opened = os.fstat(handle.fileno())
        if (opened.st_dev, opened.st_ino) != (stat.st_dev, stat.st_ino):
            raise ValueError(f"source replaced before capture: {path}")
        remaining=stat.st_size
        while remaining:
            raw=handle.readline(remaining)
            if not raw:
                raise ValueError(f"source truncated inside captured prefix: {path}")
            remaining-=len(raw)
            yield None,raw


def reproject(input_path:Path,output:Path):
    """Refine derived views from the SAME captured records; never recapture a growing source."""
    if output.exists():
        raise FileExistsError(output)
    output.parent.mkdir(parents=True,exist_ok=True,mode=0o700)
    fd,temporary=tempfile.mkstemp(prefix=f".{output.name}.partial-",dir=output.parent)
    os.close(fd)
    from types import SimpleNamespace
    original=connect(input_path)
    revised=sqlite3.connect(temporary)
    try:
        original.backup(revised)
        revised.execute("PRAGMA foreign_keys=ON")
        for table in ("parts","tool_ports","comparisons"):
            revised.execute(f"DELETE FROM {table}")
        revised.execute("DROP TABLE links")
        revised.execute("""CREATE TABLE links(source_event INTEGER NOT NULL REFERENCES events(id),
            target_event INTEGER REFERENCES events(id),kind TEXT NOT NULL,reference TEXT,evidence TEXT NOT NULL,
            UNIQUE(source_event,target_event,kind,reference))""")
        revised.commit()
        sources=original.execute("SELECT * FROM sources ORDER BY id").fetchall()
        for number,source in enumerate(sources,1):
            path=Path(source["path"])
            context={"source_key":f"source:{source['id']}",
                     "file_branch_hint":path.name.startswith("agent-") or "subagents" in path.parts}
            records=((row[0],zlib.decompress(row[1])) for row in original.execute(
                "SELECT id,raw_zlib FROM events WHERE source=? ORDER BY record_number",(source["id"],)))
            _import_source(revised,source["id"],source["provider"],path,
                           SimpleNamespace(st_size=source["captured_octets"]),context,records)
            revised.commit()
            if number==1 or number%100==0 or number==len(sources):
                print(dump({"reprojected_sources":number,"total_sources":len(sources)}),file=sys.stderr,flush=True)
        _normalize_part_roles(revised)
        _link_tool_returns(revised)
        _link_cross_source_parents(revised)
        revised.execute("INSERT OR REPLACE INTO metadata VALUES (?,?)",("projection_updated_at",dump(now())))
        revised.execute("INSERT OR REPLACE INTO metadata VALUES (?,?)",("projection_source",dump(str(input_path))))
        revised.commit()
        if revised.execute("PRAGMA foreign_key_check").fetchone() is not None:
            raise ValueError("reprojected dataset references do not reconstruct")
        original.close();revised.close()
        with open(temporary,"rb") as handle:
            os.fsync(handle.fileno())
        os.link(temporary,output)
        os.unlink(temporary)
        directory=os.open(output.parent,os.O_RDONLY)
        try:os.fsync(directory)
        finally:os.close(directory)
        return summary(output)
    except BaseException:
        original.close();revised.close()
        print(f"Unpublished/recoverable projection retained at {temporary}",file=sys.stderr)
        raise


def _import_source(db, source, provider, path, stat, context, records=None):
    previous = None
    active_human = {}
    active_agent = {}
    declared = {}
    nearest_human = {}
    nearest_agent = {}
    record_number = 0
    at = 0
    for existing,raw in records if records is not None else _prefix_records(path,stat):
        record_number += 1
        end = at + len(raw)
        try:
            record = json.loads(raw)
            if not isinstance(record, dict):
                raise ValueError("record is not an object")
            normalized = decode(provider, record, context)
            kind = str(record.get("type", "unknown"))
        except (json.JSONDecodeError, UnicodeDecodeError, ValueError) as error:
            normalized = {"author_class": "unknown", "parts": [], "calls": [], "results": [],
                          "flags": ["unparsed-record", type(error).__name__]}
            record = {}
            kind = "partial-tail" if end == stat.st_size and not raw.endswith(b"\n") else "malformed-record"
        columns=[]
        for key in ["native_id", "parent_id", "session_id", "branch_id", "workspace", "phase", "turn_id", "model"]:
            value=normalized.get(key)
            if value is not None and not isinstance(value,str):
                normalized.setdefault("flags",[]).append(f"non-string-metadata:{key}")
                value=None
            normalized[key]=value
            columns.append(value)
        parts=normalized.get("parts",[])
        for part in parts:
            if isinstance(part.get("text"),str):
                try:
                    part["text"].encode("utf-8")
                except UnicodeEncodeError:
                    part["text"]=None
                    normalized.setdefault("flags",[]).append(f"unrepresentable-text:{part['pointer']}")
        if existing is None:
            event = db.execute("""INSERT INTO events(source,record_number,byte_start,byte_end,timestamp,
            native_id,parent_id,session_id,branch_id,workspace,phase,turn_id,model,author_class,
            record_kind,flags,provider_metadata,previous_record,raw_zlib) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (source, record_number, at, end, record.get("timestamp"), *columns,
             normalized.get("author_class", "unknown"), kind, dump(normalized.get("flags", [])),
             dump({k:v for k,v in normalized.items() if k not in {"parts","calls","results","flags"}}),
                 previous, sqlite3.Binary(zlib.compress(raw, 1)))).lastrowid
        else:
            event=existing
            db.execute("""UPDATE events SET timestamp=?,native_id=?,parent_id=?,session_id=?,branch_id=?,workspace=?,
                phase=?,turn_id=?,model=?,author_class=?,record_kind=?,flags=?,provider_metadata=?,previous_record=? WHERE id=?""",
                (record.get("timestamp"),*columns,normalized.get("author_class","unknown"),kind,dump(normalized.get("flags",[])),
                 dump({k:v for k,v in normalized.items() if k not in {"parts","calls","results","flags"}}),previous,event))
        for ordinal, part in enumerate(normalized.get("parts", [])):
            db.execute("INSERT INTO parts VALUES (?,?,?,?,?)",
                       (event, ordinal, part["pointer"], part["kind"], part.get("text")))
        for direction in ("calls", "results"):
            for port in normalized.get(direction, []):
                if isinstance(port.get("call_id"),str) and port["call_id"]:
                    db.execute("INSERT INTO tool_ports VALUES (?,?,?,?,?)",
                               (event, direction, port["call_id"], port.get("name") if isinstance(port.get("name"),str) else None, port["pointer"]))
        parent_id = normalized.get("parent_id")
        scope=(normalized.get("session_id") or f"source:{source}",normalized.get("branch_id") or "main")
        parent = declared.get((scope,parent_id)) if parent_id else None
        if parent_id:
            db.execute("INSERT INTO links VALUES (?,?,?,?,?)", (event, parent, "provider-parent", parent_id,
                       "declared parent; unresolved is not replaced by adjacency"))
            anchor = nearest_human.get(parent) if parent is not None else None
            prior_agent = nearest_agent.get(parent) if parent is not None else None
            evidence = "provider-parent-chain"
        else:
            anchor = active_human.get(scope)
            prior_agent = active_agent.get(scope)
            evidence = "same-conversation-and-branch-visible-order; not semantic feedback attribution"
        author = normalized.get("author_class")
        if author == "human" and normalized.get("human_comparison_eligible",True) and any(p["kind"] in {"human-text","human-material","human-command"} for p in normalized.get("parts", [])):
            # A later human message remains a later return, not a guessed reward/correction.
            active_human[scope] = event
            anchor = event
            if prior_agent is not None:
                db.execute("INSERT INTO links VALUES (?,?,?,?,?)",(event,prior_agent,"later-human-after-agent",None,
                    evidence+"; no automatic approval, correction or topic-continuity judgment"))
        elif author == "agent-visible" and normalized.get("human_comparison_eligible",True) and any(p["kind"] in {"agent-text","agent-material"} for p in normalized.get("parts", [])):
            if anchor is not None:
                db.execute("INSERT OR IGNORE INTO comparisons VALUES (?,?,?)", (anchor, event, evidence))
            active_agent[scope]=event
            prior_agent=event
        nearest_human[event] = anchor
        nearest_agent[event] = prior_agent
        if normalized.get("native_id"):
            declared[(scope,normalized["native_id"])] = event
        previous = event
        at = end
        if record_number % 2048 == 0:
            db.commit()
    db.execute("UPDATE sources SET records=?,context=? WHERE id=?", (record_number, dump(context), source))


def _normalize_part_roles(db):
    # User-role context in a worker is not labelled as new human-authored material.
    db.execute("""UPDATE parts SET kind='branch-input-text' WHERE kind='human-text'
        AND event IN (SELECT id FROM events WHERE author_class='branch-input')""")
    db.execute("""UPDATE parts SET kind='branch-input-material' WHERE kind='human-material'
        AND event IN (SELECT id FROM events WHERE author_class='branch-input')""")


def _link_tool_returns(db):
    # Keep the complete block-level incidence. Reused/ambiguous IDs do not select a producer.
    db.execute("""CREATE TEMP TABLE call_candidates AS
        SELECT r.event AS result,r.pointer AS result_pointer,c.event AS caller,c.pointer AS call_pointer,r.call_id
        FROM tool_ports r CROSS JOIN tool_ports c INDEXED BY port_key
        CROSS JOIN events re CROSS JOIN events ce
        WHERE r.direction='results' AND c.direction='calls' AND re.source=ce.source
        AND c.call_id=r.call_id AND re.id=r.event AND ce.id=c.event
        AND coalesce(re.session_id,'')=coalesce(ce.session_id,'')
        AND coalesce(re.branch_id,'main')=coalesce(ce.branch_id,'main')
        AND ce.record_number<re.record_number""")
    db.execute("CREATE INDEX candidate_result ON call_candidates(result,result_pointer)")
    db.execute("""INSERT OR IGNORE INTO links(source_event,target_event,kind,reference,evidence)
        SELECT a.result,a.caller,
        CASE WHEN (SELECT count(*) FROM call_candidates b WHERE b.result=a.result AND b.result_pointer=a.result_pointer)=1
             THEN 'tool-result-of' ELSE 'tool-result-candidate' END,
        json_object('call_id',a.call_id,'result_pointer',a.result_pointer,'call_pointer',a.call_pointer),
        'provider call-id in source/session/branch; complete part incidence'
        FROM call_candidates a""")
    db.execute("""INSERT INTO links(source_event,target_event,kind,reference,evidence)
        SELECT r.event,NULL,'tool-result-of',json_object('call_id',r.call_id,'result_pointer',r.pointer),
        'unresolved or ambiguous call; no producer selected'
        FROM tool_ports r WHERE r.direction='results' AND NOT EXISTS
        (SELECT 1 FROM call_candidates a WHERE a.result=r.event AND a.result_pointer=r.pointer
         GROUP BY a.result,a.result_pointer HAVING count(*)=1)""")
    db.execute("DROP TABLE call_candidates")


def _link_cross_source_parents(db):
    # Preserve candidate correspondence fibres. Shared session membership alone is not parentage.
    db.execute("""INSERT OR IGNORE INTO links(source_event,target_event,kind,reference,evidence)
        SELECT l.source_event,p.id,'parent-candidate',l.reference,'same declared provider UUID; cross-source view'
        FROM links l JOIN events e ON e.id=l.source_event JOIN sources s ON s.id=e.source
        JOIN events p ON p.native_id=l.reference AND p.id!=e.id
        JOIN sources ps ON ps.id=p.source AND ps.provider=s.provider
        WHERE l.kind='provider-parent' AND l.target_event IS NULL""")


def summary(path: Path) -> dict:
    with connect(path) as db:
        return {"schema": SCHEMA, "path": str(path), "private": True,
                "sources": db.execute("SELECT count(*) FROM sources").fetchone()[0],
                "captured_octets": db.execute("SELECT coalesce(sum(captured_octets),0) FROM sources").fetchone()[0],
                "records": db.execute("SELECT count(*) FROM events").fetchone()[0],
                "parts": dict(db.execute("SELECT kind,count(*) FROM parts GROUP BY kind").fetchall()),
                "roles": dict(db.execute("SELECT author_class,count(*) FROM events GROUP BY author_class").fetchall()),
                "user_agent_comparisons": db.execute("SELECT count(*) FROM comparisons").fetchone()[0],
                "declared_comparison_families": db.execute("SELECT count(*) FROM comparison_groups").fetchone()[0],
                "links": dict(db.execute("SELECT kind,count(*) FROM links GROUP BY kind").fetchall()),
                "unresolved_references": db.execute("SELECT count(*) FROM links WHERE target_event IS NULL").fetchone()[0],
                "annotations": db.execute("SELECT count(*) FROM annotations").fetchone()[0]}


def event_view(db, event: int) -> dict:
    row = db.execute("SELECT e.*,s.provider,s.path FROM events e JOIN sources s ON s.id=e.source WHERE e.id=?", (event,)).fetchone()
    if row is None:
        raise ValueError(f"absent event {event}")
    view = dict(row)
    del view["raw_zlib"]
    view["flags"] = json.loads(view["flags"])
    view["provider_metadata"] = json.loads(view["provider_metadata"])
    view["parts"] = [dict(p) for p in db.execute("SELECT ordinal,pointer,kind,text FROM parts WHERE event=? ORDER BY ordinal", (event,))]
    return view


def visible_view(db,event,kind):
    view=event_view(db,event)
    all_parts=view["parts"]
    visible={kind,kind.replace("-text","-material")}
    if kind=="human-text":
        visible.add("human-command")
    view["parts"]=[p for p in all_parts if p["kind"] in visible]
    view["other_part_references"]=[{k:p[k] for k in ("ordinal","pointer","kind")} for p in all_parts if p["kind"] not in visible]
    return view


def export_comparisons(path: Path, output: Path):
    with connect(path) as db, private_output(output) as target:
        # One item per declared occurrence-pair family, retaining every actual captured view.
        # No text equality merge, and no extra training weight just from repeated export views.
        rows=db.execute("""SELECT c.user_event,c.agent_event,c.evidence,s.provider,
             CASE WHEN u.native_id IS NULL THEN 'capture:' || u.id ELSE 'declared:' || u.native_id END ug,
             CASE WHEN a.native_id IS NULL THEN 'capture:' || a.id ELSE 'declared:' || a.native_id END ag
             FROM comparisons c JOIN events u ON u.id=c.user_event JOIN events a ON a.id=c.agent_event
             JOIN sources s ON s.id=u.source ORDER BY s.provider,ug,ag,u.id,a.id""")
        import itertools
        for key,observations in itertools.groupby(rows,key=lambda r:(r[3],r[4],r[5])):
            views=[]
            for user,agent,evidence,*_ in observations:
                u=visible_view(db,user,"human-text");a=visible_view(db,agent,"agent-text")
                views.append({"user":u,"agent":a,"evidence":evidence,
                    "request_parent_links":[dict(r) for r in db.execute("SELECT target_event,kind,reference,evidence FROM links WHERE source_event=? AND kind IN ('provider-parent','parent-candidate')",(user,))],
                    "recorded_context_frontier":u["previous_record"],
                    "recorded_response_interval":{"source":a["source"],"after_record":u["record_number"],
                                      "before_record":a["record_number"],"automatic_input":False,
                                      "serialization_is_not_causal_reach":True},
                    "later_user_return_is_input":False})
            target.write(dump({"schema":"holonics.user-agent-comparison.v1","declared_pair_family":key,
                               "views":views,"loss":None,"agent_response_is_gold":False})+"\n")


def export_followups(path:Path,output:Path):
    with connect(path) as db,private_output(output) as target:
        for row in db.execute("SELECT source_event,target_event,evidence FROM links WHERE kind='later-human-after-agent' ORDER BY source_event"):
            target.write(dump({"schema":"holonics.later-human-observation.v1",
                "agent":visible_view(db,row[1],"agent-text"),"later_user":visible_view(db,row[0],"human-text"),
                "evidence":row[2],"feedback_interpretation":None,
                "not_available_to_original_response":True})+"\n")


def annotate(path: Path, input_path: Path):
    """Add explicitly authored, source-addressed interpretations. They do not mutate source facts."""
    with connect(path, writable=True) as db, input_path.open() as source:
        db.execute("PRAGMA foreign_keys=ON")
        for line in source:
            value = json.loads(line)
            required = {"author","truth_status","kind","label","event","rationale"}
            if not required <= value.keys() or value["truth_status"] not in {"interpretation","definition","historical"}:
                raise ValueError("curation needs author, scoped interpretation/definition/history and source rationale")
            if not value["rationale"].strip():
                raise ValueError("curation rationale is empty")
            if value.get("pointer") is not None:
                row=db.execute("SELECT raw_zlib FROM events WHERE id=?",(value["event"],)).fetchone()
                if row is None:
                    raise ValueError("curation source event is absent")
                pointed=json.loads(zlib.decompress(row[0]))
                pointer=value["pointer"]
                if not isinstance(pointer,str) or (pointer and not pointer.startswith('/')):
                    raise ValueError("curation pointer is not an absolute JSON pointer")
                for token in pointer.split('/')[1:] if pointer else []:
                    import re
                    if re.search(r'~(?![01])',token):
                        raise ValueError("invalid JSON pointer escape")
                    token=token.replace('~1','/').replace('~0','~')
                    if isinstance(pointed,list):
                        if not re.fullmatch(r'0|[1-9][0-9]*',token):
                            raise ValueError("invalid array pointer")
                        pointed=pointed[int(token)]
                    else:
                        pointed=pointed[token]
            db.execute("INSERT INTO annotations(author,truth_status,kind,label,event,target_event,pointer,rationale,created_at) VALUES (?,?,?,?,?,?,?,?,?)",
                       (value["author"],value["truth_status"],value["kind"],value["label"],value["event"],
                        value.get("target_event"),value.get("pointer"),value["rationale"],now()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    prepare = commands.add_parser("prepare")
    prepare.add_argument("--codex", type=Path, action="append", default=[])
    prepare.add_argument("--claude", type=Path, action="append", default=[])
    prepare.add_argument("--output", type=Path, required=True)
    inspect = commands.add_parser("inspect")
    inspect.add_argument("dataset", type=Path)
    export = commands.add_parser("export-comparisons")
    export.add_argument("dataset", type=Path)
    export.add_argument("--output", type=Path, required=True)
    followups=commands.add_parser("export-followups")
    followups.add_argument("dataset",type=Path)
    followups.add_argument("--output",type=Path,required=True)
    projection=commands.add_parser("reproject")
    projection.add_argument("dataset",type=Path)
    projection.add_argument("--output",type=Path,required=True)
    annotation = commands.add_parser("annotate")
    annotation.add_argument("dataset", type=Path)
    annotation.add_argument("input", type=Path)
    args = parser.parse_args()
    if args.command == "prepare":
        result = package([*(('codex', p) for p in args.codex), *(('claude', p) for p in args.claude)], args.output)
    elif args.command == "inspect":
        result = summary(args.dataset)
    elif args.command == "annotate":
        annotate(args.dataset, args.input)
        result = summary(args.dataset)
    elif args.command=="reproject":
        result=reproject(args.dataset,args.output)
    elif args.command=="export-followups":
        export_followups(args.dataset,args.output)
        result={"output":str(args.output),"private":True}
    else:
        export_comparisons(args.dataset, args.output)
        result = {"output": str(args.output), "private": True}
    print(dump(result))


if __name__ == "__main__":
    main()
