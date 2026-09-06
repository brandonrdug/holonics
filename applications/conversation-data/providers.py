"""Small provider codecs for captured conversation records.

This module is deliberately an exterior codec.  It preserves record pointers and provider
identities; it does not hash, deduplicate, resolve parents, infer meaning, or train anything.
"""

from __future__ import annotations

from copy import deepcopy
from typing import Any


_CLASSES = {
    "human",
    "agent-visible",
    "agent-internal",
    "branch-input",
    "harness",
    "runtime",
    "unknown",
}


def _pointer(*parts: object) -> str:
    """Return a stable JSON-pointer-like location for a decoded block."""

    escaped = []
    for part in parts:
        value = str(part).replace("~", "~0").replace("/", "~1")
        escaped.append(value)
    return "/" + "/".join(escaped)


def _first(mapping: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in mapping and mapping[key] is not None:
            return mapping[key]
    return None


def _object(value: Any) -> dict[str, Any]:
    """Accept only already-decoded objects; quoted scalars remain opaque."""

    if isinstance(value, dict):
        return value
    return {}


def _nested(mapping: dict[str, Any], *paths: tuple[str, ...]) -> Any:
    for path in paths:
        value: Any = mapping
        for key in path:
            if not isinstance(value, dict) or key not in value:
                value = None
                break
            value = value[key]
        if value is not None:
            return value
    return None


def _text_part(pointer: str, kind: str, text: Any) -> dict[str, Any]:
    part: dict[str, Any] = {"pointer": pointer, "kind": kind}
    if isinstance(text, str):
        part["text"] = text
    return part


def _add_flag(result: dict[str, Any], flag: str) -> None:
    if flag not in result["flags"]:
        result["flags"].append(flag)


def _set_if(result: dict[str, Any], field: str, value: Any) -> None:
    if value is not None and value != "":
        result[field] = value


def _base() -> dict[str, Any]:
    return {
        "native_id": None,
        "parent_id": None,
        "session_id": None,
        "branch_id": None,
        "workspace": None,
        "phase": None,
        "turn_id": None,
        "model": None,
        "api_message_id": None,
        "prompt_id": None,
        "request_id": None,
        "parent_session": None,
        "agent_path": None,
        "author_class": "unknown",
        "parts": [],
        "calls": [],
        "results": [],
        "flags": [],
    }


def _origin_context(context: dict[str, Any], metadata: dict[str, Any]) -> dict[str, Any]:
    """Freeze the first Codex session metadata; child files may copy it later."""

    origin = context.get("_codex_origin_session_meta")
    identifying = {
        key: deepcopy(metadata[key])
        for key in ("id", "session_id", "sessionId", "thread_id", "thread_source", "model", "cwd")
        if key in metadata
    }
    spawn = _nested(metadata, ("source", "subagent", "thread_spawn"), ("thread_spawn",))
    if isinstance(spawn, dict):
        identifying["thread_spawn"] = deepcopy(spawn)
    if origin is None:
        origin = identifying
        context["_codex_origin_session_meta"] = origin
    elif identifying != origin:
        context["_codex_copied_session_meta_seen"] = True
    return origin


def _codex_metadata(record: dict[str, Any]) -> dict[str, Any]:
    payload = _object(record.get("payload"))
    metadata = _nested(
        record,
        ("session_meta",),
        ("sessionMeta",),
        ("payload", "session_meta"),
        ("payload", "sessionMeta"),
    )
    if isinstance(metadata, dict):
        return metadata
    # Some captured session_meta records put their fields directly in payload.
    if record.get("type") == "session_meta":
        return payload
    return {}


def _apply_codex_origin(result: dict[str, Any], origin: dict[str, Any], context: dict[str, Any]) -> None:
    if origin.get("thread_source") != "subagent" and not isinstance(origin.get("thread_spawn"), dict):
        return
    spawn = origin.get("thread_spawn")
    if not isinstance(spawn, dict):
        spawn = _nested(origin, ("source", "subagent", "thread_spawn"))
    if not isinstance(spawn, dict):
        _add_flag(result, "subagent-origin-without-spawn")
        context["_codex_branch_origin"] = True
        return
    context["_codex_branch_origin"] = True
    _add_flag(result, "subagent-origin")
    _set_if(result, "parent_session", _first(spawn, "parent_thread_id", "parentThreadId"))
    _set_if(result, "agent_path", _first(spawn, "agent_path", "agentPath"))
    _set_if(result, "branch_id", _first(spawn, "agent_path", "agentPath", "branch_id", "branchId"))


def _common_fields(
    result: dict[str, Any],
    record: dict[str, Any],
    payload: dict[str, Any],
    metadata: dict[str, Any],
    context: dict[str, Any],
) -> None:
    for field, keys in {
        "parent_id": ("parent_id", "parentId", "parent_uuid", "parentUuid"),
        "branch_id": ("branch_id", "branchId", "branch"),
        "workspace": ("workspace", "workspace_root", "workspaceRoot", "cwd", "root"),
        "phase": ("phase", "channel"),
        "turn_id": ("turn_id", "turnId"),
        "model": ("model", "model_name", "modelName"),
        "parent_session": ("parent_session", "parentSession", "parent_thread_id", "parentThreadId"),
        "agent_path": ("agent_path", "agentPath"),
    }.items():
        _set_if(
            result,
            field,
            _first(record, *keys)
            or _first(payload, *keys)
            or _first(metadata, *keys)
            or _nested(record, ("meta", field), ("metadata", field)),
        )

    turn_context = _nested(record, ("turn_context",), ("payload", "turn_context"))
    if isinstance(turn_context, dict):
        _set_if(result, "turn_id", _first(turn_context, "turn_id", "turnId", "id"))
        _set_if(result, "model", _first(turn_context, "model", "model_name"))
    _set_if(result, "api_message_id", _first(record, "api_message_id", "apiMessageId"))
    _set_if(result, "prompt_id", _first(record, "prompt_id", "promptId"))
    _set_if(result, "request_id", _first(record, "request_id", "requestId"))

    if context.get("source_key") is not None:
        context.setdefault("_source_key", context["source_key"])
    if context.get("file_branch_hint"):
        _add_flag(result, "file-branch-hint")
        _add_flag(result, "branch-input")


def _class_for_text(role: str | None, context: dict[str, Any], control: bool = False) -> str:
    if control:
        return "harness"
    if role == "assistant":
        return "agent-visible"
    if context.get("file_branch_hint") or context.get("_codex_branch_origin") or context.get("_current_sidechain"):
        return "branch-input"
    if role == "user":
        return "human"
    return "unknown"


def _is_control_text(value: Any) -> bool:
    return isinstance(value, str) and (
        value.startswith("# AGENTS.md")
        or value.startswith("<environment_context")
        or value.startswith("<codex_internal_context")
        or value.startswith("<user_instructions")
        or value.startswith("<user_shell_command")
        or value.startswith("<command-name>")
        or value.startswith("<command-message>")
        or value.startswith("<local-command-stdout>")
        or value.startswith("<local-command-caveat>")
        or value.startswith("<system-reminder>")
        or value.startswith("<recommended_plugins>")
        or value.startswith("<turn_aborted>")
        or value.startswith("<image name=")
        or value == "</image>"
        or value in {"[Request interrupted by user]","[Request interrupted by user for tool use]"}
    )


def _finalize_author_class(result: dict[str, Any], role: str | None, context: dict[str, Any]) -> None:
    force_harness = bool(result.pop("_force_harness", False))
    kinds = {part.get("kind") for part in result["parts"]}
    if force_harness:
        result["author_class"] = "harness"
    elif kinds & {"agent-text","agent-material"}:
        # A branch assistant remains agent-visible; a tool/thinking companion does not turn it
        # into a human or a branch-input occurrence.
        result["author_class"] = "agent-visible"
    elif "tool-result" in kinds:
        result["author_class"] = "runtime"
    elif kinds & {"human-text","human-material","human-command"}:
        result["author_class"] = (
            "branch-input"
            if role == "user" and (context.get("file_branch_hint") or context.get("_codex_branch_origin") or context.get("_current_sidechain"))
            else "human"
        )
    elif "reasoning" in kinds or "tool-call" in kinds:
        result["author_class"] = "agent-internal"
    elif "harness-text" in kinds:
        result["author_class"] = "harness"
    elif result["author_class"] == "unknown":
        result["author_class"] = _class_for_text(role, context)


def _codex_block(
    result: dict[str, Any], block: Any, pointer: str, role: str | None, context: dict[str, Any]
) -> None:
    if not isinstance(block, dict):
        _add_flag(result, "unknown-block")
        result["parts"].append(_text_part(pointer, "opaque", block))
        return
    block_type = block.get("type")
    text = block.get("text")
    if block_type in {"input_text", "text"}:
        control = bool(result.get("_force_harness")) or (role=="user" and _is_control_text(text))
        if control:
            result["author_class"] = "harness"
            _add_flag(result, "control-surface")
        result["parts"].append(
            _text_part(pointer + "/text", "harness-text" if control else ("human-text" if role == "user" else "opaque"), text)
        )
        if role != "user":
            _add_flag(result, "noncanonical-input-text")
        return
    if block_type in {"output_text", "assistant_text"}:
        kind="harness-text" if result.get("_force_harness") else "reasoning" if result.get("_internal_phase") else "agent-text"
        result["parts"].append(_text_part(pointer + "/text", kind, text))
        return
    if block_type in {"input_image","image","image_url","input_audio","audio"}:
        kind="harness-text" if result.get("_force_harness") else "human-material" if role=="user" else "agent-material"
        result["parts"].append(_text_part(pointer,kind,None))
        return
    if block_type in {"reasoning", "thought", "thinking"}:
        result["parts"].append(_text_part(pointer, "reasoning", text or block.get("summary")))
        result["author_class"] = "agent-internal"
        return
    if block_type in {"function_call", "tool_call", "custom_tool_call"}:
        call_id = _first(block, "call_id", "callId", "id")
        result["parts"].append(_text_part(pointer, "tool-call", None))
        result["calls"].append(
            {"call_id": call_id, "name": _first(block, "name", "function"), "pointer": pointer}
        )
        result["author_class"] = "agent-internal"
        return
    if block_type in {
        "function_call_output",
        "tool_result",
        "custom_tool_result",
        "custom_tool_call_output",
    }:
        call_id = _first(block, "call_id", "callId", "tool_call_id", "toolUseId")
        result["parts"].append(_text_part(pointer, "tool-result", block.get("output", block.get("content"))))
        result["results"].append({"call_id": call_id, "pointer": pointer})
        result["author_class"] = "runtime"
        return
    result["parts"].append(_text_part(pointer, "opaque", text or block))
    _add_flag(result, "unknown-block")


def _decode_codex(record: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    result = _base()
    payload_value = record.get("payload")
    payload = _object(payload_value)
    if isinstance(payload_value, str):
        _add_flag(result, "quoted-json")
        if not payload:
            _add_flag(result, "unknown-schema")
    metadata = _codex_metadata(record)
    origin = _origin_context(context, metadata) if metadata else context.get("_codex_origin_session_meta", {})
    if context.get("_codex_copied_session_meta_seen"):
        _add_flag(result, "copied-session-meta" if record.get("type")=="session_meta" else "container-has-copied-session-meta")
    _common_fields(result, record, payload, origin if isinstance(origin, dict) else {}, context)
    if isinstance(origin, dict):
        _apply_codex_origin(result, origin, context)
    native_id = _first(payload, "id")
    _set_if(result, "native_id", native_id)
    _set_if(result, "api_message_id", _first(payload, "api_message_id", "apiMessageId", "message_id"))
    _set_if(result, "prompt_id", _first(payload, "prompt_id", "promptId"))
    _set_if(result, "request_id", _first(payload, "request_id", "requestId"))
    if record.get("type")=="turn_context":
        context["_codex_turn_context"]={k:payload[k] for k in ("turn_id","root_turn_id","model") if k in payload}
    current_turn=context.get("_codex_turn_context",{})
    for key in ("turn_id","model","root_turn_id"):
        if result.get(key) is None:
            _set_if(result,key,current_turn.get(key))
    if result["session_id"] is None:
        _set_if(result, "session_id", _first(origin, "session_id", "sessionId", "id"))
    if record.get("type") == "session_meta" or metadata:
        result["author_class"] = "runtime"
        _add_flag(result, "session-meta")
        return result
    if isinstance(payload_value, str):
        result["parts"].append(_text_part(_pointer("payload"), "opaque", payload_value))
        _add_flag(result, "quoted-payload-opaque")
        result["author_class"] = "unknown"
        return result
    role = payload.get("role") if isinstance(payload.get("role"), str) else None
    if role in {"system","developer"}:
        result["_force_harness"]=True
    result["_internal_phase"]=result.get("phase") in {"analysis","reasoning"}
    if record.get("type") == "event_msg":
        _add_flag(result, "event-mirror")
        result["author_class"] = "runtime"
        result["parts"].append(_text_part(_pointer("payload"), "opaque", payload))
    elif record.get("type")!="response_item":
        result["author_class"]="runtime"
        result["parts"].append(_text_part(_pointer("payload"),"opaque",None))
    elif payload.get("type") == "message":
        if role not in {"user","assistant","system","developer"}:
            result["author_class"]="unknown"
            result["parts"].append(_text_part("/payload/content","opaque",None))
            result["flags"].append("unknown-message-author")
            return result
        content = payload.get("content")
        if isinstance(content, list):
            for index, block in enumerate(content):
                _codex_block(result, block, _pointer("payload", "content", index), role, context)
        elif isinstance(content, str):
            control = bool(result.get("_force_harness")) or (role=="user" and _is_control_text(content))
            kind = "harness-text" if control else "reasoning" if result.get("_internal_phase") else ("human-text" if role == "user" else "agent-text")
            result["parts"].append(_text_part(_pointer("payload", "content"), kind, content))
            if control:
                result["author_class"] = "harness"
                _add_flag(result, "control-surface")
        else:
            _add_flag(result, "no-visible-parts")
        if result["author_class"] == "unknown":
            result["author_class"] = _class_for_text(role, context)
    elif payload.get("type") in {
        "reasoning", "function_call", "tool_call", "custom_tool_call",
        "function_call_output", "tool_result", "custom_tool_call_output",
    }:
        _codex_block(result, payload, _pointer("payload"), None, context)
    else:
        result["author_class"] = "runtime"
        _add_flag(result, "unknown-schema")
    _finalize_author_class(result, role, context)
    result.pop("_internal_phase",None)
    return result


def _claude_block(
    result: dict[str, Any], block: Any, pointer: str, role: str | None, context: dict[str, Any]
) -> None:
    if not isinstance(block, dict):
        _add_flag(result, "unknown-block")
        result["parts"].append(_text_part(pointer, "opaque", block))
        return
    block_type = block.get("type")
    if block_type == "text":
        text_class = _class_for_text(role, context)
        text_kind = (
            "harness-text"
            if result.get("_force_harness") or (role=="user" and _is_control_text(block.get("text")))
            else "runtime-text" if result.get("_user_tool_envelope")
            else ("human-text" if text_class in {"human", "branch-input"} else "agent-text")
        )
        if role=="user" and result.get("input_origin")=="human" and isinstance(block.get("text"),str) and block["text"].startswith(("<command-message>","<command-name>")):
            text_kind="human-command"
        result["parts"].append(
            _text_part(pointer + "/text", text_kind, block.get("text"))
        )
    elif block_type in {"image","image_url","audio","input_audio"}:
        kind="opaque" if result.get("_force_harness") or result.get("_user_tool_envelope") else "human-material" if role=="user" else "agent-material"
        result["parts"].append(_text_part(pointer,kind,None))
    elif block_type in {"thinking", "reasoning"}:
        result["parts"].append(_text_part(pointer + "/thinking", "reasoning", block.get("thinking", block.get("text"))))
        result["author_class"] = "agent-internal"
    elif block_type == "tool_use":
        call_id = _first(block, "id", "call_id", "callId")
        result["parts"].append(_text_part(pointer, "tool-call", None))
        result["calls"].append({"call_id": call_id, "name": block.get("name"), "pointer": pointer})
        result["author_class"] = "agent-internal"
    elif block_type == "tool_result":
        call_id = _first(block, "tool_use_id", "toolUseId", "call_id", "callId")
        result["parts"].append(_text_part(pointer, "tool-result", block.get("content")))
        result["results"].append({"call_id": call_id, "pointer": pointer})
        result["author_class"] = "runtime"
    else:
        result["parts"].append(_text_part(pointer, "opaque", block))
        _add_flag(result, "unknown-block")


def _decode_claude(record: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    result = _base()
    message_value = record.get("message")
    message = _object(message_value)
    if isinstance(message_value, str):
        _add_flag(result, "quoted-json")
        if not message:
            _add_flag(result, "unknown-schema")
    role = message.get("role") if isinstance(message.get("role"), str) else record.get("type") if record.get("type") in {"user","assistant"} else record.get("role")
    native_id = _first(record, "uuid")
    _set_if(result, "native_id", native_id)
    _common_fields(result, record, message, {}, context)
    _set_if(result, "session_id", _first(record, "sessionId", "session_id"))
    _set_if(result, "api_message_id", _first(message, "id"))
    _set_if(result, "prompt_id", _first(record, "promptId", "prompt_id"))
    _set_if(result, "request_id", _first(record, "requestId", "request_id"))
    origin=record.get("origin")
    result["input_origin"]=origin.get("kind") if isinstance(origin,dict) else None
    result["prompt_source"]=record.get("promptSource")
    result["compact_summary"]=bool(record.get("isCompactSummary"))
    if record.get("apiBlockIndex") is not None:
        result["api_block_index"]=record["apiBlockIndex"]
    _set_if(result, "turn_id", _first(record, "turnId", "turn_id") or _first(message,"turn_id","turnId"))
    if record.get("isMeta") or record.get("is_meta") or record.get("isCompactSummary"):
        result["author_class"] = "harness"
        result["_force_harness"] = True
        _add_flag(result, "meta-record")
    sidechain = record.get("sidechain") or record.get("isSidechain") or record.get("agentId")
    if sidechain:
        context["_current_sidechain"] = True
        result["author_class"] = "branch-input"
        _add_flag(result, "sidechain")
        _set_if(result,"branch_id",record.get("agentId") if isinstance(record.get("agentId"),str) else "sidechain-unresolved")
    else:
        context["_current_sidechain"] = False
    if isinstance(message_value, str):
        result["parts"].append(_text_part(_pointer("message"), "opaque", message_value))
        _add_flag(result, "quoted-message-opaque")
        result["author_class"]="harness" if result.pop("_force_harness",False) else "unknown"
        context.pop("_current_sidechain", None)
        return result
    content = message.get("content")
    if role=="user" and (result.get("input_origin")=="task-notification" or
        (result.get("input_origin")!="human" and isinstance(content,str) and content.startswith("<task-notification>"))):
        result["author_class"]="runtime"
        result["flags"].append("task-notification")
        result["parts"].append(_text_part("/message/content","runtime-notification",None))
        # The provider's wrapper is an exterior codec. Never search embedded prose for role/ID labels.
        if isinstance(content,str) and "<!DOCTYPE" not in content:
            import xml.etree.ElementTree as ET
            try:
                root=ET.fromstring(content)
                if root.tag=="task-notification":
                    result["runtime_task_id"]=root.findtext("task-id")
                    call_id=root.findtext("tool-use-id")
                    if call_id:
                        result["results"].append({"call_id":call_id,"pointer":"/message/content"})
            except ET.ParseError:
                result["flags"].append("opaque-task-notification-body")
        result.pop("_force_harness",None)
        context.pop("_current_sidechain",None)
        return result
    if role=="user" and record.get("promptSource")=="system":
        result["_force_harness"]=True
        result["flags"].append("system-origin-input")
    if record.get("type") not in {"user","assistant"}:
        result["author_class"]="runtime"
        result["parts"].append(_text_part("", "opaque",None))
        context.pop("_current_sidechain",None)
        return result
    if role not in {"user","assistant","system","developer"}:
        result["author_class"]="unknown"
        result["parts"].append(_text_part("/message/content","opaque",None))
        result["flags"].append("unknown-message-author")
        context.pop("_current_sidechain",None)
        return result
    if isinstance(content, list):
        result["_user_tool_envelope"]=role=="user" and any(isinstance(b,dict) and b.get("type")=="tool_result" for b in content)
        for index, block in enumerate(content):
            _claude_block(result, block, _pointer("message", "content", index), role, context)
    elif isinstance(content, str):
        control = bool(result.get("_force_harness")) or (role=="user" and _is_control_text(content))
        text_class = _class_for_text(role, context)
        text_kind = "human-text" if text_class in {"human", "branch-input"} else "agent-text"
        result["parts"].append(
            _text_part(_pointer("message", "content"), "human-command" if role=="user" and result.get("input_origin")=="human" and content.startswith(("<command-message>","<command-name>")) else "harness-text" if control else text_kind, content)
        )
        if control:
            result["author_class"] = "harness"
            _add_flag(result, "control-surface")
    else:
        _add_flag(result, "no-visible-parts")
    if result["author_class"] == "unknown":
        result["author_class"] = _class_for_text(role, context)
    _finalize_author_class(result, role, context)
    result.pop("_user_tool_envelope",None)
    context.pop("_current_sidechain", None)
    return result


def decode(provider: str, record: dict, context: dict) -> dict:
    """Decode one provider record without resolving or flattening its external relations."""

    if not isinstance(record, dict):
        return {**_base(), "flags": ["invalid-record"], "author_class": "unknown"}
    if not isinstance(context, dict):
        context = {}
    provider_name = provider.casefold()
    if provider_name in {"codex", "openai-codex"}:
        result = _decode_codex(record, context)
    elif provider_name in {"claude", "claude-code", "anthropic"}:
        result = _decode_claude(record, context)
    else:
        result = _base()
        result["author_class"] = "unknown"
        result["flags"].append("unknown-provider")
    branch_flags={"subagent-origin","subagent-origin-without-spawn","sidechain","file-branch-hint"}
    result["human_comparison_eligible"]=result["author_class"] in {"human","agent-visible"} and not branch_flags.intersection(result["flags"])
    return result
