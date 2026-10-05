#!/usr/bin/env python3
"""Repository-local technical messages; see agent_mailbox.md. Standard library only."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import uuid


AGENT = re.compile(r"[a-z][a-z0-9_-]{0,63}\Z")
MESSAGE_ID = re.compile(r"(?:ack-)?[0-9a-f]{32}\Z")
KINDS = ("note", "question", "reply")
FIELDS = {"version", "id", "timestamp", "sender", "recipient", "topic", "kind",
          "body", "references"}


class MailboxError(ValueError):
    pass


def identifier(value, pattern, label):
    if not isinstance(value, str) or not pattern.fullmatch(value):
        raise MailboxError(f"invalid {label}: {value!r}")
    return value


def canonical_mailbox(checkout=None):
    """Linked worktrees share the main checkout's mailbox; never fall back to cwd."""
    checkout = checkout or Path(__file__).resolve().parent.parent
    try:
        result = subprocess.run(
            ["git", "-C", str(checkout), "rev-parse", "--path-format=absolute",
             "--git-common-dir"], check=True, capture_output=True, text=True)
    except (OSError, subprocess.CalledProcessError) as error:
        raise MailboxError("cannot locate the main checkout; pass --mailbox ABSOLUTE_PATH") from error
    common = Path(result.stdout.strip()).resolve()
    if common.name != ".git" or not (common.parent / ".git").is_dir():
        raise MailboxError("nonstandard git layout; pass --mailbox ABSOLUTE_PATH explicitly")
    return common.parent / ".local" / "agent-mailbox"


def validate(message):
    if not isinstance(message, dict) or set(message) != FIELDS:
        raise MailboxError("message fields do not match protocol version 1")
    if type(message["version"]) is not int or message["version"] != 1:
        raise MailboxError("unsupported protocol version")
    identifier(message["id"], MESSAGE_ID, "message ID")
    identifier(message["sender"], AGENT, "sender")
    identifier(message["recipient"], AGENT, "recipient")
    if message["kind"] not in (*KINDS, "ack"):
        raise MailboxError("invalid message kind")
    for field in ("topic", "body"):
        if not isinstance(message[field], str) or not message[field].strip():
            raise MailboxError(f"{field} must be nonempty text")
    if any(ord(char) < 32 for char in message["topic"]):
        raise MailboxError("topic must be a single line without control characters")
    try:
        timestamp = datetime.strptime(message["timestamp"], "%Y-%m-%dT%H:%M:%SZ")
        if timestamp.strftime("%Y-%m-%dT%H:%M:%SZ") != message["timestamp"]:
            raise ValueError
    except (TypeError, ValueError):
        raise MailboxError("timestamp must be UTC YYYY-MM-DDTHH:MM:SSZ") from None
    references = message["references"]
    if not isinstance(references, list):
        raise MailboxError("references must be a list of message IDs")
    for reference in references:
        identifier(reference, MESSAGE_ID, "reference")
    if len(set(references)) != len(references) or message["id"] in references:
        raise MailboxError("references must be distinct and cannot reference this message")
    if message["kind"] == "ack":
        if len(references) != 1 or message["id"] != "ack-" + references[0]:
            raise MailboxError("acknowledgement ID must be ack-<original ID>")
    elif message["id"].startswith("ack-"):
        raise MailboxError("ack- IDs are reserved for acknowledgements")


class Mailbox:
    def __init__(self, root):
        root = Path(root)
        if not root.is_absolute():
            raise MailboxError("--mailbox must be an absolute path shared by both agents")
        self.root = root.resolve()
        self.messages = self.root / "messages"

    def directory(self, create=False):
        if create:
            self.root.mkdir(mode=0o700, parents=True, exist_ok=True)
            try:
                self.messages.mkdir(mode=0o700)
            except FileExistsError:
                pass
        if self.messages.is_symlink():
            raise MailboxError("messages directory cannot be a symbolic link")
        if self.messages.exists() and not self.messages.is_dir():
            raise MailboxError("messages path is not a directory")
        return self.messages.exists()

    def load(self, message_id):
        identifier(message_id, MESSAGE_ID, "message ID")
        self.directory()
        path = self.messages / (message_id + ".json")
        # Refuse symlinks and nonregular files (including FIFOs) without blocking.
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        with os.fdopen(fd, "r", encoding="utf-8") as handle:
            if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
                raise MailboxError("message must be a regular file")
            message = json.load(handle)
        validate(message)
        if message["id"] != message_id:
            raise MailboxError("message ID does not match its filename")
        return message

    def read(self, agent, message_id):
        identifier(agent, AGENT, "agent")
        message = self.load(message_id)
        if agent not in (message["sender"], message["recipient"]):
            raise MailboxError("message belongs to other agents")
        return message

    def publish(self, message):
        validate(message)
        self.directory(create=True)
        destination = self.messages / (message["id"] + ".json")
        payload = (json.dumps(message, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
        fd, temporary = tempfile.mkstemp(prefix=".pending-", dir=self.messages)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                handle.write(payload)
                handle.flush()
                os.fchmod(handle.fileno(), 0o400)
                os.fsync(handle.fileno())
            try:
                # Linking a complete file publishes atomically without ever replacing an ID.
                os.link(temporary, destination)
                created = True
            except FileExistsError:
                existing = self.load(message["id"])
                if {k: v for k, v in existing.items() if k != "timestamp"} != \
                        {k: v for k, v in message.items() if k != "timestamp"}:
                    raise MailboxError("ID already exists with different contents") from None
                created = False
        finally:
            os.unlink(temporary)
            directory_fd = os.open(self.messages, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        return {"id": message["id"], "status": "created" if created else "existing",
                "path": str(destination)}

    def send(self, agent, recipient, topic, body, kind="note", references=(), message_id=None):
        identifier(agent, AGENT, "agent")
        identifier(recipient, AGENT, "recipient")
        if kind not in KINDS:
            raise MailboxError("use ack to acknowledge a message")
        referenced = [self.read(agent, ref) for ref in references]
        if kind == "reply" and not any(
                item["recipient"] == agent and item["sender"] == recipient for item in referenced):
            raise MailboxError("reply must reference a message from its recipient to this agent")
        return self.publish(self.message(
            uuid.uuid4().hex if message_id is None else message_id,
            agent, recipient, topic, kind, body, references))

    @staticmethod
    def message(message_id, sender, recipient, topic, kind, body, references):
        return {"version": 1, "id": message_id,
                "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                "sender": sender, "recipient": recipient, "topic": topic, "kind": kind,
                "body": body, "references": list(references)}

    def ack(self, agent, message_id):
        original = self.read(agent, message_id)
        if original["recipient"] != agent or original["kind"] == "ack":
            raise MailboxError("only the addressed recipient can acknowledge a non-ack message")
        return self.publish(self.message(
            "ack-" + message_id, agent, original["sender"], original["topic"], "ack",
            "Received; this acknowledges receipt, not completion or approval.", [message_id]))

    def acknowledged(self, message):
        if message["kind"] == "ack":
            return False
        try:
            ack = self.load("ack-" + message["id"])
        except FileNotFoundError:
            return False
        if (ack["kind"], ack["sender"], ack["recipient"], ack["topic"]) != \
                ("ack", message["recipient"], message["sender"], message["topic"]):
            raise MailboxError("acknowledgement does not match the original message")
        return True

    def inbox(self, agent, include_all=False, topic=None):
        identifier(agent, AGENT, "agent")
        if not self.directory():
            return []
        messages = [self.load(path.stem) for path in self.messages.glob("*.json")]
        result = []
        for message in sorted(messages, key=lambda item: (item["timestamp"], item["id"])):
            if message["recipient"] != agent or (topic is not None and message["topic"] != topic):
                continue
            acknowledged = self.acknowledged(message)
            if include_all or (message["kind"] != "ack" and not acknowledged):
                result.append({**{k: v for k, v in message.items() if k != "body"},
                               "acknowledged": acknowledged})
        return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mailbox", help="absolute shared mailbox; default: main checkout .local/agent-mailbox")
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("root", help="print the canonical mailbox path without creating it")
    listing = commands.add_parser("list", help="list pending messages addressed to an agent as JSON lines")
    listing.add_argument("--agent", required=True)
    listing.add_argument("--all", action="store_true", help="also include acknowledgements and acknowledged messages")
    listing.add_argument("--topic")
    reading = commands.add_parser("read", help="read one incoming or own outgoing message as JSON")
    reading.add_argument("--agent", required=True)
    reading.add_argument("id")
    sending = commands.add_parser("send", help="publish an immutable message")
    sending.add_argument("--agent", required=True, help="your agreed sender ID")
    sending.add_argument("--to", required=True)
    sending.add_argument("--topic", required=True)
    sending.add_argument("--kind", choices=KINDS, default="note")
    body = sending.add_mutually_exclusive_group(required=True)
    body.add_argument("--body")
    body.add_argument("--body-file", help="UTF-8 file, or - to read stdin")
    sending.add_argument("--ref", action="append", default=[], help="related message ID; repeatable")
    sending.add_argument("--id", help="32 lowercase UUID hex digits; reuse with identical content for retries")
    acknowledging = commands.add_parser("ack", help="acknowledge receipt; safely repeatable")
    acknowledging.add_argument("--agent", required=True)
    acknowledging.add_argument("id")
    args = parser.parse_args(argv)
    try:
        mailbox = Mailbox(args.mailbox if args.mailbox is not None else canonical_mailbox())
        if args.command == "root":
            print(mailbox.root)
            return 0
        if args.command == "list":
            for message in mailbox.inbox(args.agent, args.all, args.topic):
                print(json.dumps(message, ensure_ascii=False, sort_keys=True))
            return 0
        if args.command == "read":
            result = mailbox.read(args.agent, args.id)
        elif args.command == "ack":
            result = mailbox.ack(args.agent, args.id)
        else:
            content = args.body
            if args.body_file is not None:
                content = sys.stdin.read() if args.body_file == "-" else \
                    Path(args.body_file).read_text(encoding="utf-8")
            result = mailbox.send(args.agent, args.to, args.topic, content,
                                  args.kind, args.ref, args.id)
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
        return 0
    except (MailboxError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"mailbox: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
