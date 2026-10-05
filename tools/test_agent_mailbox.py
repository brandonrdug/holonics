"""Focused mailbox checks; all writes are confined to temporary directories."""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from agent_mailbox import Mailbox, MailboxError, canonical_mailbox


TOOL = Path(__file__).with_name("agent_mailbox.py")
PINNED_ID = "a" * 32


class MailboxTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "mailbox"
        self.box = Mailbox(self.root)

    def send(self, **overrides):
        arguments = dict(agent="codex", recipient="opus", topic="contact-owner",
                         body="Owned paths: tools only.\nReceipt: λ is exact.")
        return self.box.send(**(arguments | overrides))

    def cli(self, *arguments, content=None):
        return subprocess.run(
            [sys.executable, "-B", str(TOOL), "--mailbox", str(self.root), *arguments],
            input=content, capture_output=True, text=True)

    def test_empty_list_and_root_do_not_create_mailbox(self):
        self.assertEqual(self.box.inbox("opus"), [])
        result = self.cli("root")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), str(self.root))
        self.assertFalse(self.root.exists())

    def test_send_read_ack_and_reply_have_explicit_boundaries(self):
        receipt = self.send()
        original = self.box.read("opus", receipt["id"])
        self.assertEqual(original["body"], "Owned paths: tools only.\nReceipt: λ is exact.")
        self.assertEqual(len(self.box.inbox("opus")), 1)
        self.assertEqual(self.box.inbox("codex"), [])
        with self.assertRaises(MailboxError):
            self.box.read("other", receipt["id"])
        with self.assertRaises(MailboxError):
            self.box.ack("codex", receipt["id"])
        with self.assertRaises(MailboxError):
            self.box.send("opus", "other", "contact-owner", "A reply", "reply", [receipt["id"]])
        reply = self.box.send("opus", "codex", "contact-owner", "I own the scientific paths.",
                              "reply", [receipt["id"]])
        self.assertEqual(self.box.read("codex", reply["id"])["references"], [receipt["id"]])
        # A reply never implicitly acknowledges the original.
        self.assertEqual(len(self.box.inbox("opus")), 1)
        ack = self.box.ack("opus", receipt["id"])
        self.assertEqual(ack["id"], "ack-" + receipt["id"])
        self.assertEqual(self.box.ack("opus", receipt["id"])["status"], "existing")
        self.assertEqual(self.box.inbox("opus"), [])
        self.assertTrue(self.box.inbox("opus", include_all=True)[0]["acknowledged"])
        self.assertEqual({item["kind"] for item in self.box.inbox("codex", include_all=True)},
                         {"reply", "ack"})
        with self.assertRaises(MailboxError):
            self.box.ack("codex", ack["id"])

    def test_duplicate_delivery_preserves_original_bytes_and_rejects_conflicts(self):
        first = self.send(message_id=PINNED_ID)
        path = Path(first["path"])
        original = path.read_bytes()
        make_message = Mailbox.message

        def later_message(*arguments):
            message = make_message(*arguments)
            message["timestamp"] = "2099-01-01T00:00:00Z"
            return message

        with patch("agent_mailbox.Mailbox.message", side_effect=later_message) as make:
            retry = self.send(message_id=PINNED_ID)
            self.assertEqual(make.call_count, 1)
        self.assertEqual(retry["status"], "existing")
        self.assertEqual(path.read_bytes(), original)
        for change in ({"body": "Different"}, {"recipient": "other"}, {"topic": "different"}):
            with self.assertRaises(MailboxError):
                self.send(message_id=PINNED_ID, **change)
            self.assertEqual(path.read_bytes(), original)
        self.assertEqual(path.stat().st_mode & 0o777, 0o400)
        self.assertEqual(self.root.stat().st_mode & 0o777, 0o700)
        self.assertFalse(list(self.box.messages.glob(".pending-*")))

    def test_concurrent_retries_publish_only_one_complete_message(self):
        with ThreadPoolExecutor(max_workers=8) as pool:
            receipts = list(pool.map(lambda _: self.send(message_id=PINNED_ID), range(24)))
        self.assertEqual(sum(item["status"] == "created" for item in receipts), 1)
        self.assertEqual(self.box.read("opus", PINNED_ID)["sender"], "codex")
        self.assertEqual(len(list(self.box.messages.iterdir())), 1)

    def test_publication_is_complete_before_becoming_visible_and_failure_leaves_no_message(self):
        link = os.link

        def inspect_link(source, destination):
            self.assertFalse(Path(destination).exists())
            self.assertEqual(json.loads(Path(source).read_text())["body"], "Complete body")
            link(source, destination)

        with patch("agent_mailbox.os.link", side_effect=inspect_link):
            self.send(message_id=PINNED_ID, body="Complete body")
        with patch("agent_mailbox.os.link", side_effect=OSError("simulated interruption")):
            with self.assertRaises(OSError):
                self.send(message_id="b" * 32)
        self.assertEqual(len(self.box.inbox("opus")), 1)
        self.assertFalse(list(self.box.messages.glob(".pending-*")))

    def test_identifiers_and_references_cannot_escape_the_mailbox(self):
        for value in ("../opus", "/tmp/opus", "opus/child", "Opus", "", "opus\n"):
            with self.subTest(value=value), self.assertRaises(MailboxError):
                self.send(recipient=value)
        for value in ("../../elsewhere", "/tmp/out", "", "ack-" + PINNED_ID):
            with self.subTest(value=value), self.assertRaises(MailboxError):
                self.send(message_id=value)
        with self.assertRaises(MailboxError):
            self.send(references=["../elsewhere"])
        with self.assertRaises(FileNotFoundError):
            self.send(references=[PINNED_ID])
        with self.assertRaises(MailboxError):
            Mailbox(Path("relative-mailbox"))
        self.assertFalse(self.root.exists())

    def test_symlinks_and_nonregular_messages_are_refused(self):
        self.box.directory(create=True)
        outside = Path(self.temporary.name) / "outside"
        outside.write_text("private external contents")
        candidate = self.box.messages / (PINNED_ID + ".json")
        candidate.symlink_to(outside)
        with self.assertRaises(OSError):
            self.box.read("opus", PINNED_ID)
        with self.assertRaises(OSError):
            self.send(message_id=PINNED_ID)
        self.assertEqual(outside.read_text(), "private external contents")
        candidate.unlink()
        os.mkfifo(candidate)
        with self.assertRaises(MailboxError):
            self.box.load(PINNED_ID)
        candidate.unlink()
        self.box.messages.rmdir()
        self.box.messages.symlink_to(Path(self.temporary.name))
        with self.assertRaises(MailboxError):
            self.send()

    def test_malformed_messages_and_invalid_acknowledgements_fail_visibly(self):
        receipt = self.send()
        forged = Mailbox.message("ack-" + receipt["id"], "other", "codex", "contact-owner",
                                 "ack", "Received", [receipt["id"]])
        self.box.publish(forged)  # Simulate a manual edit by another same-user process.
        with self.assertRaises(MailboxError):
            self.box.inbox("opus")
        (self.box.messages / ("b" * 32 + ".json")).write_text('{"version":1}')
        result = self.cli("list", "--agent", "opus")
        self.assertEqual(result.returncode, 1)
        self.assertIn("mailbox:", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_cli_round_trip_with_multiline_stdin_and_visible_errors(self):
        sent = self.cli("send", "--agent", "codex", "--to", "opus", "--topic", "checks",
                        "--kind", "question", "--body-file", "-", "--id", PINNED_ID,
                        content="First line\nSecond line: ∂²=0\n")
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(json.loads(sent.stdout)["status"], "created")
        listed = self.cli("list", "--agent", "opus", "--topic", "checks")
        self.assertEqual(listed.returncode, 0, listed.stderr)
        self.assertNotIn("body", json.loads(listed.stdout))
        read = self.cli("read", "--agent", "opus", PINNED_ID)
        self.assertEqual(json.loads(read.stdout)["body"], "First line\nSecond line: ∂²=0\n")
        acknowledged = self.cli("ack", "--agent", "opus", PINNED_ID)
        self.assertEqual(acknowledged.returncode, 0, acknowledged.stderr)
        self.assertEqual(self.cli("list", "--agent", "opus").stdout, "")
        missing = self.cli("read", "--agent", "opus", "b" * 32)
        self.assertEqual(missing.returncode, 1)
        self.assertIn("mailbox:", missing.stderr)

    def test_linked_worktrees_use_common_git_directory_and_detection_fails_closed(self):
        main = Path(self.temporary.name) / "main"
        (main / ".git").mkdir(parents=True)
        result = subprocess.CompletedProcess([], 0, str(main / ".git") + "\n", "")
        with patch("agent_mailbox.subprocess.run", return_value=result) as run:
            self.assertEqual(canonical_mailbox(main), canonical_mailbox(main / ".local/wt/worker"))
            self.assertIn("--git-common-dir", run.call_args.args[0])
        with patch("agent_mailbox.subprocess.run", side_effect=subprocess.CalledProcessError(1, "git")):
            with self.assertRaisesRegex(MailboxError, "pass --mailbox"):
                canonical_mailbox(main)
        result.stdout = str(main / "bare.git")
        with patch("agent_mailbox.subprocess.run", return_value=result):
            with self.assertRaisesRegex(MailboxError, "explicitly"):
                canonical_mailbox(main)


if __name__ == "__main__":
    unittest.main()
