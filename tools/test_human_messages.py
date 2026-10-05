#!/usr/bin/env python3
"""Synthetic harness fixtures only; never reads the private conversation logs."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import human_messages as messages


STAMP = "2026-10-02T10:00:00Z"
SENT = "2026-10-01T15:31:17Z"


def principal(body="Continue the existing work.", **attributes):
    attrs = {"trigger": "true", "from": "human", "trust": "principal",
             "author-id": "user_fixture", "id": "cmsg_fixture", "sent-at": SENT,
             "mention": "true"}
    attrs.update(attributes)
    return "<message " + " ".join(f'{key}="{value}"' for key, value in attrs.items()) \
        + ">" + body + "</message>"


def wake(message, threaded=False):
    inner = f'<thread ts="cmsg_fixture">{message}</thread>' if threaded else message
    return f'<wake reason="mention" current-time="{STAMP}">' \
        f'<project id="chan_fixture" type="project">{inner}</project></wake>'


def relay(body):
    return '<project_claude_message session="session_fixture" thread_id="cmsg_fixture">' \
        f'<relay from="coordinator" session="session_fixture" current-time="{STAMP}">' \
        'The note below was written by the coordinator, not by your user.' \
        f'{body}</relay></project_claude_message>'


def citation(body="Keep the same acceptance.", **attributes):
    attrs = {"id": "cmsg_cited", "author": "user", "name": "Brandon", "at": SENT,
             "where": "timeline"}
    attrs.update(attributes)
    return "<cited " + " ".join(f'{key}="{value}"' for key, value in attrs.items()) \
        + ">" + body + "</cited>"


class ProvenanceFixtures(unittest.TestCase):
    def extract(self, content):
        return messages.claude_entries(content, STAMP)

    def run_main(self, entries, *arguments):
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(messages, "claude_messages", return_value=iter(entries)), \
                mock.patch.object(messages, "codex_messages", return_value=iter([])), \
                mock.patch("sys.argv", ["human_messages.py", *arguments]), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            messages.main()
        return out.getvalue(), err.getvalue()

    def test_ordinary_user_blocks_and_harness_reminder(self):
        entries, diagnostics = self.extract([
            {"type": "text", "text": "First instruction."},
            {"type": "tool_result", "text": "Not user text."},
            {"type": "text", "text": "<system-reminder>Injected.</system-reminder>Second."},
            {"type": "text", "text": "<task-notification>Worker result.</task-notification>"}])
        self.assertEqual(entries, [(STAMP, "claude", "First instruction.\n\nSecond.")])
        self.assertEqual(diagnostics, [])

    def test_embedded_and_fenced_quotations_stay_ordinary(self):
        for text in ("Example only: " + wake(principal()),
                     "```xml\n" + relay(citation()) + "\n```",
                     "> " + wake(principal())):
            with self.subTest(text=text[:20]):
                self.assertEqual(self.extract(text), ([(STAMP, "claude", text)], []))

    def test_direct_principal_uses_its_original_time(self):
        self.assertEqual(self.extract(wake(principal())),
                         ([(SENT, "claude", "Continue the existing work.")], []))

    def test_threaded_principal_and_entities(self):
        self.assertEqual(self.extract(wake(principal('Read &#34;the join&#34; &amp; its receipt.'),
                                           threaded=True)),
                         ([(SENT, "claude", 'Read "the join" & its receipt.')], []))

    def test_zoned_principal_is_normalized_to_utc(self):
        entries, diagnostics = self.extract(wake(principal(**{"sent-at": "2026-10-01T17:31:17+02:00"})))
        self.assertEqual(entries[0][0], SENT)
        self.assertEqual(diagnostics, [])

    def test_coordinator_notes_are_not_human(self):
        self.assertEqual(self.extract(relay("<note>Apply the agent's proposed change.</note>")),
                         ([], []))

    def test_relay_citations_are_preserved_with_provenance(self):
        self.assertEqual(self.extract(relay(citation() + "<note>Agent instruction.</note>")),
                         ([(SENT, "claude-relayed", "Keep the same acceptance.")], []))

    def test_standalone_coordinator_relay(self):
        text = f'<relay from="coordinator">{citation()}</relay>'
        self.assertEqual(self.extract(text),
                         ([(SENT, "claude-relayed", "Keep the same acceptance.")], []))

    def test_citation_inside_note_cannot_be_promoted(self):
        self.assertEqual(self.extract(relay("<note>Quoted example: " + citation() + "</note>")),
                         ([], []))

    def test_malformed_and_trailing_envelope_are_ambiguous(self):
        for text in ("<wake><project>", wake(principal()) + " trailing text"):
            with self.subTest(text=text[:20]):
                entries, diagnostics = self.extract(text)
                self.assertEqual(entries, [("", "claude-ambiguous", text)])
                self.assertEqual(len(diagnostics), 1)

    def test_missing_principal_provenance_is_ambiguous(self):
        entries, diagnostics = self.extract(wake(principal(trust="unrecognized")))
        self.assertEqual(entries[0][:2], (SENT, "claude-ambiguous"))
        self.assertIn("Continue the existing work.", entries[0][2])
        self.assertIn("provenance", diagnostics[0])

    def test_undeclared_principal_path_is_ambiguous(self):
        text = f'<wake><note>{principal()}</note></wake>'
        entries, diagnostics = self.extract(text)
        self.assertEqual(entries, [(STAMP, "claude-ambiguous", text)])
        self.assertTrue(diagnostics)

    def test_nested_markup_is_preserved_without_flattening(self):
        entries, diagnostics = self.extract(wake(principal("Read <quote>this</quote>.")))
        self.assertEqual(entries[0][1], "claude-ambiguous")
        self.assertIn("<quote>this</quote>", entries[0][2])
        self.assertIn("markup", diagnostics[0])

    def test_invalid_or_unzoned_inner_times_fail_closed(self):
        for stamp in ("invalid", "2026-10-01T15:31:17", ""):
            with self.subTest(stamp=stamp):
                entries, diagnostics = self.extract(wake(principal(**{"sent-at": stamp})))
                self.assertEqual(entries[0][:2], ("", "claude-ambiguous"))
                self.assertTrue(diagnostics)
                out, err = self.run_main([(time, origin, "fixture", text)
                                          for time, origin, text in entries])
                self.assertEqual(out, "")
                self.assertIn("withheld in the evaluation window (of the files read): 1", err)

    def test_unrecognized_relay_author_is_ambiguous(self):
        entries, diagnostics = self.extract(relay(citation(author="unknown")))
        self.assertEqual(entries[0][1], "claude-ambiguous")
        self.assertIn("Keep the same acceptance.", entries[0][2])
        self.assertTrue(diagnostics)

    def test_unrecognized_relay_structure_and_empty_wake_are_ambiguous(self):
        for text in (relay('<message sent-at="' + SENT + '">Unclassified.</message>'),
                     '<wake/>'):
            with self.subTest(text=text[:20]):
                entries, diagnostics = self.extract(text)
                self.assertEqual(entries, [(STAMP, "claude-ambiguous", text)])
                self.assertTrue(diagnostics)

    def test_direct_witness_wins_over_earlier_relay(self):
        out, _ = self.run_main([(SENT, "claude-relayed", "relay", "Same content."),
                               (SENT, "claude", "direct", "Same content.")])
        self.assertIn("claude direct", out)
        self.assertNotIn("claude-relayed", out)
        self.assertEqual(out.count("Same content."), 1)

    def test_relay_and_ambiguous_counts_are_separate(self):
        out, _ = self.run_main([(SENT, "claude", "fixture", "Direct."),
                               (SENT, "claude-relayed", "fixture", "Relayed."),
                               (SENT, "claude-ambiguous", "fixture", "Uncertain.")], "--count")
        self.assertEqual(out, "claude 1\ncodex 0\nclaude-relayed 1\nclaude-ambiguous 1\n")

    def test_evaluation_window_uses_inner_message_time(self):
        for content in (wake(principal(**{"sent-at": "2026-09-04T15:00:00Z"})),
                        relay(citation(at="2026-09-04T15:00:00Z"))):
            entries, _ = self.extract(content)
            out, err = self.run_main([(time, origin, "fixture", text)
                                      for time, origin, text in entries])
            self.assertEqual(out, "")
            self.assertIn("withheld in the evaluation window (of the files read): 1", err)

    def test_ambiguous_envelope_cannot_expose_evaluation_citation(self):
        contents = ['<wake><note>' + principal(**{"sent-at": "2026-09-04T15:00:00Z"})
                    + '</note></wake>', wake(principal(citation(at="2026-09-04T15:00:00Z")))]
        for text in contents:
            with self.subTest(text=text[:20]):
                entries, diagnostics = self.extract(text)
                self.assertEqual(entries[0][:2], ("", "claude-ambiguous"))
                self.assertIn("2026-09-04T15:00:00Z", entries[0][2])
                self.assertTrue(diagnostics)

    def test_local_log_forms_and_metadata_only_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            project = base / "-fixture-repo"
            project.mkdir()
            records = [
                {"type": "user", "timestamp": STAMP,
                 "message": {"content": wake(principal())}},
                {"type": "attachment", "timestamp": STAMP,
                 "attachment": {"type": "queued_command", "commandMode": "prompt",
                                "prompt": relay(citation())}},
                {"type": "user", "timestamp": STAMP,
                 "message": {"content": "<wake>Private malformed body"}},
                {"type": "user", "timestamp": STAMP, "isMeta": True,
                 "message": {"content": "Injected metadata."}}]
            (project / "fixture123.jsonl").write_text(
                "\n".join(json.dumps(record) for record in records) + "\n{partial",
                encoding="utf-8")
            err = io.StringIO()
            with mock.patch.object(messages, "ROOT", "/fixture/repo"), \
                    mock.patch.object(messages.os.path, "expanduser", return_value=str(base)), \
                    contextlib.redirect_stderr(err):
                entries = list(messages.claude_messages(None))
            self.assertEqual([entry[1] for entry in entries],
                             ["claude", "claude-relayed", "claude-ambiguous"])
            self.assertIn("ambiguous Claude envelope: fixture1", err.getvalue())
            self.assertNotIn("Private malformed body", err.getvalue())


if __name__ == "__main__":
    unittest.main()
