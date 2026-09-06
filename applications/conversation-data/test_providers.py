import unittest

from providers import decode


class ProviderDecoderTests(unittest.TestCase):
    def test_claude_system_origin_notifications_and_summaries_are_not_human(self):
        notification=decode("claude",{"type":"user","origin":{"kind":"task-notification"},"promptSource":"system",
            "message":{"role":"user","content":"<task-notification><task-id>worker</task-id><tool-use-id>call</tool-use-id><summary>done</summary></task-notification>"}}, {"source_key":"s"})
        self.assertEqual(notification["author_class"],"runtime")
        self.assertEqual(notification["results"][0]["call_id"],"call")
        summary=decode("claude",{"type":"user","isCompactSummary":True,
            "message":{"role":"user","content":"This session is being continued from a previous conversation. Summary: ..."}}, {"source_key":"s"})
        self.assertEqual(summary["author_class"],"harness")
        self.assertFalse(summary["human_comparison_eligible"])
        interruption=decode("claude",{"type":"user","message":{"role":"user","content":[{"type":"text","text":"[Request interrupted by user]"}]}},{"source_key":"s"})
        self.assertEqual(interruption["author_class"],"harness")

    def test_provider_attributed_human_command_is_not_a_generated_control(self):
        command=decode("claude",{"type":"user","origin":{"kind":"human"},"message":{"role":"user","content":"<command-name>/loop</command-name><command-args>continue my task</command-args>"}},{"source_key":"s"})
        self.assertEqual(command["author_class"],"human")
        self.assertEqual(command["parts"][0]["kind"],"human-command")

    def test_missing_or_unknown_role_cannot_manufacture_an_agent_response(self):
        for provider,record in [
            ("codex",{"type":"response_item","payload":{"type":"message","content":"not attributed"}}),
            ("claude",{"type":"user","message":{"role":"function","content":"not human or assistant"}}),
        ]:
            result=decode(provider,record,{"source_key":"s"})
            self.assertEqual(result["author_class"],"unknown")
            self.assertFalse(result["human_comparison_eligible"])

    def test_codex_origin_metadata_is_frozen(self):
        context = {"source_key": "root.jsonl", "file_branch_hint": False}
        first = decode(
            "codex",
            {"type": "session_meta", "payload": {"id": "root", "model": "gpt", "cwd": "/repo"}},
            context,
        )
        later = decode(
            "codex",
            {"type": "session_meta", "payload": {"id": "copied-parent", "model": "old"}},
            context,
        )
        self.assertEqual(first["session_id"], "root")
        self.assertEqual(later["session_id"], "root")
        self.assertIn("copied-session-meta", later["flags"])

    def test_codex_message_boundaries_and_tool_events_remain_distinct(self):
        context = {"source_key": "root.jsonl", "file_branch_hint": False}
        message = decode(
            "codex",
            {
                "type": "response_item",
                "payload": {
                    "type": "message",
                    "role": "user",
                    "id": "u1",
                    "content": [
                        {"type": "input_text", "text": "question"},
                        {"type": "input_text", "text": "second block"},
                    ],
                },
            },
            context,
        )
        self.assertEqual(message["native_id"], "u1")
        self.assertEqual([part["pointer"] for part in message["parts"]], [
            "/payload/content/0/text",
            "/payload/content/1/text",
        ])
        call = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "function_call", "call_id": "c1", "name": "lookup"}},
            context,
        )
        result = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "function_call_output", "call_id": "c1", "output": "ret"}},
            context,
        )
        self.assertEqual(call["author_class"], "agent-internal")
        self.assertEqual(call["calls"][0]["call_id"], "c1")
        self.assertEqual(result["author_class"], "runtime")
        self.assertEqual(result["results"][0]["call_id"], "c1")

    def test_claude_tool_result_is_not_human_and_sidechain_is_branch_input(self):
        context = {"source_key": "claude.jsonl", "file_branch_hint": False}
        tool_result = decode(
            "claude",
            {
                "type": "user",
                "uuid": "result-envelope",
                "message": {
                    "role": "user",
                    "content": [{"type": "tool_result", "tool_use_id": "tool-1", "content": "world"}],
                },
            },
            context,
        )
        self.assertEqual(tool_result["author_class"], "runtime")
        self.assertEqual(tool_result["results"][0]["call_id"], "tool-1")
        branch = decode(
            "claude",
            {
                "type": "user",
                "uuid": "branch-user",
                "agentId": "agent-2",
                "message": {"role": "user", "content": [{"type": "text", "text": "branch input"}]},
            },
            context,
        )
        self.assertEqual(branch["author_class"], "branch-input")
        self.assertIn("sidechain", branch["flags"])

    def test_controls_and_unknown_provider_are_explicit(self):
        context = {"source_key": "claude.jsonl", "file_branch_hint": False}
        control = decode(
            "claude",
            {"type": "user", "uuid": "control", "message": {"role": "user", "content": "<command-name>ls"}},
            context,
        )
        self.assertEqual(control["author_class"], "harness")
        self.assertIn("control-surface", control["flags"])
        unknown = decode("other", {"id": "x"}, context)
        self.assertEqual(unknown["author_class"], "unknown")
        self.assertIn("unknown-provider", unknown["flags"])

    def test_codex_subagent_origin_freezes_parent_and_branch_attribution(self):
        context = {"source_key": "child-rollout.jsonl", "file_branch_hint": False}
        meta = decode(
            "codex",
            {
                "type": "session_meta",
                "payload": {
                    "id": "child-session",
                    "thread_source": "subagent",
                    "source": {"subagent": {"thread_spawn": {"parent_thread_id": "parent", "agent_path": "a/1"}}},
                },
            },
            context,
        )
        user = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "message", "role": "user", "id": "u", "content": [{"type": "input_text", "text": "branch request"}]}},
            context,
        )
        assistant = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "message", "role": "assistant", "id": "a", "content": [{"type": "output_text", "text": "branch answer"}]}},
            context,
        )
        copied = decode(
            "codex",
            {"type": "session_meta", "payload": {"id": "main-copy", "thread_source": "main"}},
            context,
        )
        later_user = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "message", "role": "user", "content": [{"type": "input_text", "text": "still branch"}]}},
            context,
        )
        self.assertEqual(meta["author_class"], "runtime")
        self.assertEqual(user["author_class"], "branch-input")
        self.assertEqual(user["parent_session"], "parent")
        self.assertEqual(user["agent_path"], "a/1")
        self.assertEqual(assistant["author_class"], "agent-visible")
        self.assertEqual(assistant["parts"][0]["kind"], "agent-text")
        self.assertIn("copied-session-meta", copied["flags"])
        self.assertEqual(later_user["author_class"], "branch-input")

        spawn_only = {"source_key": "declared-child"}
        decode("codex", {"type":"session_meta", "payload":{"id":"child",
            "source":{"subagent":{"thread_spawn":{"parent_thread_id":"parent","agent_path":"a/2"}}}}}, spawn_only)
        child = decode("codex", {"type":"response_item", "payload":{"type":"message","role":"user",
            "content":[{"type":"input_text","text":"controller input"}]}}, spawn_only)
        self.assertEqual(child["author_class"], "branch-input")
        self.assertFalse(child["human_comparison_eligible"])

    def test_mixed_codex_harness_and_human_blocks_keep_both_parts(self):
        result = decode(
            "codex",
            {
                "type": "response_item",
                "payload": {
                    "type": "message",
                    "role": "user",
                    "content": [
                        {"type": "input_text", "text": "# AGENTS.md instructions for /repo"},
                        {"type": "input_text", "text": "actual request"},
                    ],
                },
            },
            {"source_key": "root", "file_branch_hint": False},
        )
        self.assertEqual(result["author_class"], "human")
        self.assertEqual([part["kind"] for part in result["parts"]], ["harness-text", "human-text"])

    def test_codex_harness_prefixes_are_controls(self):
        prefixes = [
            "# AGENTS.md instructions",
            "<environment_context>",
            "<codex_internal_context>",
            "<user_instructions>",
            "<user_shell_command>",
        ]
        for text in prefixes:
            result = decode(
                "codex",
                {"type": "response_item", "payload": {"type": "message", "role": "user", "content": [{"type": "input_text", "text": text}]}},
                {"source_key": "root", "file_branch_hint": False},
            )
            self.assertEqual(result["author_class"], "harness", text)
            self.assertEqual(result["parts"][0]["kind"], "harness-text", text)

    def test_codex_turn_context_and_claude_meta_fields_are_not_collapsed(self):
        codex = decode(
            "codex",
            {"type": "response_item", "turn_context": {"turn_id": "turn-1", "model": "model-1"}, "payload": {"type": "message", "role": "assistant", "content": [{"type": "output_text", "text": "ok"}]}},
            {"source_key": "root", "file_branch_hint": False},
        )
        claude = decode(
            "claude",
            {"type": "assistant", "uuid": "uuid-1", "promptId": "prompt-1", "requestId": "request-1", "isMeta": True, "message": {"id": "generation-1", "role": "assistant", "content": [{"type": "text", "text": "meta"}]}},
            {"source_key": "root", "file_branch_hint": False},
        )
        self.assertEqual(codex["turn_id"], "turn-1")
        self.assertEqual(codex["model"], "model-1")
        self.assertEqual(claude["api_message_id"], "generation-1")
        self.assertIsNone(claude["turn_id"])
        self.assertEqual(claude["prompt_id"], "prompt-1")
        self.assertEqual(claude["request_id"], "request-1")
        self.assertEqual(claude["author_class"], "harness")
        self.assertEqual(claude["parts"][0]["kind"], "harness-text")

    def test_custom_tools_are_canonical_and_event_mirrors_are_not_dialogue(self):
        context = {"source_key": "root", "file_branch_hint": False}
        call = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "custom_tool_call", "call_id": "c", "name": "shell"}},
            context,
        )
        output = decode(
            "codex",
            {"type": "response_item", "payload": {"type": "custom_tool_call_output", "call_id": "c", "output": "ok"}},
            context,
        )
        mirror = decode(
            "codex",
            {"type": "event_msg", "payload": {"type": "message", "role": "user", "content": [{"type": "input_text", "text": "not dialogue"}]}},
            context,
        )
        self.assertEqual(call["parts"][0]["kind"], "tool-call")
        self.assertNotIn("event-mirror", call["flags"])
        self.assertEqual(output["parts"][0]["kind"], "tool-result")
        self.assertEqual(mirror["author_class"], "runtime")
        self.assertEqual(mirror["parts"][0]["kind"], "opaque")

    def test_claude_mixed_agent_blocks_and_metadata_do_not_use_generation_as_turn(self):
        result = decode(
            "claude",
            {
                "type": "assistant",
                "uuid": "native-uuid",
                "promptId": "prompt-1",
                "requestId": "request-1",
                "message": {
                    "id": "api-generation-1",
                    "role": "assistant",
                    "content": [
                        {"type": "text", "text": "visible"},
                        {"type": "thinking", "thinking": "internal"},
                        {"type": "tool_use", "id": "tool-1", "name": "lookup"},
                    ],
                },
            },
            {"source_key": "root", "file_branch_hint": False},
        )
        self.assertEqual(result["native_id"], "native-uuid")
        self.assertEqual(result["api_message_id"], "api-generation-1")
        self.assertIsNone(result["turn_id"])
        self.assertEqual(result["prompt_id"], "prompt-1")
        self.assertEqual(result["request_id"], "request-1")
        self.assertEqual(result["author_class"], "agent-visible")
        self.assertEqual([part["kind"] for part in result["parts"]], ["agent-text", "reasoning", "tool-call"])

    def test_quoted_payloads_remain_opaque(self):
        codex = decode(
            "codex",
            {"type": "response_item", "payload": '{"type":"message","role":"user","content":"fake"}'},
            {"source_key": "root", "file_branch_hint": False},
        )
        claude = decode(
            "claude",
            {"type": "user", "uuid": "u", "message": '{"role":"user","content":"fake"}'},
            {"source_key": "root", "file_branch_hint": False},
        )
        self.assertEqual(codex["parts"][0]["kind"], "opaque")
        self.assertEqual(claude["parts"][0]["kind"], "opaque")
        self.assertNotEqual(codex["author_class"], "human")
        self.assertNotEqual(claude["author_class"], "human")


if __name__ == "__main__":
    unittest.main()
