# Conversation material

[definition] A standard-library exterior packager for Claude Code and Codex JSONL logs. It keeps
actual user-agent comparison separate from tool/delegation/inference traces and does not train a
model, evaluate proofs or assign correctness/reward. See the [data guide](../../docs/CONVERSATION_DATA.md).

```sh
python3 applications/conversation-data/conversation_data.py prepare \
  --codex /home/b/.codex/sessions --claude /home/b/.claude/projects \
  --output .local/datasets/conversations-new.sqlite
python3 applications/conversation-data/conversation_data.py inspect .local/datasets/conversations-new.sqlite
python3 -m unittest discover -s applications/conversation-data -p 'test_*.py'
```

[definition] Outputs are private, new files. Raw logs and produced data must not be committed or
uploaded. `reproject` refines views from captured bytes without rereading growing source logs;
`annotate` adds explicitly authored, source-addressed curation. The dataset is material, not a
repository registry, navigation authority or release gate. No GPU, Lean, Torch or network service
is used by preparation.
