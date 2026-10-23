# Renders the first n GSM8K training problems as "question\nanswer\n" each, the passage the
# passage_ctw read scores. Input: the public train.jsonl of openai/grade-school-math.
# Usage: python3 -I render_gsm8k.py train.jsonl 1000 > gsm_1000.txt
import json, sys
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
sys.stdout.buffer.write("".join(r["question"] + "\n" + r["answer"] + "\n" for r in rows[:int(sys.argv[2])]).encode())
