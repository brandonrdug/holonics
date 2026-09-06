import json
import os
from pathlib import Path
import tempfile
import unittest
import zlib

from conversation_data import annotate, connect, export_comparisons, export_followups, package, reproject
from providers import decode


def codex_message(role,text,identity,phase=None):
    return {"type":"response_item","payload":{"type":"message","role":role,"id":identity,
            "phase":phase,"content":[{"type":"input_text" if role=="user" else "output_text","text":text}]}}


class PackageTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.root=Path(self.temp.name)
    def tearDown(self):
        self.temp.cleanup()
    def source(self,name,records,tail=b""):
        path=self.root/name
        raw=b"".join((json.dumps(r,ensure_ascii=False)+"\n").encode() for r in records)+tail
        path.write_bytes(raw)
        return path,raw

    def test_raw_reconstruction_and_correct_user_agent_operands(self):
        records=[
            {"type":"session_meta","payload":{"id":"main","thread_source":"user"}},
            codex_message("user","question","u"),
            {"type":"turn_context","payload":{"turn_id":"t","model":"model-x"}},
            codex_message("assistant","internal only","i","analysis"),
            {"type":"response_item","payload":{"type":"custom_tool_call","call_id":"c","name":"inspect","input":"command"}},
            {"type":"response_item","payload":{"type":"custom_tool_call_output","call_id":"c","output":"you> synthetic correction; checker passed"}},
            {"type":"event_msg","payload":{"type":"message","role":"assistant","content":[{"type":"output_text","text":"mirror"}]}},
            codex_message("assistant","observed answer, not gold","a","final_answer"),
            codex_message("user","that answer needs a correction","later"),
        ]
        source,raw=self.source("codex.jsonl",records,b'{"partial":')
        output=self.root/"data.sqlite"
        result=package([("codex",source)],output)
        self.assertEqual(result["user_agent_comparisons"],1)
        self.assertEqual(os.stat(output).st_mode & 0o777,0o600)
        with connect(output) as db:
            self.assertEqual(b"".join(zlib.decompress(r[0]) for r in db.execute("SELECT raw_zlib FROM events ORDER BY record_number")),raw)
            self.assertEqual(db.execute("SELECT count(*) FROM links WHERE kind='tool-result-of' AND target_event IS NOT NULL").fetchone()[0],1)
            self.assertEqual(db.execute("SELECT model FROM events WHERE native_id='a'").fetchone()[0],"model-x")
            self.assertEqual(db.execute("SELECT author_class FROM events WHERE native_id='i'").fetchone()[0],"agent-internal")
            self.assertEqual(db.execute("SELECT count(*) FROM links WHERE kind='later-human-after-agent'").fetchone()[0],1)
        exported=self.root/"comparisons.jsonl"
        export_comparisons(output,exported)
        row=json.loads(exported.read_text())
        self.assertFalse(row["agent_response_is_gold"])
        self.assertIsNone(row["loss"])
        self.assertEqual(row["views"][0]["agent"]["parts"][0]["text"],"observed answer, not gold")
        self.assertFalse(row["views"][0]["later_user_return_is_input"])
        self.assertNotIn("later_human_observation_refs",row["views"][0])
        self.assertFalse(row["views"][0]["recorded_response_interval"]["automatic_input"])
        with self.assertRaises(FileExistsError):
            package([("codex",source)],output)
        followup=self.root/"followup.jsonl";export_followups(output,followup)
        observed=json.loads(followup.read_text())
        self.assertTrue(observed["not_available_to_original_response"])
        self.assertIsNone(observed["feedback_interpretation"])

    def test_adjacency_never_crosses_conversations_and_reprojection_keeps_raw(self):
        records=[
            {"type":"user","uuid":"u","sessionId":"one","message":{"role":"user","content":"one request"}},
            {"type":"assistant","uuid":"wrong","sessionId":"two","message":{"role":"assistant","content":[{"type":"text","text":"another conversation"}]}},
            {"type":"assistant","uuid":"right","sessionId":"one","message":{"role":"assistant","model":"a changed model is not a changed conversation","content":[{"type":"text","text":"same conversation"}]}},
        ]
        source,raw=self.source("claude.jsonl",records)
        dataset=self.root/"source.sqlite";package([("claude",source)],dataset)
        source.unlink()  # Reprojection must use captured material, not a changed/missing log.
        revised=self.root/"revised.sqlite";reproject(dataset,revised)
        with connect(revised) as db:
            pair=db.execute("SELECT a.native_id FROM comparisons c JOIN events a ON a.id=c.agent_event").fetchall()
            self.assertEqual([r[0] for r in pair],["right"])
            self.assertEqual(b''.join(zlib.decompress(r[0]) for r in db.execute("SELECT raw_zlib FROM events ORDER BY id")),raw)

    def test_tool_links_preserve_parts_scope_and_ambiguity(self):
        def call(uuid,session,ids):
            return {"type":"assistant","uuid":uuid,"sessionId":session,"message":{"role":"assistant","content":[{"type":"tool_use","id":i,"name":"tool"} for i in ids]}}
        def result(uuid,session,ids):
            return {"type":"user","uuid":uuid,"sessionId":session,"message":{"role":"user","content":[{"type":"tool_result","tool_use_id":i,"content":"a tool verdict is not a human verdict"} for i in ids]}}
        records=[call("a","one",["c"]),call("other","two",["c"]),result("r","one",["c"]),
                 call("reused","one",["c"]),result("ambiguous","one",["c"]),
                 call("parallel","one",["p","q"]),result("parallel-result","one",["p","q"])]
        source,_=self.source("tools.jsonl",records);dataset=self.root/"tools.sqlite"
        package([("claude",source)],dataset)
        with connect(dataset) as db:
            links=[dict(r) for r in db.execute("SELECT e.native_id,l.kind,t.native_id AS target,l.reference FROM links l JOIN events e ON e.id=l.source_event LEFT JOIN events t ON t.id=l.target_event")]
            self.assertEqual([(r['target'],r['kind']) for r in links if r['native_id']=='r'],[('a','tool-result-of')])
            ambiguous=[r for r in links if r['native_id']=='ambiguous']
            self.assertEqual({r['target'] for r in ambiguous if r['kind']=='tool-result-candidate'},{'a','reused'})
            self.assertTrue(any(r['target'] is None for r in ambiguous))
            parallel=[r for r in links if r['native_id']=='parallel-result']
            self.assertEqual(len(parallel),2)
            self.assertEqual({json.loads(r['reference'])['result_pointer'] for r in parallel},{'/message/content/0','/message/content/1'})

    def test_explicit_parent_wins_over_latest_speaker_and_branch_is_not_human_loss(self):
        def message(role,uuid,parent,content,**extra):
            return dict(type=role,uuid=uuid,parentUuid=parent,sessionId="s",message={"role":role,"content":content},**extra)
        records=[
            message("user","u1",None,"first request"),
            message("assistant","call","u1",[{"type":"text","text":"I will inspect"},{"type":"tool_use","id":"c","name":"tool"}]),
            message("user","result","call",[{"type":"tool_result","tool_use_id":"c","content":"success"}]),
            message("user","u2","result","a different request"),
            message("assistant","a1","result",[{"type":"thinking","thinking":"private trace"},{"type":"text","text":"reply to first"}]),
            message("assistant","a2","u2",[{"type":"text","text":"reply to second"}]),
            message("assistant","branch","u2",[{"type":"text","text":"agent-to-agent response"}],isSidechain=True,agentId="worker"),
        ]
        source,_=self.source("claude.jsonl",records)
        output=self.root/"data.sqlite"
        package([("claude",source)],output)
        with connect(output) as db:
            pairs=set(tuple(r) for r in db.execute("SELECT u.native_id,a.native_id FROM comparisons c JOIN events u ON u.id=c.user_event JOIN events a ON a.id=c.agent_event"))
            self.assertEqual(pairs,{("u1","call"),("u1","a1"),("u2","a2")})
        export=self.root/"views.jsonl";export_comparisons(output,export)
        rows=[json.loads(l) for l in export.read_text().splitlines()]
        answer=next(r for r in rows if r["declared_pair_family"][2]=="declared:a1")
        self.assertEqual([p["kind"] for p in answer["views"][0]["agent"]["parts"]],["agent-text"])

    def test_copied_parent_metadata_does_not_create_human_feedback_in_child(self):
        records=[
            {"type":"session_meta","payload":{"id":"child","thread_source":"subagent","source":{"subagent":{"thread_spawn":{"parent_thread_id":"parent","agent_path":"/root/worker"}}}}},
            {"type":"session_meta","payload":{"id":"parent","thread_source":"user","source":"cli"}},
            codex_message("user","copied human context or controller input","u"),
            codex_message("assistant","worker reply","a","final_answer"),
        ]
        path,_=self.source("rollout-not-an-agent-filename.jsonl",records)
        result=package([("codex",path)],self.root/"child.sqlite")
        self.assertEqual(result["user_agent_comparisons"],0)
        self.assertEqual(result["roles"]["branch-input"],1)
        self.assertEqual(result["parts"].get("human-text",0),0)
        self.assertEqual(result["parts"]["branch-input-text"],1)

    def test_same_words_are_not_same_occurrence_and_export_views_do_not_get_extra_weight(self):
        records=[{"type":"session_meta","payload":{"id":"s","thread_source":"user"}},codex_message("user","same words","u"),codex_message("assistant","same reply","a")]
        one,_=self.source("one.jsonl",records)
        two,_=self.source("copy.jsonl",records)
        three,_=self.source("distinct.jsonl",[records[0],codex_message("user","same words","different-u"),codex_message("assistant","same reply","different-a")])
        output=self.root/"data.sqlite"
        result=package([("codex",p) for p in [one,two,three]],output)
        self.assertEqual(result["user_agent_comparisons"],3)
        export=self.root/"views.jsonl";export_comparisons(output,export)
        rows=[json.loads(l) for l in export.read_text().splitlines()]
        self.assertEqual(len(rows),2)
        self.assertEqual(sorted(len(r["views"]) for r in rows),[1,2])

    def test_images_and_mixed_harness_keep_the_actual_user_material(self):
        record={"type":"response_item","payload":{"type":"message","role":"user","id":"u","content":[
            {"type":"input_text","text":"<environment_context>generated</environment_context>"},
            {"type":"input_image","image_url":"data:image/png;base64,example"},
            {"type":"input_text","text":"look at this"}]}}
        result=decode("codex",record,{"source_key":"s"})
        self.assertEqual(result["author_class"],"human")
        self.assertEqual([p["kind"] for p in result["parts"]],["harness-text","human-material","human-text"])

    def test_generated_claude_inputs_do_not_replace_the_human_comparison(self):
        records=[
            {"type":"user","uuid":"u","sessionId":"s","message":{"role":"user","content":"actual request"}},
            {"type":"user","uuid":"notice","sessionId":"s","origin":{"kind":"task-notification"},"promptSource":"system",
             "message":{"role":"user","content":"<task-notification><summary>done</summary></task-notification>"}},
            {"type":"user","uuid":"summary","sessionId":"s","isCompactSummary":True,
             "message":{"role":"user","content":"This session is being continued from a previous conversation"}},
            {"type":"user","uuid":"loop","sessionId":"s","queuePriority":"later",
             "message":{"role":"user","content":"<command-message>loop</command-message><command-name>/loop</command-name>"}},
            {"type":"assistant","uuid":"a","sessionId":"s","message":{"role":"assistant","content":"observed response"}},
            {"type":"user","uuid":"command","sessionId":"s","origin":{"kind":"human"},
             "message":{"role":"user","content":"<command-message>loop</command-message><command-name>/loop</command-name>"}},
            {"type":"assistant","uuid":"b","sessionId":"s","message":{"role":"assistant","content":"response to human command"}},
        ]
        source,_=self.source("claude.jsonl",records)
        dataset=self.root/"data.sqlite";package([("claude",source)],dataset)
        with connect(dataset) as db:
            pairs=[tuple(r) for r in db.execute("SELECT u.native_id,a.native_id FROM comparisons c JOIN events u ON u.id=c.user_event JOIN events a ON a.id=c.agent_event ORDER BY a.id")]
            self.assertEqual(pairs,[("u","a"),("command","b")])
            self.assertEqual(db.execute("SELECT author_class FROM events WHERE native_id='loop'").fetchone()[0],"harness")
        output=self.root/"comparisons.jsonl";export_comparisons(dataset,output)
        views=[v for line in output.read_text().splitlines() for v in json.loads(line)["views"]]
        self.assertEqual({v["user"]["parts"][0]["kind"] for v in views},{"human-text","human-command"})

    def test_curation_is_source_addressed_and_does_not_rewrite_comparisons(self):
        source,_=self.source("source.jsonl",[codex_message("user","a scoped correction","u"),codex_message("assistant","observed reply","a")])
        dataset=self.root/"data.sqlite";package([("codex",source)],dataset)
        annotation=self.root/"curation.jsonl"
        value={"author":"curator","truth_status":"interpretation","kind":"rhetorical-move","label":"correction",
               "event":1,"pointer":"/payload/content/0/text","rationale":"Only this clause is being classified."}
        annotation.write_text(json.dumps(value)+'\n')
        annotate(dataset,annotation)
        value['pointer']='/not-present';annotation.write_text(json.dumps(value)+'\n')
        with self.assertRaises(KeyError):annotate(dataset,annotation)
        with connect(dataset) as db:
            self.assertEqual(db.execute('SELECT count(*) FROM annotations').fetchone()[0],1)
            self.assertEqual(db.execute('SELECT count(*) FROM comparisons').fetchone()[0],1)


if __name__=="__main__":
    unittest.main()
