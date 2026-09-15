#!/usr/bin/env python3
"""Prepare a private retrospective evaluation episode using the existing conversation codec.

This is a newly declared experimental input, not a reconstruction of an earlier model prompt.
Recorded assistant responses/later human observations stay in a separate assessment file and
are not gold answers. Native training/inference is not invoked by this exterior preparation.
"""
import argparse
from contextlib import closing
from datetime import datetime
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'applications/conversation-data'))
import conversation_data as corpus


def clock(value):
    result=datetime.fromisoformat(value.replace('Z','+00:00'))
    if result.tzinfo is None:raise ValueError('context comparison requires declared time zones')
    return result


def snapshot(reference):
    revision,path=reference.split(':',1)
    if not path or Path(path).is_absolute() or '..' in Path(path).parts:
        raise ValueError('repository source must be a relative path in a declared revision')
    commit=subprocess.check_output(['git','rev-parse','--verify',revision+'^{commit}'],cwd=ROOT,text=True).strip()
    text=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT,text=True)
    return {'commit':commit,'path':path,'text':text,'scope':'material supplied to this retrospective experiment'}


def prepare(dataset,request_id,context_ids,references,output):
    with closing(corpus.connect(dataset)) as db, db:
        request=corpus.visible_view(db,request_id,'human-text')
        if request['author_class']!='human' or not request['parts']:
            raise ValueError('request must be an actual visible human occurrence')
        candidates=[r[0] for r in db.execute('SELECT agent_event FROM comparisons WHERE user_event=? ORDER BY agent_event',(request_id,))]
        candidate_views=[corpus.visible_view(db,i,'agent-text') for i in candidates]
        context=[]
        for event in context_ids:
            view=corpus.event_view(db,event)
            if event==request_id or event in candidates or clock(view['timestamp'])>=clock(request['timestamp']):
                raise ValueError('context contains the request, a response, or later material')
            if view['author_class'] not in ('human','agent'):
                raise ValueError('context must select a visible human/agent occurrence explicitly')
            context.append(corpus.visible_view(db,event,'human-text' if view['author_class']=='human' else 'agent-text'))
        followups=[]
        for event in candidates:
            for row in db.execute("SELECT source_event,evidence FROM links WHERE kind='later-human-after-agent' AND target_event=?",(event,)):
                followups.append({'recorded_target_event':event,'link_evidence':row[1],
                                  'observation':corpus.visible_view(db,row[0],'human-text')})
    source={'schema':'holonics.evaluation-episode-input.v1','request':request,'declared_context':context,
            'repository_material':[snapshot(r) for r in references],
            'scope':'retrospective validation; selected source, not a recovered complete prompt or blind holdout',
            'candidate_or_later_return_included':False}
    assessment={'schema':'holonics.evaluation-episode-assessment.v1','request_event':request_id,
                'recorded_candidates':candidate_views,'recorded_later_observations':followups,
                'assistant_is_gold':False,'later_observation_is_feedback_on_new_output':False,
                'constraint_judgments':[],
                'instruction':'Review generated consequences against source-addressed requirements; retain contradictions and alternatives. Do not use this file as the earlier model input.'}
    output.mkdir(parents=True,exist_ok=False,mode=0o700)
    for name,value in [('input.json',source),('assessment.json',assessment)]:
        with corpus.private_output(output/name) as f:f.write(json.dumps(value,ensure_ascii=False)+'\n')
    return {'request_event':request_id,'context_events':context_ids,'recorded_candidates':len(candidate_views),
            'later_observations':len(followups),'repository_sources':len(references),
            'scope':source['scope'],'native_execution':False,'output':str(output)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dataset',type=Path,required=True)
    parser.add_argument('--request-event',type=int,required=True)
    parser.add_argument('--context-event',type=int,action='append',default=[])
    parser.add_argument('--repository-ref',action='append',default=[],help='commit:path, explicitly supplied to the new experiment')
    parser.add_argument('--output',type=Path,required=True)
    a=parser.parse_args()
    print(json.dumps(prepare(a.dataset,a.request_event,a.context_event,a.repository_ref,a.output)))


if __name__=='__main__':main()
