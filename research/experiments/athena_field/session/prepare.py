"""Exterior supervised text-edit data. This writes requests and targets, never a learner.

The context is an ordered pair of words; examples teach replacement of the first by
its correction. Whole two-word sections are generated simultaneously. Diagonal requests
are held out from development; all native maps and updates belong to the field model.
"""
import itertools, json, pathlib, sys
root=pathlib.Path(__file__).resolve().parent
words=['red','blue','green']
spec={'symbols':words,'section_symbols':2,'context_symbols':2,'codec':'whitespace-words','fractional_bits':48}
(root/'spec.json').write_text(json.dumps(spec,indent=2)+'\n')
def command(action,**fields): return {'schema':'org.holonics.hna.stream-request.v1','command':{'action':action,**fields}}
def request(pair,context,commit=False,retain=False):return command('field-request',request={'text':' '.join(pair),'context':list(context),'commit':commit,'retain_comparison':retain})
def target(pair,context):
    before,after=context
    return ' '.join(after if word==before else word for word in pair)
# The task data supplies this relation openly. It is never called by the native session.
development=[];cases=[];ordinal=0
epochs=int(sys.argv[1]) if len(sys.argv)>1 else 1
for epoch in range(epochs):
    for context in itertools.product(words,repeat=2):
        for pair in itertools.product(words,repeat=2):
            if pair[0]==pair[1]:continue
            development += [request(pair,context,True,True),command('observe-field',source=ordinal,text=target(pair,context),step_bits=1)]
            ordinal+=1
# Retain an actual producing comparison across the process boundary.
last_pair=('red','blue');last_context=('red','green')
development.append(request(last_pair,last_context,True,True))
evaluation=[command('observe-field',source=ordinal,text=target(last_pair,last_context),step_bits=1)]
for context in itertools.product(words,repeat=2):
    for word in words:
        pair=(word,word)
        cases.append({'request':' '.join(pair),'context':list(context),'target':target(pair,context)})
        evaluation.append(request(pair,context))
for name,rows in [('development.jsonl',development),('evaluation.jsonl',evaluation)]:
    (root/name).write_text(''.join(json.dumps(r)+'\n' for r in rows))
(root/'held-out.json').write_text(json.dumps(cases,indent=2)+'\n')
print(json.dumps({'development_targets':ordinal,'pending_comparison':ordinal,'held_out_cases':len(cases)}))
