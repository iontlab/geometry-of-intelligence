"""Refresh only Theorem 2.1 mappings and integrity links after compiler audit.

Keep the existing 96 expanded narratives and all original manuscript bindings.
The new graph record mirrors the existing 2.1 narrative, with a partial scope.
"""
from pathlib import Path
import copy, hashlib, json

R=Path(__file__).resolve().parents[1]
D=R/'docs/mathematics-learning'
G=R/'docs/formalization/mathematics-learning'
E=G/'explanations'
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,o,compact=False):
    p.write_text(json.dumps(o,ensure_ascii=False,indent=None if compact else 2,
        separators=(',',':') if compact else None)+'\n',encoding='utf-8',newline='\n')

data=read(G/'data.json'); nodes={n['id']:n for n in data['nodes']}
modules={m['name']:m for m in data['modules']}
r=next(r for r in read(D/'obligations.json')['records'] if r['key']=='2.1')
assert len(r['lean_declarations'])==4
reg=read(E/'registry.v0.1.json'); old=copy.deepcopy(reg)
source=next(x for x in reg['records'] if x['object_key']=='explain.mathematics-learning.source.2.1')
source['formal_mapping']={'status':r['formalization_status'],'declarations':r['lean_declarations']}
source['mathematics']['proof']=[r['proof']]
source['obligations']=r['obligations']
source['content']['where_analogy_stops']=[{'type':'paragraph','text':r['limit']}]

math=read(G/'mathematics.json')
math['results']['source.2.1']={'label':'Primary 2.1 · partial construction',
    'title':'Yoneda: author-supplied evaluation and candidate components',
    'native_key':'2.1','source':r['public_url'],'anchor':source['source']['anchor'],
    'statement':[r['mathematics']],'proof':[r['proof']],
    'limitation':r['formalization_status']+'. '+r['limit']}
for i,n in enumerate(r['lean_declarations']):
    assert nodes[n]['authored']
    math['declarations'][n]={'result':'source.2.1','role':'principal' if i==0 else 'supporting'}
save(G/'mathematics.json',math)
if not any(x['object_key']=='explain.mathematics-learning.graph.2.1' for x in reg['records']):
    graph=copy.deepcopy(source)
    graph.update(object_key='explain.mathematics-learning.graph.2.1',kind='graph-result',wiki=False)
    graph.pop('obligations');graph.pop('mathematics')
    graph['formal_mapping']={'declaration':r['lean_declarations'][0],'result_key':'source.2.1'}
    reg['records'].append(graph)
reg['repository']['commit']=data['sourceRef']
reg['graph']={'data_sha256':sha(G/'data.json'),'mathematics_sha256':sha(G/'mathematics.json')}
for x in reg['records']:
    if x['kind']!='graph-result':continue
    f=x['formal_mapping'];n=nodes[f['declaration']]
    f.update(signature=n['signature'],source_file=n['source'],
        source_sha256=modules[n['module']]['sha256'].lower(),source_commit=data['sourceRef'],
        mathematics_json_sha256=reg['graph']['mathematics_sha256'],
        pinned_source_link=n['sourceUrl'],scope_note=math['results'][f['result_key']]['limitation'])
save(E/'registry.v0.1.json',reg,compact=True)
assert (E/'registry.v0.1.json').stat().st_size<500000
release=read(E/'release.json')
release.update(release='learning-native-20261018-yoneda-partial-r12',registry_sha256=sha(E/'registry.v0.1.json'))
save(E/'release.json',release)
save(G/'source-audit.json',read(D/'original/native/source-audit.json'))
for a in old['records']:
    b=next(x for x in reg['records'] if x['object_key']==a['object_key'])
    assert a['source']==b['source']
    for layer in ['plain','story','story_key']:assert a['content'][layer]==b['content'][layer]
    if a['object_key']!='explain.mathematics-learning.source.2.1':
        assert a['content']==b['content']
        if a['kind']=='source-item':assert a==b
print('PASS: 58 source items, 39 graph records, 47 inline controls; all existing narratives and source bindings preserved.')
