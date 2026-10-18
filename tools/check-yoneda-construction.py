"""Regression check for the narrowly scoped author-supplied 2.1 construction."""
from pathlib import Path
import json, subprocess
R=Path(__file__).resolve().parents[1]
BASE='ce2d4c9338cd454cbf27d7d500949be7e6556d61'
G='docs/formalization/mathematics-learning/'
read=lambda p:json.loads((R/p).read_text(encoding='utf-8'))
old=lambda p:json.loads(subprocess.check_output(['git','show',BASE+':'+p],cwd=R))
before={n['id']:n for n in old(G+'compiled.json')}
after={n['id']:n for n in read(G+'compiled.json')}
prefix='ILab.MathematicsLearning.SetCategory.'
added={prefix+n for n in ['yonedaEvaluation','yonedaCandidateComponent','yonedaEvaluation_formula','yonedaCandidateComponent_formula']}
assert set(after)-set(before)==added and not set(before)-set(after)
for name,a in before.items():
    b=after[name]
    for field in ['signature','kind','module']:assert a[field]==b[field],(name,field)
    for field in ['dependencies','externalDependencies','axioms']:assert set(a[field])==set(b[field]),(name,field)
for p,key in [('docs/mathematics-learning/obligations.json','records'),('docs/mathematics-learning/coverage.json','records'),('docs/mathematics-learning/original/native/source-audit.json','items')]:
    a={r['key']:r for r in old(p)[key]};b={r['key']:r for r in read(p)[key]}
    assert a.keys()==b.keys()
    assert all(a[k]==b[k] for k in a if k!='2.1'),p
reg=read(G+'explanations/registry.v0.1.json');new={r['object_key']:r for r in reg['records']}
for a in old(G+'explanations/registry.v0.1.json')['records']:
    b=new[a['object_key']]
    assert a['source']==b['source']
    for layer in ['plain','story','story_key']:assert a['content'][layer]==b['content'][layer]
    if a['kind']=='source-item' and a['source']['item_key']!='2.1':assert a==b
source=new['explain.mathematics-learning.source.2.1'];graph=new['explain.mathematics-learning.graph.2.1']
assert graph['content']==source['content']
assert set(source['formal_mapping']['declarations'])==added
assert len(source['obligations'])==5 and all(not o['declarations'] for o in source['obligations'][2:])
assert read('docs/mathematics-learning/original/native/source-audit.json')['fully_formalized']==29
protected=['ILab/RQ001','formalization/rq001','docs/formalization/rq001','lean-toolchain','lakefile.toml','lake-manifest.json','integrations/dokuwiki',G+'explanations/binding.json',G+'explanations/native-source.json',G+'explanations/fixtures']
assert not subprocess.check_output(['git','diff',BASE,'--',*protected],cwd=R)
changed=subprocess.check_output(['git','diff',BASE,'--name-only','--','ILab'],cwd=R,text=True).splitlines()
assert changed==['ILab/MathematicsLearning/YonedaConstruction.lean'],changed
print('PASS: exactly four new construction/formula declarations; all 781 existing declarations, other source-item audits, manuscript bindings, expanded narratives and RQ-001 preserved; all three 2.1 exercise checks remain open.')
