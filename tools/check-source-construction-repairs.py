"""Strict baseline regression for G1–G10, including all protected source evidence."""
from pathlib import Path
import runpy
CAP=runpy.run_path(str(Path(__file__).with_name('learning-capacity.py')))
import json,runpy,subprocess
R=Path(__file__).resolve().parents[1];BASE='1cd4fe15b242ed59a7dc2c5d3e155405355b49df'
G='docs/formalization/mathematics-learning/';D='docs/mathematics-learning/'
read=lambda p:json.loads((R/p).read_text(encoding='utf-8'))
oldbytes=lambda p:subprocess.check_output(['git','show',BASE+':'+p],cwd=R)
old=lambda p:json.loads(oldbytes(p))
spec=runpy.run_path(str(Path(__file__).with_name('source-construction-repairs.py')))['REPAIRS'];changed=set(spec)|{'equivalences.motivation'}
before={n['id']:n for n in old(G+'compiled.json')};after={n['id']:n for n in read(G+'compiled.json')}
assert len(before)==785 and before.keys()<=after.keys()
for name,a in before.items():
    b=after[name]
    for field in ['signature','kind','module']:assert a[field]==b[field],(name,field)
    for field in ['dependencies','externalDependencies','axioms']:assert set(a[field])==set(b[field]),(name,field)
expected=set(n for r in spec.values() for n in r['declarations'])-set(before)
assert set(after)-set(before)==expected and len(expected)==31
for name in expected:
    n=after[name];assert n['module']=='ILab.MathematicsLearning.SourceConstructionData'
    assert set(n['axioms'])<={'propext','Classical.choice','Quot.sound'}
    assert not any(any(t in d.lower() for t in ['mkofhomequiv','adjunction.homequiv','yonedaequiv','yonedalemma','isiso_op','isiso_unop']) for d in n['externalDependencies']),name
for p,field in [(D+'obligations.json','records'),(D+'coverage.json','records'),(D+'original/native/source-audit.json','items')]:
    a={x['key']:x for x in old(p)[field]};b={x['key']:x for x in read(p)[field]};assert a.keys()==b.keys()
    for k in a:
        if k not in changed:assert a[k]==b[k],(p,k)
        if p.endswith('obligations.json'):
            for o in a[k]['obligations']:
                if o['status']=='assigned exercise solution withheld':assert o in b[k]['obligations'],(k,o['id'])
reg=read(G+'explanations/registry.v0.1.json');rs={r['object_key']:r for r in reg['records']}
for a in old(G+'explanations/registry.v0.1.json')['records']:
    b=rs[a['object_key']];assert a['content']==b['content'],a['object_key']
    if a['source']['item_key']!='equivalences.motivation':assert a['source']==b['source']
    if a['kind']=='source-item' and a['source']['item_key'] not in changed:assert a==b
assert len(reg['records'])==103 and sum(r['wiki'] for r in reg['records'])==47
size=(R/(G+'explanations/registry.v0.1.json')).stat().st_size;assert CAP['check_registry']((R/(G+'explanations/registry.v0.1.json')).read_bytes())>=5000,size
for r in reg['records']:
    if r['source']['item_key']=='equivalences.motivation':assert r['source']['page_id'].endswith(':adjunctions') and r['source']['anchor']=='adjunctions_and_equivalences'
paths=['ILab/RQ001','formalization/rq001','docs/formalization/rq001','lean-toolchain','lakefile.toml','lake-manifest.json','integrations/dokuwiki/ilabexplain/action.php',G+'explanations/fixtures',G+'explanations/binding.json',G+'explanations/native-source.json']
assert not subprocess.check_output(['git','diff',BASE,'--',*paths],cwd=R)
for p in subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,'ILab/MathematicsLearning',D+'original'],cwd=R,text=True).splitlines():
    if p.endswith('/source-audit.json'):continue
    assert not subprocess.check_output(['git','diff',BASE,'--',p],cwd=R),p
print(f'PASS: 785 existing declarations unchanged; 31 raw/formula additions; only ten authorized source records; all open obligations, 97 existing narrative contents, manuscript, pins, RQ-001 and shared plugin entry point protected; registry {size} bytes.')
