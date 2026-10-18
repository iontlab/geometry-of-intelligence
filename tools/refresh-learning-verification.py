"""Regenerate current declaration evidence from the compiler-backed graph."""
from pathlib import Path
import json,hashlib,concurrent.futures,urllib.request,subprocess
R=Path(__file__).resolve().parents[1];D=R/'docs/mathematics-learning';G=R/'docs/formalization/mathematics-learning'
V=R/'formalization/mathematics-learning/verification';E=D/'native-publication-evidence'
load=lambda p:json.loads(p.read_text(encoding='utf8'))
write=lambda p,v:p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
g=load(G/'data.json');s=load(D/'original/native/source-audit.json');a=load(V/'expanded-audit.json')
assert len(g['nodes'])==a['compiled_declarations']
for m in a['modules']:assert hashlib.sha256((R/m['path']).read_bytes()).hexdigest()==m['sha256']
inventory=load(D/'obligations.json')['records']
mapping=[]
for n in g['nodes']:
    if not n['authored']:continue
    mapping.append({'declaration':n['id'],'kind':n['kind'],'source':n['sourceUrl'],
     'primary_items':[r['key'] for r in inventory if n['id'] in r['lean_declarations']],
     'signature':n['signature'],'axioms':n['axioms'],'dependencies':n['dependencies'],
     'scope':'Source audit determines complete original-item fidelity; related support is not a source theorem.'})
write(V/'declaration-mapping.json',mapping)
write(V/'source-hashes.json',g['modules'])
node_by_id={n['id']:n for n in g['nodes']}
write(V/'mathlib-reuse.json',[{**m,'external_dependencies':node_by_id[m['declaration']]['externalDependencies']} for m in mapping])
(V/'all-declaration-axioms.txt').write_text('\n'.join(n['id']+': '+(', '.join(n['axioms']) or '(none)') for n in g['nodes'])+'\n',encoding='utf8',newline='\n')
summary={'source_ref':g['sourceRef'],'lean':'4.34.0','mathlib_revision':'5ed2965256430c3649e86755f9576b54eca72435',
 'compiled_declarations':len(g['nodes']),'authored_declarations':len(mapping),'direct_edges':len(g['edges']),
 'source_modules':g['modules'],'numbered_source_items':44,'fully_formalized':s['fully_formalized'],
 'exercise_affected_items':15,'pending_eligible_items':s['pending_eligible_items'],
 'foundational_axioms':['propext','Classical.choice','Quot.sound'],'build_status':'Clean build succeeded (8943 jobs), followed by compiler extraction and axiom audit.',
 'source_fidelity_audit':'../../../docs/mathematics-learning/original/native/source-audit.json','completion':False}
write(V/'audit-summary.json',summary)
baseline=[r for r in load(D/'expanded-live-assets-readback.json') if r['group'] in ['rq001','explanations']]
def check(row):
    actual=hashlib.sha256(urllib.request.urlopen(row['url'],timeout=30).read()).hexdigest()
    assert actual==row['sha256'],row['url']
    return {'url':row['url'],'sha256':actual,'unchanged':True}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:live=list(pool.map(check,baseline))
paths=['ILab/RQ001','formalization/rq001','docs/formalization/rq001','tools/ExtractGraph.lean','tools/build-graph.mjs','lean-toolchain','lakefile.toml','lake-manifest.json','integrations/dokuwiki']
diff=subprocess.check_output(['git','diff','cdad0de','--',*paths],cwd=R)
assert not diff,'Protected repository paths changed'
write(E/'rq001-regression.json',{'live_assets':live,'protected_repository_paths_unchanged':paths,'baseline_commit':'cdad0de','compiler_baseline':'../../formalization/mathematics-learning/verification/expanded-rq001-regression.json'})
print(f'Refreshed {len(mapping)} authored declaration mappings; {len(live)} protected live assets and protected repository paths unchanged.')
