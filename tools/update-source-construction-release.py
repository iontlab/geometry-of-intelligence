"""Refresh only approved G1–G10 mappings and their existing release integrity links."""
from pathlib import Path
import runpy
CAP=runpy.run_path(str(Path(__file__).with_name('learning-capacity.py')))
import copy,hashlib,json,runpy,subprocess
R=Path(__file__).resolve().parents[1];D=R/'docs/mathematics-learning';G=R/'docs/formalization/mathematics-learning';E=G/'explanations'
BASE='1cd4fe15b242ed59a7dc2c5d3e155405355b49df'
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,o,compact=False):p.write_text(json.dumps(o,ensure_ascii=False,indent=None if compact else 2,separators=(',',':') if compact else None)+'\n',encoding='utf-8',newline='\n')
spec=runpy.run_path(str(Path(__file__).with_name('source-construction-repairs.py')))['REPAIRS']
narratives=runpy.run_path(str(Path(__file__).with_name('source-construction-narratives.py')))['content']
old=json.loads(subprocess.check_output(['git','show',BASE+':docs/formalization/mathematics-learning/explanations/registry.v0.1.json'],cwd=R))
reg=copy.deepcopy(old); data=load(G/'data.json');nodes={n['id']:n for n in data['nodes']};modules={m['name']:m for m in data['modules']}
records={r['key']:r for r in load(D/'obligations.json')['records']};math=load(G/'mathematics.json')
principals={'1.15':'identityFunctor_object','1.17':'oppositeObjectData','1.21':'postcompositionComponent','1.23':'identityComponent','1.28':'precompositionComponent','3.3':'adjunctionForward'}
prefix='ILab.MathematicsLearning.SetCategory.'
for key in spec:
    r=records[key];source=next(x for x in reg['records'] if x['object_key']=='explain.mathematics-learning.source.'+key)
    source['formal_mapping']={'status':r['formalization_status'],'declarations':r['lean_declarations']}
    source['mathematics']['proof']=[r['proof']];source['obligations']=r['obligations']
    if key in principals:
        result='source.'+key
        math['results'][result]={'label':'Primary '+key+' · partial data','title':source['content']['plain']['title'],'native_key':key,'source':r['public_url'],'anchor':source['source']['anchor'],'statement':[r['mathematics']],'proof':[r['proof']],'limitation':r['limit']}
        for n in r['lean_declarations']:
            if n not in math['declarations']:
                math['declarations'][n]={'result':result,'role':'principal' if n==prefix+principals[key] else 'supporting'}
        graph=copy.deepcopy(source);graph.update(object_key='explain.mathematics-learning.graph.'+key,kind='graph-result',wiki=False)
        graph.pop('mathematics');graph.pop('obligations');graph['content']=narratives(key)
        graph['formal_mapping']={'declaration':prefix+principals[key],'result_key':result};reg['records'].append(graph)
    elif key=='2.6':
        result=math['declarations'][prefix+'postcomposition_bijections_detect_isomorphism']['result']
        math['results'][result]['limitation']=r['limit'];math['results'][result]['proof']=[r['proof']]
        math['declarations'][prefix+'oppositePostcomposeReadback']={'result':result,'role':'supporting'}
    elif key=='1.19':
        result=math['declarations'][prefix+'representable_object']['result']
        math['declarations'].setdefault(prefix+'representableInSmallSets',{'result':result,'role':'supporting'})

# G10 uses the exact heading observed in the internal browser and independently
# matched against anonymous HTML in the saved source-location evidence.
page='mathematics_learning:higher_category_theory:synthetic_category_theory:adjunctions'
contract=load(E/'binding.json')['pages'][page]
heading='<h3 class="sectionedit3" id="adjunctions_and_equivalences">3. Adjunctions and equivalences</h3>'
assert contract['revision']==1792321145 and contract['raw_sha256']=='cfcb5112d5da54bf836e37b27ad83b8d5ed3f8c18ad5be2aa3c0f83065c54f6e'
for r in reg['records']:
    if r['source']['item_key']=='equivalences.motivation':
        r['source'].update(page_id=page,revision=contract['revision'],whole_page_sha256=contract['raw_sha256'],source_link='https://iontlab.org/doku.php?id='+page+'&rev='+str(contract['revision'])+'#adjunctions_and_equivalences',anchor='adjunctions_and_equivalences',heading_text='3. Adjunctions and equivalences',heading_html=heading,heading_html_by_role={'anonymous':heading,'editor':heading})
math['results']['source.equivalences.motivation'].update(source='https://iontlab.org/doku.php?id='+page,anchor='adjunctions_and_equivalences')
save(G/'mathematics.json',math)
reg['repository']['commit']=data['sourceRef'];reg['graph']={'data_sha256':sha(G/'data.json'),'mathematics_sha256':sha(G/'mathematics.json')}
for r in reg['records']:
    if r['kind']!='graph-result':continue
    f=r['formal_mapping'];n=nodes[f['declaration']]
    f.update(signature=n['signature'],source_file=n['source'],source_sha256=modules[n['module']]['sha256'].lower(),source_commit=data['sourceRef'],mathematics_json_sha256=reg['graph']['mathematics_sha256'],pinned_source_link=n['sourceUrl'],scope_note=math['results'][f['result_key']]['limitation'])
for a in old['records']:
    b=next(x for x in reg['records'] if x['object_key']==a['object_key'])
    assert a['content']==b['content'],a['object_key']
    if a['source']['item_key']!='equivalences.motivation':assert a['source']==b['source']
serialized=(json.dumps(reg,ensure_ascii=False,separators=(',',':'))+'\n').encode('utf-8')
print('Complete serialized registry:',len(serialized),'bytes; headroom:',CAP['capacity']()['registry_bytes']-len(serialized))
# Keep a reviewable candidate even when the publication gate rejects it.
candidate=R.parent/'sct-ten-gaps-20261018/registry-candidate.json';candidate.write_bytes(serialized)
assert CAP['check_registry'](serialized)>=5000,'STOP: registry lacks a 5,000-byte safety margin; do not publish'
(E/'registry.v0.1.json').write_bytes(serialized)
release=load(E/'release.json');release.update(release='learning-native-20261019-source-gaps-r13',capacity_sha256=CAP['capacity_hash'](),registry_sha256=sha(E/'registry.v0.1.json'));save(E/'release.json',release)
save(G/'source-audit.json',load(D/'original/native/source-audit.json'))
print('PASS: existing 97 record contents preserved, six new graph narratives; release integrity refreshed.')
