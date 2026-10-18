"""Bind source-specific explanations to audited declarations and captured wiki bytes.

The capture directory is private deployment evidence. This tool reads it; it
performs no network write. Publish the resulting assets through WebFTP.
"""
from pathlib import Path
import argparse, copy, datetime, hashlib, html, json, re

p=argparse.ArgumentParser()
p.add_argument('--capture-dir', type=Path, required=True)
p.add_argument('--release', required=True)
a=p.parse_args()
ROOT=Path(__file__).resolve().parents[1]
GRAPH=ROOT/'docs/formalization/mathematics-learning'
EX=GRAPH/'explanations'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def digest(b): return hashlib.sha256(b).hexdigest()
def write(p,x,compact=False):
    p.write_text(json.dumps(x,ensure_ascii=False,indent=None if compact else 2,separators=(',',':') if compact else None)+'\n',encoding='utf-8',newline='\n')
def blocks(s): return [{'type':'paragraph','text':s}]

inventory=read(ROOT/'docs/mathematics-learning/obligations.json')['records']
items={r['key']:r for r in inventory}
headings=read(a.capture_dir/'wiki/statement-headings.json')
captures={c['page_id']:c for c in read(a.capture_dir/'rendered/editor-bindings.json')}
data=read(GRAPH/'data.json');nodes={n['id']:n for n in data['nodes']}
modules={m['name']:m for m in data['modules']}
seed=read(EX/'registry.v0.1.json')
math=read(GRAPH/'mathematics.json')
native_hash=digest((EX/'native-source.json').read_bytes())
math['native_source_sha256']=native_hash
old_keys={'laws','inverse','walking','surjectivity','cardinality','nonsurjective'}
old_sources={'laws':['1.5'],'inverse':['1.11'],'walking':['3.9','3.8','3.4'],
             'surjectivity':['3.9','3.6'],'nonsurjective':['3.9','3.6'],'cardinality':['3.8']}
math['results']={k:v for k,v in math['results'].items() if k in old_keys}
math['declarations']={k:v for k,v in math['declarations'].items() if v['result'] in old_keys}
old_records={r['formal_mapping'].get('result_key'):r for r in seed['records'] if r['formal_mapping'].get('result_key') in old_keys}
assert set(old_records)==old_keys

# These pairs describe each analogy, including only the statements of assignments.
story_pairs={
'1.1': [('Library charter','Closure conditions on the set universe'),('Catalogued books','Sets belonging to that universe')],
'1.2': [('Self-listing library','The assumption U ∈ U'),('Self-excluding subcatalogue','Russell separation inside U')],
'1.3': [('Library, larger library, archive','The three stipulated set universes')],
'1.4': [('Catalogue membership','Smallness, largeness or hugeness relative to the chosen universes')],
'1.5': [('Towns and permits','Objects and morphisms'),('Neutral and combined permits','Identities and composition')],
'1.6': [('Larger archive','A larger permitted universe for objects and hom sets')],
'1.7': [('Permit catalogue for a pair of towns','A hom set'),('Full atlas','The collection of objects')],
'1.8': [('Four rulebooks','Sets, pointed sets, vector spaces and topological spaces'),('Admissible transfers','Their structure-preserving morphisms')],
'1.9': [('Golden permit and return','An isomorphism and its inverse'),('Neutral round trips','The two inverse equations')],
'1.10': [('Return obeying the same rules','An inverse morphism in the same category')],
'1.11': [('Two return permits','Candidate left and right inverses'),('Regrouping permits','Associativity')],
'1.12': [('Fern’s translation','A functor'),('Consistent combined entries','Preservation of composition and identities')],
'1.13': [('Erasing special rules','Forgetful functors'),('Equipping a list','Basepoint, free-vector-space and topology functors')],
'1.14': [('Translated reversible permit','The stated preservation of isomorphisms'),('Unprovided guarantee','The assigned proof, withheld')],
'1.15': [('Atlas of route books','The stated category of categories'),('Links between books','Functors; their category-law checks are withheld')],
'1.16': [('Small-book catalogue in a larger archive','The universe level of the category of small categories')],
'1.17': [('Reversed permits','Morphisms of the opposite category')],
'1.18': [('Translation of the reversed book','A contravariant functor')],
'1.19': [('Permits arriving at one tower','The represented hom sets C(-,c)')],
'1.20': [('Comparisons at towns','Components of a natural transformation'),('Route test','The naturality equation')],
'1.21': [('Changing incoming-permit catalogues','The stated transformation induced by postcomposition')],
'1.22': [('Golden comparison permits','Invertible components of a natural transformation')],
'1.23': [('Catalogue of translators','The stated functor category'),('Comparison permits','Natural transformations')],
'1.24': [('Whole-ledger and town-by-town tests','Invertibility in the functor category and componentwise invertibility')],
'1.25': [('One room and its neutral permit','The terminal one-object category')],
'1.26': [('One-room diagrams','Functors from the terminal category'),('Compatibility with translations','The naturality asserted in Proposition 1.26, whose proof is withheld')],
'1.27': [('Filling the one-room template','The unique functor selecting the specified object')],
'1.28': [('Changing input or output books','The stated precomposition and postcomposition constructions')],
'2.1': [('Compatible labels on incoming permits','A natural transformation from a representable'),('Label at the tower','An element of F(c)')],
'2.2': [('Incoming-permit catalogue','The representable presheaf assigned by Yoneda')],
'2.3': [('Perfect correspondence between permits','Bijectivity on each hom set')],
'2.4': [('Profile catalogue retaining permits','The stated full faithfulness of Yoneda')],
'2.5': [('Detecting reversible permits and towns','The stated reflection of isomorphisms by a fully faithful functor')],
'2.6': [('Every arrival or departure test','Postcomposition or precomposition on all relevant hom sets')],
'2.7': [('Reversibly corresponding incoming catalogues','Naturally isomorphic representable presheaves')],
'3.1': [('Two translation desks','The left and right adjoint functors'),('Round-trip comparisons','Unit and counit'),('Neutral triangle journeys','The triangle identities')],
'3.2': [('Equipping a plain list','The specified left-adjoint constructions'),('Opposite topology desks','Discrete and indiscrete adjunctions with the forgetful functor')],
'3.3': [('Two descriptions of a request','The two hom sets in the stated adjunction correspondence')],
'3.4': [('Translation out and back','Quasi-inverse functors'),('Compatible golden permits','The two natural isomorphisms')],
'3.5': [('Exact return translations','A strict isomorphism of categories'),('Golden adjunction comparisons','Invertible unit and counit')],
'3.6': [('Town represented up to a golden permit','An object isomorphic to one in the functor’s image')],
'3.7': [('Unique permit preimages','Fullness and faithfulness'),('Chosen town representatives','Essential surjectivity with choices used to construct a quasi-inverse')],
'3.8': [('North and south','The two distinct objects'),('One permit per ordered pair','Singleton hom sets')],
'3.9': [('One-room model and two-room ledger','The terminal category and walking isomorphism')],
'intro.what': [('Comparisons between permits','Higher morphisms')],
'intro.higher_morphisms': [('Successive comparison ledgers','Higher morphisms between parallel lower morphisms')],
'intro.invertibility': [('Regrouping certificates and their comparisons','Weak composition laws and higher coherence')],
'intro.paths': [('Redrawn journeys with fixed endpoints','Endpoint-fixed path homotopies')],
'intro.groupoids': [('Reversible path ledger','The motivating fundamental infinity-groupoid')],
'intro.models': [('Blueprints and charter','Concrete models and an axiomatic approach')],
'intro.hott': [('Chosen identifications and their comparisons','Identity types in the intended homotopy type theory')],
'intro.identity': [('Certificates comparing certificates','Iterated identity types')],
'intro.sip': [('Different labels for a two-state group','Isomorphic presentations of the cyclic group of order two'),('Printed identity name','A presentation-dependent property')],
'intro.synthetic': [('A charter with one-way permits','The announced synthetic language with noninvertible morphisms')],
'intro.course': [('Titles of future chapters','Topics announced outside this installment')],
'strict.motivation': [('Differently labelled ledgers','Different presentations of category objects')],
'equivalences.motivation': [('One-room and two-room ledgers','Equivalent categories with different object counts')],
'3.5.adjoint_upgrade': [('Adjusting round-trip certificates','Coherent unit/counit choices for an adjoint equivalence')]
}
assert set(story_pairs)==set(items)

contract={'render_contract':'learning-exact-fragment-1',
          'freshness_endpoint':'ilabexplain_learning_status',
          'boundary':'Exact whole TPL_CONTENT_DISPLAY fragment, with separate anonymous and editor digests; no normalization.',
          'pages':{}}
source_tuples={}
for page,c in captures.items():
    lesson=page.split(':')[-1]
    raw=(a.capture_dir/'wiki'/(lesson+'.txt')).read_bytes()
    assert digest(raw)==c['raw_sha256'],lesson
    document=(a.capture_dir/'rendered'/(lesson+'.anonymous.html')).read_text(encoding='utf-8')
    # This exact template boundary was checked against the live RQ-001 binding digest.
    fragment=document.split('<!-- wikipage start -->\n                    ',1)[1].split('                    <!-- wikipage stop -->',1)[0]
    modified=re.search(r'Last modified: <time datetime="([^"]+)"',document)[1]
    assert int(datetime.datetime.fromisoformat(modified).timestamp())==c['revision']
    contract['pages'][page]={'revision':c['revision'],'raw_sha256':c['raw_sha256'],
        'fragments':{'anonymous':[digest(fragment.encode())],'editor':[c['fragment_sha256']]}}
    (EX/'fixtures').mkdir(exist_ok=True)
    (EX/'fixtures'/(lesson+'.txt')).write_bytes(raw)
    for r in (r for r in inventory if r['page_id']==page):
        expected=headings[r['key']]['heading_text']
        matches=[(anchor,markup) for markup,anchor,text in re.findall(r'(<h[23][^>]*id="([^"]+)"[^>]*>(.*?)</h[23]>)',fragment,re.S) if html.unescape(re.sub('<[^>]+>','',text))==expected]
        assert len(matches)==1,(r['key'],matches)
        anchor,markup=matches[0]
        editor=[h for h in c['headings'] if h['anchor']==anchor and h['text']==expected]
        assert len(editor)==1
        label=(r['kind']+' '+r['key']) if r['kind']!='unnumbered' else r['topic']
        source_tuples[r['key']]={'page_id':page,'revision':c['revision'],'whole_page_sha256':c['raw_sha256'],
            'source_link':r['public_url']+'&rev='+str(c['revision'])+'#'+anchor,
            'anchor':anchor,'legacy_anchor':headings[r['key']].get('legacy_anchor',anchor),'heading_text':expected,'heading_html':markup,
            'heading_html_by_role':{'anonymous':markup,'editor':editor[0]['html']},
            'item_key':r['key'],'item_label':label,
            'primary_sha256':'5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc',
            'primary_items':[{'key':r['key'],'pages':r['source_pages'],'section':r['source_section']}]}

for key in old_keys:
    source_key=old_sources[key][0]
    math['results'][key]['source']=items[source_key]['public_url']
    math['results'][key]['anchor']=source_tuples[source_key]['anchor']
    math['results'][key]['native_key']=source_key
    math['results'][key]['limitation']='This retained declaration is independent supporting mathematics. Complete original-item verification is determined by the source audit and the Source statement selector.'

for r in inventory:
    ids=[n for n in r['lean_declarations'] if n not in math['declarations']]
    if not ids:continue
    assert all(nodes[n]['authored'] for n in ids)
    key='source.'+r['key']
    math['results'][key]={'label':'Primary '+r['key'],'title':r['topic'],
        'native_key':r['key'],
        'source':r['public_url'],'anchor':source_tuples[r['key']]['anchor'],
        'statement':[r['mathematics']], 'proof':[r['proof']],
        'limitation':r['formalization_status']+'. '+r['limit']+' Each referenced signature specifies the precise checked formulation.'}
    for i,n in enumerate(ids):
        math['declarations'][n]={'result':key,'role':'principal' if i==0 else 'supporting'}
write(GRAPH/'mathematics.json',math)
math_hash=digest((GRAPH/'mathematics.json').read_bytes())

records=[]
for r in inventory:
    key=r['key']
    content={'plain':{'title':r['topic'],'blocks':blocks(r['plain'])},
        'story':{'title':'Story / Fairy Tale · '+key,'label':'Story analogy',
          'disclaimer':'This story is an analogy, not the mathematical statement or proof.', 'blocks':blocks(r['story'])},
        'story_key':[{'story_element':x,'scientific_counterpart':y} for x,y in story_pairs[key]],
        'where_analogy_stops':blocks(r['limit'])}
    records.append({'object_key':'explain.mathematics-learning.source.'+key,'kind':'source-item',
        'locale':'en','wiki':headings[key]['inline'],'release_ready':True,
        'review':{'status':'AI-authored; independent human review not claimed'},
        'source':source_tuples[key], 'formal_mapping':{'status':r['formalization_status'],'declarations':r['lean_declarations']},
        'mathematics':{'statement':[r['mathematics']],'proof':[r['proof']]},
        'obligations':r['obligations'],'content':content})

for name,m in math['declarations'].items():
    if m['role']!='principal':continue
    key=m['result'];n=nodes[name]
    if key in old_keys:
        record=copy.deepcopy(old_records[key]);source_key=old_sources[key][0]
    else:
        source_key=key.removeprefix('source.')
        record=copy.deepcopy(next(r for r in records if r['source']['item_key']==source_key))
        record['object_key']='explain.mathematics-learning.graph.'+source_key
        record.pop('obligations');record.pop('mathematics')
    record.update(kind='graph-result',wiki=False)
    record['source']=copy.deepcopy(source_tuples[source_key])
    if key in old_keys:
        record['source']['primary_items']=[source_tuples[k]['primary_items'][0] for k in old_sources[key]]
    record['formal_mapping']={'declaration':name,'result_key':key,'signature':n['signature'],
        'source_file':n['source'],'source_sha256':modules[n['module']]['sha256'].lower(),
        'source_commit':data['sourceRef'],'mathematics_json_sha256':math_hash,
        'pinned_source_link':n['sourceUrl'],'scope_note':math['results'][key]['limitation']}
    records.append(record)

reg={'schema_version':'explanation-content-draft-1','content_format':{'version':'plain-text-blocks-1'},
    'native_source_sha256':native_hash,
    'repository':{'commit':data['sourceRef']},
    'graph':{'data_sha256':digest((GRAPH/'data.json').read_bytes()),'mathematics_sha256':math_hash},
    'release':{'enabled':True,'publication_authorized':True},'records':records}
write(EX/'registry.v0.1.json',reg,compact=True)
assert (EX/'registry.v0.1.json').stat().st_size<500000
write(EX/'binding.json',contract)
write(EX/'release.json',{'enabled':True,'publication_authorized':True,'release':a.release,
    'render_contract':contract['render_contract'],'registry_sha256':digest((EX/'registry.v0.1.json').read_bytes())})
assert len(source_tuples)==58
print(f'{len(records)} bound records: 58 source items, {len(records)-58} graph explanations; {sum(r["wiki"] for r in records)} inline controls; {len(math["declarations"])} Blueprint declarations; registry {(EX/"registry.v0.1.json").stat().st_size} bytes.')
