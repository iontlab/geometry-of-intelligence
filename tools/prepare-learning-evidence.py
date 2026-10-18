"""Prepare current verification records and wiki updates from checked release data."""
from pathlib import Path
from collections import Counter
import json,sys
ROOT=Path(__file__).resolve().parents[1]
W=Path(sys.argv[1]);G=ROOT/'docs/formalization/mathematics-learning';V=ROOT/'formalization/mathematics-learning/verification';D=ROOT/'docs/mathematics-learning'
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def text(p,s):p.write_text(s,encoding='utf-8',newline='\n')
data=read(G/'data.json');math=read(G/'mathematics.json');reg=read(G/'explanations/registry.v0.1.json');items=read(D/'obligations.json')['records']
source={r['source']['item_key']:r for r in reg['records'] if r['kind']=='source-item'}
authored=[n for n in data['nodes'] if n['authored']]
blue=set(math['declarations']);auth=set(n['id'] for n in authored)
blue_edges=sum(e['source'] in blue and e['target'] in blue for e in data['edges'])
auth_edges=sum(e['source'] in auth and e['target'] in auth for e in data['edges'])
counts=dict(Counter(o['status'] for r in items for o in r['obligations']))
summary={'source_ref':data['sourceRef'],'lean':data['lean'],'mathlib_revision':data['mathlibRevision'],'audit_exit_code':0,
 'compiled_declarations':len(data['nodes']),'authored_declarations':len(authored),'direct_edges':len(data['edges']),
 'blueprint_declarations':len(blue),'blueprint_edges':blue_edges,'authored_visible_edges':auth_edges,
 'source_modules':data['modules'],'foundational_axioms':['Classical.choice','Quot.sound','propext'],
 'build_status':'Clean project build succeeded (8937 jobs), followed by the 225-declaration compiler audit.',
 'source_items':58,'obligations':132,'obligation_status_counts':counts,'exercise_markers':17,'exercise_items':15,
 'inline_controls':47,'graph_explanations':37,'source_inspector_items':58}
write(V/'audit-summary.json',summary)
mapping=[]
for n in authored:
    mapping.append({'declaration':n['id'],'kind':n['sourceKind'],'source':n['sourceUrl'],
        'primary_items':[r['key'] for r in items if n['id'] in r['lean_declarations']],
        'signature':n['signature'],'axioms':n['axioms'],'external_dependencies':n['externalDependencies']})
write(V/'declaration-mapping.json',mapping)
write(V/'mathlib-reuse.json',[r for r in mapping if r['external_dependencies']])
text(V/'all-declaration-axioms.txt','\n'.join(n['id']+': '+(', '.join(n['axioms']) or '(none)') for n in data['nodes'])+'\n')
text(V/'declaration-audit.log','PASS: extracted and audited 225 project declarations from compiled Lean types and values.\n')
for f in ['live-assets-readback.json','live-inline-qa.json']:
    write(D/('expanded-'+f),read(W/f))
for lesson in ['foundations','size','categories','functors','natural_transformations','yoneda','adjunctions','equivalences']:
    text(D/'wiki-current'/(lesson+'.txt'),(W/'wiki'/(lesson+'.txt')).read_text(encoding='utf-8'))

wiki='''====== Non-exercise mathematics — verification ======

**[Draft] · Checked statements have exact, item-specific scope.** The binding source is Lyne Moser (Universität Hamburg) and Tashi Walde (Universität Regensburg), //Lecture Notes: Synthetic Category Theory//, the supplied 13-page installment. [[:mathematics_learning:higher_category_theory:synthetic_category_theory:sources|Attribution, official author links and source conventions]]. This is independent iLab exposition with AI assistance, not a verbatim republication or an assertion of author endorsement. Independent human mathematical review is not claimed.

===== Current checked release =====

The existing Lean 4.34.0 / pinned Mathlib v4.34.0 project passed a clean build (8937 jobs), then a compiler audit of **225 declarations in nine learning modules**, including **116 authored declarations**. The graph has **428 direct project-local dependency edges**. Its Mathematical Blueprint has **109 mapped declarations and 70 direct visible edges**; the ordinary authored-declaration view has **84 visible edges**. Compiler-generated declarations are available through the Full Lean Graph toggle.

The audit rejects admitted expressions, project-added axioms and any foundational dependency outside ''propext'', ''Classical.choice'' and ''Quot.sound''. Exact types, source hashes and transitive axiom dependencies are recorded. Definitions, assumptions and Mathlib wrappers are distinguished from newly written proofs; compilation does not turn a definition or a universe assumption into an existence theorem.

The source inventory contains **58 items and 132 individually tracked obligations**: 112 are checked in their stated Lean formulations; 15 records intentionally withhold assigned solutions; five require a specified higher model or different foundations. The 15 withholding records account for all 17 exercise markers across 15 numbered items. Multiple assigned steps within one item remain one explicit withholding record. This is not a claim that all 13 pages are fully Lean-formalized.

===== Teaching boundary =====

Assigned proofs and checks are withheld for **1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded opposite-isomorphism exercise in 2.6, and 3.3**. Statements, numbering and attribution remain. Proposition 1.26 is explicitly an assigned proof despite its proposition label. The non-assigned main hom-set criterion in 2.6 remains checked; its assigned opposite-arrow step is not exported as a solution.

The previous publication needed correction: solution walkthroughs in four lessons and six exercise-related authored exports, with two generated helpers, were withdrawn from the current edition. The expanded release also withholds prepared exercise solutions. Historical Git commits and wiki revisions can still contain withdrawn material; current-edition removal does not erase that history. [[:mathematics_learning:higher_category_theory:synthetic_category_theory:coverage|Complete source inventory and exclusion table]].

===== Checked scope and remaining boundaries =====

The checked ordinary material includes category, functor and natural-transformation definitions; identities and associativity; inverse uniqueness; the four category examples and their isomorphisms; seven functor examples; non-exercise Yoneda consequences; four adjunction examples; quasi-inverse equivalences and the general equivalence criterion; and the finite walking-isomorphism example. Existing Mathlib results are reused explicitly and are not claimed as original iLab theorems.

The set-universe module encodes the stated closure properties in ''ZFSet'' and proves consequences under the supplied hierarchy assumptions. It does not prove that the stipulated universes exist. Category-size examples use explicitly scoped Lean type universes, not a literal ZFSet encoding of every source category. Equality transport and a cyclic-two/sign-group example are checked; these do not prove univalence or the Structure Identity Principle.

Five source obligations remain outside the available foundations: introduction p. 1 all-dimensional weak coherence; pp. 1–2 the full fundamental infinity-groupoid; pp. 2–3 types as infinity-groupoids; p. 2 faithful non-proof-irrelevant iterated identities; and p. 3 the Structure Identity Principle. Endpoint-fixed path homotopies and their ordinary fundamental groupoid are checked scoped results, not a solution to those full higher-foundation obligations. The source's future course topics supply no additional proof-bearing statements in this installment.

===== Working explanation controls =====

The existing eight lessons have 47 inline controls: all 44 numbered statements, plus three scoped introductory/adjoint-upgrade entries. Each opens **Mathematics | Plain | Story | Lean | Verification** for that source item. The graph provides the same five layers for 37 principal results, with supporting declarations linked to their main result. Internal helpers retain only meaningful technical layers. A source selector also gives access to all 58 inventory items without adding fictitious graph nodes.

The release binds every explanation to an exact chapter revision and raw-source digest, a stable heading, the primary PDF reference and, where applicable, the actual Lean signature, module hash and source commit. The approved extension of the existing ''ilabexplain'' plugin checks exact server-rendered fragments and current source freshness. Stale or unavailable bindings withhold the interactive explanation. AI authorship and the absence of independent human review are stated explicitly.

Plain and Story were exercised in the live browser in all eight chapters. The public graph's five-layer theorem deep link was also exercised. All 16 deployed learning assets match the staged release, while all 14 protected live RQ-001 graph/explanation assets remain byte-identical. The four RQ-001 source modules and evidence are unchanged; its fresh compiler extraction reproduces all 202 declarations byte-for-byte.

===== Reproduce and inspect =====

''SOURCE_COMMIT'' is the exact checked Lean source commit. Lean commit: ''293d5d0c0c3f3dded4688b3ccd6a33939ac5102b''. Mathlib revision: ''5ed2965256430c3649e86755f9576b54eca72435''.

[[https://iontlab.org/formalization/mathematics-learning/|Interactive graph]] · [[https://github.com/iontlab/geometry-of-intelligence/tree/codex/mathematics-learning-parity/formalization/mathematics-learning/verification|Build, audit, source mappings and Mathlib provenance]] · [[https://github.com/iontlab/geometry-of-intelligence/blob/codex/mathematics-learning-parity/docs/mathematics-learning/obligations.json|All source obligations]]

^ Source module ^ SHA-256 ^
'''.replace('SOURCE_COMMIT',data['sourceRef'])
wiki=wiki.replace('**84 visible edges**',f'**{auth_edges} visible edges**')
for m in data['modules']:
    wiki+='| '+m['name'].split('.')[-1]+'.lean | '+"''"+m['sha256'].lower()+"''"+' |\n'
wiki+='\nBack: [[:mathematics_learning:higher_category_theory:synthetic_category_theory:coverage|Source coverage]] · [[:mathematics_learning:higher_category_theory:synthetic_category_theory:start|Reading path]]\n'
text(W/'wiki/verification.txt',wiki)

old=(W.parent/'exercise-correction/wiki/coverage.txt').read_text(encoding='utf-8')
head=old.split('===== Numbered items =====')[0]
start=head.index('**Formalization status:**')
head=head[:start]+'''**Formalization status:** nine modules, 225 compiler-audited declarations and 132 tracked obligations. Of these obligations, 112 are checked in their stated formulations, 15 deliberately withhold assigned solutions, and five require a different higher model or foundations. These counts do not assert full Lean coverage of the source. [[:mathematics_learning:higher_category_theory:synthetic_category_theory:verification|Exact scopes and evidence]].\n\n'''
for kind,title in [('numbered','Numbered items'),('unnumbered','Substantive unnumbered material')]:
    head+='===== '+title+' =====\n\n^ Source item ^ PDF pages ^ Topic and exact chapter anchor ^ Source proof status ^ Formalization status / inspector ^\n'
    for r in items:
        if (r['kind']=='unnumbered')!=(kind=='unnumbered'):continue
        s=source[r['key']]['source'];label=(r['kind']+' '+r['key']) if kind=='numbered' else r['key']
        status=r['formalization_status'].replace('|','/')
        head+='| '+label+' | '+', '.join(map(str,r['source_pages']))+' | [[:'+r['page_id']+'#'+s['anchor']+'|'+r['topic'].replace('|','/')+']] | '+r['source_proof_status'].replace('|','/')+' | [[https://iontlab.org/formalization/mathematics-learning/?statement='+r['key']+'&layer=verification|'+status+']] |\n'
    head+='\n'
head+=old[old.index('===== Assigned exercises excluded from publication ====='):]
text(W/'wiki/coverage.txt',head)
print(json.dumps(summary|{'source_modules':len(data['modules'])},indent=2))
