"""Source-first, item-level correspondence. Counts never infer mathematical fidelity.

This is an editorial audit checked against the original manuscript, not a
compiler proof of the correspondence. Every mapped declaration must exist
in the independently extracted compiler inventory. Pending items stay pending.
"""
from pathlib import Path
import hashlib, json
R=Path(__file__).resolve().parents[1]
D=R/'docs/mathematics-learning'
G=R/'docs/formalization/mathematics-learning'
load=lambda p:json.loads(p.read_text(encoding='utf8'))
def save(p,o):p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf8',newline='\n')
P='ILab.MathematicsLearning.'
full={
 '1.1':('SetUniverse','Exactly the four closure clauses on ZFC sets. No transitivity clause is added.'),
 '1.2':('universe_not_member','The source Russell separation argument proves U ∉ U using its stated subset closure.'),
 '1.3':('UniverseHierarchy','Three universes, their subset inclusions and both membership hypotheses are explicit data; existence is assumed.'),
 '1.4':('IsSmallSet IsLargeSet IsHugeSet','Small, large and huge mean literal membership in the three stipulated universes.'),
 '1.5':('SetCategory','Objects and hom sets belong to the stipulated large universe; all identity, composition and associativity data are fields. Membership-type functions correspond to set functions by SetFunction.graphEquiv.'),
 '1.6':('SetCategory','Use SetCategory H.large for strict categories and SetCategory H.huge for huge strict categories. Both object and hom bounds are literal membership.'),
 '1.7':('SetCategory.IsLocallySmall SetCategory.IsSmall','The two source membership predicates are explicit, including the small object set in IsSmall.'),
 '1.9':('SetCategory.IsIsomorphism SetCategory.ObjectsIsomorphic','Existential two-sided inverse and existential isomorphism between objects, on the original set members. No choice of inverse is required by the predicate.'),
 '1.11':('SetCategory.unique_inverse','Given an isomorphism, proves existence and uniqueness of a two-sided inverse. The source identity/composition operations agree definitionally with the represented Mathlib operations.'),
 '1.12':('SetCategory.SourceFunctor SetCategory.functorEquiv','The object function, every hom function and both laws are explicit; a proved two-way data equivalence relates these to Mathlib functors on the identical object/hom members.'),
 '1.18':('SetCategory.SourceContravariantFunctor SetCategory.contravariantFunctorEquiv','The reversed hom functions and reversed composition law match the source, with a proved two-way data correspondence to functors from the opposite membership-type category.'),
 '1.20':('SetCategory.SourceTransformation SetCategory.transformationEquiv','The component functions and naturality square are preserved by a proved data equivalence; Lean writes composition in the opposite textual order.'),
 '1.22':('SetCategory.IsNaturalIsomorphism','Exactly pointwise existence of two-sided inverses. This definition does not export the assigned proof of Proposition 1.24.'),
 '1.25':('terminalSetCategory terminalObject terminal_object_unique terminal_morphism_unique','The object set and every hom set are literal singletons belonging to the source large universe.'),
 '1.27':('selectSetObject selectSetObject_unique','For each original object, proves unique existence of a functor from the set-coded singleton category taking its object to that object. Does not construct the assigned functor-category isomorphism in 1.26.'),
 '2.3':('SetCategory.IsFullyFaithful','Exactly bijectivity of every hom function on the source object and morphism members.'),
 '3.1':('SetCategory.SourceAdjunction SetCategory.sourceAdjunction_left_triangle SetCategory.sourceAdjunction_right_triangle','Mathlib Adjunction has precisely the unit, counit, and two component triangle equations; here it is instantiated only on the faithfully represented set-coded categories and functors.'),
 '3.4':('SetCategory.IsEquivalence','Existential reverse functor and unit/counit natural transformations with pointwise two-sided inverses. No triangle equation is added to the definition.'),
 '3.5':('SetCategory.strict_inverse_is_equivalence SetCategory.adjoint_equivalences SetCategory.equivalence_promotes_to_adjoint','Both bullets and the final Fact are proved: strict inverses imply equivalence, both functors of an adjoint equivalence are equivalences, and every equivalence admits an adjoint upgrade.'),
 '3.6':('SetCategory.IsEssentiallySurjective SetCategory.essentiallySurjective_agrees','For every target object, an actual source object and isomorphism from its image are required. The library correspondence is proved on those same objects and morphisms.'),
 '3.7':('SetCategory.fundamental_theorem','Both directions connect the source existential quasi-inverse condition with essential-surjectivity witnesses and bijectivity on every hom set. Original Proof. Next time. remains unchanged in the manuscript.'),
 '3.8':('walkingSetCategory walkingZero walkingOne walking_zero_ne_one walking_objects walking_hom_singleton walkingSetIso','Two distinct ZFC object codes, exactly those two objects, literal singleton hom sets, identities and mutually inverse arrows.'),
 '3.9':('includeWalkingZero walking_inclusion_equivalence','The actual singleton-to-walking-isomorphism inclusion is proved an equivalence in the source definition. The printed 0≅0 in the original prose is retained, not silently corrected.'),
}
pending={
 '1.8':('smallSetsCategory smallSets_locallySmall smallSets_not_small','Set is complete. Pointed sets, topological spaces and vector spaces still need explicit bounded set codes, operation-preserving Mathlib correspondences, and non-smallness proofs for those exact collections.'),
 '1.10':('smallSets_isomorphism_iff_bijective','Set is complete. The isomorphism characterizations for pointed sets, vector spaces and topological spaces require the pending exact structured-set encodings from 1.8.'),
 '1.13':('','The forgetful, added-basepoint, free-vector-space, discrete and indiscrete functors need set-coded object/hom implementations and operation-preserving correspondences. Existing type-universe examples alone do not close this item.'),
 '1.16':('','Needs set codes for all small categories and their functors, hom-set membership in the small universe, non-smallness of the exact object collection, and the huge-category inclusion. Construction 1.15 category-law exercise must remain withheld.'),
 '2.7':('','The ordinary Mathlib Yoneda result is retained as independent support. Still needs a representation theorem for the actual small-set-valued representables and their natural isomorphisms, preserving the source universe domains without publishing the assigned 1.19/2.1/2.4 solutions.'),
 '3.2':('','The four actual example adjunctions require the pending structured-set categories and functors from 1.8/1.13, including the exact free-vector-space carrier and source universe bounds.'),
}
assigned={a['item'] for a in load(D/'exercise-exclusions.json')['assignments']}
nodes={n['id']:n for n in load(G/'compiled.json')}
old=load(D/'obligations.json')
history=D/'original/native/prior-independent-inventory.json'
if not history.exists():save(history,old)
baseline={r['key']:r for r in load(history)['records']}
source=load(D/'original/native/items.json')
rows=[]
for item in source:
    key=item['key']; prev=baseline[key]
    if key in assigned:
        names='';status='exercise_withheld'
        reason=('The embedded opposite-invertibility step is assigned. Original complete portions and the exercise marker remain. No completed assigned proof is mapped.' if key=='2.6' else 'Assigned proof/construction checks are withheld. The complete original statement and every author-written partial proof remain published.')
    elif key in full:
        names,reason=full[key];status='fully_formalized'
    else:
        names,reason=pending[key];status='pending'
    declarations=[P+n for n in names.split()]
    assert all(n in nodes for n in declarations),(key,declarations)
    rows.append({'key':key,'chapter':item['chapter'],'kind':item['kind'],
      'source_pages':item['source_pages'],'source_native_file':item['native_source'],
      'source_line':item['source_line'],'source_sha256':item['sha256'],
      'status':status,'declarations':declarations,'correspondence':reason,
      'prior_independent_declarations':prev['lean_declarations'],
      'prior_mapping_assessment':'Previous generic/category-type declarations alone were not treated as proof of the source set-universe formulation. Valid independent work is retained.'})
assert len(rows)==44 and len(full)==23 and len(pending)==6 and len(assigned)==15
chapter_counts={}
for chapter in ['foundations','size','categories','functors','natural_transformations','yoneda','adjunctions','equivalences']:
    subset=[r for r in rows if r['chapter']==chapter]
    chapter_counts[chapter]={'numbered_items':len(subset),**{k:sum(r['status']==k for r in subset) for k in ['fully_formalized','exercise_withheld','pending']}}
save(D/'original/native/source-audit.json',{
 'source_pdf_sha256':hashlib.sha256((D/'original/moser-walde-13-pages.pdf').read_bytes()).hexdigest(),
 'review':'Source-first editorial correspondence checked against the manuscript; no independent human review or compiler proof of prose equivalence claimed.',
 'numbered_items':44,'fully_formalized':23,'exercise_affected_items':15,'pending_eligible_items':6,
 'completion':False,'chapter_counts':chapter_counts,'items':rows,
 'unnumbered':'Fourteen interface passage groups are retained separately. Introductory higher identity types, univalence, all-dimensional coherence and the proposed synthetic extension await the authors’ later axioms. They are not replaced by Lean Eq or ordinary categories.'})

# Update the existing inventory fields used by the unchanged controls.
current=[]
for prev in old['records']:
    r=dict(prev); key=r['key']
    row=next((x for x in rows if x['key']==key),None)
    if row:
        r['formalization_status']={'fully_formalized':'Faithfully formalized and compiler-verified in the source set-universe representation','pending':'Incomplete original source obligation','exercise_withheld':'Assigned exercise solution withheld; original text retained'}[row['status']]
        r['lean_declarations']=row['declarations']
        r['limit']=row['correspondence']
        r['obligations']=[{'id':key+'.source','statement':row['correspondence'],
          'status':'assigned exercise solution withheld' if key in assigned else r['formalization_status'],
          'declarations':row['declarations'],'scope':row['correspondence']}]
    else:
        # Existing contextual declarations are retained, explicitly as support.
        r['formalization_status']='Source passage / supporting ordinary mathematics; no complete higher-foundation verification claimed'
        if key=='3.5.adjoint_upgrade':
            r['lean_declarations']=[P+'SetCategory.equivalence_promotes_to_adjoint']
            r['formalization_status']='Faithfully formalized with the source set-universe bounds; included in item 3.5, not counted twice'
    current.append(r)
save(D/'obligations.json',{**old,'records':current,'source_fidelity_audit':'original/native/source-audit.json'})
coverage=load(D/'coverage.json')
for row in coverage['records']:
    r=next(r for r in current if r['key']==row['key'])
    row['lean_status']=r['formalization_status'];row['lean_declarations']=r['lean_declarations']
save(D/'coverage.json',coverage)
print('44 numbered source items: 23 fully formalized; 15 exercise-affected; 6 eligible items pending. Overall objective remains incomplete.')
