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
full.update({
 '1.8':('smallSetsCategory smallSets_locallySmall smallSets_not_small SmallPointedSets.category SmallPointedSets.locallySmall SmallPointedSets.not_small SmallVectorSpaces.category SmallVectorSpaces.locallySmall SmallVectorSpaces.not_small SmallTopologicalSpaces.category SmallTopologicalSpaces.locallySmall SmallTopologicalSpaces.not_small',
   'All four categories use actual small ZFC carriers and structure-preserving function graphs. Injective pointed/topology/vector codes give large object sets; all hom sets belong to the small universe. Proved operation-preserving hom bijections justify the Mathlib models. Every exact object collection is proved not small. The coefficient field is small under the source convention that sets are small unless otherwise specified.'),
 '1.10':('smallSets_isomorphism_iff_bijective SmallPointedSets.isomorphism_iff_bijective SmallVectorSpaces.isomorphism_iff_bijective SmallTopologicalSpaces.isomorphism_iff_homeomorphism',
   'The four tests apply to the actual Example 1.8 set-coded morphisms: bijections, point-preserving bijections, linear bijections, and homeomorphisms. Fully faithful model bridges preserve the exact underlying functions and inverse equations.'),
 '1.13':('SmallPointedSets.forget SmallVectorSpaces.forget SmallTopologicalSpaces.forget SmallPointedSets.addPoint SmallVectorSpaces.free SmallTopologicalSpaces.discrete SmallTopologicalSpaces.indiscrete SmallTopologicalSpaces.discrete_opens SmallTopologicalSpaces.indiscrete_opens SetFreeVectors.linearEquiv',
   'All seven functors operate on the exact set-coded categories. Forgetful functors retain the carrier and graph. The adjoined point is the Option-equivalent disjoint-point set; free vectors are actual graphs of finitely supported coefficient functions with a proved linear equivalence to the direct sum. Discrete and indiscrete open sets are proved exactly P(S) and {empty,S}. Commuting model isomorphisms certify the object and arrow correspondences.'),
 '1.16':('SmallCategoryUniverse.smallCategoriesAsHugeObject SmallCategoryUniverse.hugeObject_decodes SmallCategoryUniverse.smallCategories_locallySmall SmallCategoryUniverse.smallCategories_not_small SmallCategoryUniverse.smallObjectEquiv SetCategory.functorCodeEquiv',
   'Injective ZFC codes retain complete category and functor data. A proved bijection includes every source-small strict category, not a skeleton. Functor codes lie in an explicit small function-set bound; the category object collection is large and not small. Its complete code is an object of the huge category of large categories. Existing Mathlib Cat laws are reused internally through the general model bridge; no independent solution of the assigned 1.15 category-law checks is exported.'),
 '2.7':('SetCategory.representable_objects_isomorphic_iff SetCategory.representable_object SetCategory.representable_map SetCategory.representable_model',
   'Representables take values in the actual small hom sets and their arrows are literally the graphs of source precomposition. The proved model correspondence transports natural isomorphisms in both directions. The conclusion uses the source componentwise two-sided-inverse definition. Mathlib Yoneda is reused internally for this non-exercise corollary; no independent proofs of the assigned 1.19/2.1/2.4 exercises are supplied.'),
 '3.2':('SmallPointedSets.addPointAdjunction SmallVectorSpaces.freeAdjunction SmallTopologicalSpaces.discreteAdjunction SmallTopologicalSpaces.indiscreteAdjunction',
   'All four unit/counit adjunctions are on the actual Example 1.8 categories and Example 1.13 functors. The library adjunctions are restricted only after fully faithful hom correspondences and both commuting model squares have been proved. Free-vector, disjoint-point and topology carriers satisfy the source universe bounds. No general assigned 3.3 hom-bijection proof is exported.'),
})
pending={}
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
        if key=='2.6':
            names='SetCategory.postcomposition_bijections_detect_isomorphism'
            status='mixed_exercise'
            reason='The author-proved (i) iff (ii) portion is verified on the exact source hom members, retaining local smallness. The assigned opposite-invertibility step and a complete three-way proof remain withheld; this item is not counted as fully formalized.'
        if key=='2.1':
            names='SetCategory.yonedaEvaluation SetCategory.yonedaCandidateComponent SetCategory.yonedaEvaluation_formula SetCategory.yonedaCandidateComponent_formula'
            status='partial_construction'
            reason='Verified author-supplied construction steps on the original small-set carriers: evaluation alpha_c(id_c), and the candidate component functions f maps to F(f)(u), with definitional formula readbacks. The candidate is only a family of functions, not a completed natural transformation. Its naturality, mutual inverseness, and naturality in c and F remain assigned exercises; the complete Yoneda theorem is not verified here. The existing representable and set-function bridge are reused as prerequisites, not counted as newly solved exercises.'
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
assert len(rows)==44 and len(full)==29 and len(pending)==0 and len(assigned)==15
chapter_counts={}
for chapter in ['foundations','size','categories','functors','natural_transformations','yoneda','adjunctions','equivalences']:
    subset=[r for r in rows if r['chapter']==chapter]
    chapter_counts[chapter]={'numbered_items':len(subset),**{k:sum(r['status']==k for r in subset) for k in ['fully_formalized','exercise_withheld','pending']}}
    chapter_counts[chapter]['exercise_withheld']+=sum(r['status'] in ['mixed_exercise','partial_construction'] for r in subset)
save(D/'original/native/source-audit.json',{
 'source_pdf_sha256':hashlib.sha256((D/'original/moser-walde-13-pages.pdf').read_bytes()).hexdigest(),
 'review':'Source-first editorial correspondence checked against the manuscript; no independent human review or compiler proof of prose equivalence claimed.',
 'numbered_items':44,'fully_formalized':len(full),'exercise_affected_items':15,'pending_eligible_items':len(pending),
 'completion':False,'chapter_counts':chapter_counts,'items':rows,
 'unnumbered':'Fourteen interface passage groups are retained separately. Introductory higher identity types, univalence, all-dimensional coherence and the proposed synthetic extension await the authors’ later axioms. They are not replaced by Lean Eq or ordinary categories.'})

# Update the existing inventory fields used by the unchanged controls.
current=[]
for prev in old['records']:
    r=dict(prev); key=r['key']
    row=next((x for x in rows if x['key']==key),None)
    if row:
        r['formalization_status']={'fully_formalized':'Faithfully formalized and compiler-verified in the source set-universe representation','pending':'Incomplete original source obligation','exercise_withheld':'Assigned exercise solution withheld; original text retained','mixed_exercise':'Author-proved (i) iff (ii) verified; embedded exercise solution withheld','partial_construction':'Verified author-supplied construction steps; complete Yoneda theorem not verified; assigned checks remain open'}[row['status']]
        r['lean_declarations']=row['declarations']
        r['limit']=row['correspondence']
        r['obligations']=[{'id':key+'.source','statement':row['correspondence'],
          'status':'assigned exercise solution withheld' if key in assigned else r['formalization_status'],
          'declarations':row['declarations'],'scope':row['correspondence']}]
        if key=='2.6':
            r['obligations'][0]['status']='Author-proved (i) iff (ii) verified on exact source hom sets'
            r['obligations'].append({'id':key+'.exercise','statement':'The opposite-invertibility step is assigned by the authors.','status':'assigned exercise solution withheld','declarations':[],'scope':'No independently generated solution or complete three-way proof is published.'})
        if key=='2.1':
            r['proof']='The authors explicitly define evaluation alpha maps to alpha_c(id_c), and candidate components (alpha_u)_x(f)=F(f)(u). These functions and their defining formulas are checked on the source small-set carriers. Assigned exercise solution withheld: naturality of the candidate family, mutual inverseness, and naturality in c and F. No completed candidate natural transformation or Yoneda bijection is exported.'
            r['obligations']=[
              {'id':'2.1.evaluation','statement':'Evaluation at the identity: alpha maps to alpha_c(id_c).','status':'Verified author-supplied construction step','declarations':[P+'SetCategory.yonedaEvaluation',P+'SetCategory.yonedaEvaluation_formula'],'scope':'A function on already given natural transformations; the formula readback is definitional.'},
              {'id':'2.1.components','statement':'For u in F(c), the component at x sends f:x -> c to F(f)(u).','status':'Verified author-supplied construction step','declarations':[P+'SetCategory.yonedaCandidateComponent',P+'SetCategory.yonedaCandidateComponent_formula'],'scope':'Only the family of component functions is constructed, not a natural transformation.'},
              *[{'id':'2.1.'+k,'statement':s,'status':'assigned exercise solution withheld','declarations':[],'scope':'Open: no proof or completed construction exported.'} for k,s in [('candidate_naturality','Check that the candidate components form a well-defined natural transformation.'),('mutual_inverse','Check that evaluation and the proposed inverse are mutually inverse.'),('parameter_naturality','Check naturality in both c and F.')]]]
    else:
        # Existing contextual declarations are retained, explicitly as support.
        r['formalization_status']='Source passage / supporting ordinary mathematics; no complete higher-foundation verification claimed'
        if key=='3.5.adjoint_upgrade':
            r['lean_declarations']=[P+'SetCategory.equivalence_promotes_to_adjoint']
            r['formalization_status']='Faithfully formalized with the source set-universe bounds; included in item 3.5, not counted twice'
            r['obligations']=[{'id':key+'.source','statement':'Every source equivalence can be promoted to an adjoint equivalence.','status':r['formalization_status'],'declarations':r['lean_declarations'],'scope':'The source quasi-inverse is promoted on the same set-coded categories.'}]
        if key=='intro.sip':
            r['lean_declarations']=[P+n for n in ('order_two_invariant equality_substitution equality_transport ConcreteGroupPresentations.presentationIso ConcreteGroupPresentations.zeroOne_multiplication ConcreteGroupPresentations.signs_multiplication ConcreteGroupPresentations.zeroOne_identity ConcreteGroupPresentations.signs_identity_ne_zero').split()]
            r['limit']='The concrete integer carriers {0,1} and {1,-1}, their exact operations and different numerical identities are represented by proved equivalences. Order-two invariance and equality transport are checked. The higher Structure Identity Principle itself awaits the authors’ later univalent foundations.'
            r['obligations']=[{'id':key+'.concrete','statement':'The two printed integer-carrier groups are isomorphic, but only the first has numerical identity zero; order-two existence is invariant under group isomorphism. Equality transports predicates and structures.','status':'Precisely specified ordinary mathematical assertions verified','declarations':r['lean_declarations'],'scope':r['limit']},
              {'id':key+'.higher','statement':'Group identifications correspond to group isomorphisms in the intended higher identity types.','status':'Awaits later source definitions and univalent foundations','declarations':[],'scope':'No ordinary Lean equality replacement or invented axiom is used.'}]
        if key=='equivalences.motivation':
            r['lean_declarations']=[P+n for n in ('walking_inclusion_equivalence strict_inverse_object_bijective walking_not_strictly_isomorphic_sets').split()]
            r['limit']='The exact set-coded one-object and two-object categories are equivalent but have no strictly inverse functors; strict inverses imply an actual object bijection. Prospective synthetic equality-isomorphism principles await later axioms.'
            r['obligations']=[{'id':key+'.strict','statement':'Strict inverse functors give a bijection of object sets; equivalent categories need not have one.','status':'Verified on the exact set-coded categories','declarations':r['lean_declarations'],'scope':r['limit']},
              {'id':key+'.synthetic','statement':'The intended synthetic foundation builds in invariance under isomorphism.','status':'Prospective source description; later axioms awaited','declarations':[],'scope':'No missing synthetic foundations are invented.'}]
    assert all(n in nodes for n in r['lean_declarations']), (key,r['lean_declarations'])
    current.append(r)
save(D/'obligations.json',{**old,'records':current,'source_fidelity_audit':'original/native/source-audit.json'})
coverage=load(D/'coverage.json')
for row in coverage['records']:
    r=next(r for r in current if r['key']==row['key'])
    row['lean_status']=r['formalization_status'];row['lean_declarations']=r['lean_declarations']
save(D/'coverage.json',coverage)
print('44 numbered source items: 29 faithfully formalized; 15 exercise-affected; no eligible numbered item pending. Later higher axioms remain explicitly deferred; release completion requires fresh live QA.')
