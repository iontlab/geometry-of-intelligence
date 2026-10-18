"""Bind independently authored source obligations to actual audited declarations.

Editorial correspondence is explicit metadata, not a compiler theorem that
the prose is equivalent to a signature. Every referenced declaration must
exist in the compiled audit; the review does not claim human sign-off.
"""
from pathlib import Path
import json, re
R=Path(__file__).resolve().parents[1]
D=R/'docs/mathematics-learning'
G=R/'docs/formalization/mathematics-learning'
def load(p): return json.loads(p.read_text(encoding='utf-8'))
def save(p,o): p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
spec=load(D/'numbered-statements.json')|load(D/'unnumbered-statements.json')
coverage=load(D/'coverage.json')
exclusions={a['item']:a for a in load(D/'exercise-exclusions.json')['assignments']}
nodes={n['id']:n for n in load(G/'compiled.json')}
P='ILab.MathematicsLearning.'
# Groups correspond, in order, to the individual source obligations.
bindings={
'1.1':['SetUniverse','SetUniverse.naturals SetUniverse.subsets SetUniverse.powersets SetUniverse.unions'],
'1.2':['universe_not_member'],
'1.3':['UniverseHierarchy'],
'1.4':['IsSmallSet IsLargeSet IsHugeSet','smallSet_is_large largeSet_is_huge'],
'1.5':['StrictCategory','categoryLeftIdentity','categoryRightIdentity','categoryAssociativity'],
'1.6':['StrictCategory'],
'1.7':['LocallySmallCategory','SmallStrictCategory'],
'1.8':['setsCategory','pointedSetsCategory','vectorSpacesCategory','spacesCategory','sets_locally_small pointed_locally_small vector_spaces_locally_small spaces_locally_small','sets_not_small pointed_sets_not_small vector_spaces_not_small spaces_not_small collection_of_small_sets_not_small'],
'1.9':['Isomorphism','invertible_iff_two_sided_inverse','ObjectsIsomorphic'],
'1.10':['setIsoIffBijective','pointed_iso_iff_bijective','vector_iso_iff_bijective','topIsoIffHomeomorphism'],
'1.11':['inverse_unique'],
'1.12':['CategoryFunctor','functorIdentityLaw','functorCompositionLaw'],
'1.13':['forgetPoint','forgetVector','forgetTopology','addBasepoint','freeVectorSpace freeVectorMapOnBasis','discreteTopology','indiscreteTopology'],
'1.16':['smallCategoriesAsLargerObject','small_categories_locally_small','small_categories_not_small'],
'1.18':['ContravariantFunctor','functorIdentityLaw contravariant_composition'],
'1.20':['NaturalTransformation','naturalityEquation'],
'1.22':['ComponentwiseNaturalIsomorphism','ComponentwiseNaturalIsomorphism'],
'1.25':['TerminalCategory OneRoom','oneRoomCategory','functorToTerminal functorToTerminal_unique'],
'1.27':['selectObject','terminal_functor_unique'],
'2.3':['fullyFaithfulIffBijective','fullyFaithfulHomEquiv'],
'2.6':['isoIffPostcompositionBijective','isoIffPrecompositionBijective',None],
'2.7':['yoneda_object_iso_iff'],
'3.1':['AdjunctionData','naturalityEquation','adjunctionLeftTriangle','adjunctionRightTriangle'],
'3.2':['basepointAdjunction','vectorSpaceAdjunction','discreteAdjunction','indiscreteAdjunction'],
'3.4':['QuasiInverseData','equivalenceToQuasiInverse','quasiInverseToEquivalence'],
'3.5':['categoryIsoToEquivalence','adjunctionToEquivalence','adjunctionToEquivalence'],
'3.6':['EssentiallySurjective','essentially_surjective_iff'],
'3.7':['quasi_inverse_iff_fully_faithful_essSurj','quasi_inverse_iff_fully_faithful_essSurj','quasi_inverse_iff_fully_faithful_essSurj','quasi_inverse_iff_fully_faithful_essSurj'],
'3.8':['Room','roomCategory','roomIso','room_cardinality'],
'3.9':['includeRoom','walking_inclusion_full walking_inclusion_faithful','inclusion_essentially_surjective','walkingEquivalence','inclusion_not_surjective'],
'intro.invertibility':[None],
'intro.paths':['pathCompositionAssociativity','pathLeftIdentity pathRightIdentity','pathLeftInverse pathRightInverse',None],
'intro.hott':[None],
'intro.identity':[None],
'intro.sip':['equality_substitution','equality_transport','order_two_invariant','cyclicTwoSigns cyclic_two_zero_maps_to_one cyclic_two_one_maps_to_neg_one',None],
'equivalences.motivation':['one_room_cardinality','walking_not_strictly_isomorphic'],
'3.5.adjoint_upgrade':['quasiInverseToEquivalence'],
}
# Split compound source checks where independently testable assertions occur.
fine={
'1.1': [('Encode the four set-universe closure conditions','SetUniverse'),('Naturals belong to the universe','SetUniverse.naturals'),('Subset closure','SetUniverse.subsets'),('Power-set closure','SetUniverse.powersets'),('Indexed-union closure','SetUniverse.unions')],
'1.4': [('Define small membership','IsSmallSet'),('Define large membership','IsLargeSet'),('Define huge membership','IsHugeSet'),('Small implies large','smallSet_is_large'),('Large implies huge','largeSet_is_huge')],
'1.8': [(label+' forms a category',d) for label,d in [('Sets','setsCategory'),('Pointed sets','pointedSetsCategory'),('Vector spaces','vectorSpacesCategory'),('Topological spaces','spacesCategory')]]+
        [(label+' is locally small',d) for label,d in [('Sets','sets_locally_small'),('Pointed sets','pointed_locally_small'),('Vector spaces','vector_spaces_locally_small'),('Topological spaces','spaces_locally_small')]]+
        [(label+' is not small in the type-universe formulation',d) for label,d in [('Sets','sets_not_small'),('Pointed sets','pointed_sets_not_small'),('Vector spaces','vector_spaces_not_small'),('Topological spaces','spaces_not_small')]]+
        [('In the explicit ZFC formulation, the collection of U-small sets is not U-small','collection_of_small_sets_not_small')],
'3.1': [('Unit natural transformation','adjunctionUnit'),('Counit natural transformation','adjunctionCounit'),('Unit naturality','adjunction_unit_naturality'),('Counit naturality','adjunction_counit_naturality'),('Left triangle identity','adjunctionLeftTriangle'),('Right triangle identity','adjunctionRightTriangle')],
'intro.paths': [('Associativity up to endpoint-fixed homotopy','pathCompositionAssociativity'),('Left identity up to homotopy','pathLeftIdentity'),('Right identity up to homotopy','pathRightIdentity'),('First inverse homotopy','pathLeftInverse'),('Second inverse homotopy','pathRightInverse'),('Full all-dimensional groupoid in a precise higher model',None)],
}
for key in exclusions:
    if key != '2.6':
        fine.pop(key,None)
        bindings[key]=[None]*len(spec[key]['obligations'])
bindings['1.22']=['ComponentwiseNaturalIsomorphism']*len(spec['1.22']['obligations'])
bindings['2.6'][-1]=None
for key,pairs in fine.items():
    spec[key]['obligations']=[a for a,b in pairs]
    bindings[key]=[b for a,b in pairs]
records=[]
for source in coverage['records']:
    key=source['key']; s=spec[key]
    groups=bindings.get(key,[])
    assert len(groups)==len(s['obligations']), (key,len(groups),len(s['obligations']))
    obligations=[]
    for i,(statement,group) in enumerate(zip(s['obligations'],groups),1):
        exercise = key in exclusions and (key!='2.6' or i==3)
        ids=[P+n for n in group.split()] if group else []
        assert all(n in nodes for n in ids), [key,[n for n in ids if n not in nodes]]
        status='assigned exercise solution withheld' if exercise else 'checked in the stated Lean formulation' if ids else 'requires different foundations or a specified higher-category model'
        note=('The lecturers assign this proof or construction check. Statements and source-supplied data remain; no solution is published.' if exercise else
              'Lean is proof-irrelevant; these notes only announce the intended higher foundations. No all-dimensional coherence or univalence theorem is claimed.' if not ids else
              'A typed ordinary-category formulation. Lean type-universe bounds are not literal membership in the source’s three ZFC set-universes.' if key in {'1.5','1.6','1.7','1.8','1.15','1.16'} else
              'Exact checked data/law or an explicitly scoped Mathlib reuse. Construction fields and equivalence inverse laws are part of the referenced signatures/data.')
        obligations.append(dict(id=key+'.'+str(i),statement=statement,status=status,declarations=ids,scope=note))
    declarations=list(dict.fromkeys(n for o in obligations for n in o['declarations']))
    # Only source-authored declarations are principal UI targets; projections
    # remain in the obligation evidence and compiled graph as generated nodes.
    source_names=set()
    for path in (R/'ILab/MathematicsLearning').glob('*.lean'):
        source_names.update(P+m[1] for m in re.findall(r'^(?:noncomputable\s+)?(structure|inductive|def|abbrev|instance|theorem|lemma)\s+(\w+)',path.read_text(encoding='utf-8'),re.M))
    authored=[n for n in declarations if n in source_names]
    r={k:source[k] for k in ['key','kind','source_section','original_number','source_pages','lesson','page_id','public_url','source_proof_status','dependencies','topic']}
    r.update(s)
    r['obligations']=obligations;r['lean_declarations']=authored
    r['formalization_status']=('Assigned exercise solution withheld; source statement retained' if key in exclusions and key!='2.6' else
        'Non-exercise hom-bijection criterion checked; embedded opposite-invertibility exercise withheld' if key=='2.6' else
        'Not proof-bearing; source definition or motivation without a supplied formal higher model' if not obligations else
        'Partially checked; higher-foundation obligation remains' if any(not o['declarations'] for o in obligations) and authored else
        'Requires the intended higher foundations/model' if not authored else
        'Checked ordinary type-universe formulation; literal set-coded size bridge not claimed' if key in {'1.5','1.6','1.7','1.8','1.15','1.16'} else
        'Checked definition/hypotheses or proof in the stated Lean formulation')
    source['lean_status']=r['formalization_status'];source['lean_declarations']=authored
    source['lean_feasibility']='Assigned solutions excluded by teaching scope, independently of formalizability.' if key in exclusions else 'See obligation-level inventory for exact scope, proof reuse and remaining foundation obligations.'
    records.append(r)
assert len(records)==58
save(D/'obligations.json',dict(schema=1,source_sha256=coverage['source_sha256'],review='AI-authored source alignment; no independent human review claimed',records=records))
save(D/'coverage.json',coverage)
print(f"{len(records)} source items; {sum(len(r['obligations']) for r in records)} individually tracked obligations")
