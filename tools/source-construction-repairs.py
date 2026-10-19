"""Approved G1–G9 mappings; consumed by the existing source audit and release tools."""
P='ILab.MathematicsLearning.'
S=P+'SetCategory.'
def sc(names):return [S+n for n in names.split()]
def formulas(names):return [S+n+'_formula' for n in names.split()]
REPAIRS={
 '1.15':dict(reuse=[P+'SmallCategoryUniverse.'+n for n in ['category','smallCategories','largeCategories','homEquiv']]+sc('functorCodeEquiv'),raw=[],formula=sc('identityFunctor_object identityFunctor_arrow compositeFunctor_object compositeFunctor_arrow'),scope='Existing source category/functor codes and homEquiv are reused. Identity and composite object/arrow formulas are read back on their membership models. Category laws remain inherited infrastructure; the source category-well-definedness exercise is withheld.'),
 '1.17':dict(reuse=[],raw=sc('oppositeObjectData oppositeHomData oppositeIdentityData oppositeComposeData'),formula=formulas('oppositeObjectData oppositeHomData oppositeIdentityData oppositeComposeData'),scope='Same object set, reversed hom sets, unchanged identity, and reversed raw composition only. No opposite SetCategory or category-law proof is constructed; well-definedness remains assigned.'),
 '1.19':dict(reuse=sc('representableInSmallSets representable_object representable_map'),raw=[],formula=[],scope='Reuse the existing small hom-set object and precomposition graph formulas from 2.7, retaining its mappings and local-smallness premise. Library functor infrastructure is not a source-authored solution of the assigned functor-well-definedness check.'),
 '1.21':dict(reuse=[],raw=sc('postcompositionComponent'),formula=formulas('postcompositionComponent'),scope='For f:c→d the component at x sends g:x→c to g ≫ f. It returns an arrow in the source hom set, not a natural transformation. Naturality/well-definedness remains assigned.'),
 '1.23':dict(reuse=sc('SourceFunctor functorEquiv SourceTransformation transformationEquiv'),raw=sc('identityComponent verticalCompositeComponent'),formula=formulas('identityComponent verticalCompositeComponent'),scope='Given functors and transformations, expose only id at F(x) and α_x ≫ β_x. Components are raw arrows; their naturality and the functor-category laws remain assigned.'),
 '1.28':dict(reuse=[],raw=sc('precompositionComponent postcompositionTransformationComponent'),formula=sc('compositeFunctor_object compositeFunctor_arrow')+formulas('precompositionComponent postcompositionTransformationComponent'),scope='Precomposition sends G to F ⋙ G with component α_(Fx); postcomposition sends G to G ⋙ F with component F(α_x). Existing functor composition supplies the object assignments. Neither whole whiskering functor nor either assigned well-definedness check is exported.'),
 '2.2':dict(reuse=sc('representableInSmallSets representable_object representable_map postcompositionComponent postcompositionComponent_formula'),raw=[],formula=[],scope='Share the representable object/arrow formulas of 1.19 and the raw arrow component of 1.21. The local-smallness premise remains. These assignments are not a completed Yoneda functor; functor well-definedness and full faithfulness remain unproved as source exercises.'),
 '2.6':dict(reuse=sc('postcomposition_bijections_detect_isomorphism'),raw=[],formula=sc('oppositePostcomposeReadback'),scope='Preserve the checked (i)↔(ii). For f:c→d and g:d→x, (g.op ≫ f.op).unop = f ≫ g identifies the induced map. The authors’ further reduction assumes the assigned IsIso f ↔ IsIso f.op. Only the formula is added: no opposite set-coded model or full three-way proof. isoIffPrecompositionBijective is independent Mathlib support.'),
 '3.3':dict(reuse=[],raw=sc('adjunctionForward adjunctionBackward unitCandidateComponent counitCandidateComponent'),formula=formulas('adjunctionForward adjunctionBackward unitCandidateComponent counitCandidateComponent'),scope='From a given adjunction: g↦η_x ≫ R(g) and f↦L(f) ≫ ε_y. Conversely, GIVEN hom-set bijections φ natural in x,y: η_x=φ_(x,Lx)(id), ε_y=φ_(Ry,y)⁻¹(id). The component formulas use underlying bijections only; naturality of φ is source context, not proved. Mutual inverses, naturality of hom maps/candidates, and both triangle checks remain assigned. No complete representable adjunction theorem is verified.'),
}
for r in REPAIRS.values():r['declarations']=r['reuse']+r['raw']+r['formula']

def apply_record(record, previous):
    key=record['key']; spec=REPAIRS[key]
    record['formalization_status']='Verified authored data/formulas only; assigned checks remain open'
    if key=='2.6':record['formalization_status']='Author-proved (i) iff (ii) and map formula verified; assigned opposite-invertibility withheld'
    record['lean_declarations']=spec['declarations'];record['limit']=spec['scope']
    record['proof']=spec['scope']+' Assigned exercise solution withheld.'
    # Keep every existing open obligation and its stable identifier verbatim.
    withheld=[o for o in previous['obligations'] if o['status']=='assigned exercise solution withheld']
    record['obligations']=[{'id':key+'.'+kind,'statement':label,'status':status,'declarations':spec[kind],'scope':'Partial data only; assigned checks withheld.'}
      for kind,label,status in [('reuse','Existing checked model/formula reuse','existing_checked_mathlib_or_model_reuse'),('raw','Authors’ raw data or component functions','authored_raw_data_verified'),('formula','Definitional formula readbacks','authored_formula_readback_verified')] if spec[kind]]+withheld
    assert withheld,key
    # Explicit classification alongside existing status wording, without changing open tasks.
    record['exercise_checks']='exercise_checks_withheld'
