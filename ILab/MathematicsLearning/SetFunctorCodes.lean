import ILab.MathematicsLearning.SetCategoryCodes

/-! Codes for exactly the object and hom functions of Definition 1.12.
The bounding set is explicit and small; it does not presume that a type
universe is the manuscript's set universe. -/
namespace ILab.MathematicsLearning.SetCategory
universe u
open CategoryTheory SetIndexedFamily
variable {U : ZFSet.{u}} {C D : SetCategory U}

noncomputable def functorObjectCode (F : SourceFunctor C D) : ZFSet.{u} :=
  graph C.objects (fun x => (F.obj ⟨x⟩).member.val)

noncomputable def functorMapCode (F : SourceFunctor C D) : ZFSet.{u} :=
  graph C.objects (fun x => graph C.objects (fun y =>
    graph (C.hom x y) (fun f => (F.map (X := ⟨x⟩) (Y := ⟨y⟩) f).val)))

noncomputable def functorCode (F : SourceFunctor C D) : ZFSet.{u} :=
  ZFSet.pair (functorObjectCode F) (functorMapCode F)

theorem functorCode_injective (C D : SetCategory U) :
    Function.Injective (@functorCode U C D) := by
  rintro ⟨obj, map, hid, hcomp⟩ ⟨obj', map', hid', hcomp'⟩ h
  obtain ⟨ho, hm⟩ := ZFSet.pair_inj.mp h
  have heobj : obj = obj' := by
    funext x
    apply (objectEquiv D).injective
    apply Subtype.ext
    exact congrFun (graph_injective C.objects ho) x.member
  cases heobj
  have hemap : @map = @map' := by
    funext x y f
    apply Subtype.ext
    have hx := congrFun (graph_injective C.objects hm) x.member
    have hy := congrFun (graph_injective C.objects hx) y.member
    exact congrFun (graph_injective (C.hom x.member y.member) hy) f
  cases hemap
  rfl

noncomputable def functorBound (C D : SetCategory U) : ZFSet.{u} :=
  ZFSet.prod (ZFSet.funs C.objects D.objects)
    (ZFSet.funs C.objects (ZFSet.funs C.objects (ZFSet.powerset (ZFSet.prod (allHoms C) (allHoms D)))))

theorem functorBound_mem (hU : SetUniverse U) (C D : SetCategory U) : functorBound C D ∈ U :=
  hU.product_mem (hU.functions_mem C.objects_mem D.objects_mem)
    (hU.functions_mem C.objects_mem (hU.functions_mem C.objects_mem
      (hU.powersets _ (hU.product_mem (allHoms_mem hU C) (allHoms_mem hU D)))))

theorem functorCode_mem_bound (F : SourceFunctor C D) : functorCode F ∈ functorBound C D := by
  apply ZFSet.pair_mem_prod.mpr
  constructor
  · exact graph_mem_funs _ (fun x => (F.obj ⟨x⟩).member.property)
  · apply graph_mem_funs
    intro x
    apply graph_mem_funs
    intro y
    apply ZFSet.mem_powerset.mpr
    intro z hz
    obtain ⟨f, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨hom_subset_allHoms C x y f.property,
      hom_subset_allHoms D _ _ (F.map f).property⟩

theorem sourceFunctor_small (C D : SetCategory U) : Small.{u} (SourceFunctor C D) :=
  small_of_injective
    (f := fun F : SourceFunctor C D => (⟨functorCode F, functorCode_mem_bound F⟩ : functorBound C D))
    (by
      intro F G h
      exact functorCode_injective C D (congrArg (fun x : functorBound C D => x.val) h))

noncomputable def functorCodes (C D : SetCategory U) : ZFSet.{u} :=
  letI := sourceFunctor_small C D
  ZFSet.range (@functorCode U C D)

noncomputable def functorCodeEquiv (C D : SetCategory U) :
    SourceFunctor C D ≃ functorCodes C D := by
  letI := sourceFunctor_small C D
  exact Equiv.ofBijective (fun F => ⟨functorCode F, ZFSet.mem_range_self F⟩)
    ⟨by
      intro F G h
      exact functorCode_injective C D (congrArg (fun x : functorCodes C D => x.val) h), by
      intro G
      obtain ⟨F, hF⟩ := ZFSet.mem_range.mp G.property
      exact ⟨F, Subtype.ext hF⟩⟩

theorem functorCodes_mem (hU : SetUniverse U) (C D : SetCategory U) : functorCodes C D ∈ U := by
  let := sourceFunctor_small C D
  apply hU.subsets _ (functorBound_mem hU C D)
  intro F hF
  obtain ⟨G, rfl⟩ := ZFSet.mem_range.mp hF
  exact functorCode_mem_bound G

end ILab.MathematicsLearning.SetCategory
