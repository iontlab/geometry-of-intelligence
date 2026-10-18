import ILab.MathematicsLearning.SetFreeVectors
import ILab.MathematicsLearning.SmallPointedAdjunction
import ILab.MathematicsLearning.SetSubsets

/-! The remaining vector-space bounds, Example 1.13 functors and Example 3.2
adjunction. The free space has exactly the set-coded finitely supported
coefficient functions; its Mathlib correspondence is a linear equivalence. -/
namespace ILab.MathematicsLearning.SmallVectorSpaces
universe u
open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
noncomputable def forget (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    SetCategory.Object (category H K) ⥤ SetCategory.Object (smallSetsCategory H) where
  obj A := ⟨(data A.member).1⟩
  map {A B} f := SetFunction.funsEquiv (data A.member).1.val (data B.member).1.val
    ((toModuleCat H K).map f).hom.toFun
  map_id A := by
    change SetFunction.funsEquiv _ _ ((toModuleCat H K).map (𝟙 A)).hom.toFun =
      SetFunction.funsEquiv _ _ id
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {A B C} f g := by
    change SetFunction.funsEquiv _ _ ((toModuleCat H K).map (f ≫ g)).hom.toFun =
      SetFunction.funsEquiv _ _
        (((SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _
          ((toModuleCat H K).map g).hom.toFun)) ∘
         ((SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _
          ((toModuleCat H K).map f).hom.toFun)))
    simp only [Equiv.symm_apply_apply, CategoryTheory.Functor.map_comp]
    rfl

noncomputable def freeData (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val]
    (A : SetCategory.Object (smallSetsCategory H)) : Data H.small K.val :=
  ⟨⟨SetFreeVectors.carrier A.member.val K.val,
      SetFreeVectors.carrier_mem H.small_universe A.member.property K.property⟩,
    SetFreeVectors.vectorStructure A.member.val K.val⟩

noncomputable def freeObject (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val]
    (A : SetCategory.Object (smallSetsCategory H)) : SetCategory.Object (category H K) :=
  ⟨objectEquiv H.small K.val (freeData H K A)⟩

noncomputable def freeModelIso (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val]
    (A : SetCategory.Object (smallSetsCategory H)) :
    (ModuleCat.free K.val).obj ((smallSetsToTypes H).obj A) ≅
      (toModuleCat H K).obj (freeObject H K A) := by
  change ModuleCat.of K.val (A.member.val →₀ K.val) ≅
    @ModuleCat.of K.val _ (data (objectEquiv H.small K.val (freeData H K A))).1.val
      (data (objectEquiv H.small K.val (freeData H K A))).2.group
      (data (objectEquiv H.small K.val (freeData H K A))).2.module
  have h : data (objectEquiv H.small K.val (freeData H K A)) = freeData H K A :=
    (objectEquiv H.small K.val).symm_apply_apply _
  rw [h]
  exact (SetFreeVectors.linearEquiv A.member.val K.val).toModuleIso

noncomputable def free (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    SetCategory.Object (smallSetsCategory H) ⥤ SetCategory.Object (category H K) :=
  SetCategory.liftToModel (smallSetsToTypes H ⋙ ModuleCat.free K.val) (toModuleCat H K)
    (toModuleCatFullyFaithful H K) (freeObject H K) (freeModelIso H K)

noncomputable def free_model (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    smallSetsToTypes H ⋙ ModuleCat.free K.val ≅ free H K ⋙ toModuleCat H K :=
  SetCategory.liftToModelIso (smallSetsToTypes H ⋙ ModuleCat.free K.val) (toModuleCat H K)
    (toModuleCatFullyFaithful H K) (freeObject H K) (freeModelIso H K)

set_option backward.isDefEq.respectTransparency false in
noncomputable def forget_model (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    toModuleCat H K ⋙ CategoryTheory.forget (ModuleCat K.val) ≅
      forget H K ⋙ smallSetsToTypes H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply TypeCat.homEquiv.injective
    change ((toModuleCat H K).map f).hom.toFun =
      (SetFunction.funsEquiv _ _).symm
        (SetFunction.funsEquiv _ _ ((toModuleCat H K).map f).hom.toFun)
    exact (Equiv.symm_apply_apply _ _).symm)

noncomputable def freeAdjunction (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    free H K ⊣ forget H K :=
  (ModuleCat.adj K.val).restrictFullyFaithful (smallSetsToTypesFullyFaithful H)
    (toModuleCatFullyFaithful H K) (free_model H K) (forget_model H K)

/-- If the object set were small, the union of all its carriers would be small.
The free space indexed by its powerset injects that powerset into the union,
contradicting Cantor. This uses no transitivity or unstated size axiom. -/
theorem not_small (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    ¬ (category H K).IsSmall H.small := by
  intro h
  let B := ZFSet.iUnion (fun A : objects H.small K.val => (data A).1.val)
  have hB : B ∈ H.small :=
    H.small_universe.unions _ h.1 _ (fun A => (data A).1.property)
  let P : SetCategory.Object (smallSetsCategory H) :=
    ⟨⟨ZFSet.powerset B, H.small_universe.powersets B hB⟩⟩
  have hsub : SetFreeVectors.carrier (ZFSet.powerset B) K.val ⊆ B := by
    intro x hx
    apply ZFSet.mem_iUnion.mpr
    refine ⟨(freeObject H K P).member, ?_⟩
    have hd : data (freeObject H K P).member = freeData H K P :=
      (objectEquiv H.small K.val).symm_apply_apply _
    rw [hd]
    exact hx
  let inclusion : SetFreeVectors.carrier (ZFSet.powerset B) K.val → B :=
    fun x => ⟨x.val, hsub x.property⟩
  have hinj : Function.Injective inclusion := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun b : B => b.val) hxy)
  let f : Set B → B := inclusion ∘ SetFreeVectors.basisVector (ZFSet.powerset B) K.val ∘
    SetSubset.equiv B
  exact Function.cantor_injective f
    (hinj.comp ((SetFreeVectors.basisVector_injective _ _).comp (SetSubset.equiv B).injective))

end ILab.MathematicsLearning.SmallVectorSpaces
