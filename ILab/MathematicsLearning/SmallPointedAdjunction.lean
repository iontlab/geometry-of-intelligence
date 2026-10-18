import ILab.MathematicsLearning.SmallPointedSets
import ILab.MathematicsLearning.SetOption
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! The adjoined-basepoint functor and adjunction on the actual small-set
categories. The library adjunction is restricted only after the object and
hom correspondences, including the commuting squares, have been proved. -/
namespace ILab.MathematicsLearning
universe u
open CategoryTheory

noncomputable def smallSetsToTypes (H : UniverseHierarchy.{u}) :
    SetCategory.Object (smallSetsCategory H) ⥤ Type (u+1) where
  obj A := A.member.val
  map {A B} f := TypeCat.homEquiv.symm ((SetFunction.funsEquiv A.member.val B.member.val).symm f)
  map_id A := by
    apply TypeCat.homEquiv.injective
    change (SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _ id) = id
    exact Equiv.symm_apply_apply _ _
  map_comp {A B C} f g := by
    apply TypeCat.homEquiv.injective
    change (SetFunction.funsEquiv _ _).symm
      (SetFunction.funsEquiv _ _
        ((SetFunction.funsEquiv _ _).symm g ∘ (SetFunction.funsEquiv _ _).symm f)) = _
    exact Equiv.symm_apply_apply _ _

noncomputable def smallSetsToTypesFullyFaithful (H : UniverseHierarchy.{u}) :
    (smallSetsToTypes H).FullyFaithful where
  preimage {A B} f := SetFunction.funsEquiv A.member.val B.member.val (TypeCat.homEquiv f)
  map_preimage {A B} f := by
    apply TypeCat.homEquiv.injective
    change (SetFunction.funsEquiv A.member.val B.member.val).symm
      (SetFunction.funsEquiv A.member.val B.member.val (TypeCat.homEquiv f)) =
        TypeCat.homEquiv f
    exact Equiv.symm_apply_apply _ _
  preimage_map f := Equiv.apply_symm_apply _ _

namespace SmallPointedSets

noncomputable def toPointedFullyFaithful (H : UniverseHierarchy.{u}) :
    (toPointed H).FullyFaithful :=
  SetCategory.modelFullyFaithful (objects_mem H) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

noncomputable def addedPointData (H : UniverseHierarchy.{u})
    (A : SetCategory.Object (smallSetsCategory H)) : Data H.small :=
  ⟨⟨SetOption.carrier A.member.val,
    SetOption.carrier_mem H.small_universe A.member.property⟩, SetOption.point A.member.val⟩

noncomputable def addedPointObject (H : UniverseHierarchy.{u})
    (A : SetCategory.Object (smallSetsCategory H)) : SetCategory.Object (category H) :=
  ⟨objectEquiv H.small (addedPointData H A)⟩

noncomputable def addedPointModelIso (H : UniverseHierarchy.{u})
    (A : SetCategory.Object (smallSetsCategory H)) :
    typeToPointed.obj ((smallSetsToTypes H).obj A) ≅
      (toPointed H).obj (addedPointObject H A) := by
  change Pointed.of (none : Option A.member.val) ≅
    Pointed.of (data (objectEquiv H.small (addedPointData H A))).2
  have h : data (objectEquiv H.small (addedPointData H A)) = addedPointData H A :=
    (objectEquiv H.small).symm_apply_apply _
  rw [h]
  exact Pointed.Iso.mk (SetOption.equiv A.member.val) rfl

/-- Example 1.13: the set-coded disjoint addition of one distinguished point. -/
noncomputable def addPoint (H : UniverseHierarchy.{u}) :
    SetCategory.Object (smallSetsCategory H) ⥤ SetCategory.Object (category H) :=
  SetCategory.liftToModel (smallSetsToTypes H ⋙ typeToPointed) (toPointed H)
    (toPointedFullyFaithful H) (addedPointObject H) (addedPointModelIso H)

noncomputable def addPoint_model (H : UniverseHierarchy.{u}) :
    smallSetsToTypes H ⋙ typeToPointed ≅ addPoint H ⋙ toPointed H :=
  SetCategory.liftToModelIso (smallSetsToTypes H ⋙ typeToPointed) (toPointed H)
    (toPointedFullyFaithful H) (addedPointObject H) (addedPointModelIso H)

set_option backward.isDefEq.respectTransparency false in
noncomputable def forget_model (H : UniverseHierarchy.{u}) :
    toPointed H ⋙ CategoryTheory.forget Pointed ≅ forget H ⋙ smallSetsToTypes H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply TypeCat.homEquiv.injective
    change ((toPointed H).map f).toFun =
      (SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _ ((toPointed H).map f).toFun)
    exact (Equiv.symm_apply_apply _ _).symm)

/-- Example 3.2: actual small-set addition is left adjoint to forgetting the point. -/
noncomputable def addPointAdjunction (H : UniverseHierarchy.{u}) : addPoint H ⊣ forget H :=
  typeToPointedForgetAdjunction.restrictFullyFaithful
    (smallSetsToTypesFullyFaithful H) (toPointedFullyFaithful H)
    (addPoint_model H) (forget_model H)

end SmallPointedSets
end ILab.MathematicsLearning
