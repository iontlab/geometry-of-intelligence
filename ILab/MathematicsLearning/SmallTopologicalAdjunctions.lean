import ILab.MathematicsLearning.SmallTopologicalSpaces
import ILab.MathematicsLearning.SmallPointedAdjunction

/-! The exact topology functors of Example 1.13 and their Example 3.2
adjunctions on ZFC small-set carriers. The representations commute with
Mathlib's functors, and the unit/counit adjunctions are restricted along those
proved correspondences. -/
namespace ILab.MathematicsLearning.SmallTopologicalSpaces
universe u
open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
noncomputable def forget (H : UniverseHierarchy.{u}) :
    SetCategory.Object (category H) ⥤ SetCategory.Object (smallSetsCategory H) where
  obj A := ⟨(data A.member).1⟩
  map {A B} f := SetFunction.funsEquiv (data A.member).1.val (data B.member).1.val
    ((toTopCat H).map f).hom.toFun
  map_id A := by
    change SetFunction.funsEquiv _ _ ((toTopCat H).map (𝟙 A)).hom.toFun =
      SetFunction.funsEquiv _ _ id
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {A B C} f g := by
    change SetFunction.funsEquiv _ _ ((toTopCat H).map (f ≫ g)).hom.toFun =
      SetFunction.funsEquiv _ _
        (((SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _
          ((toTopCat H).map g).hom.toFun)) ∘
         ((SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _
          ((toTopCat H).map f).hom.toFun)))
    simp only [Equiv.symm_apply_apply, CategoryTheory.Functor.map_comp]
    rfl

noncomputable def topologyObject (H : UniverseHierarchy.{u})
    (A : SetCategory.Object (smallSetsCategory H)) (t : TopologicalSpace A.member.val) :
    SetCategory.Object (category H) := ⟨objectEquiv H.small ⟨A.member, t⟩⟩

noncomputable def topologyModelIso (H : UniverseHierarchy.{u})
    (A : SetCategory.Object (smallSetsCategory H)) (t : TopologicalSpace A.member.val) :
    @TopCat.of A.member.val t ≅ (toTopCat H).obj (topologyObject H A t) := by
  change @TopCat.of A.member.val t ≅
    @TopCat.of (data (objectEquiv H.small ⟨A.member, t⟩)).1.val
      (data (objectEquiv H.small ⟨A.member, t⟩)).2
  have h : data (objectEquiv H.small ⟨A.member, t⟩) = ⟨A.member, t⟩ :=
    (objectEquiv H.small).symm_apply_apply _
  rw [h]

/-- The discrete topology is precisely the ZFC powerset in the source. -/
theorem discrete_opens (A : ZFSet.{u}) : opens A ⊥ = ZFSet.powerset A := by
  apply ZFSet.ext
  intro S
  constructor
  · exact fun h => opens_subset A ⊥ h
  · intro hS
    obtain ⟨s, hs⟩ := (SetSubset.equiv A).surjective ⟨S, hS⟩
    have hs' : SetSubset.encode A s = S := congrArg (fun x : ZFSet.powerset A => x.val) hs
    rw [← hs', encode_mem_opens]
    trivial

/-- The indiscrete topology has exactly the two stated open subsets. -/
theorem indiscrete_opens (A : ZFSet.{u}) : opens A ⊤ = {∅, A} := by
  apply ZFSet.ext
  intro S
  constructor
  · intro hS
    obtain ⟨s, hs, ho⟩ := (ZFSet.mem_sep.mp hS).2
    have ho' : @IsOpen A ⊤ s := ho
    rcases (TopologicalSpace.isOpen_top_iff s).mp ho' with rfl | rfl
    · simp only [SetSubset.encode_empty] at hs
      simp [← hs]
    · simp only [SetSubset.encode_univ] at hs
      simp [← hs]
  · intro hS
    rcases ZFSet.mem_pair.mp hS with hs | hs
    · rw [hs, ← SetSubset.encode_empty A, encode_mem_opens]
      exact @isOpen_empty _ ⊤
    · rw [hs]
      simpa only [SetSubset.encode_univ] using
        (encode_mem_opens A ⊤ Set.univ).mpr (@isOpen_univ _ ⊤)

noncomputable def discrete (H : UniverseHierarchy.{u}) :
    SetCategory.Object (smallSetsCategory H) ⥤ SetCategory.Object (category H) :=
  SetCategory.liftToModel (smallSetsToTypes H ⋙ TopCat.discrete) (toTopCat H)
    (toTopCatFullyFaithful H) (fun A => topologyObject H A ⊥)
    (fun A => topologyModelIso H A ⊥)

noncomputable def indiscrete (H : UniverseHierarchy.{u}) :
    SetCategory.Object (smallSetsCategory H) ⥤ SetCategory.Object (category H) :=
  SetCategory.liftToModel (smallSetsToTypes H ⋙ TopCat.trivial) (toTopCat H)
    (toTopCatFullyFaithful H) (fun A => topologyObject H A ⊤)
    (fun A => topologyModelIso H A ⊤)

noncomputable def discrete_model (H : UniverseHierarchy.{u}) :
    smallSetsToTypes H ⋙ TopCat.discrete ≅ discrete H ⋙ toTopCat H :=
  SetCategory.liftToModelIso (smallSetsToTypes H ⋙ TopCat.discrete) (toTopCat H)
    (toTopCatFullyFaithful H) (fun A => topologyObject H A ⊥)
    (fun A => topologyModelIso H A ⊥)

noncomputable def indiscrete_model (H : UniverseHierarchy.{u}) :
    smallSetsToTypes H ⋙ TopCat.trivial ≅ indiscrete H ⋙ toTopCat H :=
  SetCategory.liftToModelIso (smallSetsToTypes H ⋙ TopCat.trivial) (toTopCat H)
    (toTopCatFullyFaithful H) (fun A => topologyObject H A ⊤)
    (fun A => topologyModelIso H A ⊤)

set_option backward.isDefEq.respectTransparency false in
noncomputable def forget_model (H : UniverseHierarchy.{u}) :
    toTopCat H ⋙ CategoryTheory.forget TopCat ≅ forget H ⋙ smallSetsToTypes H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    apply TypeCat.homEquiv.injective
    change ((toTopCat H).map f).hom.toFun =
      (SetFunction.funsEquiv _ _).symm
        (SetFunction.funsEquiv _ _ ((toTopCat H).map f).hom.toFun)
    exact (Equiv.symm_apply_apply _ _).symm)

noncomputable def discreteAdjunction (H : UniverseHierarchy.{u}) : discrete H ⊣ forget H :=
  TopCat.adj₁.restrictFullyFaithful (smallSetsToTypesFullyFaithful H)
    (toTopCatFullyFaithful H) (discrete_model H) (forget_model H)

noncomputable def indiscreteAdjunction (H : UniverseHierarchy.{u}) : forget H ⊣ indiscrete H :=
  TopCat.adj₂.restrictFullyFaithful (toTopCatFullyFaithful H)
    (smallSetsToTypesFullyFaithful H) (forget_model H) (indiscrete_model H)

end ILab.MathematicsLearning.SmallTopologicalSpaces
