import ILab.MathematicsLearning.SetCategories
import ILab.MathematicsLearning.SetUniverseClosure

/-! Operation-preserving representations of concrete categories by ZFC sets.
This is implementation support, not an additional manuscript theorem. -/
namespace ILab.MathematicsLearning
universe u v w
open CategoryTheory

namespace SetFunction

noncomputable def restricted (A B : ZFSet.{u}) (P : (A → B) → Prop) : ZFSet.{u} :=
  ZFSet.sep (fun G => ∃ f : A → B, graph f = G ∧ P f) (ZFSet.funs A B)

theorem graph_mem_restricted {A B : ZFSet.{u}} (P : (A → B) → Prop) (f : A → B) :
    graph f ∈ restricted A B P ↔ P f := by
  constructor
  · intro h
    obtain ⟨g, hg, hp⟩ := (ZFSet.mem_sep.mp h).2
    have he : g = f := (graphEquiv A B).injective (Subtype.ext hg)
    simpa [he] using hp
  · intro hp
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_funs.mpr (graph_isFunc f), f, rfl, hp⟩

noncomputable def restrictedEquiv (A B : ZFSet.{u}) (P : (A → B) → Prop) :
    {f : A → B // P f} ≃ restricted A B P :=
  Equiv.ofBijective
    (fun f => ⟨graph f.val, (graph_mem_restricted P f.val).mpr f.property⟩)
    ⟨by
      intro f g h
      apply Subtype.ext
      have he : graph f.val = graph g.val :=
        congrArg (fun x : restricted A B P => x.val) h
      exact (graphEquiv A B).injective (Subtype.ext he), by
      intro G
      obtain ⟨f, hf, hp⟩ := (ZFSet.mem_sep.mp G.property).2
      exact ⟨⟨f, hp⟩, Subtype.ext hf⟩⟩

theorem restricted_mem {U A B : ZFSet.{u}} (hU : SetUniverse U)
    (hA : A ∈ U) (hB : B ∈ U) (P : (A → B) → Prop) : restricted A B P ∈ U :=
  hU.subsets _ (hU.functions_mem hA hB) _ ZFSet.sep_subset

end SetFunction

namespace SetCategory

/-- A model with the specified ZFC objects and hom sets; all operations are
transported through explicit bijections, rather than merely analogous. -/
noncomputable def ofModel {U O : ZFSet.{u}} (hO : O ∈ U)
    {C : Type v} [Category.{w} C] (obj : O → C)
    (hom : O → O → ZFSet.{u}) (hhom : ∀ X Y, hom X Y ∈ U)
    (e : ∀ X Y, (obj X ⟶ obj Y) ≃ hom X Y) : SetCategory U where
  objects := O
  objects_mem := hO
  hom := hom
  hom_mem := hhom
  identity X := e X X (𝟙 (obj X))
  compose {X Y Z} f g := e X Z ((e X Y).symm f ≫ (e Y Z).symm g)
  identity_comp := by intros; simp
  comp_identity := by intros; simp
  associative := by intros; simp [Category.assoc]

noncomputable def modelFunctor {U O : ZFSet.{u}} (hO : O ∈ U)
    {C : Type v} [Category.{w} C] (obj : O → C)
    (hom : O → O → ZFSet.{u}) (hhom : ∀ X Y, hom X Y ∈ U)
    (e : ∀ X Y, (obj X ⟶ obj Y) ≃ hom X Y) :
    Object (ofModel hO obj hom hhom e) ⥤ C where
  obj X := obj X.member
  map {X Y} f := (e X.member Y.member).symm f
  map_id := by intros; exact Equiv.symm_apply_apply _ _
  map_comp := by intros; exact Equiv.symm_apply_apply _ _

theorem modelFunctor_bijective {U O : ZFSet.{u}} (hO : O ∈ U)
    {C : Type v} [Category.{w} C] (obj : O → C)
    (hom : O → O → ZFSet.{u}) (hhom : ∀ X Y, hom X Y ∈ U)
    (e : ∀ X Y, (obj X ⟶ obj Y) ≃ hom X Y)
    (X Y : Object (ofModel hO obj hom hhom e)) :
    Function.Bijective ((modelFunctor hO obj hom hhom e).map (X := X) (Y := Y)) :=
  (e X.member Y.member).symm.bijective

/-- A specified model correspondence supplies explicit preimages of all homs. -/
noncomputable def modelFullyFaithful {U O : ZFSet.{u}} (hO : O ∈ U)
    {C : Type v} [Category.{w} C] (obj : O → C)
    (hom : O → O → ZFSet.{u}) (hhom : ∀ X Y, hom X Y ∈ U)
    (e : ∀ X Y, (obj X ⟶ obj Y) ≃ hom X Y) :
    (modelFunctor hO obj hom hhom e).FullyFaithful where
  preimage {X Y} f := e X.member Y.member f
  map_preimage _ := Equiv.symm_apply_apply _ _
  preimage_map _ := Equiv.apply_symm_apply _ _

/-- Restrict a modeled functor to specified object codes and their proved
isomorphisms. The commuting square is given by `liftToModelIso` below. -/
noncomputable def liftToModel {A C D : Type*} [Category A] [Category C] [Category D]
    (F : A ⥤ D) (i : C ⥤ D) (hi : i.FullyFaithful) (obj : A → C)
    (e : ∀ X, F.obj X ≅ i.obj (obj X)) : A ⥤ C where
  obj := obj
  map {X Y} f := hi.preimage ((e X).inv ≫ F.map f ≫ (e Y).hom)
  map_id X := by simp
  map_comp {X Y Z} f g := by
    apply hi.map_injective
    simp [Category.assoc]

noncomputable def liftToModelIso {A C D : Type*} [Category A] [Category C] [Category D]
    (F : A ⥤ D) (i : C ⥤ D) (hi : i.FullyFaithful) (obj : A → C)
    (e : ∀ X, F.obj X ≅ i.obj (obj X)) :
    F ≅ liftToModel F i hi obj e ⋙ i :=
  NatIso.ofComponents e (by intro X Y f; simp [liftToModel])

end SetCategory
end ILab.MathematicsLearning
