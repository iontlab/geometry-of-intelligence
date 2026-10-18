import ILab.MathematicsLearning.SmallPointedAdjunction
import ILab.MathematicsLearning.YonedaAdjunction
import Mathlib.CategoryTheory.Whiskering

/-! Corollary 2.7 on the original small-set-valued representables.
The representation below reuses Mathlib's existing Yoneda functor through
the proved set-function bridge. It does not give a new proof of the assigned
functor-law, Yoneda-lemma or full-faithfulness exercises, or export those
exercise theorems. Its purpose is to retain the exact codomain and hom sets
in the non-exercise object-isomorphism corollary. -/
namespace ILab.MathematicsLearning.SetCategory
universe u
open CategoryTheory Opposite

variable (H : UniverseHierarchy.{u}) (C : SetCategory H.large)
    (hC : C.IsLocallySmall H.small)

/-- The author-proved (i) iff (ii) portion of Corollary 2.6 on the exact
source hom members. The assigned opposite-invertibility step, and hence a
complete three-way proof, is deliberately not exported. -/
theorem postcomposition_bijections_detect_isomorphism
    (_hC : C.IsLocallySmall H.small) {c d : Object C} (f : c ⟶ d) :
    IsIsomorphism f ↔ ∀ x : Object C,
      Function.Bijective (fun g : C.hom x.member c.member => C.compose g f) := by
  rw [isIsomorphism_iff_isIso]
  exact CategoryTheory.isIso_iff_yoneda_map_bijective f

noncomputable def representableInSmallSets (c : Object C) :
    (Object C)ᵒᵖ ⥤ Object (smallSetsCategory H) :=
  liftToModel (yoneda.obj c) (smallSetsToTypes H) (smallSetsToTypesFullyFaithful H)
    (fun X => ⟨⟨C.hom X.unop.member c.member, hC _ _⟩⟩) (fun _ => Iso.refl _)

theorem representable_object (c : Object C) (x : (Object C)ᵒᵖ) :
    ((representableInSmallSets H C hC c).obj x).member.val =
      C.hom x.unop.member c.member := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The represented arrow is literally the graph of source precomposition. -/
theorem representable_map (c : Object C) {x y : Object C} (f : x ⟶ y) :
    ((representableInSmallSets H C hC c).map f.op).val =
      SetFunction.graph (fun g : C.hom y.member c.member => C.compose f g) := rfl

noncomputable def representable_model (c : Object C) :
    yoneda.obj c ≅ representableInSmallSets H C hC c ⋙ smallSetsToTypes H :=
  liftToModelIso (yoneda.obj c) (smallSetsToTypes H) (smallSetsToTypesFullyFaithful H)
    (fun X => ⟨⟨C.hom X.unop.member c.member, hC _ _⟩⟩) (fun _ => Iso.refl _)

/-- The right side uses the manuscript's componentwise definition of natural
isomorphism, between functors whose values are the actual small hom sets. -/
theorem representable_objects_isomorphic_iff (x y : Object C) :
    ObjectsIsomorphic C x y ↔
      ∃ α : representableInSmallSets H C hC x ⟶ representableInSmallSets H C hC y,
        ∀ z, IsIsomorphism (α.app z) := by
  let J := (CategoryTheory.Functor.whiskeringRight (Object C)ᵒᵖ (Object (smallSetsCategory H))
    (Type (u+1))).obj (smallSetsToTypes H)
  let hJ := (smallSetsToTypesFullyFaithful H).whiskeringRight (Object C)ᵒᵖ
  constructor
  · rintro ⟨f, hf⟩
    let : IsIso f := (isIsomorphism_iff_isIso f).mp hf
    let e := (representable_model H C hC x).symm ≪≫ yoneda.mapIso (asIso f) ≪≫
      representable_model H C hC y
    let a := hJ.preimageIso e
    exact ⟨a.hom, fun z => (isIsomorphism_iff_isIso (a.hom.app z)).mpr inferInstance⟩
  · rintro ⟨α, hα⟩
    let : ∀ z, IsIso (α.app z) := fun z => (isIsomorphism_iff_isIso (α.app z)).mp (hα z)
    let : IsIso α := NatIso.isIso_of_isIso_app α
    let e := representable_model H C hC x ≪≫ J.mapIso (asIso α) ≪≫
      (representable_model H C hC y).symm
    obtain ⟨i⟩ := (yoneda_object_iso_iff x y).mpr ⟨e⟩
    exact ⟨i.hom, (isIsomorphism_iff_isIso i.hom).mpr inferInstance⟩

end ILab.MathematicsLearning.SetCategory
