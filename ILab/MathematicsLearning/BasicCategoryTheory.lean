import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category

/-!
# Ordinary category theory: selected Moser–Walde learning exercises

Independent educational proofs for primary items 1.5, 1.11, 1.14,
1.20, and 1.23. These statements concern ordinary Mathlib categories.
They do not formalize HoTT, set-universe existence, or synthetic categories.
Composition `f ≫ g` means the primary source's `g ∘ f`.
-/

namespace ILab.MathematicsLearning

open CategoryTheory
universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- Item 1.5: inserting identities does not change a composable pair. -/
theorem identity_padded_composite {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (𝟙 X ≫ f) ≫ (g ≫ 𝟙 Z) = f ≫ g := by
  rw [Category.id_comp, Category.comp_id]

/-- Item 1.11, strengthened: a right inverse and a left inverse agree. -/
theorem inverse_unique {X Y : C} (f : X ⟶ Y) (g h : Y ⟶ X)
    (hg : g ≫ f = 𝟙 Y) (hh : f ≫ h = 𝟙 X) : g = h := by
  calc
    g = g ≫ 𝟙 X := (Category.comp_id g).symm
    _ = g ≫ (f ≫ h) := by rw [hh]
    _ = (g ≫ f) ≫ h := (Category.assoc g f h).symm
    _ = h := by rw [hg, Category.id_comp]

/-- Item 1.14: the image of an inverse satisfies the first inverse equation. -/
theorem mapped_inverse_left (F : C ⥤ D) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) :
    F.map f ≫ F.map g = 𝟙 (F.obj X) := by
  rw [← F.map_comp, h, F.map_id]

/-- Item 1.14: the image satisfies the second inverse equation too. -/
theorem mapped_inverse_right (F : C ⥤ D) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) (h : g ≫ f = 𝟙 Y) :
    F.map g ≫ F.map f = 𝟙 (F.obj Y) := by
  rw [← F.map_comp, h, F.map_id]

/-- Item 1.14: package the two checked equations as an isomorphism. -/
def mappedIso (F : C ⥤ D) {X Y : C} (e : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map e.hom
  inv := F.map e.inv
  hom_inv_id := mapped_inverse_left F e.hom e.inv e.hom_inv_id
  inv_hom_id := mapped_inverse_right F e.hom e.inv e.inv_hom_id

/-- The educational construction agrees with Mathlib's existing mapIso. -/
theorem mappedIso_eq_mapIso (F : C ⥤ D) {X Y : C} (e : X ≅ Y) :
    mappedIso F e = F.mapIso e := by
  ext
  rfl

/-- Items 1.20/1.23: composing naturality squares gives another square. -/
theorem composite_naturality {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ (α.app Y ≫ β.app Y) = (α.app X ≫ β.app X) ≫ H.map f := by
  calc
    F.map f ≫ (α.app Y ≫ β.app Y)
        = (F.map f ≫ α.app Y) ≫ β.app Y := (Category.assoc _ _ _).symm
    _ = (α.app X ≫ G.map f) ≫ β.app Y := by rw [α.naturality f]
    _ = α.app X ≫ (G.map f ≫ β.app Y) := Category.assoc _ _ _
    _ = α.app X ≫ (β.app X ≫ H.map f) := by rw [β.naturality f]
    _ = (α.app X ≫ β.app X) ≫ H.map f := (Category.assoc _ _ _).symm

/-- Item 1.23: the functor-category composite has the expected components. -/
theorem vertical_composite_component {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

end ILab.MathematicsLearning
