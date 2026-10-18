import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category

/-!
# Ordinary category theory: non-exercise Moser–Walde foundations

Independent educational proofs for primary items 1.5 and 1.11.
Assigned exercise solutions are excluded from publication. These statements concern ordinary Mathlib categories.
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

end ILab.MathematicsLearning
