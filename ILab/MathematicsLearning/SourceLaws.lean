import ILab.MathematicsLearning.YonedaAdjunction
import ILab.MathematicsLearning.CategoryConstructions

/-! # Non-exercise defining equations for the source inventory
These expose laws already contained in the checked structures, so the
educational inventory can bind each equation to an exact declaration.
-/
namespace ILab.MathematicsLearning
open CategoryTheory Opposite
universe u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 1.9: the source uses existence, not a chosen isomorphism. -/
def ObjectsIsomorphic (X Y : C) : Prop := Nonempty (X ≅ Y)

/-- 3.1: projections and naturality for both adjunction comparisons. -/
abbrev adjunctionUnit := @Adjunction.unit
abbrev adjunctionCounit := @Adjunction.counit

theorem adjunction_unit_naturality {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {X Y : C} (f : X ⟶ Y) :
    f ≫ a.unit.app Y = a.unit.app X ≫ G.map (F.map f) := a.unit.naturality f

theorem adjunction_counit_naturality {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {X Y : D} (f : X ⟶ Y) :
    F.map (G.map f) ≫ a.counit.app Y = a.counit.app X ≫ f := a.counit.naturality f

/-- 1.9: the unbundled source definition agrees with IsIso. -/
theorem invertible_iff_two_sided_inverse {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · intro h
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
  · rintro ⟨g, h, k⟩
    exact ⟨⟨g, h, k⟩⟩

/-- 1.18: the reversal of composition is visible in the formula. -/
theorem contravariant_composition (F : Cᵒᵖ ⥤ D) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g).op = F.map g.op ≫ F.map f.op := by
  rw [op_comp, F.map_comp]

/-- 3.6: the source's existential witness formulation. -/
theorem essentially_surjective_iff (F : C ⥤ D) :
    F.EssSurj ↔ ∀ Y : D, ∃ X : C, Nonempty (F.obj X ≅ Y) := by
  constructor
  · intro h Y
    exact h.mem_essImage Y
  · intro h
    exact ⟨h⟩

end ILab.MathematicsLearning
