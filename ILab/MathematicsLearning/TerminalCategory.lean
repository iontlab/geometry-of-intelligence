import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Category.Cat
import ILab.MathematicsLearning.WalkingIsomorphism

/-! # Non-exercise terminal-category and walking-isomorphism material
The assigned evaluation-isomorphism proof (1.26) is withheld.
-/
namespace ILab.MathematicsLearning
open CategoryTheory
universe u v

abbrev TerminalCategory := Discrete PUnit.{u+1}
abbrev functorToTerminal := @Functor.star
abbrev functorToTerminal_unique := @Functor.punit_ext'
abbrev selectObject := @Functor.fromPUnit

/-- 1.27: a functor out of the terminal category is determined by its object. -/
theorem terminal_functor_unique (C : Type u) [Category.{v} C]
    (F : TerminalCategory.{u} ⥤ C) :
    Functor.fromPUnit (F.obj ⟨PUnit.unit⟩) = F := by
  apply Discrete.functor_ext
  intro i
  cases i
  rfl

instance oneRoomFintype : Fintype OneRoom := ⟨{OneRoom.only}, by intro X; cases X; simp⟩

theorem one_room_cardinality : Fintype.card OneRoom = 1 := by decide

/-- The introductory equivalence example is not an isomorphism of categories. -/
theorem walking_not_strictly_isomorphic :
    ¬ Nonempty (Cat.of OneRoom ≅ Cat.of Room) := by
  rintro ⟨e⟩
  let objIso := (Cat.objects).mapIso e
  have h := Fintype.card_congr (show OneRoom ≃ Room from objIso.toEquiv)
  change Fintype.card OneRoom = Fintype.card Room at h
  rw [one_room_cardinality, room_cardinality] at h
  contradiction

/-- 3.9: both the Full and Faithful claims follow from the constructed equivalence. -/
theorem walking_inclusion_full : includeRoom.Full := walkingEquivalence.full_functor
theorem walking_inclusion_faithful : includeRoom.Faithful := walkingEquivalence.faithful_functor

end ILab.MathematicsLearning
