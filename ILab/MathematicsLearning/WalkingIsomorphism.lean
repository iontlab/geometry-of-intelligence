import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Fintype.Card

/-!
# A finite walking-isomorphism example

Primary items 1.25, 3.4, 3.8 and 3.9. Two distinct objects with singleton
hom types are equivalent to a one-object category. The inclusion is not
surjective on objects. The bundled Mathlib equivalence also checks a triangle
law, more data than primary Definition 3.4 asks for.
-/

namespace ILab.MathematicsLearning
open CategoryTheory

inductive Room where
  | north
  | south
  deriving DecidableEq

instance roomFintype : Fintype Room where
  elems := {Room.north, Room.south}
  complete := by intro X; cases X <;> simp

inductive OneRoom where
  | only
  deriving DecidableEq

instance roomCategory : SmallCategory Room where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

instance oneRoomCategory : SmallCategory OneRoom where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- Item 3.8: the unique arrow between any two rooms is invertible. -/
def roomIso (X Y : Room) : X ≅ Y where
  hom := PUnit.unit
  inv := PUnit.unit

/-- Item 3.9: choose the north room. -/
def includeRoom : OneRoom ⥤ Room where
  obj _ := .north
  map _ := PUnit.unit

/-- Collapse both rooms to the one-object category. -/
def collapseRoom : Room ⥤ OneRoom where
  obj _ := .only
  map _ := PUnit.unit

/-- Items 3.4/3.9: a checked adjoint equivalence, with singleton components. -/
def walkingEquivalence : OneRoom ≌ Room where
  functor := includeRoom
  inverse := collapseRoom
  unitIso := NatIso.ofComponents
    (fun _ => { hom := PUnit.unit, inv := PUnit.unit })
    (by intros; rfl)
  counitIso := NatIso.ofComponents (fun X => roomIso .north X) (by intros; rfl)
  functor_unitIso_comp _ := rfl

/-- Literal object surjectivity fails although the inclusion is an equivalence. -/
theorem inclusion_not_surjective : ¬ Function.Surjective includeRoom.obj := by
  intro h
  obtain ⟨X, hX⟩ := h Room.south
  cases X
  cases hX

/-- Both target objects are isomorphic to the image of the unique source object. -/
theorem inclusion_essentially_surjective (Y : Room) :
    Nonempty (includeRoom.obj OneRoom.only ≅ Y) := ⟨roomIso .north Y⟩

/-- The example has exactly two objects, not one object with two names. -/
theorem room_cardinality : Fintype.card Room = 2 := by decide

end ILab.MathematicsLearning
