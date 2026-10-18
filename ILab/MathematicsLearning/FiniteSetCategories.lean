import ILab.MathematicsLearning.SetCategoryEquivalences
import ILab.MathematicsLearning.SetUniverseClosure

/-! Source Constructions 1.25 and 3.8, and Proposition 3.9, with finite ZFC
object/hom sets in the stipulated universe. Singleton hom sets are literal
singletons. The object codes 0 = ∅ and 1 = {∅} are distinct.
The original text of 3.9 (including its printed 0≅0) is not altered. -/
namespace ILab.MathematicsLearning
open CategoryTheory SetCategory
universe u

def singletonMorphism : ZFSet.{u} := {∅}

theorem singletonMorphism_eq (a b : singletonMorphism.{u}) : a = b := by
  apply Subtype.ext
  exact (ZFSet.mem_singleton.mp a.property).trans (ZFSet.mem_singleton.mp b.property).symm

def singletonArrow : singletonMorphism.{u} := ⟨∅, ZFSet.mem_singleton.mpr rfl⟩

def singletonHomCategory {U : ZFSet.{u}} (hU : SetUniverse U)
    (A : ZFSet.{u}) (hA : A ∈ U) : SetCategory U where
  objects := A
  objects_mem := hA
  hom _ _ := singletonMorphism
  hom_mem _ _ := hU.singleton_mem hU.empty_mem
  identity _ := singletonArrow
  compose _ _ := singletonArrow
  identity_comp f := singletonMorphism_eq _ f
  comp_identity f := singletonMorphism_eq _ f
  associative _ _ _ := rfl

def terminalSetCategory (H : UniverseHierarchy.{u}) : SetCategory H.large :=
  singletonHomCategory H.large_universe {∅}
    (H.large_universe.singleton_mem H.large_universe.empty_mem)

def terminalObject (H : UniverseHierarchy.{u}) : Object (terminalSetCategory H) :=
  ⟨singletonArrow⟩

theorem terminal_object_unique (H : UniverseHierarchy.{u})
    (X : Object (terminalSetCategory H)) : X = terminalObject H := by
  cases X with
  | mk x => exact congrArg Object.mk (singletonMorphism_eq x singletonArrow)

theorem terminal_morphism_unique (H : UniverseHierarchy.{u})
    (f : terminalObject H ⟶ terminalObject H) : f = 𝟙 (terminalObject H) :=
  singletonMorphism_eq _ _

def walkingSetCategory (H : UniverseHierarchy.{u}) : SetCategory H.large :=
  singletonHomCategory H.large_universe {∅, {∅}}
    (H.large_universe.pair_mem H.large_universe.empty_mem
      (H.large_universe.singleton_mem H.large_universe.empty_mem))

def walkingZero (H : UniverseHierarchy.{u}) : Object (walkingSetCategory H) :=
  ⟨⟨∅, by simp [walkingSetCategory, singletonHomCategory]⟩⟩

def walkingOne (H : UniverseHierarchy.{u}) : Object (walkingSetCategory H) :=
  ⟨⟨{∅}, by simp [walkingSetCategory, singletonHomCategory]⟩⟩

theorem walking_zero_ne_one (H : UniverseHierarchy.{u}) : walkingZero H ≠ walkingOne H := by
  intro h
  have e := congrArg (fun X : Object (walkingSetCategory H) => X.member.val) h
  have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
  change (∅ : ZFSet.{u}) = {∅} at e
  rw [← e] at hm
  simp at hm

theorem walking_objects (H : UniverseHierarchy.{u}) (X : Object (walkingSetCategory H)) :
    X = walkingZero H ∨ X = walkingOne H := by
  have h := X.member.property
  change X.member.val ∈ ({∅, {∅}} : ZFSet.{u}) at h
  simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at h
  rcases h with h | h
  · left
    cases X with
    | mk x => exact congrArg Object.mk (Subtype.ext h)
  · right
    cases X with
    | mk x => exact congrArg Object.mk (Subtype.ext h)

theorem walking_hom_singleton (H : UniverseHierarchy.{u})
    (X Y : Object (walkingSetCategory H)) :
    ∃! _f : X ⟶ Y, True :=
  ⟨singletonArrow, trivial, fun f _ => singletonMorphism_eq f singletonArrow⟩

def walkingSetIso (H : UniverseHierarchy.{u})
    (X Y : Object (walkingSetCategory H)) : X ≅ Y where
  hom := singletonArrow
  inv := singletonArrow

def includeWalkingZero (H : UniverseHierarchy.{u}) :
    SourceFunctor (terminalSetCategory H) (walkingSetCategory H) where
  obj _ := walkingZero H
  map _ := singletonArrow
  map_identity _ := rfl
  map_composite _ _ := rfl

/-- Proposition 3.9: the actual singleton-to-two-object inclusion is an
equivalence in Definition 3.4's sense, with the source universe bounds. -/
theorem walking_inclusion_equivalence (H : UniverseHierarchy.{u}) :
    SetCategory.IsEquivalence (includeWalkingZero H) := by
  apply (fundamental_theorem _).mpr
  constructor
  · intro Y
    exact ⟨terminalObject H, (walkingSetIso H (walkingZero H) Y).hom,
      ⟨singletonArrow, rfl, rfl⟩⟩
  · intro X Y
    constructor
    · intro f g _
      exact singletonMorphism_eq f g
    · intro f
      exact ⟨singletonArrow, singletonMorphism_eq _ f⟩

/-- Remark 1.27, object selection only; the assigned functor-category
isomorphism and its naturality in 1.26 are not constructed. -/
def selectSetObject (H : UniverseHierarchy.{u}) (C : SetCategory H.large) (X : Object C) :
    SourceFunctor (terminalSetCategory H) C :=
  SourceFunctor.fromMathlib ((Functor.const (Object (terminalSetCategory H))).obj X)

theorem selectSetObject_unique (H : UniverseHierarchy.{u}) (C : SetCategory H.large)
    (X : Object C) :
    ∃! F : SourceFunctor (terminalSetCategory H) C, F.obj (terminalObject H) = X := by
  refine ⟨selectSetObject H C X, rfl, ?_⟩
  intro F hF
  apply (functorEquiv _ _).injective
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro Y
    rw [terminal_object_unique H Y]
    exact hF
  · intro Y Z f
    have hY := terminal_object_unique H Y
    have hZ := terminal_object_unique H Z
    subst Y
    subst Z
    have hf := terminal_morphism_unique H f
    subst f
    simp

end ILab.MathematicsLearning
