import ILab.MathematicsLearning.SetFunctions
import ILab.MathematicsLearning.BasicCategoryTheory
import ILab.MathematicsLearning.SourceLaws

/-!
# Moser–Walde strict categories with literal set-universe bounds

`SetCategory U` is Definition 1.5 (or Remark 1.6 with the huge universe):
objects and every hom set are ZFC sets belonging to U. Identities, composition,
and all three laws are exactly the source data. `SetFunction.graphEquiv`
justifies representing set functions by functions of their membership types.
`Object C` merely tags an element of C's object set; it adds no objects.
Its Mathlib category has literally the same hom members, identity and
composition. The `rfl` bridge equations below document this correspondence.

No universe existence, transitivity, cardinal-size correspondence, or new
axiom is assumed by this translation. Smallness remains membership in the
specified small set-universe, rather than Mathlib's `Small` predicate.
-/

namespace ILab.MathematicsLearning
universe u

structure SetCategory (U : ZFSet.{u}) where
  objects : ZFSet.{u}
  objects_mem : objects ∈ U
  hom : objects → objects → ZFSet.{u}
  hom_mem : ∀ x y, hom x y ∈ U
  identity : ∀ x, hom x x
  compose : ∀ {x y z}, hom x y → hom y z → hom x z
  identity_comp : ∀ {x y} (f : hom x y), compose (identity x) f = f
  comp_identity : ∀ {x y} (f : hom x y), compose f (identity y) = f
  associative : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z),
    compose (compose f g) h = compose f (compose g h)

namespace SetCategory
open CategoryTheory
variable {U : ZFSet.{u}}

structure Object (C : SetCategory U) where
  member : C.objects

def objectEquiv (C : SetCategory U) : Object C ≃ C.objects where
  toFun := Object.member
  invFun := Object.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (C : SetCategory U) : Category (Object C) where
  Hom X Y := C.hom X.member Y.member
  id X := C.identity X.member
  comp f g := C.compose f g
  id_comp := C.identity_comp
  comp_id := C.comp_identity
  assoc := C.associative

theorem hom_members (C : SetCategory U) (X Y : Object C) :
    (X ⟶ Y) = (C.hom X.member Y.member : Type (u+1)) := rfl

theorem identity_agrees (C : SetCategory U) (X : Object C) :
    (𝟙 X : X ⟶ X) = C.identity X.member := rfl

theorem composition_agrees (C : SetCategory U) {X Y Z : Object C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = C.compose f g := rfl

/-- Definition 1.7: local smallness is hom-set membership, not type size. -/
def IsLocallySmall (S : ZFSet.{u}) (C : SetCategory U) : Prop :=
  ∀ x y, C.hom x y ∈ S

/-- Definition 1.7: both source conditions, including object-set membership. -/
def IsSmall (S : ZFSet.{u}) (C : SetCategory U) : Prop :=
  C.objects ∈ S ∧ C.IsLocallySmall S

/-- Definition 1.9 uses an existential inverse, not selected inverse data. -/
def IsIsomorphism {C : SetCategory U} {X Y : Object C} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, C.compose f g = C.identity X.member ∧
    C.compose g f = C.identity Y.member

/-- The final paragraph of Definition 1.9: existence of an isomorphism. -/
def ObjectsIsomorphic (C : SetCategory U) (X Y : Object C) : Prop :=
  ∃ f : X ⟶ Y, IsIsomorphism f

theorem isIsomorphism_iff_isIso {C : SetCategory U} {X Y : Object C} (f : X ⟶ Y) :
    IsIsomorphism f ↔ IsIso f :=
  (invertible_iff_two_sided_inverse f).symm

/-- Proposition 1.11, with the original existence hypothesis and unique conclusion. -/
theorem unique_inverse {C : SetCategory U} {X Y : Object C}
    (f : X ⟶ Y) (hf : IsIsomorphism f) :
    ∃! g : Y ⟶ X, C.compose f g = C.identity X.member ∧
      C.compose g f = C.identity Y.member := by
  obtain ⟨g, hfg, hgf⟩ := hf
  refine ⟨g, ⟨hfg, hgf⟩, ?_⟩
  intro h hh
  exact inverse_unique f h g hh.2 hfg

/-- Definition 1.12: functions on precisely the source object and hom members. -/
structure SourceFunctor (C D : SetCategory U) where
  obj : Object C → Object D
  map : ∀ {X Y : Object C}, (X ⟶ Y) → (obj X ⟶ obj Y)
  map_identity : ∀ X, map (𝟙 X) = 𝟙 (obj X)
  map_composite : ∀ {X Y Z : Object C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f ≫ map g

def SourceFunctor.toMathlib {C D : SetCategory U} (F : SourceFunctor C D) :
    Object C ⥤ Object D where
  obj := F.obj
  map := F.map
  map_id := F.map_identity
  map_comp := F.map_composite

def SourceFunctor.fromMathlib {C D : SetCategory U} (F : Object C ⥤ Object D) :
    SourceFunctor C D where
  obj := F.obj
  map := F.map
  map_identity := F.map_id
  map_composite := F.map_comp

/-- Both directions preserve all data; proof fields are propositions. -/
def functorEquiv (C D : SetCategory U) :
    SourceFunctor C D ≃ (Object C ⥤ Object D) where
  toFun := SourceFunctor.toMathlib
  invFun := SourceFunctor.fromMathlib
  left_inv F := by cases F; rfl
  right_inv F := by cases F; rfl

/-- Remark 1.18: the source's arrow-reversing data and its two laws. -/
structure SourceContravariantFunctor (C D : SetCategory U) where
  obj : Object C → Object D
  map : ∀ {X Y : Object C}, (X ⟶ Y) → (obj Y ⟶ obj X)
  map_identity : ∀ X, map (𝟙 X) = 𝟙 (obj X)
  map_composite : ∀ {X Y Z : Object C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map g ≫ map f

/-- The existing opposite-category library representation reverses exactly
the source hom members and composition. This data equivalence does not
export the category-law exercise of Construction 1.17. -/
def contravariantFunctorEquiv (C D : SetCategory U) :
    SourceContravariantFunctor C D ≃ (Object C)ᵒᵖ ⥤ Object D where
  toFun F :=
    { obj := fun X => F.obj X.unop
      map := fun f => F.map f.unop
      map_id := fun X => F.map_identity X.unop
      map_comp := fun f g => F.map_composite g.unop f.unop }
  invFun F :=
    { obj := fun X => F.obj (Opposite.op X)
      map := fun f => F.map f.op
      map_identity := fun X => F.map_id (Opposite.op X)
      map_composite := fun f g => F.map_comp g.op f.op }
  left_inv F := by cases F; rfl
  right_inv F := by cases F; rfl

/-- Definition 1.20: the source's component equation in Lean composition order. -/
structure SourceTransformation {C D : SetCategory U} (F G : SourceFunctor C D) where
  component : ∀ X, F.obj X ⟶ G.obj X
  naturality : ∀ {X Y} (f : X ⟶ Y),
    component X ≫ G.map f = F.map f ≫ component Y

def transformationEquiv {C D : SetCategory U} (F G : SourceFunctor C D) :
    SourceTransformation F G ≃ (F.toMathlib ⟶ G.toMathlib) where
  toFun a := { app := a.component, naturality := fun _ _ f => (a.naturality f).symm }
  invFun a := { component := a.app, naturality := fun f => (a.naturality f).symm }
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

/-- Definition 1.22, exactly pointwise invertibility; no exercise 1.24 proof. -/
def IsNaturalIsomorphism {C D : SetCategory U} {F G : SourceFunctor C D}
    (a : SourceTransformation F G) : Prop := ∀ X, IsIsomorphism (a.component X)

/-- Definition 2.3, exactly a bijection on every hom set. -/
def IsFullyFaithful {C D : SetCategory U} (F : SourceFunctor C D) : Prop :=
  ∀ X Y, Function.Bijective (F.map (X := X) (Y := Y))

/-- Definition 3.6 with precisely the source witnesses and domains. -/
def IsEssentiallySurjective {C D : SetCategory U} (F : SourceFunctor C D) : Prop :=
  ∀ Y : Object D, ∃ X : Object C, ∃ f : F.obj X ⟶ Y, IsIsomorphism f

end SetCategory
end ILab.MathematicsLearning
