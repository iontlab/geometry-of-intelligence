import ILab.MathematicsLearning.SetCategoryEquivalences
import ILab.MathematicsLearning.SmallCategoryUniverse

/-!
# Authored raw construction data, with assigned checks withheld

Moser–Walde 1.15, 1.17, 1.21, 1.23, 1.28, 2.2, 2.6 and 3.3.
All objects and arrows are members of the existing set-coded categories.
The functions below return raw components, never new natural transformations,
functor categories, Yoneda functors, hom equivalences or adjunctions.
The equations are definitional readbacks only. Category/functor laws,
naturality, inverse and triangle checks assigned in the source remain open.
-/
namespace ILab.MathematicsLearning.SetCategory
open CategoryTheory Opposite
universe u
variable {U : ZFSet.{u}} {C D E : SetCategory U}

/-- 1.17: the opposite has literally the original object set. -/
def oppositeObjectData (C : SetCategory U) : ZFSet.{u} := C.objects
def oppositeHomData (C : SetCategory U) (x y : C.objects) : ZFSet.{u} := C.hom y x
def oppositeIdentityData (C : SetCategory U) (x : C.objects) : C.hom x x := C.identity x
def oppositeComposeData (C : SetCategory U) {x y z : C.objects}
    (f : C.hom y x) (g : C.hom z y) : C.hom z x := C.compose g f

theorem oppositeObjectData_formula : oppositeObjectData C = C.objects := rfl
theorem oppositeHomData_formula (x y : C.objects) : oppositeHomData C x y = C.hom y x := rfl
theorem oppositeIdentityData_formula (x : C.objects) : oppositeIdentityData C x = C.identity x := rfl
theorem oppositeComposeData_formula {x y z : C.objects} (f : C.hom y x) (g : C.hom z y) :
    oppositeComposeData C f g = C.compose g f := rfl

/-- 1.21 and 2.2: postcomposition at one object; naturality is not asserted. -/
def postcompositionComponent {c d : Object C} (f : c ⟶ d) (x : Object C)
    (g : x ⟶ c) : x ⟶ d := g ≫ f
theorem postcompositionComponent_formula {c d : Object C} (f : c ⟶ d)
    (x : Object C) (g : x ⟶ c) : postcompositionComponent f x g = C.compose g f := rfl

/-- 1.23: only the identity component on an already given functor. -/
def identityComponent (F : Object C ⥤ Object D) (x : Object C) :
    F.obj x ⟶ F.obj x := 𝟙 (F.obj x)
def verticalCompositeComponent {F G K : Object C ⥤ Object D}
    (α : F ⟶ G) (β : G ⟶ K) (x : Object C) : F.obj x ⟶ K.obj x := α.app x ≫ β.app x
theorem identityComponent_formula (F : Object C ⥤ Object D) (x : Object C) :
    identityComponent F x = D.identity (F.obj x).member := rfl
theorem verticalCompositeComponent_formula {F G K : Object C ⥤ Object D}
    (α : F ⟶ G) (β : G ⟶ K) (x : Object C) :
    verticalCompositeComponent α β x = D.compose (α.app x) (β.app x) := rfl

/-- 1.15 and both object assignments of 1.28 reuse existing composition.
SourceFunctor and functorCodeEquiv provide the source-data/code bridges. -/
theorem identityFunctor_object (x : Object C) : (𝟭 (Object C)).obj x = x := rfl
theorem identityFunctor_arrow {x y : Object C} (f : x ⟶ y) : (𝟭 (Object C)).map f = f := rfl
theorem compositeFunctor_object (F : Object C ⥤ Object D) (G : Object D ⥤ Object E)
    (x : Object C) : (F ⋙ G).obj x = G.obj (F.obj x) := rfl
theorem compositeFunctor_arrow (F : Object C ⥤ Object D) (G : Object D ⥤ Object E)
    {x y : Object C} (f : x ⟶ y) : (F ⋙ G).map f = G.map (F.map f) := rfl

/-- 1.28: precomposition samples an already given transformation at F(x). -/
def precompositionComponent (F : Object C ⥤ Object D)
    {G K : Object D ⥤ Object E} (α : G ⟶ K) (x : Object C) :
    G.obj (F.obj x) ⟶ K.obj (F.obj x) := α.app (F.obj x)
/-- 1.28: postcomposition applies the given functor to an existing component. -/
def postcompositionTransformationComponent (F : Object C ⥤ Object D)
    {G K : Object E ⥤ Object C} (α : G ⟶ K) (x : Object E) :
    F.obj (G.obj x) ⟶ F.obj (K.obj x) := F.map (α.app x)
theorem precompositionComponent_formula (F : Object C ⥤ Object D)
    {G K : Object D ⥤ Object E} (α : G ⟶ K) (x : Object C) :
    precompositionComponent F α x = α.app (F.obj x) := rfl
theorem postcompositionTransformationComponent_formula (F : Object C ⥤ Object D)
    {G K : Object E ⥤ Object C} (α : G ⟶ K) (x : Object E) :
    postcompositionTransformationComponent F α x = F.map (α.app x) := rfl

/-- 2.6: the map identification only. The opposite-isomorphism equivalence
is an assigned premise, not proved or invoked by this readback. -/
theorem oppositePostcomposeReadback {c d x : Object C} (f : c ⟶ d) (g : d ⟶ x) :
    (g.op ≫ f.op).unop = f ≫ g := rfl

/-- 3.3: forward hom function from an ALREADY GIVEN adjunction. -/
def adjunctionForward {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R) (x : Object C) (y : Object D) (g : L.obj x ⟶ y) :
    x ⟶ R.obj y := a.unit.app x ≫ R.map g
/-- 3.3: backward hom function; no inverse equation is proved. -/
def adjunctionBackward {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R) (x : Object C) (y : Object D) (f : x ⟶ R.obj y) :
    L.obj x ⟶ y := L.map f ≫ a.counit.app y
theorem adjunctionForward_formula {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R) (x : Object C) (y : Object D) (g : L.obj x ⟶ y) :
    adjunctionForward a x y g = C.compose (a.unit.app x) (R.map g) := rfl
theorem adjunctionBackward_formula {L : SourceFunctor C D} {R : SourceFunctor D C}
    (a : SourceAdjunction L R) (x : Object C) (y : Object D) (f : x ⟶ R.obj y) :
    adjunctionBackward a x y f = D.compose (L.map f) (a.counit.app y) := rfl

/-- 3.3: phi is GIVEN natural hom-set bijection data in the manuscript.
This formula uses only its underlying given bijections. Naturality of phi
is retained as source context, not derived here; neither candidate is
packaged as a natural transformation and no triangle check is supplied. -/
def unitCandidateComponent {L : SourceFunctor C D} {R : SourceFunctor D C}
    (φ : ∀ x y, (L.obj x ⟶ y) ≃ (x ⟶ R.obj y)) (x : Object C) :
    x ⟶ R.obj (L.obj x) := φ x (L.obj x) (𝟙 (L.obj x))
def counitCandidateComponent {L : SourceFunctor C D} {R : SourceFunctor D C}
    (φ : ∀ x y, (L.obj x ⟶ y) ≃ (x ⟶ R.obj y)) (y : Object D) :
    L.obj (R.obj y) ⟶ y := (φ (R.obj y) y).symm (𝟙 (R.obj y))
theorem unitCandidateComponent_formula {L : SourceFunctor C D} {R : SourceFunctor D C}
    (φ : ∀ x y, (L.obj x ⟶ y) ≃ (x ⟶ R.obj y)) (x : Object C) :
    unitCandidateComponent φ x = φ x (L.obj x) (𝟙 (L.obj x)) := rfl
theorem counitCandidateComponent_formula {L : SourceFunctor C D} {R : SourceFunctor D C}
    (φ : ∀ x y, (L.obj x ⟶ y) ≃ (x ⟶ R.obj y)) (y : Object D) :
    counitCandidateComponent φ y = (φ (R.obj y) y).symm (𝟙 (R.obj y)) := rfl
end ILab.MathematicsLearning.SetCategory
