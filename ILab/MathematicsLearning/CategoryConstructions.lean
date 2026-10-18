import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Topology.Category.TopCat.Adjunctions

/-!
# Definitions and concrete examples, Moser–Walde Chapter 1 and Example 3.2

Exact reuse is labelled as such. Set/category size in this module is expressed
by Lean type universes, separately from `SetUniverses.lean`'s ZFC predicates.
-/
namespace ILab.MathematicsLearning
open CategoryTheory Opposite
universe u v u' v' u'' v''

/-- 1.5/1.6: object and morphism levels remain independent. -/
abbrev StrictCategory (C : Type u) := Category.{v} C
abbrev categoryLeftIdentity := @Category.id_comp
abbrev categoryRightIdentity := @Category.comp_id
abbrev categoryAssociativity := @Category.assoc
/-- 1.7: the checked small-category interface. -/
abbrev SmallStrictCategory (C : Type u) := SmallCategory C

/-- 1.8: these instances contain identity, composition and all category laws. -/
abbrev setsCategory : LargeCategory (Type u) := inferInstance
abbrev pointedSetsCategory : LargeCategory Pointed.{u} := inferInstance
abbrev vectorSpacesCategory (k : Type u) [Field k] : LargeCategory (ModuleCat.{u} k) :=
  inferInstance
abbrev spacesCategory : LargeCategory TopCat.{u} := inferInstance

abbrev LocallySmallCategory (C : Type u) [Category.{v} C] := LocallySmall.{u'} C
theorem sets_locally_small : LocallySmall.{u} (Type u) := inferInstance
theorem pointed_locally_small : LocallySmall.{u} Pointed.{u} := inferInstance
theorem vector_spaces_locally_small (k : Type u) [Field k] :
    LocallySmall.{u} (ModuleCat.{u} k) := inferInstance
theorem spaces_locally_small : LocallySmall.{u} TopCat.{u} := inferInstance

/-- 1.10: a pointed map is invertible precisely when its function is bijective. -/
theorem pointed_iso_iff_bijective {X Y : Pointed.{u}} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective f.toFun := by
  constructor
  · intro h
    exact (CategoryTheory.isIso_iff_bijective ((forget Pointed).map f)).mp inferInstance
  · intro h
    let e := Equiv.ofBijective f.toFun h
    let i : X ≅ Y := Pointed.Iso.mk e f.map_point
    have hi : i.hom = f := rfl
    rw [← hi]
    infer_instance

/-- 1.10: a linear map between vector spaces is invertible iff bijective. -/
theorem vector_iso_iff_bijective (k : Type u) [Field k]
    {X Y : ModuleCat.{u} k} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f := by
  constructor
  · intro h
    exact (CategoryTheory.isIso_iff_bijective ((forget (ModuleCat k)).map f)).mp inferInstance
  · intro h
    have : IsIso ((forget (ModuleCat k)).map f) :=
      (CategoryTheory.isIso_iff_bijective _).mpr h
    exact isIso_of_reflects_iso f (forget (ModuleCat k))

/-- 1.9: inverse morphism and both equations are fields of Iso. -/
abbrev Isomorphism := @CategoryTheory.Iso
abbrev InvertibleMorphism := @CategoryTheory.IsIso
/-- 1.10: sets and spaces have different invertibility tests. -/
abbrev setIsoIffBijective := @CategoryTheory.isIso_iff_bijective
abbrev topIsoIffHomeomorphism := @TopCat.isIso_iff_isHomeomorph
abbrev pointedIsoOfEquiv := @Pointed.Iso.mk

/-- 1.12: the functor includes preservation of identities and composites. -/
abbrev CategoryFunctor := @CategoryTheory.Functor
abbrev functorIdentityLaw := @Functor.map_id
abbrev functorCompositionLaw := @Functor.map_comp

/-- 1.13: the seven source functors. -/
def forgetPoint : Pointed.{u} ⥤ Type u := forget Pointed
def forgetVector (k : Type u) [Field k] : ModuleCat.{u} k ⥤ Type u := forget _
def forgetTopology : TopCat.{u} ⥤ Type u := forget _
abbrev addBasepoint := @typeToPointed
noncomputable abbrev freeVectorSpace := @ModuleCat.free
abbrev discreteTopology := @TopCat.discrete
abbrev indiscreteTopology := @TopCat.trivial
noncomputable abbrev freeVectorMapOnBasis := @ModuleCat.free_map_apply

abbrev ContravariantFunctor (C : Type u) [Category.{v} C]
    (D : Type u') [Category.{v'} D] := Cᵒᵖ ⥤ D

/-- 1.20: component data and the defining naturality law. -/
abbrev NaturalTransformation := @CategoryTheory.NatTrans
abbrev naturalityEquation := @NatTrans.naturality
/-- 1.22: the source definition is a predicate on components; no inverse construction. -/
def ComponentwiseNaturalIsomorphism {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F G : C ⥤ D} (α : F ⟶ G) : Prop :=
  ∀ X, IsIso (α.app X)

/-- 3.2: the four exact adjunctions. Modules specialize here to vector spaces. -/
abbrev basepointAdjunction := @typeToPointedForgetAdjunction
noncomputable def vectorSpaceAdjunction (k : Type u) [Field k] :
    ModuleCat.free k ⊣ forget (ModuleCat.{u} k) := ModuleCat.adj k
abbrev discreteAdjunction := @TopCat.adj₁
abbrev indiscreteAdjunction := @TopCat.adj₂

/-- 3.5: a strict category isomorphism supplies an equivalence. -/
abbrev categoryIsoToEquivalence := @Cat.equivOfIso

end ILab.MathematicsLearning
