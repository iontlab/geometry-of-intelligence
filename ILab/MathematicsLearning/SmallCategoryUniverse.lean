import ILab.MathematicsLearning.SetFunctorCodes
import ILab.MathematicsLearning.FiniteSetCategories
import Mathlib.CategoryTheory.Category.Cat

/-! Remark 1.16 with actual category and functor codes in the stipulated
universes. Category composition is inherited from the existing Mathlib Cat
model by the general proved representation mechanism. No independent proof
of the assigned Construction 1.15 category laws is exported or explained.
The new source results here are the exact size and inclusion assertions. -/
namespace ILab.MathematicsLearning.SmallCategoryUniverse
universe u
open CategoryTheory SetCategory

noncomputable def decode {U : ZFSet.{u}} (hU : SetUniverse U) (A : codes hU) : SetCategory U :=
  (codeEquiv hU).symm A

noncomputable def model {U : ZFSet.{u}} (hU : SetUniverse U) (A : codes hU) : Cat :=
  Cat.of (Object (decode hU A))

noncomputable def hom {U : ZFSet.{u}} (hU : SetUniverse U) (A B : codes hU) : ZFSet.{u} :=
  functorCodes (decode hU A) (decode hU B)

noncomputable def homEquiv {U : ZFSet.{u}} (hU : SetUniverse U) (A B : codes hU) :
    (model hU A ⟶ model hU B) ≃ hom hU A B :=
  ((Cat.Hom.equivFunctor _ _).trans (functorEquiv (decode hU A) (decode hU B)).symm).trans
    (functorCodeEquiv _ _)

noncomputable def category {U V : ZFSet.{u}} (hU : SetUniverse U) (hV : SetUniverse V)
    (hUV : U ∈ V) (hsub : U ⊆ V) : SetCategory V :=
  ofModel (codes_mem hU hV hUV) (model hU) (hom hU)
    (fun _ _ => hsub (functorCodes_mem hU _ _)) (homEquiv hU)

noncomputable def toCat {U V : ZFSet.{u}} (hU : SetUniverse U) (hV : SetUniverse V)
    (hUV : U ∈ V) (hsub : U ⊆ V) : Object (category hU hV hUV hsub) ⥤ Cat :=
  modelFunctor (codes_mem hU hV hUV) (model hU) (hom hU)
    (fun _ _ => hsub (functorCodes_mem hU _ _)) (homEquiv hU)

noncomputable def toCatFullyFaithful {U V : ZFSet.{u}} (hU : SetUniverse U) (hV : SetUniverse V)
    (hUV : U ∈ V) (hsub : U ⊆ V) : (toCat hU hV hUV hsub).FullyFaithful :=
  modelFullyFaithful (codes_mem hU hV hUV) (model hU) (hom hU)
    (fun _ _ => hsub (functorCodes_mem hU _ _)) (homEquiv hU)

/-- The codes include every source-small strict category, not just a skeleton. -/
noncomputable def smallObjectEquiv {U V : ZFSet.{u}} (hU : SetUniverse U) (hsub : U ⊆ V) :
    codes hU ≃ {C : SetCategory V // C.IsSmall U} :=
  (codeEquiv hU).symm.trans
    { toFun := fun C => ⟨enlarge hsub C, enlarge_small hsub C⟩
      invFun := fun C => restrict C.val C.property
      left_inv := by intro C; cases C; rfl
      right_inv := fun C => Subtype.ext (enlarge_restrict hsub C.val C.property) }

theorem locallySmall {U V : ZFSet.{u}} (hU : SetUniverse U) (hV : SetUniverse V)
    (hUV : U ∈ V) (hsub : U ⊆ V) : (category hU hV hUV hsub).IsLocallySmall U :=
  fun _ _ => functorCodes_mem hU _ _

theorem not_small {U V : ZFSet.{u}} (hU : SetUniverse U) (hV : SetUniverse V)
    (hUV : U ∈ V) (hsub : U ⊆ V) : ¬ (category hU hV hUV hsub).IsSmall U := by
  intro h
  let p : codes hU → ZFSet.{u} := fun A => (decode hU A).objects
  have hp : ZFSet.range p ∈ U := hU.range_mem h.1 p (fun A => (decode hU A).objects_mem)
  have he : ZFSet.range p = U := by
    ext A
    constructor
    · intro hA
      obtain ⟨B, rfl⟩ := ZFSet.mem_range.mp hA
      exact (decode hU B).objects_mem
    · intro hA
      refine ZFSet.mem_range.mpr ⟨codeEquiv hU (singletonHomCategory hU A hA), ?_⟩
      simp [p, decode, singletonHomCategory]
  rw [he] at hp
  exact universe_not_member U hU.subsets hp

noncomputable def smallCategories (H : UniverseHierarchy.{u}) : SetCategory H.large :=
  category H.small_universe H.large_universe H.small_mem_large H.small_subset_large

noncomputable def largeCategories (H : UniverseHierarchy.{u}) : SetCategory H.huge :=
  category H.large_universe H.huge_universe H.large_mem_huge H.large_subset_huge

/-- First assertion of 1.16: the actual small-category category is an object
of the huge category of large categories, with its complete data retained. -/
noncomputable def smallCategoriesAsHugeObject (H : UniverseHierarchy.{u}) :
    Object (largeCategories H) := ⟨codeEquiv H.large_universe (smallCategories H)⟩

theorem hugeObject_decodes (H : UniverseHierarchy.{u}) :
    decode H.large_universe (smallCategoriesAsHugeObject H).member = smallCategories H :=
  (codeEquiv H.large_universe).symm_apply_apply _

theorem smallCategories_locallySmall (H : UniverseHierarchy.{u}) :
    (smallCategories H).IsLocallySmall H.small :=
  locallySmall H.small_universe H.large_universe H.small_mem_large H.small_subset_large

theorem smallCategories_not_small (H : UniverseHierarchy.{u}) :
    ¬ (smallCategories H).IsSmall H.small :=
  not_small H.small_universe H.large_universe H.small_mem_large H.small_subset_large

end ILab.MathematicsLearning.SmallCategoryUniverse
