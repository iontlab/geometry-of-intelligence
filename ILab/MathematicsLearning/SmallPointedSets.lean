import ILab.MathematicsLearning.SetCategoryModels
import Mathlib.CategoryTheory.Category.Pointed
import ILab.MathematicsLearning.SmallSetsCategory
import ILab.MathematicsLearning.CategoryConstructions

/-! The pointed-set part of original Examples 1.8 and 1.10.
The code of (A,a) is the ordered pair (A,{a}). The singleton is intentional:
subset closure puts it in the stated universe without assuming transitivity.
Its injective encoding and exact hom correspondence are proved below. -/
namespace ILab.MathematicsLearning
universe u
open CategoryTheory

namespace SmallPointedSets

abbrev Data (U : ZFSet.{u}) := Σ A : U, A.val

def encode {U : ZFSet.{u}} (A : Data U) : ZFSet.{u} :=
  ZFSet.pair A.1.val {A.2.val}

theorem encode_injective (U : ZFSet.{u}) : Function.Injective (@encode U) := by
  rintro ⟨⟨A, hA⟩, ⟨a, ha⟩⟩ ⟨⟨B, hB⟩, ⟨b, hb⟩⟩ h
  obtain ⟨hAB, hab⟩ := ZFSet.pair_inj.mp h
  have hab' := ZFSet.singleton_inj.mp hab
  cases hAB
  cases hab'
  rfl

noncomputable def objects (U : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (@encode U)

noncomputable def objectEquiv (U : ZFSet.{u}) : Data U ≃ objects U :=
  Equiv.ofBijective (fun A => ⟨encode A, ZFSet.mem_range_self A⟩)
    ⟨by
      intro A B h
      exact encode_injective U (congrArg (fun x : objects U => x.val) h), by
      intro x
      obtain ⟨A, hA⟩ := ZFSet.mem_range.mp x.property
      exact ⟨A, Subtype.ext hA⟩⟩

theorem objects_mem (H : UniverseHierarchy.{u}) : objects H.small ∈ H.large := by
  apply H.large_universe.subsets _
    (H.large_universe.product_mem H.small_mem_large H.small_mem_large)
  intro x hx
  obtain ⟨A, rfl⟩ := ZFSet.mem_range.mp hx
  apply ZFSet.pair_mem_prod.mpr
  refine ⟨A.1.property, H.small_universe.subsets A.1.val A.1.property {A.2.val} ?_⟩
  intro y hy
  have he := ZFSet.mem_singleton.mp hy
  rw [he]
  exact A.2.property

noncomputable def data {U : ZFSet.{u}} (A : objects U) : Data U :=
  (objectEquiv U).symm A

noncomputable def model {U : ZFSet.{u}} (A : objects U) : Pointed :=
  Pointed.of (data A).2

noncomputable def hom {U : ZFSet.{u}} (A B : objects U) : ZFSet.{u} :=
  SetFunction.restricted (data A).1.val (data B).1.val (fun f => f (data A).2 = (data B).2)

noncomputable def homEquiv {U : ZFSet.{u}} (A B : objects U) :
    (model A ⟶ model B) ≃ hom A B :=
  (show (model A ⟶ model B) ≃
      {f : (data A).1.val → (data B).1.val // f (data A).2 = (data B).2} from
    { toFun := fun f => ⟨f.toFun, f.map_point⟩
      invFun := fun f => ⟨f.val, f.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (SetFunction.restrictedEquiv _ _ _)

theorem hom_mem {U : ZFSet.{u}} (hU : SetUniverse U) (A B : objects U) : hom A B ∈ U :=
  SetFunction.restricted_mem hU (data A).1.property (data B).1.property _

noncomputable def category (H : UniverseHierarchy.{u}) : SetCategory H.large :=
  SetCategory.ofModel (objects_mem H) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

theorem locallySmall (H : UniverseHierarchy.{u}) :
    (category H).IsLocallySmall H.small := hom_mem H.small_universe

/-- Exact hom bijections and functor laws provide the Mathlib correspondence. -/
noncomputable def toPointed (H : UniverseHierarchy.{u}) :
    SetCategory.Object (category H) ⥤ Pointed :=
  SetCategory.modelFunctor (objects_mem H) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

theorem toPointed_bijective (H : UniverseHierarchy.{u})
    (A B : SetCategory.Object (category H)) :
    Function.Bijective ((toPointed H).map (X := A) (Y := B)) :=
  (homEquiv A.member B.member).symm.bijective

/-- Example 1.10 for the actual pointed-set graphs from Example 1.8. -/
theorem isomorphism_iff_bijective (H : UniverseHierarchy.{u})
    {A B : SetCategory.Object (category H)} (f : A ⟶ B) :
    SetCategory.IsIsomorphism f ↔
      Function.Bijective ((toPointed H).map f).toFun := by
  let F := toPointed H
  let : F.Full := ⟨fun {X Y} => (toPointed_bijective H X Y).surjective⟩
  let : F.Faithful := ⟨fun {X Y} => (toPointed_bijective H X Y).injective⟩
  rw [SetCategory.isIsomorphism_iff_isIso]
  constructor
  · intro hf
    let := hf
    exact (pointed_iso_iff_bijective (F.map f)).mp inferInstance
  · intro hf
    let : IsIso (F.map f) := (pointed_iso_iff_bijective (F.map f)).mpr hf
    exact isIso_of_reflects_iso f F

set_option backward.isDefEq.respectTransparency false in
/-- Example 1.13: erase precisely the chosen point, retaining its carrier set. -/
noncomputable def forget (H : UniverseHierarchy.{u}) :
    SetCategory.Object (category H) ⥤ SetCategory.Object (smallSetsCategory H) where
  obj A := ⟨(data A.member).1⟩
  map {A B} f := SetFunction.funsEquiv (data A.member).1.val (data B.member).1.val
    ((toPointed H).map f).toFun
  map_id A := by
    change SetFunction.funsEquiv _ _ ((toPointed H).map (𝟙 A)).toFun =
      SetFunction.funsEquiv _ _ id
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp {A B C} f g := by
    change SetFunction.funsEquiv _ _ ((toPointed H).map (f ≫ g)).toFun =
      SetFunction.funsEquiv _ _
        (((SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _
          ((toPointed H).map g).toFun)) ∘
         ((SetFunction.funsEquiv _ _).symm (SetFunction.funsEquiv _ _
          ((toPointed H).map f).toFun)))
    simp only [Equiv.symm_apply_apply, CategoryTheory.Functor.map_comp]
    rfl

theorem not_small (H : UniverseHierarchy.{u}) : ¬ (category H).IsSmall H.small := by
  intro h
  let p : objects H.small → ZFSet.{u} := fun A => (data A).1.val
  have hp : ZFSet.range p ∈ H.small :=
    H.small_universe.range_mem h.1 p (fun A => (data A).1.property)
  have he : ZFSet.range p ∪ {∅} = H.small := by
    ext A
    constructor
    · intro hA
      rcases ZFSet.mem_union.mp hA with hA | hA
      · obtain ⟨B, rfl⟩ := ZFSet.mem_range.mp hA
        exact (data B).1.property
      · have he := ZFSet.mem_singleton.mp hA
        simpa [he] using H.small_universe.empty_mem
    · intro hA
      by_cases hempty : A = ∅
      · exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr hempty))
      · have hex : ∃ a, a ∈ A := by
          by_contra hn
          apply hempty
          apply ZFSet.ext
          intro a
          simp only [ZFSet.notMem_empty, iff_false]
          exact fun ha => hn ⟨a, ha⟩
        obtain ⟨a, ha⟩ := hex
        let B : Data H.small := ⟨⟨A, hA⟩, ⟨a, ha⟩⟩
        apply ZFSet.mem_union.mpr
        apply Or.inl
        apply ZFSet.mem_range.mpr
        refine ⟨objectEquiv H.small B, ?_⟩
        simp [p, data, B]
  have hh := H.small_universe.union_mem hp
    (H.small_universe.singleton_mem H.small_universe.empty_mem)
  rw [he] at hh
  exact universe_not_member H.small H.small_universe.subsets hh

end SmallPointedSets
end ILab.MathematicsLearning
