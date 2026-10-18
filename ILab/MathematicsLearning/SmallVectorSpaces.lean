import ILab.MathematicsLearning.SetCategoryModels
import ILab.MathematicsLearning.SmallSetsCategory
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Group.Ext

/-! Vector spaces on the manuscript's small ZFC sets. The object code records
the actual carrier, addition graph and scalar-action graph. The remaining
group operations are uniquely determined by addition; this is proved in the
injectivity of the code, rather than silently discarded. -/
namespace ILab.MathematicsLearning
universe u
open CategoryTheory

namespace SmallVectorSpaces

structure Structure (K A : ZFSet.{u}) [Field K] where
  group : AddCommGroup A
  module : @Module K A _ group.toAddCommMonoid

def addition {K A : ZFSet.{u}} [Field K] (s : Structure K A) : A → A → A :=
  letI := s.group
  (· + ·)

def scalarAction {K A : ZFSet.{u}} [Field K] (s : Structure K A) : K → A → A :=
  letI := s.group
  letI := s.module
  (· • ·)

theorem structure_ext {K A : ZFSet.{u}} [Field K] {s t : Structure K A}
    (ha : addition s = addition t) (hm : scalarAction s = scalarAction t) : s = t := by
  rcases s with ⟨g, m⟩
  rcases t with ⟨g', m'⟩
  have hg : g = g' := AddCommGroup.ext ha
  cases hg
  have he : m = m' := Module.ext' _ _ (fun k a => congrFun (congrFun hm k) a)
  cases he
  rfl

private instance structureSmall (K A : ZFSet.{u}) [Field K] : Small.{u} (Structure K A) :=
  small_of_injective (f := fun s : Structure K A => (addition s, scalarAction s)) (by
    intro s t h
    exact structure_ext (congrArg Prod.fst h) (congrArg Prod.snd h))

abbrev Data (U K : ZFSet.{u}) [Field K] := Σ A : U, Structure K A.val

noncomputable def operationCode (B A : ZFSet.{u}) (f : B → A → A) : ZFSet.{u} :=
  SetFunction.graph (fun b => SetFunction.funsEquiv A A (f b))

theorem operationCode_injective (B A : ZFSet.{u}) :
    Function.Injective (operationCode B A) := by
  intro f g h
  have he := (SetFunction.graphEquiv B (ZFSet.funs A A)).injective (Subtype.ext h)
  funext b
  exact (SetFunction.funsEquiv A A).injective (congrFun he b)

theorem operationCode_mem {U B A : ZFSet.{u}} (hU : SetUniverse U)
    (hB : B ∈ U) (hA : A ∈ U) (f : B → A → A) : operationCode B A f ∈ U :=
  hU.subsets _ (hU.product_mem hB (hU.functions_mem hA hA)) _
    (SetFunction.graph_isFunc (fun b => SetFunction.funsEquiv A A (f b))).1

noncomputable def encode {U K : ZFSet.{u}} [Field K] (A : Data U K) : ZFSet.{u} :=
  ZFSet.pair A.1.val (ZFSet.pair (operationCode A.1.val A.1.val (addition A.2))
    (operationCode K A.1.val (scalarAction A.2)))

theorem encode_injective (U K : ZFSet.{u}) [Field K] :
    Function.Injective (@encode U K _) := by
  rintro ⟨⟨A, hA⟩, s⟩ ⟨⟨B, hB⟩, t⟩ h
  obtain ⟨hAB, hst⟩ := ZFSet.pair_inj.mp h
  cases hAB
  obtain ⟨ha, hm⟩ := ZFSet.pair_inj.mp hst
  have hs := structure_ext (operationCode_injective A A ha) (operationCode_injective K A hm)
  cases hs
  rfl

noncomputable def objects (U K : ZFSet.{u}) [Field K] : ZFSet.{u} := ZFSet.range (@encode U K _)

noncomputable def objectEquiv (U K : ZFSet.{u}) [Field K] : Data U K ≃ objects U K :=
  Equiv.ofBijective (fun A => ⟨encode A, ZFSet.mem_range_self A⟩)
    ⟨by
      intro A B h
      exact encode_injective U K (congrArg (fun x : objects U K => x.val) h), by
      intro x
      obtain ⟨A, hA⟩ := ZFSet.mem_range.mp x.property
      exact ⟨A, Subtype.ext hA⟩⟩

theorem objects_mem (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    objects H.small K.val ∈ H.large := by
  apply H.large_universe.subsets _
    (H.large_universe.product_mem H.small_mem_large
      (H.large_universe.product_mem H.small_mem_large H.small_mem_large))
  intro x hx
  obtain ⟨A, rfl⟩ := ZFSet.mem_range.mp hx
  exact ZFSet.pair_mem_prod.mpr ⟨A.1.property, ZFSet.pair_mem_prod.mpr
    ⟨operationCode_mem H.small_universe A.1.property A.1.property _,
      operationCode_mem H.small_universe K.property A.1.property _⟩⟩

noncomputable def data {U K : ZFSet.{u}} [Field K] (A : objects U K) : Data U K :=
  (objectEquiv U K).symm A

noncomputable def model {U K : ZFSet.{u}} [Field K] (A : objects U K) : ModuleCat K :=
  @ModuleCat.of K _ (data A).1.val (data A).2.group (data A).2.module

noncomputable def hom {U K : ZFSet.{u}} [Field K] (A B : objects U K) : ZFSet.{u} :=
  SetFunction.restricted (data A).1.val (data B).1.val
    (fun f => (∀ x y, f (addition (data A).2 x y) = addition (data B).2 (f x) (f y)) ∧
      (∀ k x, f (scalarAction (data A).2 k x) = scalarAction (data B).2 k (f x)))

noncomputable def homEquiv {U K : ZFSet.{u}} [Field K] (A B : objects U K) :
    (model A ⟶ model B) ≃ hom A B := by
  letI := (data A).2.group
  letI := (data B).2.group
  letI := (data A).2.module
  letI := (data B).2.module
  exact (show (model A ⟶ model B) ≃
      {f : (data A).1.val → (data B).1.val //
        (∀ x y, f (x + y) = f x + f y) ∧ (∀ k : K, ∀ x, f (k • x) = k • f x)} from
    { toFun := fun f => ⟨f.hom.toFun, f.hom.map_add, f.hom.map_smul⟩
      invFun := fun f => ModuleCat.ofHom
        { toFun := f.val
          map_add' := f.property.1
          map_smul' := f.property.2 }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (SetFunction.restrictedEquiv _ _ _)

theorem hom_mem {U K : ZFSet.{u}} [Field K] (hU : SetUniverse U)
    (A B : objects U K) : hom A B ∈ U :=
  SetFunction.restricted_mem hU (data A).1.property (data B).1.property _

noncomputable def category (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    SetCategory H.large :=
  SetCategory.ofModel (objects_mem H K) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

theorem locallySmall (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    (category H K).IsLocallySmall H.small := hom_mem H.small_universe

noncomputable def toModuleCat (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val] :
    SetCategory.Object (category H K) ⥤ ModuleCat K.val :=
  SetCategory.modelFunctor (objects_mem H K) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

noncomputable def toModuleCatFullyFaithful (H : UniverseHierarchy.{u})
    (K : H.small) [Field K.val] : (toModuleCat H K).FullyFaithful :=
  SetCategory.modelFullyFaithful (objects_mem H K) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

/-- Example 1.10: the actual linear graph is invertible exactly when bijective. -/
theorem isomorphism_iff_bijective (H : UniverseHierarchy.{u}) (K : H.small) [Field K.val]
    {A B : SetCategory.Object (category H K)} (f : A ⟶ B) :
    SetCategory.IsIsomorphism f ↔ Function.Bijective ((toModuleCat H K).map f) := by
  let F := toModuleCat H K
  let : F.Full := (toModuleCatFullyFaithful H K).full
  let : F.Faithful := (toModuleCatFullyFaithful H K).faithful
  rw [SetCategory.isIsomorphism_iff_isIso]
  constructor
  · intro hf
    let := hf
    exact (CategoryTheory.isIso_iff_bijective
      ((CategoryTheory.forget (ModuleCat K.val)).map (F.map f))).mp inferInstance
  · intro hf
    let : IsIso ((CategoryTheory.forget (ModuleCat K.val)).map (F.map f)) :=
      (CategoryTheory.isIso_iff_bijective _).mpr hf
    let : IsIso (F.map f) := isIso_of_reflects_iso _ (CategoryTheory.forget (ModuleCat K.val))
    exact isIso_of_reflects_iso f F

end SmallVectorSpaces
end ILab.MathematicsLearning
