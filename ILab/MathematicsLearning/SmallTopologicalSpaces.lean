import ILab.MathematicsLearning.SetCategoryModels
import ILab.MathematicsLearning.SetSubsets
import ILab.MathematicsLearning.SmallSetsCategory
import Mathlib.Topology.Category.TopCat.Adjunctions

/-! The topological-space parts of Examples 1.8 and 1.10, encoded by the
actual ordered pair (A, τ), where A is a small ZFC set and τ its set of opens.
No transitivity assumption on the source universes is needed. -/
namespace ILab.MathematicsLearning
universe u
open CategoryTheory

namespace SmallTopologicalSpaces

private instance topologySmall (A : ZFSet.{u}) : Small.{u} (TopologicalSpace A) :=
  small_of_injective (f := fun t : TopologicalSpace A => t.IsOpen) (by
    intro t s h
    cases t
    cases s
    cases h
    rfl)

abbrev Data (U : ZFSet.{u}) := Σ A : U, TopologicalSpace A.val

noncomputable def opens (A : ZFSet.{u}) (t : TopologicalSpace A) : ZFSet.{u} :=
  ZFSet.sep (fun s => ∃ S : Set A, SetSubset.encode A S = s ∧ t.IsOpen S)
    (ZFSet.powerset A)

theorem opens_subset (A : ZFSet.{u}) (t : TopologicalSpace A) :
    opens A t ⊆ ZFSet.powerset A := ZFSet.sep_subset

@[simp] theorem encode_mem_opens (A : ZFSet.{u}) (t : TopologicalSpace A) (S : Set A) :
    SetSubset.encode A S ∈ opens A t ↔ t.IsOpen S := by
  constructor
  · intro h
    obtain ⟨T, hT, ht⟩ := (ZFSet.mem_sep.mp h).2
    have he := SetSubset.encode_injective A hT
    simpa [he] using ht
  · intro h
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (SetSubset.encode_subset A S), S, rfl, h⟩

theorem opens_injective (A : ZFSet.{u}) : Function.Injective (opens A) := by
  intro t s h
  apply TopologicalSpace.ext
  funext S
  apply propext
  change t.IsOpen S ↔ s.IsOpen S
  rw [← encode_mem_opens A t S, ← encode_mem_opens A s S, h]

noncomputable def encode {U : ZFSet.{u}} (A : Data U) : ZFSet.{u} :=
  ZFSet.pair A.1.val (opens A.1.val A.2)

theorem encode_injective (U : ZFSet.{u}) : Function.Injective (@encode U) := by
  rintro ⟨⟨A, hA⟩, t⟩ ⟨⟨B, hB⟩, s⟩ h
  obtain ⟨hAB, hts⟩ := ZFSet.pair_inj.mp h
  cases hAB
  have ht := opens_injective A hts
  cases ht
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
  exact ZFSet.pair_mem_prod.mpr ⟨A.1.property,
    H.small_universe.subsets _ (H.small_universe.powersets _ A.1.property) _
      (opens_subset A.1.val A.2)⟩

noncomputable def data {U : ZFSet.{u}} (A : objects U) : Data U :=
  (objectEquiv U).symm A

noncomputable def model {U : ZFSet.{u}} (A : objects U) : TopCat :=
  @TopCat.of (data A).1.val (data A).2

noncomputable def hom {U : ZFSet.{u}} (A B : objects U) : ZFSet.{u} :=
  SetFunction.restricted (data A).1.val (data B).1.val
    (@Continuous _ _ (data A).2 (data B).2)

noncomputable def homEquiv {U : ZFSet.{u}} (A B : objects U) :
    (model A ⟶ model B) ≃ hom A B :=
  (show (model A ⟶ model B) ≃
      {f : (data A).1.val → (data B).1.val //
        @Continuous _ _ (data A).2 (data B).2 f} from
    { toFun := fun f => ⟨f.hom.toFun, f.hom.continuous⟩
      invFun := fun f => @TopCat.ofHom _ _ (data A).2 (data B).2
        (@ContinuousMap.mk _ _ (data A).2 (data B).2 f.val f.property)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (SetFunction.restrictedEquiv _ _ _)

theorem hom_mem {U : ZFSet.{u}} (hU : SetUniverse U) (A B : objects U) : hom A B ∈ U :=
  SetFunction.restricted_mem hU (data A).1.property (data B).1.property _

noncomputable def category (H : UniverseHierarchy.{u}) : SetCategory H.large :=
  SetCategory.ofModel (objects_mem H) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

theorem locallySmall (H : UniverseHierarchy.{u}) :
    (category H).IsLocallySmall H.small := hom_mem H.small_universe

noncomputable def toTopCat (H : UniverseHierarchy.{u}) :
    SetCategory.Object (category H) ⥤ TopCat :=
  SetCategory.modelFunctor (objects_mem H) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

noncomputable def toTopCatFullyFaithful (H : UniverseHierarchy.{u}) :
    (toTopCat H).FullyFaithful :=
  SetCategory.modelFullyFaithful (objects_mem H) model hom
    (fun A B => H.small_subset_large (hom_mem H.small_universe A B)) homEquiv

/-- Example 1.10 for the continuous maps on the original small set carriers. -/
theorem isomorphism_iff_homeomorphism (H : UniverseHierarchy.{u})
    {A B : SetCategory.Object (category H)} (f : A ⟶ B) :
    SetCategory.IsIsomorphism f ↔ IsHomeomorph ((toTopCat H).map f) := by
  let F := toTopCat H
  let : F.Full := (toTopCatFullyFaithful H).full
  let : F.Faithful := (toTopCatFullyFaithful H).faithful
  rw [SetCategory.isIsomorphism_iff_isIso]
  constructor
  · intro hf
    let := hf
    exact (TopCat.isIso_iff_isHomeomorph (F.map f)).mp inferInstance
  · intro hf
    let : IsIso (F.map f) := (TopCat.isIso_iff_isHomeomorph (F.map f)).mpr hf
    exact isIso_of_reflects_iso f F

theorem not_small (H : UniverseHierarchy.{u}) : ¬ (category H).IsSmall H.small := by
  intro h
  let p : objects H.small → ZFSet.{u} := fun A => (data A).1.val
  have hp : ZFSet.range p ∈ H.small :=
    H.small_universe.range_mem h.1 p (fun A => (data A).1.property)
  have he : ZFSet.range p = H.small := by
    ext A
    constructor
    · intro hA
      obtain ⟨B, rfl⟩ := ZFSet.mem_range.mp hA
      exact (data B).1.property
    · intro hA
      let B : Data H.small := ⟨⟨A, hA⟩, ⊥⟩
      refine ZFSet.mem_range.mpr ⟨objectEquiv H.small B, ?_⟩
      simp [p, data, B]
  rw [he] at hp
  exact universe_not_member H.small H.small_universe.subsets hp

end SmallTopologicalSpaces
end ILab.MathematicsLearning
