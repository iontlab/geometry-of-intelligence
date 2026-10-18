import Mathlib.SetTheory.ZFC.Basic

/-!
# Explicit set-universe hypotheses (Moser–Walde 1.1–1.4)

These are predicates on Mathlib's well-founded ZFC sets, not new axioms.
Existence of three such universes is deliberately a parameter. Lean's type
universes are not identified with membership in these sets.
-/
namespace ILab.MathematicsLearning
universe u

/-- Item 1.1: the four closure requirements, with indexed unions explicit. -/
structure SetUniverse (U : ZFSet.{u}) : Prop where
  naturals : ZFSet.omega ∈ U
  subsets : ∀ A ∈ U, ∀ B : ZFSet.{u}, B ⊆ A → B ∈ U
  powersets : ∀ A ∈ U, ZFSet.powerset A ∈ U
  unions : ∀ I ∈ U, ∀ A : I → ZFSet.{u},
    (∀ i, A i ∈ U) → ZFSet.iUnion A ∈ U

/-- Item 1.2: Russell's separation argument uses only subset closure. -/
theorem universe_not_member (U : ZFSet.{u})
    (closed : ∀ A ∈ U, ∀ B : ZFSet.{u}, B ⊆ A → B ∈ U) : U ∉ U := by
  intro h
  let R := ZFSet.sep (fun A => A ∉ A) U
  have hR : R ∈ U := closed U h R ZFSet.sep_subset
  have diagonal : R ∈ R ↔ R ∉ R := by
    change R ∈ ZFSet.sep (fun A => A ∉ A) U ↔ R ∉ R
    simp only [ZFSet.mem_sep, hR, true_and]
  have hn : R ∉ R := fun hr => diagonal.mp hr hr
  exact hn (diagonal.mpr hn)

/-- Item 1.3: assumed nested universes; no existence theorem is asserted. -/
structure UniverseHierarchy where
  small : ZFSet.{u}
  large : ZFSet.{u}
  huge : ZFSet.{u}
  small_universe : SetUniverse small
  large_universe : SetUniverse large
  huge_universe : SetUniverse huge
  small_subset_large : small ⊆ large
  large_subset_huge : large ⊆ huge
  small_mem_large : small ∈ large
  large_mem_huge : large ∈ huge

/-- Item 1.4: the source's relative membership predicates. -/
def IsSmallSet (H : UniverseHierarchy.{u}) (A : ZFSet.{u}) : Prop := A ∈ H.small
def IsLargeSet (H : UniverseHierarchy.{u}) (A : ZFSet.{u}) : Prop := A ∈ H.large
def IsHugeSet (H : UniverseHierarchy.{u}) (A : ZFSet.{u}) : Prop := A ∈ H.huge

theorem smallSet_is_large (H : UniverseHierarchy.{u}) {A : ZFSet.{u}}
    (h : IsSmallSet H A) : IsLargeSet H A := H.small_subset_large h

theorem largeSet_is_huge (H : UniverseHierarchy.{u}) {A : ZFSet.{u}}
    (h : IsLargeSet H A) : IsHugeSet H A := H.large_subset_huge h

/-- Item 1.8 (Set case): the collection U of all U-small sets is not U-small. -/
theorem collection_of_small_sets_not_small (H : UniverseHierarchy.{u}) :
    ¬ IsSmallSet H H.small := universe_not_member H.small H.small_universe.subsets

/-- Introduction: equality transports predicates. This is not univalence. -/
theorem equality_substitution {A : Sort u} {x y : A} (h : x = y) (P : A → Prop) :
    P x ↔ P y := by cases h; rfl

/-- Introduction: transport of dependent data along equality. -/
def equality_transport {A : Sort u} {x y : A} (h : x = y) (P : A → Sort*) :
    P x → P y := h ▸ id

end ILab.MathematicsLearning
