import ILab.MathematicsLearning.SetCategories
import ILab.MathematicsLearning.SetUniverseClosure

/-! The Set case of Example 1.8, with exactly the source's membership-based size.
The objects are all members of the assumed small universe, and hom sets are
the ZFC sets of functions. Unlike `Type u`, neither carrier is a substitute
for the manuscript's specified collection. -/
namespace ILab.MathematicsLearning
universe u
open CategoryTheory
open SetFunction

noncomputable def smallSetsCategory (H : UniverseHierarchy.{u}) : SetCategory H.large where
  objects := H.small
  objects_mem := H.small_mem_large
  hom A B := ZFSet.funs A.val B.val
  hom_mem A B := H.small_subset_large
    (H.small_universe.functions_mem A.property B.property)
  identity A := funsEquiv A.val A.val id
  compose {A B C} f g := funsEquiv A.val C.val
    ((funsEquiv B.val C.val).symm g ∘ (funsEquiv A.val B.val).symm f)
  identity_comp := by
    intro A B f
    simp
  comp_identity := by
    intro A B f
    simp
  associative := by
    intro A B C D f g h
    simp [Function.comp_assoc]

theorem smallSets_locallySmall (H : UniverseHierarchy.{u}) :
    (smallSetsCategory H).IsLocallySmall H.small := by
  intro A B
  exact H.small_universe.functions_mem A.property B.property

theorem smallSets_not_small (H : UniverseHierarchy.{u}) :
    ¬ (smallSetsCategory H).IsSmall H.small := by
  intro h
  exact universe_not_member H.small H.small_universe.subsets h.1

/-- Exact object correspondence: no change of set carriers or object equality. -/
noncomputable def smallSets_objects (H : UniverseHierarchy.{u}) :
    SetCategory.Object (smallSetsCategory H) ≃ H.small :=
  SetCategory.objectEquiv _

/-- Example 1.10 (Set): graph invertibility is precisely function bijectivity. -/
theorem smallSets_isomorphism_iff_bijective (H : UniverseHierarchy.{u})
    {A B : SetCategory.Object (smallSetsCategory H)} (f : A ⟶ B) :
    SetCategory.IsIsomorphism f ↔
      Function.Bijective ((funsEquiv A.member.val B.member.val).symm f) := by
  classical
  let e := funsEquiv A.member.val B.member.val
  let d := funsEquiv B.member.val A.member.val
  constructor
  · rintro ⟨g, hfg, hgf⟩
    have left : Function.LeftInverse (d.symm g) (e.symm f) := by
      intro a
      have h := congrArg (fun t => (funsEquiv A.member.val A.member.val).symm t a) hfg
      simpa [smallSetsCategory, SetCategory.instCategoryObject, e, d] using h
    have right : Function.RightInverse (d.symm g) (e.symm f) := by
      intro b
      have h := congrArg (fun t => (funsEquiv B.member.val B.member.val).symm t b) hgf
      simpa [smallSetsCategory, SetCategory.instCategoryObject, e, d] using h
    exact ⟨left.injective, right.surjective⟩
  · intro hf
    let equiv := Equiv.ofBijective (e.symm f) hf
    refine ⟨d equiv.symm, ?_, ?_⟩
    · change funsEquiv A.member.val A.member.val
        ((funsEquiv B.member.val A.member.val).symm (d equiv.symm) ∘ e.symm f) =
        funsEquiv A.member.val A.member.val id
      apply congrArg (funsEquiv A.member.val A.member.val)
      funext a
      dsimp only [d, Function.comp_apply]
      rw [Equiv.symm_apply_apply]
      exact equiv.symm_apply_apply a
    · change funsEquiv B.member.val B.member.val
        (e.symm f ∘ (funsEquiv B.member.val A.member.val).symm (d equiv.symm)) =
        funsEquiv B.member.val B.member.val id
      apply congrArg (funsEquiv B.member.val B.member.val)
      funext b
      dsimp only [d, Function.comp_apply]
      rw [Equiv.symm_apply_apply]
      exact equiv.apply_symm_apply b

end ILab.MathematicsLearning
