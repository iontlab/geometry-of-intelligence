import ILab.MathematicsLearning.FiniteSetCategories

/-! The unnumbered strict-versus-equivalent comparison on the manuscript's
actual set-coded singleton and two-object categories. -/
namespace ILab.MathematicsLearning
universe u
open CategoryTheory SetCategory

theorem strict_inverse_object_bijective {U : ZFSet.{u}} {C D : SetCategory U}
    (F : SourceFunctor C D) (G : SourceFunctor D C)
    (hGF : F.toMathlib ⋙ G.toMathlib = 𝟭 (Object C))
    (hFG : G.toMathlib ⋙ F.toMathlib = 𝟭 (Object D)) : Function.Bijective F.obj := by
  have hleft : Function.LeftInverse G.obj F.obj := by
    intro X
    exact congrArg (fun K : Object C ⥤ Object C => K.obj X) hGF
  have hright : Function.RightInverse G.obj F.obj := by
    intro Y
    exact congrArg (fun K : Object D ⥤ Object D => K.obj Y) hFG
  exact ⟨hleft.injective, hright.surjective⟩

theorem terminal_to_walking_not_surjective (H : UniverseHierarchy.{u})
    (f : Object (terminalSetCategory H) → Object (walkingSetCategory H)) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨x, hx⟩ := hf (walkingZero H)
  obtain ⟨y, hy⟩ := hf (walkingOne H)
  have hxy : x = y := (terminal_object_unique H x).trans (terminal_object_unique H y).symm
  exact walking_zero_ne_one H (hx.symm.trans ((congrArg f hxy).trans hy))

theorem walking_not_strictly_isomorphic_sets (H : UniverseHierarchy.{u}) :
    ¬ ∃ F : SourceFunctor (terminalSetCategory H) (walkingSetCategory H),
      ∃ G : SourceFunctor (walkingSetCategory H) (terminalSetCategory H),
        F.toMathlib ⋙ G.toMathlib = 𝟭 _ ∧ G.toMathlib ⋙ F.toMathlib = 𝟭 _ := by
  rintro ⟨F, G, hGF, hFG⟩
  exact terminal_to_walking_not_surjective H F.obj
    (strict_inverse_object_bijective F G hGF hFG).surjective

end ILab.MathematicsLearning
