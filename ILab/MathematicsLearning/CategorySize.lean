import ILab.MathematicsLearning.CategoryConstructions

/-!
# Size claims for the type-universe implementations (1.8 and 1.16)

Here `Small.{u}` means equivalent to a type in universe u. These are actual
non-smallness proofs, not just a declaration that an object type lives one
level higher. Set-theoretic membership is separately encoded in SetUniverses.
-/
namespace ILab.MathematicsLearning
open CategoryTheory
universe u v

/-- A small collection of small carriers cannot contain an embedding of every
small type: the union of all carriers would contradict Cantor's theorem. -/
theorem not_small_of_universal_embedding (C : Type v) (carrier : C → Type u)
    (covers : ∀ X : Type u, ∃ c, Nonempty (X ↪ carrier c)) : ¬ Small.{u} C := by
  intro hc
  let : Small.{u} C := hc
  let S := Shrink.{u} (Σ c, carrier c)
  obtain ⟨c, ⟨f⟩⟩ := covers (Set S)
  let e := equivShrink (Σ c, carrier c)
  apply Function.cantor_injective (fun A : Set S => e ⟨c, f A⟩)
  intro A B h
  apply f.injective
  have h' := e.injective h
  exact eq_of_heq (Sigma.mk.inj h').2

theorem sets_not_small : ¬ Small.{u} (Type u) := not_small_type

theorem pointed_sets_not_small : ¬ Small.{u} Pointed.{u} :=
  not_small_of_universal_embedding Pointed (fun X => X)
    (fun X => ⟨typeToPointed.obj X, ⟨⟨Option.some, Option.some_injective X⟩⟩⟩)

theorem spaces_not_small : ¬ Small.{u} TopCat.{u} :=
  not_small_of_universal_embedding TopCat (fun X => X)
    (fun X => ⟨TopCat.discrete.obj X, ⟨Function.Embedding.refl X⟩⟩)

theorem vector_spaces_not_small (k : Type u) [Field k] :
    ¬ Small.{u} (ModuleCat.{u} k) :=
  not_small_of_universal_embedding (ModuleCat k) (fun X => X)
    (fun X => ⟨(ModuleCat.free k).obj X,
      ⟨⟨fun x => Finsupp.single x 1, Finsupp.single_left_injective one_ne_zero⟩⟩⟩)

theorem small_categories_not_small : ¬ Small.{u} Cat.{u,u} :=
  not_small_of_universal_embedding Cat (fun X => X)
    (fun X => ⟨Cat.of (Discrete X), ⟨⟨Discrete.mk, fun _ _ h => congrArg Discrete.as h⟩⟩⟩)

theorem small_categories_locally_small : LocallySmall.{u} Cat.{u,u} := inferInstance

/-- 1.16: Cat of small categories is an object in a larger category of categories. -/
def smallCategoriesAsLargerObject : Cat.{u,u+1} := Cat.of Cat.{u,u}

end ILab.MathematicsLearning
