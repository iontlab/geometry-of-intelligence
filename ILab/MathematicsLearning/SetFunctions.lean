import ILab.MathematicsLearning.SetUniverses

/-!
# Set functions and their membership-type representation

The source's sets remain `ZFSet`s. A term of `A` is literally a member of `A`,
not an arbitrary type of a chosen Lean universe. This module proves that a
function between these membership types has exactly the usual set-theoretic
graph, and that every such graph comes from one unique function. Consequently
using membership-type functions for operations in the set-coded categories
does not change their mathematical data.
-/

namespace ILab.MathematicsLearning
namespace SetFunction
universe u

noncomputable def graph {A B : ZFSet.{u}} (f : A → B) : ZFSet.{u} :=
  ZFSet.range (fun a : A => ZFSet.pair a.val (f a).val)

theorem pair_mem_graph {A B : ZFSet.{u}} (f : A → B) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ graph f ↔ ∃ ha : a ∈ A, (f ⟨a, ha⟩).val = b := by
  simp only [graph, ZFSet.mem_range, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨x, hx⟩, rfl, h⟩
    exact ⟨hx, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨⟨a, ha⟩, rfl, h⟩

theorem graph_isFunc {A B : ZFSet.{u}} (f : A → B) :
    ZFSet.IsFunc A B (graph f) := by
  constructor
  · intro z hz
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨a.property, (f a).property⟩
  · intro a ha
    refine ⟨(f ⟨a, ha⟩).val, (pair_mem_graph f a _).mpr ⟨ha, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨_, h⟩ := (pair_mem_graph f a b).mp hb
    exact h.symm

noncomputable def evaluate {A B G : ZFSet.{u}} (h : ZFSet.IsFunc A B G)
    (a : A) : B :=
  let b := Classical.choose (h.2 a.val a.property)
  ⟨b, (ZFSet.pair_mem_prod.mp (h.1 (Classical.choose_spec
    (h.2 a.val a.property)).1)).2⟩

theorem pair_mem_evaluate {A B G : ZFSet.{u}} (h : ZFSet.IsFunc A B G) (a : A) :
    ZFSet.pair a.val (evaluate h a).val ∈ G :=
  (Classical.choose_spec (h.2 a.val a.property)).1

theorem evaluate_graph {A B : ZFSet.{u}} (f : A → B) :
    evaluate (graph_isFunc f) = f := by
  funext a
  apply Subtype.ext
  obtain ⟨_, h⟩ := (pair_mem_graph f _ _).mp (pair_mem_evaluate (graph_isFunc f) a)
  exact h.symm

theorem graph_evaluate {A B G : ZFSet.{u}} (h : ZFSet.IsFunc A B G) :
    graph (evaluate h) = G := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    exact pair_mem_evaluate h a
  · intro hz
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (h.1 hz)
    have hb := (h.2 a ha).unique (pair_mem_evaluate h ⟨a, ha⟩) hz
    exact (pair_mem_graph (evaluate h) a b).mpr ⟨ha, hb⟩

/-- Every function between membership types corresponds to exactly one ZFC graph. -/
noncomputable def graphEquiv (A B : ZFSet.{u}) :
    (A → B) ≃ {G : ZFSet.{u} // ZFSet.IsFunc A B G} where
  toFun f := ⟨graph f, graph_isFunc f⟩
  invFun G := evaluate G.property
  left_inv := evaluate_graph
  right_inv G := Subtype.ext (graph_evaluate G.property)

/-- The same correspondence, with the codomain literally the set of functions. -/
noncomputable def funsEquiv (A B : ZFSet.{u}) : (A → B) ≃ ZFSet.funs A B where
  toFun f := ⟨graph f, ZFSet.mem_funs.mpr (graph_isFunc f)⟩
  invFun G := evaluate (ZFSet.mem_funs.mp G.property)
  left_inv := evaluate_graph
  right_inv G := Subtype.ext (graph_evaluate (ZFSet.mem_funs.mp G.property))

end SetFunction
end ILab.MathematicsLearning
