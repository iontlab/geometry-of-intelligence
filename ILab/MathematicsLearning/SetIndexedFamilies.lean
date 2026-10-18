import ILab.MathematicsLearning.SetUniverseClosure

/-! Faithful ZFC graphs of set-indexed families, including families whose
values are sets rather than members of a fixed specified codomain. -/
namespace ILab.MathematicsLearning.SetIndexedFamily
universe u

noncomputable def graph (I : ZFSet.{u}) (f : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i => ZFSet.pair i.val (f i))

theorem graph_injective (I : ZFSet.{u}) : Function.Injective (graph I) := by
  intro f g h
  funext i
  have hi : ZFSet.pair i.val (f i) ∈ graph I g := by
    rw [← h]
    exact ZFSet.mem_range_self i
  obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hi
  obtain ⟨hji, hgf⟩ := ZFSet.pair_inj.mp hj
  have hji' : j = i := Subtype.ext hji
  simpa [hji'] using hgf.symm

theorem graph_eq_functionGraph {I S : ZFSet.{u}} (f : I → S) :
    graph I (fun i => (f i).val) = SetFunction.graph f := rfl

theorem graph_mem_funs {I S : ZFSet.{u}} (f : I → ZFSet.{u}) (hf : ∀ i, f i ∈ S) :
    graph I f ∈ ZFSet.funs I S :=
  ZFSet.mem_funs.mpr (SetFunction.graph_isFunc (fun i => (⟨f i, hf i⟩ : S)))

theorem graph_mem {U I : ZFSet.{u}} (hU : SetUniverse U) (hI : I ∈ U)
    (f : I → ZFSet.{u}) (hf : ∀ i, f i ∈ U) : graph I f ∈ U := by
  have hr := hU.range_mem hI f hf
  exact hU.subsets _ (hU.product_mem hI hr) _
    (SetFunction.graph_isFunc (fun i => (⟨f i, ZFSet.mem_range_self i⟩ : ZFSet.range f))).1

theorem graph_mem_of_values {U I S : ZFSet.{u}} (hU : SetUniverse U)
    (hI : I ∈ U) (hS : S ∈ U) (f : I → ZFSet.{u}) (hf : ∀ i, f i ∈ S) :
    graph I f ∈ U :=
  hU.subsets _ (hU.product_mem hI hS) _
    (SetFunction.graph_isFunc (fun i => (⟨f i, hf i⟩ : S))).1

end ILab.MathematicsLearning.SetIndexedFamily
