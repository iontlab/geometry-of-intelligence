import ILab.MathematicsLearning.SetFunctions

/-! Closure facts derived from precisely the four source universe assumptions.
No transitivity or closure under arbitrary external unions is added. -/
namespace ILab.MathematicsLearning
namespace SetUniverse
universe u
variable {U : ZFSet.{u}} (hU : SetUniverse U)
include hU

theorem empty_mem : (∅ : ZFSet.{u}) ∈ U :=
  hU.subsets ZFSet.omega hU.naturals ∅ (ZFSet.empty_subset _)

theorem singleton_mem {A : ZFSet.{u}} (hA : A ∈ U) : ({A} : ZFSet.{u}) ∈ U := by
  apply hU.subsets (ZFSet.powerset A) (hU.powersets A hA) {A}
  intro x hx
  have hx' : x = A := ZFSet.mem_singleton.mp hx
  subst x
  exact ZFSet.mem_powerset.mpr (fun _ hx => hx)

theorem union_mem {A B : ZFSet.{u}} (hA : A ∈ U) (hB : B ∈ U) : A ∪ B ∈ U := by
  classical
  let I := ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u}))
  have hI : I ∈ U := hU.powersets _ (hU.powersets _ hU.empty_mem)
  have h0 : (∅ : ZFSet.{u}) ∈ I := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  have h1 : ({∅} : ZFSet.{u}) ∈ I := by
    apply ZFSet.mem_powerset.mpr
    intro x hx
    have hx' : x = ∅ := ZFSet.mem_singleton.mp hx
    subst x
    exact ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  have hne : ({∅} : ZFSet.{u}) ≠ ∅ := by
    intro h
    have he : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
    rw [h] at he
    simp at he
  let family (i : I) := if i.val = ∅ then A else B
  have heq : ZFSet.iUnion family = A ∪ B := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_iUnion, ZFSet.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      dsimp [family] at hi
      split_ifs at hi with h
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hx | hx)
      · exact ⟨⟨∅, h0⟩, by simpa [family] using hx⟩
      · exact ⟨⟨{∅}, h1⟩, by simpa [family, hne] using hx⟩
  rw [← heq]
  apply hU.unions I hI family
  intro i
  dsimp [family]
  split_ifs <;> assumption

theorem pair_mem {A B : ZFSet.{u}} (hA : A ∈ U) (hB : B ∈ U) :
    ({A, B} : ZFSet.{u}) ∈ U := by
  have h := hU.union_mem (hU.singleton_mem hA) (hU.singleton_mem hB)
  have heq : ({A} : ZFSet.{u}) ∪ {B} = {A, B} := by
    ext x
    simp
  simpa [heq] using h

theorem orderedPair_mem {A B : ZFSet.{u}} (hA : A ∈ U) (hB : B ∈ U) :
    ZFSet.pair A B ∈ U :=
  hU.pair_mem (hU.singleton_mem hA) (hU.pair_mem hA hB)

theorem product_mem {A B : ZFSet.{u}} (hA : A ∈ U) (hB : B ∈ U) :
    ZFSet.prod A B ∈ U := by
  apply hU.subsets _ (hU.powersets _ (hU.powersets _ (hU.union_mem hA hB)))
  unfold ZFSet.prod ZFSet.pairSep
  exact ZFSet.sep_subset

theorem functions_mem {A B : ZFSet.{u}} (hA : A ∈ U) (hB : B ∈ U) :
    ZFSet.funs A B ∈ U :=
  hU.subsets _ (hU.powersets _ (hU.product_mem hA hB)) _ ZFSet.sep_subset

theorem range_mem {I : ZFSet.{u}} (hI : I ∈ U)
    (f : I → ZFSet.{u}) (hf : ∀ i, f i ∈ U) : ZFSet.range f ∈ U := by
  have he : ZFSet.range f = ZFSet.iUnion (fun i => ({f i} : ZFSet.{u})) := by
    ext x
    simp [eq_comm]
  rw [he]
  exact hU.unions I hI _ (fun i => hU.singleton_mem (hf i))

end SetUniverse
end ILab.MathematicsLearning
