import ILab.MathematicsLearning.SetUniverseClosure

/-! Subsets of a ZFC membership type are represented by their actual ZFC sets.
This explicit correspondence is used to encode topologies. -/
namespace ILab.MathematicsLearning.SetSubset
universe u

noncomputable def encode (A : ZFSet.{u}) (s : Set A) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ hx : x ∈ A, (⟨x, hx⟩ : A) ∈ s) A

theorem encode_subset (A : ZFSet.{u}) (s : Set A) : encode A s ⊆ A := ZFSet.sep_subset

@[simp] theorem mem_encode (A : ZFSet.{u}) (s : Set A) (x : A) :
    x.val ∈ encode A s ↔ x ∈ s := by
  simp [encode, x.property]

theorem encode_injective (A : ZFSet.{u}) : Function.Injective (encode A) := by
  intro s t h
  ext x
  rw [← mem_encode, ← mem_encode, h]

noncomputable def equiv (A : ZFSet.{u}) : Set A ≃ ZFSet.powerset A :=
  Equiv.ofBijective (fun s => ⟨encode A s, ZFSet.mem_powerset.mpr (encode_subset A s)⟩)
    ⟨by
      intro s t h
      exact encode_injective A (congrArg (fun x : ZFSet.powerset A => x.val) h), by
      intro s
      refine ⟨{x : A | x.val ∈ s.val}, Subtype.ext ?_⟩
      ext x
      simp only [encode, ZFSet.mem_sep, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨_, hx, hxs⟩
        exact hxs
      · intro hx
        exact ⟨ZFSet.mem_powerset.mp s.property hx, ZFSet.mem_powerset.mp s.property hx, hx⟩⟩

@[simp] theorem encode_empty (A : ZFSet.{u}) : encode A ∅ = ∅ := by
  ext x
  simp [encode]

@[simp] theorem encode_univ (A : ZFSet.{u}) : encode A Set.univ = A := by
  ext x
  simp [encode]

end ILab.MathematicsLearning.SetSubset
