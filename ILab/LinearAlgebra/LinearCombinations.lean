import ILab.LinearAlgebra.LinearMapsFamilies
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Holstein §4.1, pp.62–65. Arbitrary fields/modules, no finite-dimension assumption.
Finite support is essential for arbitrary generating sets. Fin n is zero indexed;
Holstein's displayed positions 1,...,n are obtained by adding one to the index.
Original typographical errors are retained in Mathematics, not asserted here. -/
namespace ILab.LinearAlgebra
open Function
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Definition4.1.1: coefficients have finite support, even for an infinite family. -/
noncomputable def finiteSupportCombination (v : ι → V) : (ι →₀ K) →ₗ[K] V :=
  Finsupp.linearCombination K v

theorem finiteSupportCombinationValue (v : ι → V) (c : ι →₀ K) :
    finiteSupportCombination v c = c.sum (fun i a => a • v i) := rfl

theorem spanMembershipFiniteCombination (M : Set V) (x : V) :
    x ∈ Submodule.span K M ↔ ∃ (n : ℕ) (c : Fin n → K) (v : Fin n → M),
      ∑ i, c i • (v i : V) = x := Submodule.mem_span_set'

theorem spanEmptyIsZero : Submodule.span K (∅ : Set V) = ⊥ :=
  Submodule.span_empty

/-- Satz4.1.2: the Submodule carries all three closure conditions. -/
def generatedSubspace (M : Set V) : Submodule K V := Submodule.span K M

theorem generatedContains (M : Set V) : M ⊆ generatedSubspace (K := K) M :=
  Submodule.subset_span

theorem generatedMinimal (M : Set V) (W : Submodule K V) (h : M ⊆ W) :
    generatedSubspace (K := K) M ≤ W := Submodule.span_le.mpr h

theorem generatedIntersection (M : Set V) :
    generatedSubspace (K := K) M = sInf {W : Submodule K V | M ⊆ W} := by
  apply le_antisymm
  · exact le_sInf fun W hW => generatedMinimal (K := K) M W hW
  · exact sInf_le (generatedContains (K := K) M)

/-- Beispiele4.1.3: general finite or infinite family of subspaces. -/
theorem spanOfSubspaceUnion (W : ι → Submodule K V) :
    Submodule.span K (⋃ i, (W i : Set V)) = ⨆ i, W i := by
  simp only [Submodule.span_iUnion, Submodule.span_eq]

theorem standardVectorsSpan (n : ℕ) :
    Submodule.span K (Set.range (Pi.basisFun K (Fin n))) = ⊤ :=
  (Pi.basisFun K (Fin n)).span_eq

theorem singletonSpanMembership (v x : V) :
    x ∈ Submodule.span K {v} ↔ ∃ a : K, a • v = x := by
  exact Submodule.mem_span_singleton

/-- Definition4.1.4 and Bemerkungen4.1.5: indexed families, not deduplicated sets. -/
theorem independentZeroRelation (v : ι → V) :
    LinearIndependent K v ↔ ∀ c : ι →₀ K,
      finiteSupportCombination v c = 0 → c = 0 := linearIndependent_iff

theorem dependentNontrivialRelation (v : ι → V) :
    ¬ LinearIndependent K v ↔ ∃ c : ι →₀ K,
      c ≠ 0 ∧ finiteSupportCombination v c = 0 := by
  rw [independentZeroRelation]
  push Not
  exact exists_congr fun c => and_comm

theorem independentFiniteCharacter (v : ι → V) :
    LinearIndependent K v ↔ ∀ s : Finset ι,
      LinearIndependent K (fun i : s => v i) :=
  linearIndependent_iff_finset_linearIndependent

theorem emptyFamilyIndependent (v : Fin 0 → V) : LinearIndependent K v :=
  linearIndependent_empty_type

theorem standardVectorsIndependent (n : ℕ) :
    LinearIndependent K (Pi.basisFun K (Fin n)) :=
  (Pi.basisFun K (Fin n)).linearIndependent

theorem standardSubsetIndependent (n : ℕ) (s : Set (Fin n)) :
    LinearIndependent K (fun i : s => Pi.basisFun K (Fin n) i) :=
  (standardVectorsIndependent n).comp _ Subtype.val_injective

theorem repeatedPositionsDependent (v : ι → V) (i j : ι)
    (hij : i ≠ j) (hv : v i = v j) : ¬ LinearIndependent K v := by
  intro h
  exact hij (h.injective hv)

theorem singlePositionIndependent (v : V) :
    LinearIndependent K (fun _ : Fin 1 => v) ↔ v ≠ 0 := linearIndependent_unique_iff

/-- Lemma4.1.6: both directions, including existence and arbitrary finite support. -/
theorem independentUniqueRepresentation (v : ι → V) :
    LinearIndependent K v ↔ ∀ x ∈ Submodule.span K (Set.range v),
      ∃! c : ι →₀ K, finiteSupportCombination v c = x := by
  constructor
  · intro h x hx
    have hr := Finsupp.range_linearCombination K (v := v)
    obtain ⟨c, hc⟩ := (LinearMap.mem_range.mp (hr.symm ▸ hx))
    exact ⟨c, hc, fun d hd => h (hd.trans hc.symm)⟩
  · intro h
    apply (independentZeroRelation v).mpr
    intro c hc
    obtain ⟨d, hd, hu⟩ := h 0 (Submodule.zero_mem _)
    exact (hu c hc).trans (hu 0 (by simp [finiteSupportCombination])).symm

theorem coefficientDifferenceZero (v : ι → V) (c d : ι →₀ K)
    (h : finiteSupportCombination v c = finiteSupportCombination v d) :
    finiteSupportCombination v (c - d) = 0 := by
  rw [map_sub, h, sub_self]

theorem nullRelationChangesRepresentation (v : ι → V) (c z : ι →₀ K)
    (hz : finiteSupportCombination v z = 0) (hne : z ≠ 0) :
    c + z ≠ c ∧ finiteSupportCombination v (c + z) = finiteSupportCombination v c := by
  constructor
  · intro h
    exact hne (add_left_cancel (h.trans (add_zero c).symm))
  · rw [map_add, hz, add_zero]

/-- Definition4.1.7 records positions, not an order on the values in V. -/
abbrev OrderedVectorFamily (V : Type*) (n : ℕ) := Fin n → V

abbrev CountableOrderedVectorFamily (V : Type*) := ℕ → V

/-- Lemma4.1.8: an actual linear map on all coefficient vectors, also n=0. -/
noncomputable def familyCoordinateMap {n : ℕ} (v : Fin n → V) : (Fin n → K) →ₗ[K] V :=
  Fintype.linearCombination K v

theorem familyCoordinateFormula {n : ℕ} (v : Fin n → V) (c : Fin n → K) :
    familyCoordinateMap (K := K) v c = ∑ i, c i • v i :=
  Fintype.linearCombination_apply K v c

theorem familyCoordinateStandardVector {n : ℕ} (v : Fin n → V) (i : Fin n) :
    familyCoordinateMap (K := K) v (Pi.single i 1) = v i := by
  simp [familyCoordinateMap, Fintype.linearCombination_apply_single]

theorem familyCoordinateImage {n : ℕ} (v : Fin n → V) :
    LinearMap.range (familyCoordinateMap (K := K) v) = Submodule.span K (Set.range v) :=
  Fintype.range_linearCombination K v

theorem familyCoordinateSurjective {n : ℕ} (v : Fin n → V) :
    Surjective (familyCoordinateMap (K := K) v) ↔ Submodule.span K (Set.range v) = ⊤ := by
  rw [← LinearMap.range_eq_top, familyCoordinateImage]

theorem familyCoordinateInjective {n : ℕ} (v : Fin n → V) :
    Injective (familyCoordinateMap (K := K) v) ↔ LinearIndependent K v :=
  linearIndependent_iff_injective_fintypeLinearCombination.symm

theorem familyCoordinateUnique {n : ℕ} (v : Fin n → V)
    (f : (Fin n → K) →ₗ[K] V) (hf : ∀ i, f (Pi.single i 1) = v i) :
    f = familyCoordinateMap (K := K) v := by
  apply (Pi.basisFun K (Fin n)).ext
  intro i
  simpa [Pi.basisFun_apply] using (hf i).trans (familyCoordinateStandardVector (K := K) v i).symm

end ILab.LinearAlgebra
