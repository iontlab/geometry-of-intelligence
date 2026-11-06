import ILab.LinearAlgebra.LinearCombinations
import ILab.LinearAlgebra.FieldsComplex
import ILab.LinearAlgebra.RingsPolynomials
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Holstein §4.2, pp.65–70. No alteration of the existing Dimensions module.
Sets use subtypes; ordered families retain indices. Fin n is zero indexed.
Holstein's infinity collapses all infinite cardinal dimensions to a single value;
it is NOT Mathlib's natural-valued finrank outside finite-dimensional spaces.
The exercise-only proof of 4.2.10 is not presented as original source text. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module Function Set Submodule
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def isGeneratingSet (M : Set V) : Prop := span K M = ⊤
def isVectorBasisSet (M : Set V) : Prop := LinearIndepOn K id M ∧ isGeneratingSet (K := K) M
def isMinimalGeneratingSet (M : Set V) : Prop :=
  isGeneratingSet (K := K) M ∧ ∀ v ∈ M, ¬isGeneratingSet (K := K) (M \ {v})
def isMaximalIndependentSet (M : Set V) : Prop :=
  LinearIndepOn K id M ∧ ∀ v ∉ M, ¬LinearIndepOn K id (insert v M)

theorem basisSetCharacterization (M : Set V) :
    isVectorBasisSet (K := K) M ↔ LinearIndepOn K id M ∧ span K M = ⊤ := Iff.rfl

def isOrderedVectorBasis {n : ℕ} (v : Fin n → V) : Prop :=
  LinearIndependent K v ∧ span K (range v) = ⊤

def orderedBasisFromFamily {n : ℕ} (v : Fin n → V) (h : isOrderedVectorBasis (K := K) v) :
    Basis (Fin n) K V := Basis.mk h.1 h.2.ge

theorem orderedBasisValues {n : ℕ} (v : Fin n → V) (h : isOrderedVectorBasis (K := K) v) :
    ⇑(orderedBasisFromFamily v h) = v := Basis.coe_mk ..

theorem standardOrderedBasis (n : ℕ) : isOrderedVectorBasis (K := K) (Pi.basisFun K (Fin n)) :=
  ⟨standardVectorsIndependent n, standardVectorsSpan n⟩

theorem basisIffMinimalGenerating (M : Set V) :
    isVectorBasisSet (K := K) M ↔ isMinimalGeneratingSet (K := K) M := by
  constructor
  · rintro ⟨hli, hsp⟩
    refine ⟨hsp, fun v hv he => ?_⟩
    have hn := hli.notMem_span hv
    simp only [image_id] at hn
    exact hn (he.symm ▸ mem_top)
  · rintro ⟨hsp, hmin⟩
    refine ⟨?_, hsp⟩
    rw [linearIndepOn_iff_notMem_span]
    intro v hv
    simp only [image_id, id_eq]
    intro hm
    have hi : insert v (M \ {v}) = M := by ext x; simp; aesop
    have hm' : v ∈ span K (M \ {v}) := by simpa using hm
    have he := span_insert_eq_span hm'
    rw [hi] at he
    exact hmin v hv (he.symm.trans hsp)

theorem basisIffMaximalIndependent (M : Set V) :
    isVectorBasisSet (K := K) M ↔ isMaximalIndependentSet (K := K) M := by
  constructor
  · rintro ⟨hli, hsp⟩
    refine ⟨hli, fun v hv hi => ?_⟩
    have hn := hi.notMem_span_of_insert hv
    simp only [id_eq] at hn
    simp only [Set.image_id'] at hn
    exact hn (hsp.symm ▸ mem_top)
  · rintro ⟨hli, hmax⟩
    refine ⟨hli, top_unique ?_⟩
    intro v _
    by_contra h
    exact hmax v (fun hm => h (subset_span hm)) (hli.id_insert h)

theorem finiteGenerationByFiniteSet : Module.Finite K V ↔
    ∃ M : Set V, M.Finite ∧ isGeneratingSet (K := K) M := by
  rw [Module.finite_def, Submodule.fg_def]
  rfl

theorem arbitrarilyLargeIndependentFamilies (h : ¬Module.Finite K V) (n : ℕ) :
    ∃ v : Fin n → V, LinearIndependent K v := by
  apply exists_linearIndependent_of_le_rank
  have hinf : Cardinal.aleph0 ≤ Module.rank K V := le_of_not_gt (mt Module.rank_lt_aleph0_iff.mp h)
  exact (Cardinal.natCast_le_aleph0 (n := n)).trans hinf

theorem selectBasisFromFiniteGenerators (M : Set V) (hm : M.Finite)
    (hsp : isGeneratingSet (K := K) M) :
    ∃ B : Set V, B ⊆ M ∧ B.Finite ∧ isVectorBasisSet (K := K) B := by
  let b := Basis.ofSpan hsp.ge
  have hsub : range b ⊆ M := Basis.ofSpan_subset hsp.ge
  exact ⟨range b, hsub, hm.subset hsub, b.linearIndependent.linearIndepOn_id, b.span_eq⟩

/-- The exact indexed replacement and nonzero-coordinate condition of 4.2.8. -/
theorem exchangedFamilyIndependent [DecidableEq ι] (b : Basis ι K V) (w : V) (k : ι)
    (hk : b.repr w k ≠ 0) : LinearIndependent K (Function.update b k w) := by
  apply b.linearIndependent.update k w
  refine ⟨1, by simp, b.repr w, ?_, ?_⟩
  · simpa only [mem_nonZeroDivisors_iff_ne_zero] using hk
  · simpa only [one_smul] using (b.linearCombination_repr w).symm

def exchangedOrderedBasis [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (w : V) (k : ι)
    (hk : b.repr w k ≠ 0) : Basis ι K V := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  let hi := exchangedFamilyIndependent b w k hk
  exact Basis.mk hi (hi.span_eq_top_of_card_eq_finrank' (finrank_eq_card_basis b).symm).ge

theorem exchangedOrderedBasisValues [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (w : V) (k : ι) (hk : b.repr w k ≠ 0) :
    ⇑(exchangedOrderedBasis b w k hk) = Function.update b k w := by unfold exchangedOrderedBasis; exact Basis.coe_mk ..

theorem zeroCoordinateExchangeFails [DecidableEq ι] (b : Basis ι K V) (w : V) (k : ι)
    (hk : b.repr w k = 0) : b k ∉ span K (range (Function.update b k w)) := by
  intro h
  have hz : ∀ x ∈ span K (range (Function.update b k w)), b.repr x k = 0 := by
    intro x hx
    induction hx using span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      by_cases hi : i = k
      · subst i; simpa using hk
      · simp [Function.update_of_ne hi, Basis.repr_self, hi]
    | zero => simp
    | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
    | smul a x hx ih => simp [map_smul, ih]
  have := hz (b k) h
  simpa using this

/-- Set form of Steinitz: an independent set is incorporated using only original basis vectors. -/
theorem incorporateIndependentSet (B S : Set V) (hb : isVectorBasisSet (K := K) B)
    (hs : LinearIndepOn K id S) :
    ∃ C : Set V, S ⊆ C ∧ C ⊆ S ∪ B ∧ isVectorBasisSet (K := K) C := by
  have ht : ⊤ ≤ span K (S ∪ B) := by rw [span_union, hb.2, sup_top_eq]
  let b := Basis.extendLe hs (subset_union_left : S ⊆ S ∪ B) ht
  exact ⟨range b, Basis.subset_extendLe hs _ ht, Basis.extendLe_subset hs _ ht,
    b.linearIndependent.linearIndepOn_id, b.span_eq⟩

theorem independentFamilyLengthBound [Fintype ι] [FiniteDimensional K V] (v : ι → V)
    (hv : LinearIndependent K v) : Fintype.card ι ≤ finrank K V := hv.fintype_card_le_finrank

theorem extendIndependentSetToBasis (S : Set V) (hs : LinearIndepOn K id S) :
    ∃ B : Set V, S ⊆ B ∧ isVectorBasisSet (K := K) B := by
  let b := Basis.extend hs
  refine ⟨range b, ?_, b.linearIndependent.linearIndepOn_id, b.span_eq⟩
  rw [Basis.range_extend]
  exact hs.subset_extend _

def basisLength [Fintype ι] (_b : Basis ι K V) : ℕ := Fintype.card ι

theorem basisLengthEqualsFinrank [Fintype ι] (b : Basis ι K V) :
    basisLength b = finrank K V := (finrank_eq_card_basis b).symm

theorem everyBasisFinite [FiniteDimensional K V] (b : Basis ι K V) : Finite ι :=
  Module.Finite.finite_basis b

theorem basisLengthsEqual {κ : Type*} [Fintype ι] [Fintype κ]
    (b : Basis ι K V) (c : Basis κ K V) : basisLength b = basisLength c :=
  (basisLengthEqualsFinrank b).trans (basisLengthEqualsFinrank c).symm

def holsteinDimension (K V : Type*) [Field K] [AddCommGroup V] [Module K V] : ℕ∞ := by
  classical
  exact if Module.Finite K V then (finrank K V : ℕ∞) else ⊤

theorem holsteinDimensionFinite [FiniteDimensional K V] :
    holsteinDimension K V = (finrank K V : ℕ∞) := by simp [holsteinDimension, show Module.Finite K V from inferInstance]

theorem holsteinDimensionInfinite (h : ¬Module.Finite K V) : holsteinDimension K V = ⊤ := by
  simp [holsteinDimension, h]

theorem holsteinDimensionCoordinates (n : ℕ) : holsteinDimension K (Fin n → K) = n := by
  rw [holsteinDimensionFinite, Module.finrank_fintype_fun_eq_card]
  simp

theorem holsteinDimensionZero : holsteinDimension K (Fin 0 → K) = 0 := by
  simpa using (holsteinDimensionCoordinates (K := K) 0)

theorem holsteinDimensionComplexReal : holsteinDimension ℝ ℂ = 2 := by
  rw [holsteinDimensionFinite, Complex.finrank_real_complex]
  rfl

theorem holsteinDimensionComplexComplex : holsteinDimension ℂ ℂ = 1 := by
  rw [holsteinDimensionFinite, Module.finrank_self]
  rfl

theorem holsteinDimensionPolynomials : holsteinDimension K (Polynomial K) = ⊤ :=
  holsteinDimensionInfinite Polynomial.not_finite

theorem subspaceFiniteGeneration [FiniteDimensional K V] (W : Submodule K V) :
    Module.Finite K W := inferInstance

theorem subspaceDimensionBound [FiniteDimensional K V] (W : Submodule K V) :
    finrank K W ≤ finrank K V := Submodule.finrank_le W

theorem subspaceEqualOfEqualDimension [FiniteDimensional K V] (W : Submodule K V)
    (h : finrank K W = finrank K V) : W = ⊤ := Submodule.eq_top_of_finrank_eq h

end ILab.LinearAlgebra
