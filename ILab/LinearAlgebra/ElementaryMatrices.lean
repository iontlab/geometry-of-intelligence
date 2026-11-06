import ILab.LinearAlgebra.MoreMatrices
import ILab.LinearAlgebra.Dimensions
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Holstein §5.3, LA-P018, printed81–87. General field, finite rectangular
matrices. The original faulty swap formula and swapped indices are separately
preserved in Mathematics, not asserted here. Stufenform means the non-reduced
condition; the pivot normalization does not require zeros above leading entries.
This is a mathematical formalization, not a verified JavaScript algorithm. -/
noncomputable section
namespace ILab.LinearAlgebra
open Matrix Module
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] {m n : ℕ}

def fieldSystemSolutions (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) : Set (Fin n → K) :=
  {x | A.mulVec x = b}

theorem fieldHomogeneousZero (A : Matrix (Fin m) (Fin n) K) :
    (0 : Fin n → K) ∈ fieldSystemSolutions A 0 := by
  simp [fieldSystemSolutions]

theorem fieldSolutionsAffine (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (x₀ : Fin n → K) (hx₀ : x₀ ∈ fieldSystemSolutions A b) :
    fieldSystemSolutions A b = {x | ∃ v ∈ LinearMap.ker A.mulVecLin, x = x₀ + v} := by
  ext x
  constructor
  · intro hx
    refine ⟨x - x₀, ?_, by abel⟩
    change A.mulVec (x - x₀) = 0
    rw [Matrix.mulVec_sub, show A.mulVec x = b from hx,
      show A.mulVec x₀ = b from hx₀, sub_self]
  · rintro ⟨v, hv, rfl⟩
    change A.mulVec (x₀ + v) = b
    rw [Matrix.mulVec_add, show A.mulVec x₀ = b from hx₀,
      show A.mulVec v = 0 from hv, add_zero]

theorem fieldSolutionDifference (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (x y : Fin n → K) (hx : x ∈ fieldSystemSolutions A b)
    (hy : y ∈ fieldSystemSolutions A b) : x-y ∈ LinearMap.ker A.mulVecLin := by
  change A.mulVec (x-y) = 0
  rw [Matrix.mulVec_sub, show A.mulVec x = b from hx, show A.mulVec y = b from hy, sub_self]

def holsteinSpecialEchelon (A : Matrix (Fin m) (Fin n) K) : Prop :=
  A.IsRowEchelon ∧ ∀ i j, A.IsLeadingEntry i j → A i j = 1

def firstNonzeroPivot (A : Matrix (Fin m) (Fin n) K) (i : Fin m) : WithTop (Fin n) :=
  if h : A i = 0 then ⊤ else ↑(Classical.choose (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp h))

theorem echelonPivotCertificate (A : Matrix (Fin m) (Fin n) K) (hA : A.IsRowEchelon) :
    A.IsPivotedBy (firstNonzeroPivot A) := by
  classical
  refine ⟨hA, ?_⟩
  intro i
  by_cases h : A i = 0
  · simp [firstNonzeroPivot, h]
  · have hc := Classical.choose_spec (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp h)
    simp only [firstNonzeroPivot, dite_eq_right h]
    refine ⟨?_, ?_⟩
    · intro j hj
      exact hc.1 j (WithTop.coe_lt_coe.mp hj)
    · intro c hc'
      have he := WithTop.coe_injective hc'
      simpa [← he] using hc.2

theorem echelonRankNonzeroRows (A : Matrix (Fin m) (Fin n) K) (hA : A.IsRowEchelon) :
    A.rank = (Finset.univ.filter fun i => A i ≠ 0).card := by
  classical
  rw [(echelonPivotCertificate A hA).rank_eq]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (echelonPivotCertificate A hA).eq_top_iff

theorem matrixNullityRank (A : Matrix (Fin m) (Fin n) K) :
    finrank K (LinearMap.ker A.mulVecLin) + A.rank = n := by
  simpa [finiteRank, Matrix.rank] using (rankNullity A.mulVecLin).symm

theorem echelonNullity (A : Matrix (Fin m) (Fin n) K) (hA : A.IsRowEchelon) :
    finrank K (LinearMap.ker A.mulVecLin) =
      n - (Finset.univ.filter fun i => A i ≠ 0).card := by
  classical
  have h := matrixNullityRank A
  rw [echelonRankNonzeroRows A hA] at h
  omega

theorem fieldInconsistentZeroRow (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (i : Fin m) (hz : ∀ j, A i j = 0) (hb : b i ≠ 0) : fieldSystemSolutions A b = ∅ := by
  ext x
  constructor
  · intro hx
    have hi := congrFun hx i
    simp [Matrix.mulVec, dotProduct, hz] at hi
    exact hb hi.symm
  · intro hx
    exact False.elim hx

theorem invertibleLeftSolutions (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (T : Matrix.GeneralLinearGroup (Fin m) K) :
    fieldSystemSolutions ((T : Matrix (Fin m) (Fin m) K) * A)
      ((T : Matrix (Fin m) (Fin m) K).mulVec b) = fieldSystemSolutions A b := by
  ext x
  change (T.val * A).mulVec x = T.val.mulVec b ↔ A.mulVec x = b
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have hh := congrArg (fun v => (↑T⁻¹ : Matrix (Fin m) (Fin m) K).mulVec v) h
    simpa [Matrix.mulVec_mulVec] using hh
  · intro h
    rw [h]

def scaleElementary (i : Fin m) (c : Kˣ) : Matrix.GeneralLinearGroup (Fin m) K :=
  Matrix.GeneralLinearGroup.rowScale i c

def swapElementary (i j : Fin m) : Matrix.GeneralLinearGroup (Fin m) K :=
  Matrix.GeneralLinearGroup.swap K i j

def addElementary (source target : Fin m) (h : target ≠ source) (c : K) :
    Matrix.GeneralLinearGroup (Fin m) K :=
  Matrix.GeneralLinearGroup.transvection target source h c

theorem scaleElementaryInverse (i : Fin m) (c : K) (hc : c ≠ 0) :
    Matrix.rowScale i c * Matrix.rowScale i c⁻¹ = (1 : Matrix (Fin m) (Fin m) K) ∧
    Matrix.rowScale i c⁻¹ * Matrix.rowScale i c = 1 := by
  simp [hc]

theorem swapElementaryInverse (i j : Fin m) :
    Matrix.swap K i j * Matrix.swap K i j = (1 : Matrix (Fin m) (Fin m) K) :=
  Matrix.swap_mul_self i j

theorem addElementaryInverse (source target : Fin m) (h : target ≠ source) (c : K) :
    Matrix.transvection target source c * Matrix.transvection target source (-c) =
      (1 : Matrix (Fin m) (Fin m) K) := by
  simpa using Matrix.transvection_mul_transvection_same target source h c (-c)

theorem scaleElementaryAction (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (c : K) :
    Matrix.rowScale i c * A = A.updateRow i (c • A.row i) :=
  Matrix.rowScale_mul i c A

theorem swapElementaryAction (A : Matrix (Fin m) (Fin n) K) (i j : Fin m) :
    ∀ k, (Matrix.swap K i j * A) i k = A j k :=
  fun k => Matrix.swap_mul_apply_left i j k A

theorem addElementaryAction (A : Matrix (Fin m) (Fin n) K) (source target : Fin m) (c : K) :
    ∀ k, (Matrix.transvection target source c * A) target k = A target k + c * A source k :=
  fun k => Matrix.transvection_mul_apply_same target source k c A

theorem elementaryScaleSolutions (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (i : Fin m) (c : Kˣ) :
    fieldSystemSolutions ((scaleElementary i c).val * A)
      ((scaleElementary i c : Matrix (Fin m) (Fin m) K).mulVec b) = fieldSystemSolutions A b :=
  invertibleLeftSolutions A b (scaleElementary i c)

theorem elementarySwapSolutions (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (i j : Fin m) :
    fieldSystemSolutions ((swapElementary (K := K) i j).val * A)
      ((swapElementary (K := K) i j).val.mulVec b) = fieldSystemSolutions A b :=
  invertibleLeftSolutions A b (swapElementary i j)

theorem elementaryAddSolutions (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (source target : Fin m) (h : target ≠ source) (c : K) :
    fieldSystemSolutions ((addElementary source target h c).val * A)
      ((addElementary source target h c : Matrix (Fin m) (Fin m) K).mulVec b) = fieldSystemSolutions A b :=
  invertibleLeftSolutions A b (addElementary source target h c)

def IsHolsteinElementary (T : Matrix (Fin n) (Fin n) K) : Prop :=
  (∃ i c, c ≠ 0 ∧ T = Matrix.rowScale i c) ∨
  (∃ i j, i ≠ j ∧ T = Matrix.swap K i j) ∨
  (∃ i j c, i ≠ j ∧ T = Matrix.transvection i j c)

theorem diagonalElementaryProduct (d : Fin n → K) (hd : ∀ i, d i ≠ 0) :
    ∃ L : List (Matrix (Fin n) (Fin n) K), (∀ T ∈ L, IsHolsteinElementary T) ∧
      L.prod = Matrix.diagonal d := by
  classical
  refine ⟨List.ofFn (fun i : Fin n => Matrix.rowScale i (d i)), ?_, ?_⟩
  · intro T hT
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact Or.inl ⟨i, d i, hd i, rfl⟩
  · have h := map_list_prod (Matrix.diagonalRingHom (Fin n) K)
      (List.ofFn fun i : Fin n => Pi.mulSingle i (d i))
    simpa [List.map_ofFn, Matrix.rowScale, Function.comp_def, Matrix.diagonalRingHom_apply, List.prod_ofFn,
      Finset.univ_prod_mulSingle] using h.symm

theorem invertibleElementaryProduct (A : Matrix.GeneralLinearGroup (Fin n) K) :
    ∃ L : List (Matrix (Fin n) (Fin n) K), (∀ T ∈ L, IsHolsteinElementary T) ∧
      L.prod = (A : Matrix (Fin n) (Fin n) K) := by
  classical
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∃ L : List (Matrix (Fin n) (Fin n) K),
      (∀ T ∈ L, IsHolsteinElementary T) ∧ L.prod = M) (A : Matrix (Fin n) (Fin n) K)
  · exact (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  · intro d hd
    apply diagonalElementaryProduct d
    intro i
    exact (Finset.prod_ne_zero_iff.mp (by simpa only [Matrix.det_diagonal] using hd)) i
      (Finset.mem_univ i)
  · intro t
    refine ⟨[t.toMatrix], ?_, by simp⟩
    intro T hT
    have hT' : T = t.toMatrix := by simpa using hT
    subst T
    unfold IsHolsteinElementary
    exact Or.inr (Or.inr ⟨t.i,t.j,t.c,t.hij,rfl⟩)
  · intro B C _ _ hB hC
    obtain ⟨L,hL,rfl⟩ := hB
    obtain ⟨L',hL',rfl⟩ := hC
    exact ⟨L++L', by simpa only [List.mem_append, or_imp] using fun T => ⟨hL T,hL' T⟩,
      List.prod_append⟩

theorem leftInverseIsRightInverse (A B : Matrix (Fin n) (Fin n) K) (h : B*A=1) : A*B=1 :=
  mul_eq_one_comm.mp h

theorem rightInverseIsLeftInverse (A B : Matrix (Fin n) (Fin n) K) (h : A*B=1) : B*A=1 :=
  mul_eq_one_comm.mp h

theorem reductionCertificateInverse (A P : Matrix (Fin n) (Fin n) K) (h : P*A=1) :
    P*A=1 ∧ A*P=1 := ⟨h, leftInverseIsRightInverse A P h⟩

theorem matrixInverseFromReduction (A P : Matrix (Fin n) (Fin n) K) (h : P*A=1) :
    hasTwoSidedMatrixInverse A := ⟨P, (reductionCertificateInverse A P h).2, h⟩

def originalInversionMatrix : Matrix (Fin 3) (Fin 3) ℚ := !![1,1,1;1,2,4;1,4,9]
def originalInversionResult : Matrix (Fin 3) (Fin 3) ℚ := !![-2,5,-2;5,-8,3;-2,3,-1]

theorem originalInversionProducts : originalInversionMatrix * originalInversionResult = 1 ∧
    originalInversionResult * originalInversionMatrix = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [originalInversionMatrix, originalInversionResult, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rectangularOneSidedCounterexample :
    (!![1,0] : Matrix (Fin 1) (Fin 2) ℚ) * (!![1;0] : Matrix (Fin 2) (Fin 1) ℚ) = 1 ∧
    (!![1;0] : Matrix (Fin 2) (Fin 1) ℚ) * (!![1,0] : Matrix (Fin 1) (Fin 2) ℚ) ≠ 1 := by
  constructor
  · ext i j
    fin_cases i; fin_cases j
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  · intro h
    have hh := congrArg (fun M => M 1 1) h
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at hh

/-- Exact scalar occurring in the third original complex elimination step.
The complete displayed complex matrix sequence is additionally checked by software;
this theorem makes only this explicit scalar claim. -/
theorem complexPivotNormalization :
    (1 + Complex.I) * ((1 - Complex.I) / 2) = (1 : ℂ) := by
  ring_nf
  simp [Complex.I_sq] <;> norm_num <;> ring

theorem complexLastPivot :
    Complex.I - 1 + (1 - Complex.I) * (1 - Complex.I) = -1 - Complex.I := by
  ring_nf
  simp [Complex.I_sq] <;> norm_num <;> ring

end ILab.LinearAlgebra
