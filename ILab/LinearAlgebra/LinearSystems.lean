import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Holstein 1.3, printed pp. 10–14. Real systems with finite column index.
The browser algorithm is separate from these exact mathematical theorems. -/
namespace ILab.LinearAlgebra

variable {m n : Type*} [Fintype n]

/-- Definition 1.3.1: all simultaneous solutions, in Mathlib's matrix notation. -/
def linearSystemSolutions (A : Matrix m n ℝ) (b : m → ℝ) : Set (n → ℝ) :=
  {x | A.mulVec x = b}

theorem homogeneousZeroSolution (A : Matrix m n ℝ) :
    (0 : n → ℝ) ∈ linearSystemSolutions A 0 := by
  simp [linearSystemSolutions]

theorem inconsistentZeroRow (A : Matrix m n ℝ) (b : m → ℝ) (i : m)
    (hz : ∀ j, A i j = 0) (hb : b i ≠ 0) : linearSystemSolutions A b = ∅ := by
  ext x
  constructor
  · intro hx
    have h := congrFun hx i
    simp [Matrix.mulVec, dotProduct, hz] at h
    exact hb h.symm
  · intro hx
    exact False.elim hx

variable [DecidableEq m]

def swapEquationRows (A : Matrix m n ℝ) (i k : m) : Matrix m n ℝ :=
  fun r j => A (Equiv.swap i k r) j

def swapEquationRhs (b : m → ℝ) (i k : m) : m → ℝ :=
  fun r => b (Equiv.swap i k r)

theorem rowSwapSolutions (A : Matrix m n ℝ) (b : m → ℝ) (i k : m) :
    linearSystemSolutions (swapEquationRows A i k) (swapEquationRhs b i k) =
      linearSystemSolutions A b := by
  ext x
  constructor
  · intro h
    funext r
    have hr := congrFun h (Equiv.swap i k r)
    simpa [swapEquationRows, swapEquationRhs, Matrix.mulVec, dotProduct] using hr
  · intro h
    funext r
    simpa [swapEquationRows, swapEquationRhs, Matrix.mulVec, dotProduct] using
      congrFun h (Equiv.swap i k r)

def scaleEquationRow (A : Matrix m n ℝ) (i : m) (c : ℝ) : Matrix m n ℝ :=
  fun r j => if r = i then c * A r j else A r j

def scaleEquationRhs (b : m → ℝ) (i : m) (c : ℝ) : m → ℝ :=
  fun r => if r = i then c * b r else b r

theorem scaledRowEvaluation (A : Matrix m n ℝ) (i : m) (c : ℝ) (x : n → ℝ) (r : m) :
    (scaleEquationRow A i c).mulVec x r =
      if r = i then c * A.mulVec x r else A.mulVec x r := by
  by_cases h : r = i
  · simp [scaleEquationRow, Matrix.mulVec, dotProduct, h, Finset.mul_sum, mul_assoc]
  · simp [scaleEquationRow, Matrix.mulVec, dotProduct, h]

theorem rowScaleSolutions (A : Matrix m n ℝ) (b : m → ℝ) (i : m) (c : ℝ)
    (hc : c ≠ 0) :
    linearSystemSolutions (scaleEquationRow A i c) (scaleEquationRhs b i c) =
      linearSystemSolutions A b := by
  ext x
  constructor
  · intro h
    funext r
    have hr := congrFun h r
    change (scaleEquationRow A i c).mulVec x r = scaleEquationRhs b i c r at hr
    rw [scaledRowEvaluation] at hr
    by_cases hi : r = i
    · simp only [scaleEquationRhs, ite_eq_left hi] at hr
      exact mul_left_cancel₀ hc hr
    · simpa [scaleEquationRhs, hi] using hr
  · intro h
    funext r
    rw [scaledRowEvaluation]
    simp [scaleEquationRhs, show A.mulVec x = b from h]

def addEquationRow (A : Matrix m n ℝ) (i k : m) (c : ℝ) : Matrix m n ℝ :=
  fun r j => if r = i then A r j + c * A k j else A r j

def addEquationRhs (b : m → ℝ) (i k : m) (c : ℝ) : m → ℝ :=
  fun r => if r = i then b r + c * b k else b r

theorem addedRowEvaluation (A : Matrix m n ℝ) (i k : m) (c : ℝ) (x : n → ℝ) (r : m) :
    (addEquationRow A i k c).mulVec x r =
      if r = i then A.mulVec x r + c * A.mulVec x k else A.mulVec x r := by
  by_cases h : r = i
  · simp [addEquationRow, Matrix.mulVec, dotProduct, h, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  · simp [addEquationRow, Matrix.mulVec, dotProduct, h]

theorem rowAddSolutions (A : Matrix m n ℝ) (b : m → ℝ) (i k : m) (c : ℝ)
    (hik : i ≠ k) :
    linearSystemSolutions (addEquationRow A i k c) (addEquationRhs b i k c) =
      linearSystemSolutions A b := by
  ext x
  constructor
  · intro h
    have hk := congrFun h k
    change (addEquationRow A i k c).mulVec x k = addEquationRhs b i k c k at hk
    rw [addedRowEvaluation] at hk
    simp only [addEquationRhs, ite_eq_right (Ne.symm hik)] at hk
    funext r
    have hr := congrFun h r
    change (addEquationRow A i k c).mulVec x r = addEquationRhs b i k c r at hr
    rw [addedRowEvaluation] at hr
    by_cases hi : r = i
    · simp only [addEquationRhs, ite_eq_left hi] at hr
      rw [hk] at hr
      exact add_right_cancel hr
    · simpa [addEquationRhs, hi] using hr
  · intro h
    funext r
    rw [addedRowEvaluation]
    simp [addEquationRhs, show A.mulVec x = b from h]

/-- A permitted elementary operation includes exactly the necessary side conditions. -/
inductive EquationRowOperation (m : Type*) where
  | swap (i k : m)
  | scale (i : m) (c : ℝ) (nonzero : c ≠ 0)
  | add (i k : m) (c : ℝ) (different : i ≠ k)

def applyEquationRowOperation (op : EquationRowOperation m)
    (s : Matrix m n ℝ × (m → ℝ)) : Matrix m n ℝ × (m → ℝ) :=
  match op with
  | .swap i k => (swapEquationRows s.1 i k, swapEquationRhs s.2 i k)
  | .scale i c _ => (scaleEquationRow s.1 i c, scaleEquationRhs s.2 i c)
  | .add i k c _ => (addEquationRow s.1 i k c, addEquationRhs s.2 i k c)

theorem elementaryOperationSolutions (op : EquationRowOperation m)
    (s : Matrix m n ℝ × (m → ℝ)) :
    linearSystemSolutions (applyEquationRowOperation op s).1
      (applyEquationRowOperation op s).2 = linearSystemSolutions s.1 s.2 := by
  cases op with
  | swap i k => exact rowSwapSolutions s.1 s.2 i k
  | scale i c hc => exact rowScaleSolutions s.1 s.2 i c hc
  | add i k c hik => exact rowAddSolutions s.1 s.2 i k c hik

def applyEquationRowSequence (ops : List (EquationRowOperation m))
    (s : Matrix m n ℝ × (m → ℝ)) : Matrix m n ℝ × (m → ℝ) :=
  ops.foldl (fun state op => applyEquationRowOperation op state) s

/-- Satz 1.3.6, including any finite sequence of allowed operations. -/
theorem rowSequenceSolutions (ops : List (EquationRowOperation m))
    (s : Matrix m n ℝ × (m → ℝ)) :
    linearSystemSolutions (applyEquationRowSequence ops s).1
      (applyEquationRowSequence ops s).2 = linearSystemSolutions s.1 s.2 := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (applyEquationRowOperation op s)).trans (elementaryOperationSolutions op s)

/-- Beispiel 1.3.9: the exact original coefficient matrix and right side. -/
def holstein139Matrix : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,1;5,10,-20;2,8,4]
def holstein139Rhs : Fin 3 → ℝ := ![1,5,14]

theorem holstein139UniqueSolution :
    linearSystemSolutions holstein139Matrix holstein139Rhs = {![5,0,1]} := by
  ext x
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    norm_num [holstein139Matrix, holstein139Rhs, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] at h0 h1 h2
    change x = ![5,0,1]
    funext i
    fin_cases i <;> simp <;> linarith
  · intro h
    change x = ![5,0,1] at h
    subst x
    change holstein139Matrix.mulVec ![5,0,1] = holstein139Rhs
    ext i
    fin_cases i <;> norm_num [holstein139Matrix, holstein139Rhs, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Beispiel 1.3.4: the free coordinate parametrizes the entire solution line. -/
theorem holstein134SolutionLine :
    linearSystemSolutions (!![1,2,4;0,0,1;0,0,0] : Matrix (Fin 3) (Fin 3) ℝ) ![4,5,0] =
      {x | ∃ t : ℝ, x = ![-16-2*t,t,5]} := by
  ext x
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    refine ⟨x 1, ?_⟩
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro ⟨t, rfl⟩
    change ( !![1,2,4;0,0,1;0,0,0] : Matrix (Fin 3) (Fin 3) ℝ).mulVec ![-16-2*t,t,5] = ![4,5,0]
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    all_goals ring

theorem zeroScalingNotEquivalent :
    linearSystemSolutions
        (scaleEquationRow (!![1] : Matrix (Fin 1) (Fin 1) ℝ) 0 0)
        (scaleEquationRhs (![1] : Fin 1 → ℝ) 0 0) ≠
      linearSystemSolutions (!![1] : Matrix (Fin 1) (Fin 1) ℝ) ![1] := by
  intro h
  have hz : (0 : Fin 1 → ℝ) ∈ linearSystemSolutions
      (scaleEquationRow (!![1] : Matrix (Fin 1) (Fin 1) ℝ) 0 0)
      (scaleEquationRhs (![1] : Fin 1 → ℝ) 0 0) := by
    change (scaleEquationRow (!![1] : Matrix (Fin 1) (Fin 1) ℝ) 0 0).mulVec 0 =
      scaleEquationRhs ![1] 0 0
    ext i
    fin_cases i
    norm_num [Matrix.mulVec, scaleEquationRhs]
  rw [h] at hz
  have hh := congrFun hz 0
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hh

end ILab.LinearAlgebra
