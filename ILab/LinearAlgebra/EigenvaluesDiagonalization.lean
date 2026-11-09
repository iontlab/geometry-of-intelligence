import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-! Holstein §§9.1–9.2. Formal polynomials are related to the original
polynomial functions by explicit evaluation. Ground fields are never extended silently. -/
namespace ILab.LinearAlgebra
open Matrix Module Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def HolsteinEigenvector (f : Module.End K V) (a : K) (v : V) : Prop := v≠0 ∧ f v=a • v
theorem holsteinEigenvectorIff (f : Module.End K V) (a : K) (v : V) :
    HolsteinEigenvector f a v ↔ f.HasEigenvector a v := by
  simp [HolsteinEigenvector,Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff,and_comm]
theorem eigenvectorNonzero (f : Module.End K V) (a : K) : ¬ HolsteinEigenvector f a 0 := by
  simp [HolsteinEigenvector]
theorem eigenSpaceContainsZero (f : Module.End K V) (a : K) : (0:V) ∈ f.eigenspace a :=
  (f.eigenspace a).zero_mem
theorem eigenSpaceAsKernel (f : Module.End K V) (a : K) :
    f.eigenspace a = LinearMap.ker (f-a • 1) := Module.End.eigenspace_def
theorem eigenSpaceZero (f : Module.End K V) : f.eigenspace 0=LinearMap.ker f :=
  Module.End.eigenspace_zero f
theorem eigenSpaceClosure (f : Module.End K V) (a b : K) (u v : V)
    (hu : u ∈ f.eigenspace a) (hv : v ∈ f.eigenspace a) :
    u+v ∈ f.eigenspace a ∧ b • u ∈ f.eigenspace a :=
  ⟨(f.eigenspace a).add_mem hu hv,(f.eigenspace a).smul_mem b hu⟩
noncomputable def geometricMultiplicity (f : Module.End K V) (a : K) : ℕ :=
  Module.finrank K (f.eigenspace a)
theorem geometricMultiplicityPositive [FiniteDimensional K V] (f : Module.End K V)
    (a : K) (ha : f.HasEigenvalue a) : 0<geometricMultiplicity f a := by
  have h := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 ha)
  simpa [geometricMultiplicity] using h
theorem eigenvectorsDistinctIndependent {ι : Type*} (f : Module.End K V)
    (a : ι→K) (ha : Function.Injective a) (v : ι→V)
    (hv : ∀ i,f.HasEigenvector (a i) (v i)) : LinearIndependent K v :=
  f.eigenvectors_linearIndependent' a ha v hv
theorem eigenvalueFamilyBound [FiniteDimensional K V] {m : ℕ} (f : Module.End K V)
    (a : Fin m→K) (ha : Function.Injective a) (v : Fin m→V)
    (hv : ∀ i,f.HasEigenvector (a i) (v i)) : m ≤ Module.finrank K V := by
  simpa using (eigenvectorsDistinctIndependent f a ha v hv).fintype_card_le_finrank
def IsEigenbasis {ι : Type*} (f : Module.End K V) (b : Basis ι K V) : Prop :=
  ∀ i,∃ a,f.HasEigenvector a (b i)
noncomputable def eigenbasisOfFullDistinct [FiniteDimensional K V] {n : ℕ}
    (f : Module.End K V) (a : Fin n→K) (ha : Function.Injective a)
    (v : Fin n→V) (hv : ∀ i,f.HasEigenvector (a i) (v i))
    (hdim : n=Module.finrank K V) : Basis (Fin n) K V := by
  let hi := eigenvectorsDistinctIndependent f a ha v hv
  exact Basis.mk hi (hi.span_eq_top_of_card_eq_finrank' (by simpa using hdim)).ge
theorem eigenbasisOfFullDistinctIsEigenbasis [FiniteDimensional K V] {n : ℕ}
    (f : Module.End K V) (a : Fin n→K) (ha : Function.Injective a)
    (v : Fin n→V) (hv : ∀ i,f.HasEigenvector (a i) (v i)) (hdim : n=Module.finrank K V) :
    IsEigenbasis f (eigenbasisOfFullDistinct f a ha v hv hdim) := by
  intro i; exact ⟨a i,by simpa [eigenbasisOfFullDistinct] using hv i⟩
noncomputable def characteristicFunction [FiniteDimensional K V] (f : Module.End K V) (a : K) : K :=
  (a • 1-f).det
theorem characteristicFunctionEval [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    characteristicFunction f a=f.charpoly.eval a := (LinearMap.eval_charpoly f a).symm
theorem eigenvalueIffCharacteristicZero [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    f.HasEigenvalue a ↔ characteristicFunction f a=0 := by
  rw [characteristicFunctionEval];exact f.hasEigenvalue_iff_isRoot_charpoly a
theorem characteristicInBasis [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.End K V) (b : Basis ι K V) : (LinearMap.toMatrix b b f).charpoly=f.charpoly :=
  LinearMap.charpoly_toMatrix f b
theorem characteristicMatrixEval {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (a : K) :
    A.charpoly.eval a=(Matrix.scalar (Fin n) a-A).det := Matrix.eval_charpoly A a
theorem characteristicSimilarity {n : ℕ} (P : (Matrix (Fin n) (Fin n) K)ˣ)
    (A : Matrix (Fin n) (Fin n) K) : ((P:Matrix (Fin n) (Fin n) K)*A*((P:Matrix (Fin n) (Fin n) K)⁻¹)).charpoly=A.charpoly :=
  Matrix.charpoly_units_conj P A
theorem characteristicMonic {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : A.charpoly.Monic := A.charpoly_monic
theorem characteristicDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : A.charpoly.natDegree=n := by
  simpa using A.charpoly_natDegree_eq_dim
theorem characteristicTrace {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) K) :
    A.charpoly.coeff (n-1)= -A.trace := by
  simpa using congrArg Neg.neg (A.trace_eq_neg_charpoly_coeff).symm
theorem characteristicConstant {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    A.charpoly.coeff 0= (-1:K)^n*A.det := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpoly]
  simp [Matrix.det_neg]
def fibonacciMatrix : Matrix (Fin 2) (Fin 2) ℕ := !![1,1;1,0]
theorem fibonacciRecursion (n : ℕ) : Nat.fib (n+2)=Nat.fib n+Nat.fib (n+1) := Nat.fib_add_two
theorem fibonacciMatrixAction (n : ℕ) :
    (fibonacciMatrix^n).mulVec ![1,0] = ![Nat.fib (n+1),Nat.fib n] := by
  induction n with
  | zero => simp [Nat.fib_zero,Nat.fib_one]
  | succ n ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih]
    ext i;fin_cases i <;> simp [fibonacciMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Nat.fib_add_two,Nat.add_assoc]
    all_goals omega
theorem fibonacciBinet (n : ℕ) : (Nat.fib n : ℝ)=
    (((1+Real.sqrt 5)/2)^n-((1-Real.sqrt 5)/2)^n)/Real.sqrt 5 := Real.coe_fib_eq n
def originalKernelStage : Matrix (Fin 4) (Fin 4) ℚ := !![2,1,3,4;0,2,1,0;0,0,0,1;0,0,0,0]
theorem originalKernelCorrected : originalKernelStage.mulVec ![5/2,1,-2,0]=0 := by
  norm_num [originalKernelStage, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
theorem originalKernelPrintedFails : originalKernelStage.mulVec ![-5/2,1,-2,0]≠0 := by
  norm_num [originalKernelStage, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
theorem printedCubicFails : ((-1:ℚ)^3+(-1)^2-11*(-1)-12)=-1 := by norm_num
theorem printedCubicFactorCorrection (x : ℚ) : (x+1)*(x^2+x-12)=x^3+2*x^2-11*x-12 := by ring
def jordanExample (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![1,1;0,1]
theorem jordanEigenvectors (a : K) (v : Fin 2→K) :
    (jordanExample K).mulVec v=a • v ∧ v≠0 ↔ a=1 ∧ v 1=0 ∧ v 0≠0 := by
  have hcoord : (jordanExample K).mulVec v=a • v ↔
      v 0+v 1=a*v 0 ∧ v 1=a*v 1 := by
    simp [jordanExample, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      funext_iff, Fin.forall_fin_two]
  rw [hcoord]
  constructor
  · rintro ⟨⟨h0,h1⟩,hn⟩
    have hnon : v 0≠0 ∨ v 1≠0 := by
      by_contra h
      push_neg at h
      apply hn
      ext i; fin_cases i <;> simp [h.1,h.2]
    by_cases hz : v 1=0
    · have hv : v 0≠0 := hnon.resolve_right (not_not_intro hz)
      have ha : a=1 := (mul_right_cancel₀ hv) (by simpa [hz] using h0.symm)
      exact ⟨ha,hz,hv⟩
    · have ha : a=1 := (mul_right_cancel₀ hz) (by simpa using h1.symm)
      have hv : v 1=0 := by simpa [ha] using h0
      exact False.elim (hz hv)
  · rintro ⟨rfl,h1,h0⟩
    refine ⟨by simp [h1],?_⟩
    intro h; exact h0 (congrFun h 0)

theorem jordanNoEigenbasis (b : Basis (Fin 2) K (Fin 2→K)) :
    ¬ IsEigenbasis ((jordanExample K).mulVecLin) b := by
  intro hb
  have hz : ∀ i, b i 1=0 := by
    intro i
    obtain ⟨a,ha⟩ := hb i
    have hv := (holsteinEigenvectorIff ((jordanExample K).mulVecLin) a (b i)).mpr ha
    exact ((jordanEigenvectors a (b i)).mp ⟨hv.2,hv.1⟩).2.1
  have h := congrFun (b.sum_repr (![0,1] : Fin 2→K)) 1
  simpa [Fin.sum_univ_two, hz] using h

def fibonacciRealMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,0]

theorem fibonacciEigenpair (a : ℝ) (ha : a^2=a+1) :
    HolsteinEigenvector fibonacciRealMatrix.mulVecLin a ![a,1] := by
  constructor
  · intro h; have := congrFun h 1; simpa using this
  · ext i; fin_cases i <;> simp [fibonacciRealMatrix,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ, pow_two] at * <;> nlinarith

theorem fibonacciGoldenEigenpair :
    HolsteinEigenvector fibonacciRealMatrix.mulVecLin Real.goldenRatio ![Real.goldenRatio,1] := by
  apply fibonacciEigenpair
  have h := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  dsimp [Real.goldenRatio]
  nlinarith

theorem fibonacciConjugateEigenpair :
    HolsteinEigenvector fibonacciRealMatrix.mulVecLin Real.goldenConj ![Real.goldenConj,1] := by
  apply fibonacciEigenpair
  have h := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  dsimp [Real.goldenConj]
  nlinarith

theorem fibonacciEigenbasisDet :
    (!![Real.goldenRatio,Real.goldenConj;1,1] : Matrix (Fin 2) (Fin 2) ℝ).det=Real.sqrt 5 := by
  simp [Matrix.det_fin_two,Real.goldenRatio,Real.goldenConj]
end ILab.LinearAlgebra
