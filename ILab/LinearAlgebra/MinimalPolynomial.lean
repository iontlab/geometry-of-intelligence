import ILab.LinearAlgebra.Triangularizability
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic

/-! Holstein §9.6. General Cayley–Hamilton is Mathlib's proof, not a formalization
of the source's subfield-of-C triangular induction. Positive-degree claims
require a nontrivial carrier. Matrix 0×0 has minimal polynomial 1.
No verification of JavaScript algorithms is asserted. -/
noncomputable section
namespace ILab.LinearAlgebra
open Polynomial Module
set_option maxHeartbeats 700000
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem matrixCayleyHamilton {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : aeval A A.charpoly = 0 := Matrix.aeval_self_charpoly A

theorem endomorphismCayleyHamilton [FiniteDimensional K V] (f : Module.End K V) :
    aeval f f.charpoly = 0 := LinearMap.aeval_self_charpoly f

theorem matrixAnnihilatorExists {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : ∃ p : K[X], p.Monic ∧ aeval A p = 0 :=
  ⟨A.charpoly, Matrix.charpoly_monic A, matrixCayleyHamilton A⟩

theorem minimalPolynomialMonic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : (minpoly K A).Monic := minpoly.monic (Matrix.isIntegral A)

theorem minimalPolynomialAnnihilates {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : aeval A (minpoly K A) = 0 := minpoly.aeval K A

theorem minimalPolynomialDividesIff {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (q : K[X]) : minpoly K A ∣ q ↔ aeval A q = 0 := minpoly.dvd_iff

theorem minimalPolynomialDividesCharpoly {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : minpoly K A ∣ A.charpoly := Matrix.minpoly_dvd_charpoly A

theorem minimalPolynomialDegreeBound {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : (minpoly K A).natDegree ≤ A.charpoly.natDegree :=
  Polynomial.natDegree_le_of_dvd (minimalPolynomialDividesCharpoly A)
    (Matrix.charpoly_monic A).ne_zero

theorem minimalPolynomialPositiveDegree {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n K) : 0 < (minpoly K A).natDegree :=
  minpoly.natDegree_pos (Matrix.isIntegral A)

theorem minimalPolynomialMinimalDegree {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (q : K[X]) (hne : q ≠ 0) (h : aeval A q = 0) :
    (minpoly K A).degree ≤ q.degree := minpoly.degree_le_of_ne_zero K A hne h

theorem minimalPolynomialUnique {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (p : K[X]) (hm : p.Monic) (ha : aeval A p = 0)
    (hl : ∀ q : K[X], q.Monic → aeval A q = 0 → p.degree ≤ q.degree) :
    p = minpoly K A := minpoly.unique K A hm ha hl

theorem minimalPolynomialRemainderEvaluation {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (q : K[X]) : aeval A (q %ₘ minpoly K A) = aeval A q :=
  minpoly.aeval_modByMonic_minpoly q A

theorem minimalPolynomialAnnihilatorRemainder {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (q : K[X]) : aeval A q = 0 ↔ q %ₘ minpoly K A = 0 := by
  rw [← minimalPolynomialDividesIff, ← Polynomial.modByMonic_eq_zero_iff_dvd (minimalPolynomialMonic A)]

theorem minimalPolynomialAlgebraEquivalence {B C : Type*} [Ring B] [Ring C]
    [Algebra K B] [Algebra K C] (e : B ≃ₐ[K] C) (x : B) :
    minpoly K (e x) = minpoly K x := minpoly.algEquiv_eq e x

theorem polynomialEvaluationAlgebraEquivalence {B C : Type*} [Ring B] [Ring C]
    [Algebra K B] [Algebra K C] (e : B ≃ₐ[K] C) (x : B) (q : K[X]) :
    aeval (e x) q = e (aeval x q) := Polynomial.aeval_algHom_apply e x q

theorem endomorphismMinimalPolynomialBasis {n : Type*} [Fintype n] [DecidableEq n]
    (b : Basis n K V) (f : Module.End K V) :
    minpoly K (LinearMap.toMatrix b b f) = minpoly K f := LinearMap.minpoly_toMatrix b f

theorem endomorphismMinimalPolynomialConjugate (e : V ≃ₗ[K] V) (f : Module.End K V) :
    minpoly K ((e.conjAlgEquiv K) f) = minpoly K f :=
  minimalPolynomialAlgebraEquivalence (e.conjAlgEquiv K) f

theorem endomorphismMinimalPolynomialDivides [FiniteDimensional K V]
    (f : Module.End K V) (q : K[X]) : minpoly K f ∣ q ↔ aeval f q = 0 := minpoly.dvd_iff

theorem eigenvectorPolynomialEvaluation (f : Module.End K V) (q : K[X]) (a : K) (v : V)
    (hv : f.HasEigenvector a v) : (aeval f q) v = q.eval a • v :=
  Module.End.aeval_apply_of_hasEigenvector hv

theorem eigenvalueMinimalPolynomialRoot [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    f.HasEigenvalue a ↔ (minpoly K f).IsRoot a := Module.End.hasEigenvalue_iff_isRoot

theorem endomorphismMinimalCharpolySameRoots [FiniteDimensional K V]
    (f : Module.End K V) (a : K) : (minpoly K f).IsRoot a ↔ f.charpoly.IsRoot a :=
  (eigenvalueMinimalPolynomialRoot f a).symm.trans
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f a)

theorem matrixMinimalCharpolySameRoots {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (a : K) : (minpoly K A).IsRoot a ↔ A.charpoly.IsRoot a := by
  simpa only [Matrix.minpoly_toLin', Matrix.charpoly_toLin'] using
    endomorphismMinimalCharpolySameRoots A.toLin' a

theorem minimalPolynomialRootMultiplicity {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (a : K) :
    (minpoly K A).rootMultiplicity a ≤ A.charpoly.rootMultiplicity a :=
  Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd (Matrix.charpoly_monic A).ne_zero
    (minimalPolynomialDividesCharpoly A) a

theorem minimalPolynomialScalar {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (a : K) : minpoly K (algebraMap K (Matrix n n K) a) = X - C a := minpoly.eq_X_sub_C (B := Matrix n n K) a

theorem minimalPolynomialZero {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    minpoly K (0 : Matrix n n K) = X := minpoly.zero K (Matrix n n K)

theorem minimalPolynomialIdentity {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    minpoly K (1 : Matrix n n K) = X - 1 := minpoly.one K (Matrix n n K)

theorem minimalPolynomialNullSpace (A : Matrix (Fin 0) (Fin 0) K) : minpoly K A = 1 :=
  minpoly.subsingleton K A

/-- The first original non-scalar example. -/
def holsteinNilpotent : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;0,0]

theorem holsteinNilpotentSquare : holsteinNilpotent ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [holsteinNilpotent, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem holsteinNilpotentMinimalPolynomial : minpoly ℚ holsteinNilpotent = X^2 := by
  refine minpoly.eq_of_linearIndependent ℚ holsteinNilpotent (monic_X_pow 2) ?_ 2 (by simp) ?_
  · simpa using holsteinNilpotentSquare
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 1) hc
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 0) hc
    simp [Fin.sum_univ_two, holsteinNilpotent] at h01 h00
    fin_cases i <;> simp_all

/-- The source's fourth original matrix, over Q. -/
def holsteinMinimalExample : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0,-7,0,0;0,0,0,0;0,0,7,0;0,0,0,7]

theorem holsteinMinimalExampleSquare : holsteinMinimalExample^2 =
    !![0,0,0,0;0,0,0,0;0,0,49,0;0,0,0,49] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holsteinMinimalExample, pow_two, Matrix.mul_apply, Fin.sum_univ_four]

theorem holsteinMinimalExampleAnnihilator :
    aeval holsteinMinimalExample ((X^2 * (X - C 7)) : ℚ[X]) = 0 := by
  rw [map_mul, map_pow, aeval_X, holsteinMinimalExampleSquare, map_sub, aeval_C]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holsteinMinimalExample, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.algebraMap_matrix_apply, Matrix.sub_apply]

theorem holsteinMinimalExampleMinpoly :
    minpoly ℚ holsteinMinimalExample = X^2 * (X - C 7) := by
  refine minpoly.eq_of_linearIndependent ℚ holsteinMinimalExample
    ((monic_X_pow 2).mul (monic_X_sub_C 7)) holsteinMinimalExampleAnnihilator 3 (by compute_degree!) ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h00 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℚ => A 0 0) hc
  have h01 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℚ => A 0 1) hc
  have h22 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℚ => A 2 2) hc
  simp [Fin.sum_univ_three, holsteinMinimalExampleSquare] at h00 h01 h22
  norm_num [holsteinMinimalExample] at h00 h01 h22
  fin_cases i <;> dsimp <;> linarith

local instance characteristicSevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

def holsteinCharacteristicSeven : Matrix (Fin 4) (Fin 4) (ZMod 7) :=
  !![0,-7,0,0;0,0,0,0;0,0,7,0;0,0,0,7]

theorem holsteinCharacteristicSevenZero : holsteinCharacteristicSeven = 0 := by
  decide

theorem holsteinCharacteristicSevenMinpoly : minpoly (ZMod 7) holsteinCharacteristicSeven = X := by
  rw [holsteinCharacteristicSevenZero]
  exact minimalPolynomialZero (K := ZMod 7) (n := Fin 4)

/-- Direct counterexample to replacing the formal determinant argument by trace. -/
theorem naiveTraceCounterexample :
    (2:ℚ) • holsteinNilpotent - (Matrix.trace holsteinNilpotent) • (1 : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 1) h
  norm_num [holsteinNilpotent, Matrix.sub_apply, Matrix.smul_apply, Matrix.trace, Fin.sum_univ_two] at hh

/-- The actual column step in the corrected triangular induction. -/
theorem triangularAnnihilatorNextColumn {n : ℕ} (A Q : Matrix (Fin n) (Fin n) K)
    (i : Fin n) (hA : A.IsUpperTriangular)
    (hQ : ∀ j : Fin n, j < i → ∀ r, Q r j = 0) :
    ∀ r, (Q * (A - A i i • (1 : Matrix (Fin n) (Fin n) K))) r i = 0 := by
  classical
  intro r
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j < i
  · simp [hQ j hj r]
  · by_cases he : j = i
    · subst j
      simp
    · have hlt : i < j := by omega
      have hz : A j i = 0 := hA hlt
      simp [Matrix.sub_apply, Matrix.smul_apply, hz, he]

theorem holsteinNilpotentCharpoly : holsteinNilpotent.charpoly = (X^2 : ℚ[X]) := by
  norm_num [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_two, holsteinNilpotent]
  ring

theorem holsteinMinimalExampleCharpoly :
    holsteinMinimalExample.charpoly = (X^2 * (X-C 7)^2 : ℚ[X]) := by
  have h : holsteinMinimalExample.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [holsteinMinimalExample] at *
  rw [upperCharacteristicPolynomial holsteinMinimalExample h]
  simp [Fin.prod_univ_succ, holsteinMinimalExample]
  ring
end ILab.LinearAlgebra


