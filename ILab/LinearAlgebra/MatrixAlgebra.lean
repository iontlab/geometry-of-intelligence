import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
Holstein, printed pp. 75–77. Fin n is indexed from zero in Lean;
this changes index notation, not matrix entries or multiplication order.
All dimensions may differ, including zero dimensions.
-/

namespace ILab.LinearAlgebra

open Matrix
variable {K : Type*} [Field K] {m n p q : ℕ}

/-- Definition 5.1.2, matrix in the standard bases. -/
def representingMatrix (f : (Fin n → K) →ₗ[K] (Fin m → K)) : Matrix (Fin m) (Fin n) K :=
  LinearMap.toMatrix' f

theorem representingMatrixEntry (f : (Fin n → K) →ₗ[K] (Fin m → K))
    (i : Fin m) (j : Fin n) :
    representingMatrix f i j = f (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply f i j

/-- Definition 5.1.4, the linear map represented by a matrix. -/
def linearOfMatrix (A : Matrix (Fin m) (Fin n) K) : (Fin n → K) →ₗ[K] (Fin m → K) :=
  Matrix.toLin' A

theorem matrixVectorEntry (A : Matrix (Fin m) (Fin n) K) (v : Fin n → K) (i : Fin m) :
    (A *ᵥ v) i = ∑ j, A i j * v j := rfl

theorem linearOfMatrixAction (A : Matrix (Fin m) (Fin n) K) (v : Fin n → K) :
    linearOfMatrix A v = A *ᵥ v := rfl

theorem representingMatrixAction (f : (Fin n → K) →ₗ[K] (Fin m → K)) (v : Fin n → K) :
    representingMatrix f *ᵥ v = f v :=
  LinearMap.toMatrix'_mulVec f v

theorem representingMatrixInverse (A : Matrix (Fin m) (Fin n) K) :
    representingMatrix (linearOfMatrix A) = A :=
  LinearMap.toMatrix'_toLin' A

theorem linearOfMatrixInverse (f : (Fin n → K) →ₗ[K] (Fin m → K)) :
    linearOfMatrix (representingMatrix f) = f :=
  Matrix.toLin'_toMatrix' f

/-- Definition 5.1.7, entry formula for rectangular multiplication. -/
theorem matrixProductEntry (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (i : Fin m) (j : Fin p) :
    (A * B) i j = ∑ k, A i k * B k j := rfl

/-- Betrachtung 5.1.6: the right-hand factor acts first. -/
theorem representingMatrixComposition
    (g : (Fin n → K) →ₗ[K] (Fin m → K)) (f : (Fin p → K) →ₗ[K] (Fin n → K)) :
    representingMatrix (g.comp f) = representingMatrix g * representingMatrix f :=
  LinearMap.toMatrix'_comp g f

theorem linearOfMatrixProduct (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K) :
    linearOfMatrix (A * B) = (linearOfMatrix A).comp (linearOfMatrix B) :=
  Matrix.toLin'_mul A B

theorem matrixProductAction (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (v : Fin p → K) :
    (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) := by
  exact (Matrix.mulVec_mulVec v A B).symm

/-- Lemma 5.1.10: correctly typed rectangular associativity. -/
theorem matrixAssociativity (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin p) K) (C : Matrix (Fin p) (Fin q) K) :
    (A * B) * C = A * (B * C) :=
  Matrix.mul_assoc A B C

/-- Holstein's second proof: transport associativity of composition through matrices. -/
theorem matrixAssociativityByComposition (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin p) K) (C : Matrix (Fin p) (Fin q) K) :
    (A * B) * C = A * (B * C) := by
  apply (Matrix.toLin').injective
  change linearOfMatrix ((A * B) * C) = linearOfMatrix (A * (B * C))
  simp only [linearOfMatrixProduct, LinearMap.comp_assoc]

/-- Definition 5.1.11. -/
def identityMatrix (n : ℕ) : Matrix (Fin n) (Fin n) K := 1

theorem identityEntry (i j : Fin n) :
    (identityMatrix n : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 :=
  Matrix.one_apply

theorem identityRepresentsIdentity :
    representingMatrix (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)) = identityMatrix n :=
  LinearMap.toMatrix'_id

/-- Lemma 5.1.12, left identity has the row dimension m. -/
theorem matrixLeftIdentity (A : Matrix (Fin m) (Fin n) K) :
    identityMatrix m * A = A :=
  Matrix.one_mul A

/-- Lemma 5.1.12, right identity has the column dimension n. -/
theorem matrixRightIdentity (A : Matrix (Fin m) (Fin n) K) :
    A * identityMatrix n = A :=
  Matrix.mul_one A

theorem identityAction (v : Fin n → K) : (identityMatrix n : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
  Matrix.one_mulVec v

/-- Holstein's actual matrices in Bemerkung 5.1.13, over an arbitrary field. -/
def counterA (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
def counterB (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]

theorem counterProductAB :
    counterA K * counterB K = !![(1 : K), 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [counterA, counterB, Matrix.mul_apply, Fin.sum_univ_two]

theorem counterProductBA :
    counterB K * counterA K = !![(0 : K), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [counterA, counterB, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrixNoncommutativity : counterA K * counterB K ≠ counterB K * counterA K := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
  rw [counterProductAB, counterProductBA] at h00
  simp at h00

end ILab.LinearAlgebra
