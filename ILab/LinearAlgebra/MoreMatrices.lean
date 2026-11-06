import ILab.LinearAlgebra.MatrixAlgebra
import ILab.LinearAlgebra.BasisMaps
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Holstein §5.2, printed78–81. Original plan LA-P017 (not LA-P015).
Matrix indices are (row,column), Fin indices are zero based. The printed swapped
indices and a'_ji=b_ij typo are retained in the source and separately discussed.
All statements below have their correct typed index ranges. Fin0 is allowed.
Finite bases are explicit for the Hom dimension result; no infinite-dimensional
extension of the corollary is claimed. Old MatrixAlgebra declarations unchanged. -/
noncomputable section
namespace ILab.LinearAlgebra
open Matrix Module Function
variable {K : Type*} [Field K] {m n r : ℕ}

theorem matrixAdditionEntry (A B : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    (A + B) i j = A i j + B i j := rfl

theorem matrixScalarEntry (a : K) (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    (a • A) i j = a * A i j := rfl

theorem matrixTransposeEntry (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    Aᵀ j i = A i j := rfl

theorem matrixTransposeTwice (A : Matrix (Fin m) (Fin n) K) : Aᵀᵀ = A :=
  Matrix.transpose_transpose A

def matrixUnitBasis (m n : ℕ) : Basis (Fin m × Fin n) K (Matrix (Fin m) (Fin n) K) :=
  Matrix.stdBasis K (Fin m) (Fin n)

theorem matrixUnitBasisValues (i : Fin m) (j : Fin n) :
    matrixUnitBasis (K := K) m n (i,j) = Matrix.single i j 1 :=
  Matrix.stdBasis_eq_single K i j

theorem matrixUnitExpansion (A : Matrix (Fin m) (Fin n) K) :
    A = ∑ i, ∑ j, Matrix.single i j (A i j) := Matrix.matrix_eq_sum_single A

theorem matrixSpaceDimension (m n : ℕ) : finrank K (Matrix (Fin m) (Fin n) K) = m*n := by
  simp [Module.finrank_matrix, Module.finrank_self]

theorem matrixScalarProduct (a : K) (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin r) K) :
    A * (a • B) = a • (A * B) ∧ (a • A) * B = a • (A * B) :=
  ⟨Matrix.mul_smul A a B, Matrix.smul_mul a A B⟩

theorem matrixProductDistributes (A A' : Matrix (Fin m) (Fin n) K)
    (B B' : Matrix (Fin n) (Fin r) K) :
    A * (B+B') = A*B+A*B' ∧ (A+A')*B = A*B+A'*B := ⟨Matrix.mul_add .., Matrix.add_mul ..⟩

theorem transposeMatrixProduct (A : Matrix (Fin m) (Fin n) K)
    (B : Matrix (Fin n) (Fin r) K) : (A*B)ᵀ = Bᵀ*Aᵀ := Matrix.transpose_mul A B

def hasTwoSidedMatrixInverse (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ B, A*B=1 ∧ B*A=1

theorem matrixInvertibleIffUnit (A : Matrix (Fin n) (Fin n) K) :
    hasTwoSidedMatrixInverse A ↔ IsUnit A := by
  constructor
  · rintro ⟨B,hAB,hBA⟩; exact ⟨⟨A,B,hAB,hBA⟩,rfl⟩
  · rintro ⟨u,rfl⟩; exact ⟨↑u⁻¹,u.val_inv,u.inv_val⟩

theorem twoSidedMatrixInverseUnique (A B C : Matrix (Fin n) (Fin n) K)
    (hBA : B*A=1) (hAC : A*C=1) : B=C := by
  calc B = B*1 := (matrixRightIdentity B).symm
       _ = B*(A*C) := by rw [hAC]
       _ = (B*A)*C := (matrixAssociativity B A C).symm
       _ = C := by rw [hBA, one_mul]

def inverseTwoByTwo (a b c d : K) : Matrix (Fin 2) (Fin 2) K :=
  (a*d-b*c)⁻¹ • !![d,-b;-c,a]

theorem inverseTwoByTwoProducts (a b c d : K) (h : a*d-b*c≠0) :
    !![a,b;c,d]*inverseTwoByTwo a b c d=1 ∧
    inverseTwoByTwo a b c d*!![a,b;c,d]=1 := by
  have hl : !![a,b;c,d]*!![d,-b;-c,a]=(a*d-b*c) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  have hr : !![d,-b;-c,a]*!![a,b;c,d]=(a*d-b*c) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  constructor
  · rw [inverseTwoByTwo, Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ h, one_smul]
  · rw [inverseTwoByTwo, Matrix.smul_mul, hr, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem originalMatrixInverse :
    inverseTwoByTwo (2:ℚ) 1 0 3 = !![(1/2:ℚ),-1/6;0,1/3] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [inverseTwoByTwo]

abbrev GeneralLinearMatrices (n : ℕ) (K : Type*) [Field K] :=
  Matrix.GeneralLinearGroup (Fin n) K

def generalLinearMatrixGroup (n : ℕ) : Group (GeneralLinearMatrices n K) := inferInstance

theorem generalLinearMatrixProduct (A B : GeneralLinearMatrices n K) :
    ((A*B : GeneralLinearMatrices n K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) := rfl

theorem generalLinearInverseProducts (A : GeneralLinearMatrices n K) :
    (A : Matrix (Fin n) (Fin n) K) * (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) = 1 ∧
    (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := ⟨A.val_inv,A.inv_val⟩

theorem generalLinearProductInverse (A B : GeneralLinearMatrices n K) :
    (A*B)⁻¹=B⁻¹*A⁻¹ := mul_inv_rev A B

theorem nonemptyZeroMatrixNotInvertible (n : ℕ) (h : 0<n) :
    ¬hasTwoSidedMatrixInverse (0 : Matrix (Fin n) (Fin n) K) := by
  rintro ⟨B,hB,_⟩
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0,h⟩ ⟨0,h⟩) hB
  simpa using he

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def matrixRepresentation (a : Basis (Fin n) K V) (b : Basis (Fin m) K W) :
    (V →ₗ[K] W) ≃ₗ[K] Matrix (Fin m) (Fin n) K := LinearMap.toMatrix a b

theorem matrixRepresentationEntry (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (f : V →ₗ[K] W) (i : Fin m) (j : Fin n) :
    matrixRepresentation a b f i j = b.repr (f (a j)) i :=
  LinearMap.toMatrix_apply a b f i j

theorem matrixRepresentationAdd (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (f g : V →ₗ[K] W) : matrixRepresentation a b (f+g)=
      matrixRepresentation a b f + matrixRepresentation a b g := (matrixRepresentation a b).map_add f g

theorem matrixRepresentationScalar (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (c : K) (f : V →ₗ[K] W) : matrixRepresentation a b (c • f)=
      c • matrixRepresentation a b f := (matrixRepresentation a b).map_smul c f

theorem matrixRepresentationBijective (a : Basis (Fin n) K V) (b : Basis (Fin m) K W) :
    Bijective (matrixRepresentation a b) := (matrixRepresentation a b).bijective

theorem prescribedMatrixUnique (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (A : Matrix (Fin m) (Fin n) K) : ∃! f : V →ₗ[K] W, matrixRepresentation a b f=A :=
  (matrixRepresentation a b).bijective.existsUnique A

def elementaryLinearMap (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (i : Fin m) (j : Fin n) : V →ₗ[K] W := mapByBasis a fun k => if k=j then b i else 0

theorem elementaryLinearMapValues (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (i : Fin m) (j k : Fin n) : elementaryLinearMap a b i j (a k)=if k=j then b i else 0 :=
  mapByBasisValues a _ k

theorem elementaryLinearMapMatrix (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (i : Fin m) (j : Fin n) : matrixRepresentation a b (elementaryLinearMap a b i j)=
      Matrix.single i j 1 := by
  ext l k
  by_cases h : k=j
  · subst k; simp [matrixRepresentationEntry, elementaryLinearMapValues, Matrix.single, Basis.repr_self, Finsupp.single_apply, eq_comm]
  · simp [matrixRepresentationEntry, elementaryLinearMapValues, Matrix.single, h, Ne.symm h]

def elementaryHomBasis (a : Basis (Fin n) K V) (b : Basis (Fin m) K W) :
    Basis (Fin m × Fin n) K (V →ₗ[K] W) := (matrixUnitBasis m n).map (matrixRepresentation a b).symm

theorem elementaryHomBasisMatrix (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (i : Fin m) (j : Fin n) : matrixRepresentation a b (elementaryHomBasis a b (i,j))=
      Matrix.single i j 1 := by simp [elementaryHomBasis, matrixUnitBasisValues]

theorem elementaryHomBasisFormula (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (i : Fin m) (j : Fin n) : elementaryHomBasis a b (i,j)=elementaryLinearMap a b i j := by
  apply (matrixRepresentation a b).injective
  rw [elementaryHomBasisMatrix,elementaryLinearMapMatrix]

theorem linearMapSpaceDimension [FiniteDimensional K V] [FiniteDimensional K W] :
    finrank K (V →ₗ[K] W) = finrank K V * finrank K W := Module.finrank_linearMap K K V W

theorem identityInEveryBasis (a : Basis (Fin n) K V) :
    matrixRepresentation a a (LinearMap.id : V →ₗ[K] V)=identityMatrix n :=
  LinearMap.toMatrix_id a

end ILab.LinearAlgebra
