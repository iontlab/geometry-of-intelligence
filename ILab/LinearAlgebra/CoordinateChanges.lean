import ILab.LinearAlgebra.MoreMatrices
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Holstein §5.4 (LA-P019), printed87–92, PDF89–94.
Holstein T_{a'}^a maps old a-coordinates to new a'-coordinates.
The first argument of coordinateChange is the old basis; the second is new.
Finite index types Fin n include dimension zero. General fields, arbitrary
vector spaces with the specified finite bases, and unequal source/target
sizes are retained. Concrete reflection computations are over R.
The source's ambiguous labels in Remark5.4.5.4 are kept in the edition and
separately explained; the scalar example below explicitly assumes c != 0. -/
noncomputable section
namespace ILab.LinearAlgebra
open Matrix Module
variable {K : Type*} [Field K] {m n k : ℕ}
variable {V W Z : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

def coordinateSynthesis (a : Basis (Fin n) K V) : (Fin n → K) ≃ₗ[K] V := a.equivFun.symm

theorem synthesizeReadCoordinates (a : Basis (Fin n) K V) (v : V) :
    coordinateSynthesis a (a.equivFun v) = v := a.equivFun.symm_apply_apply v

theorem readSynthesizedCoordinates (a : Basis (Fin n) K V) (x : Fin n → K) :
    a.equivFun (coordinateSynthesis a x) = x := a.equivFun.apply_symm_apply x

def coordinateTransport (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (f : V →ₗ[K] W) : (Fin n → K) →ₗ[K] (Fin m → K) :=
  b.equivFun.toLinearMap.comp (f.comp (coordinateSynthesis a).toLinearMap)

theorem matrixViaCoordinateIsomorphisms (a : Basis (Fin n) K V)
    (b : Basis (Fin m) K W) (f : V →ₗ[K] W) :
    matrixRepresentation a b f = LinearMap.toMatrix' (coordinateTransport a b f) := by
  ext i j
  simp [matrixRepresentationEntry, LinearMap.toMatrix'_apply, coordinateTransport,
    coordinateSynthesis, Basis.equivFun_symm_apply, Pi.single_apply]

theorem matchingBasisComposition (a : Basis (Fin n) K V) (b : Basis (Fin m) K W)
    (c : Basis (Fin k) K Z) (f : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    matrixRepresentation a c (g.comp f) =
      matrixRepresentation b c g * matrixRepresentation a b f :=
  LinearMap.toMatrix_comp a b c g f

def coordinateChange (a a' : Basis (Fin n) K V) : Matrix (Fin n) (Fin n) K :=
  matrixRepresentation a a' LinearMap.id

theorem coordinateChangeConvention (a a' : Basis (Fin n) K V) :
    coordinateChange a a' = a'.toMatrix a := LinearMap.toMatrix_id_eq_basis_toMatrix a a'

theorem coordinateChangeEntry (a a' : Basis (Fin n) K V) (i j : Fin n) :
    coordinateChange a a' i j = a'.repr (a j) i := matrixRepresentationEntry a a' _ i j

theorem coordinateChangeSelf (a : Basis (Fin n) K V) : coordinateChange a a = 1 :=
  LinearMap.toMatrix_id a

theorem coordinateChangeInverseProducts (a a' : Basis (Fin n) K V) :
    coordinateChange a a' * coordinateChange a' a = 1 ∧
    coordinateChange a' a * coordinateChange a a' = 1 := by
  constructor
  · simpa [coordinateChange, matrixRepresentation] using (LinearMap.toMatrix_comp a' a a' LinearMap.id LinearMap.id).symm
  · simpa [coordinateChange, matrixRepresentation] using (LinearMap.toMatrix_comp a a' a LinearMap.id LinearMap.id).symm

theorem coordinateChangeIsUnit (a a' : Basis (Fin n) K V) : IsUnit (coordinateChange a a') :=
  (matrixInvertibleIffUnit _).mp ⟨coordinateChange a' a, coordinateChangeInverseProducts a a'⟩

theorem coordinateChangeInverse (a a' : Basis (Fin n) K V) :
    (coordinateChange a a')⁻¹ = coordinateChange a' a := by
  exact Matrix.inv_eq_left_inv (coordinateChangeInverseProducts a a').2

theorem coordinateChangeVector (a a' : Basis (Fin n) K V) (v : V) :
    coordinateChange a a' *ᵥ a.equivFun v = a'.equivFun v :=
  LinearMap.toMatrix_mulVec_repr a a' LinearMap.id v

theorem coordinateChangeTriangle (a a' : Basis (Fin n) K V) (x : Fin n → K) :
    coordinateSynthesis a' (coordinateChange a a' *ᵥ x) = coordinateSynthesis a x := by
  have h := coordinateChangeVector a a' (coordinateSynthesis a x)
  rw [readSynthesizedCoordinates] at h
  rw [h, synthesizeReadCoordinates]

theorem coordinateChangeChain (a b c : Basis (Fin n) K V) :
    coordinateChange b c * coordinateChange a b = coordinateChange a c := by
  simpa [coordinateChange, matrixRepresentation] using
    (LinearMap.toMatrix_comp a b c LinearMap.id LinearMap.id).symm

theorem matrixChangeFormulaReverse (a a' : Basis (Fin n) K V)
    (b b' : Basis (Fin m) K W) (f : V →ₗ[K] W) :
    matrixRepresentation a' b' f =
      coordinateChange b b' * matrixRepresentation a b f * coordinateChange a' a := by
  simp only [coordinateChange, matrixRepresentation]
  rw [← LinearMap.toMatrix_comp a b b', ← LinearMap.toMatrix_comp a' a b']
  simp

theorem matrixChangeFormula (a a' : Basis (Fin n) K V)
    (b b' : Basis (Fin m) K W) (f : V →ₗ[K] W) :
    matrixRepresentation a' b' f =
      coordinateChange b b' * matrixRepresentation a b f * (coordinateChange a a')⁻¹ := by
  rw [coordinateChangeInverse]
  exact matrixChangeFormulaReverse a a' b b' f

theorem endomorphismChangeFormula (a a' : Basis (Fin n) K V) (f : V →ₗ[K] V) :
    matrixRepresentation a' a' f =
      coordinateChange a a' * matrixRepresentation a a f * (coordinateChange a a')⁻¹ :=
  matrixChangeFormula a a' a a' f

theorem mismatchedMiddleBasis (a : Basis (Fin n) K V) (b c : Basis (Fin m) K W)
    (d : Basis (Fin k) K Z) (f : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    matrixRepresentation a d (g.comp f) =
      matrixRepresentation c d g * coordinateChange b c * matrixRepresentation a b f := by
  simp only [coordinateChange, matrixRepresentation]
  rw [← LinearMap.toMatrix_comp b c d, ← LinearMap.toMatrix_comp a b d]
  simp

theorem oneDimensionalCoordinateScaling (c x : K) (hc : c ≠ 0) :
    c * (x / c) = x ∧ x / c = c⁻¹ * x := by
  constructor <;> field_simp <;> ring

def reflectionBasisMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,-1;1,1]
def reflectionInverseBasisMatrix : Matrix (Fin 2) (Fin 2) ℝ := (1/2 : ℝ) • !![1,1;-1,1]
def reflectionStandardMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;1,0]
def reflectionAdaptedMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,-1]

theorem reflectionBasisInverseProducts :
    reflectionBasisMatrix * reflectionInverseBasisMatrix = 1 ∧
    reflectionInverseBasisMatrix * reflectionBasisMatrix = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [reflectionBasisMatrix,reflectionInverseBasisMatrix,Matrix.mul_apply,Fin.sum_univ_two]

theorem reflectionAdaptedBasisImages :
    reflectionStandardMatrix *ᵥ (![1,1] : Fin 2 → ℝ) = ![1,1] ∧
    reflectionStandardMatrix *ᵥ (![-1,1] : Fin 2 → ℝ) = ![1,-1] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [reflectionStandardMatrix,Matrix.mulVec,Fin.sum_univ_two]

theorem reflectionOriginalChangeCalculation :
    reflectionBasisMatrix * reflectionAdaptedMatrix * reflectionInverseBasisMatrix =
      reflectionStandardMatrix := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [reflectionBasisMatrix,reflectionInverseBasisMatrix,reflectionAdaptedMatrix,
      reflectionStandardMatrix,Matrix.mul_apply,Fin.sum_univ_two]

theorem reflectionCoordinatePaths (x : Fin 2 → ℝ) :
    reflectionStandardMatrix *ᵥ x = reflectionBasisMatrix *ᵥ
      (reflectionAdaptedMatrix *ᵥ (reflectionInverseBasisMatrix *ᵥ x)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, reflectionOriginalChangeCalculation]

end ILab.LinearAlgebra
