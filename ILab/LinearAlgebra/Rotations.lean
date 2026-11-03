import ILab.LinearAlgebra.MatrixAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-! Holstein, examples 5.1.5 and 5.1.9, printed pp. 76–77. -/
namespace ILab.LinearAlgebra
open Matrix

noncomputable def rotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotationAction (θ x y : ℝ) :
    rotation θ *ᵥ ![x, y] =
      ![Real.cos θ * x - Real.sin θ * y, Real.sin θ * x + Real.cos θ * y] := by
  ext i
  fin_cases i <;> simp [rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem rotationComposition (α β : ℝ) :
    rotation α * rotation β = rotation (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

noncomputable def rotationLinear (θ : ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  linearOfMatrix (rotation θ)

theorem rotationRepresentsRotation (θ : ℝ) :
    representingMatrix (rotationLinear θ) = rotation θ :=
  representingMatrixInverse (rotation θ)

theorem rotationLinearComposition (α β : ℝ) :
    (rotationLinear α).comp (rotationLinear β) = rotationLinear (α + β) := by
  change (linearOfMatrix (rotation α)).comp (linearOfMatrix (rotation β)) =
    linearOfMatrix (rotation (α + β))
  rw [← linearOfMatrixProduct, rotationComposition]

theorem rotationZero : rotation 0 = (identityMatrix 2 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, identityMatrix]

end ILab.LinearAlgebra
