import ILab.LinearAlgebra.LaplaceDeterminants
import ILab.LinearAlgebra.Rotations
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Determinant

/-! Holstein §7.4. Classical adjugate, not conjugate transpose.
Finite square matrices over arbitrary fields, including characteristic two.
Existing Mathlib results are reused explicitly. The source proof ordering and
the exercise reference for Cramer are preserved in the separate original text.
No verification of browser algorithms or geometry is claimed. -/
noncomputable section
namespace ILab.LinearAlgebra
open Matrix Module
variable {K : Type*} [Field K] {n : ℕ}
local instance : DecidableEq K := Classical.decEq K

theorem detProduct (A B : Matrix (Fin n) (Fin n) K) :
    (A*B).det = A.det*B.det := Matrix.det_mul A B

theorem detSingularProduct (A B : Matrix (Fin n) (Fin n) K)
    (h : A.det=0 ∨ B.det=0) : (A*B).det=0 := by
  rw [detProduct]; rcases h with h|h <;> simp [h]

theorem detElementaryAddition (i j : Fin n) (h : i ≠ j) (s : K) :
    (Matrix.transvection i j s).det=1 := Matrix.det_transvection_of_ne i j h s

theorem detElementarySwap (i j : Fin n) (h : i ≠ j) :
    ((1 : Matrix (Fin n) (Fin n) K).submatrix (Equiv.swap i j) id).det = -1 := by
  rw [Matrix.det_permute]; simp [Equiv.Perm.sign_swap h]

theorem detElementaryScale (i : Fin n) (s : K) :
    (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : K)) i s)).det=s := by
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem detSimilarity (A T : Matrix (Fin n) (Fin n) K) (hT : T.det ≠ 0) :
    (T*A*T⁻¹).det=A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
  simp only [Ring.inverse_eq_inv]
  field_simp

theorem detInverse (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    A⁻¹.det=A.det⁻¹ := by
  simpa only [Ring.inverse_eq_inv] using Matrix.det_nonsing_inv A

def determinantGroupHom : Matrix.GeneralLinearGroup (Fin n) K →* Kˣ :=
  Matrix.GeneralLinearGroup.det

theorem determinantGroupHomProduct (A B : Matrix.GeneralLinearGroup (Fin n) K) :
    determinantGroupHom (A*B)=determinantGroupHom A*determinantGroupHom B :=
  map_mul determinantGroupHom A B

def classicalAdjugate (A : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  fun i j => (-1 : K)^(i.val+j.val)*(deletionMinor A j i).det

theorem classicalAdjugateEntry (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (i j : Fin (n+1)) :
    classicalAdjugate A i j = (-1 : K)^(i.val+j.val)*(deletionMinor A j i).det := rfl

theorem classicalAdjugateEqualsMathlib (A : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    classicalAdjugate A=A.adjugate := by
  ext i j
  simp only [classicalAdjugate, deletionMinor, Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [Nat.add_comm i.val j.val]

theorem classicalAdjugateRight (A : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    A*classicalAdjugate A=A.det • (1 : Matrix (Fin (n+1)) (Fin (n+1)) K) := by
  rw [classicalAdjugateEqualsMathlib]; exact Matrix.mul_adjugate A

theorem classicalAdjugateLeft (A : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    classicalAdjugate A*A=A.det • (1 : Matrix (Fin (n+1)) (Fin (n+1)) K) := by
  rw [classicalAdjugateEqualsMathlib]; exact Matrix.adjugate_mul A

theorem classicalAdjugateInverse (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (hA : A.det ≠ 0) : A⁻¹=A.det⁻¹ • classicalAdjugate A := by
  rw [classicalAdjugateEqualsMathlib, Matrix.inv_def, Ring.inverse_eq_inv]

theorem classicalAdjugateTwo (a b c d : K) :
    classicalAdjugate (!![a,b;c,d] : Matrix (Fin 2) (Fin 2) K)=!![d,-b;-c,a] := by
  rw [classicalAdjugateEqualsMathlib, Matrix.adjugate_fin_two_of]

theorem classicalInverseTwo (a b c d : K) (h : a*d-b*c ≠ 0) :
    (!![a,b;c,d] : Matrix (Fin 2) (Fin 2) K)⁻¹=(a*d-b*c)⁻¹ • !![d,-b;-c,a] := by
  rw [classicalAdjugateInverse _ (by simpa [Matrix.det_fin_two] using h),
    classicalAdjugateTwo, Matrix.det_fin_two]
  rfl

theorem cramerUniqueSolution (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K)
    (hA : A.det ≠ 0) : ∃! x : Fin n → K, A*ᵥ x=b := by
  refine ⟨A⁻¹*ᵥb, ?_, ?_⟩
  · change A*ᵥ(A⁻¹*ᵥb)=b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  · intro x hx
    calc
      x = A⁻¹*ᵥ(A*ᵥx) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
      _ = A⁻¹*ᵥb := by rw [hx]

theorem cramerCoordinate (A : Matrix (Fin n) (Fin n) K) (b x : Fin n → K)
    (hA : A.det ≠ 0) (hx : A*ᵥx=b) (i : Fin n) :
    x i=(A.updateCol i b).det/A.det := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have he : x=A⁻¹*ᵥb := by
    calc
      x = A⁻¹*ᵥ(A*ᵥx) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
      _ = A⁻¹*ᵥb := by rw [hx]
  have h := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer A b hunit) i
  rw [← he] at h
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at h
  exact (eq_div_iff hA).mpr (by simpa [mul_comm] using h)

theorem endomorphismBasisIndependence {V : Type*} [AddCommGroup V] [Module K V]
    (b c : Basis (Fin n) K V) (f : V →ₗ[K] V) :
    (LinearMap.toMatrix b b f).det=(LinearMap.toMatrix c c f).det :=
  LinearMap.det_toMatrix_eq_det_toMatrix b c f

theorem endomorphismDetFromBasis {V : Type*} [AddCommGroup V] [Module K V]
    (b : Basis (Fin n) K V) (f : V →ₗ[K] V) :
    (LinearMap.toMatrix b b f).det=LinearMap.det f := LinearMap.det_toMatrix b f

theorem endomorphismDetComposition {V : Type*} [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] V) : LinearMap.det (f.comp g)=LinearMap.det f*LinearMap.det g :=
  LinearMap.det_comp f g

theorem endomorphismDetAutomorphism {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ LinearMap.det f ≠ 0 := by
  rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem automorphismInverseDet {V : Type*} [AddCommGroup V] [Module K V]
    (f : V ≃ₗ[K] V) : LinearEquiv.det f.symm=(LinearEquiv.det f)⁻¹ := by
  exact map_inv LinearEquiv.det f

noncomputable def reflectionAxis (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2*θ), Real.sin (2*θ);Real.sin (2*θ), -Real.cos (2*θ)]

theorem rotationDetOne (θ : ℝ) : (rotation θ).det=1 := by
  simp only [rotation, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem reflectionDetNegOne (θ : ℝ) : (reflectionAxis θ).det = -1 := by
  simp only [reflectionAxis, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  nlinarith [Real.sin_sq_add_cos_sq (2*θ)]

end ILab.LinearAlgebra
