import ILab.LinearAlgebra.ElementaryMatrices
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! Holstein §12.2. Bilinear maps on two possibly different spaces are represented
by curried linear maps. Finite-dimensional and square hypotheses are explicit.
No symmetry or restriction on characteristic is assumed. Integration on C⁰ is
an original analytic example, not formalized by the polynomial browser model. -/
namespace ILab.LinearAlgebra
open Module Matrix
universe u v w
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

def bilinearSpace := V →ₗ[K] W →ₗ[K] K

theorem bilinearSeparateAdd (B : V →ₗ[K] W →ₗ[K] K) (v v' : V) (w w' : W) :
    B (v+v') w = B v w + B v' w ∧ B v (w+w') = B v w + B v w' := by simp

theorem bilinearSeparateScalar (B : V →ₗ[K] W →ₗ[K] K) (a : K) (v : V) (w : W) :
    B (a • v) w = a * B v w ∧ B v (a • w) = a * B v w := by simp

theorem bilinearPointwise (B C : V →ₗ[K] W →ₗ[K] K) (a : K) (v : V) (w : W) :
    (B + a • C) v w = B v w + a * C v w := by simp

def bilinearMultiplication : K →ₗ[K] K →ₗ[K] K := LinearMap.mul K K

def bilinearEvaluation : Module.Dual K V →ₗ[K] V →ₗ[K] K := LinearMap.id

theorem bilinearEvaluationApply (φ : Module.Dual K V) (v : V) :
    bilinearEvaluation φ v = φ v := rfl

theorem bilinearEvaluationNondegenerate :
    (bilinearEvaluation (K:=K) (V:=V)).Nondegenerate := by
  constructor
  · intro φ h
    ext v
    exact h v
  · intro v h
    by_contra hn
    obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one K hn
    have : (1:K)=0 := hφ.symm.trans (h φ)
    exact one_ne_zero this

def bilinearCurry : (V →ₗ[K] W →ₗ[K] K) ≃ₗ[K] (V →ₗ[K] Module.Dual K W) :=
  LinearEquiv.refl K _

theorem bilinearCurryApply (B : V →ₗ[K] W →ₗ[K] K) (v : V) (w : W) :
    bilinearCurry B v w = B v w := rfl

theorem bilinearUncurryApply (h : V →ₗ[K] Module.Dual K W) (v : V) (w : W) :
    bilinearCurry.symm h v w = h v w := rfl

theorem bilinearCurryRoundtrip (B : V →ₗ[K] W →ₗ[K] K) :
    bilinearCurry.symm (bilinearCurry B) = B := bilinearCurry.symm_apply_apply B

theorem bilinearUncurryRoundtrip (h : V →ₗ[K] Module.Dual K W) :
    bilinearCurry (bilinearCurry.symm h) = h := bilinearCurry.apply_symm_apply h

theorem bilinearDimension [FiniteDimensional K V] [FiniteDimensional K W] :
    Module.finrank K (V →ₗ[K] W →ₗ[K] K) = Module.finrank K V * Module.finrank K W := by
  rw [Module.finrank_linearMap, Subspace.dual_finrank_eq]

theorem bilinearLeftInjective (B : V →ₗ[K] W →ₗ[K] K) :
    B.SeparatingLeft ↔ Function.Injective (bilinearCurry B) := by
  change B.SeparatingLeft ↔ Function.Injective B
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]

theorem bilinearRightInjective (B : V →ₗ[K] W →ₗ[K] K) :
    B.SeparatingRight ↔ Function.Injective B.flip := by
  rw [LinearMap.separatingRight_iff_flip_ker_eq_bot, LinearMap.ker_eq_bot]

section MatrixRepresentation
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (a : Basis ι K V) (b : Basis κ K W)

noncomputable def bilinearMatrixEquiv : (V →ₗ[K] W →ₗ[K] K) ≃ₗ[K] Matrix ι κ K :=
  LinearMap.toMatrix₂ a b

theorem bilinearMatrixEntry (B : V →ₗ[K] W →ₗ[K] K) (i : ι) (j : κ) :
    bilinearMatrixEquiv a b B i j = B (a i) (b j) := LinearMap.toMatrix₂_apply a b B i j

theorem bilinearBasisDetermines (B C : V →ₗ[K] W →ₗ[K] K)
    (h : ∀ i j, B (a i) (b j) = C (a i) (b j)) : B = C := by
  apply (bilinearMatrixEquiv a b).injective
  ext i j
  simpa only [bilinearMatrixEntry] using h i j

theorem bilinearBasisExpansion (B : V →ₗ[K] W →ₗ[K] K) (v : V) (w : W) :
    B v w = (a.repr v) ⬝ᵥ (bilinearMatrixEquiv a b B) *ᵥ (b.repr w) :=
  apply_eq_dotProduct_toMatrix₂_mulVec a b B v w

theorem bilinearCurryMatrixTranspose (B : V →ₗ[K] W →ₗ[K] K) :
    bilinearMatrixEquiv a b B = (LinearMap.toMatrix a b.dualBasis (bilinearCurry B))ᵀ := by
  ext i j
  simp [bilinearMatrixEquiv, LinearMap.toMatrix_apply, bilinearCurry,
    Module.Basis.dualBasis_repr]

theorem bilinearBasisChange (a' : Basis ι K V) (b' : Basis κ K W)
    (B : V →ₗ[K] W →ₗ[K] K) :
    bilinearMatrixEquiv a b B =
      (a'.toMatrix a)ᵀ * bilinearMatrixEquiv a' b' B * b'.toMatrix b := by
  exact (LinearMap.toMatrix₂_mul_basis_toMatrix a' b' a b B).symm

noncomputable def bilinearFromMatrix (B : Matrix ι κ K) :
    (ι → K) →ₗ[K] (κ → K) →ₗ[K] K := Matrix.toLinearMap₂' K B

theorem bilinearFromMatrixApply (B : Matrix ι κ K) (x : ι → K) (y : κ → K) :
    bilinearFromMatrix B x y = x ⬝ᵥ B *ᵥ y := by
  exact Matrix.toLinearMap₂'_apply' B x y
end MatrixRepresentation

section Congruence
variable {n : Type*} [Fintype n] [DecidableEq n]

def bilinearCongruent (B C : Matrix n n K) : Prop :=
  ∃ S : (Matrix n n K)ˣ, C = (S : Matrix n n K)ᵀ * B * S

theorem bilinearCongruentRefl (B : Matrix n n K) : bilinearCongruent B B := by
  refine ⟨1, ?_⟩
  simp

theorem bilinearCongruentSymm {B C : Matrix n n K} (h : bilinearCongruent B C) :
    bilinearCongruent C B := by
  obtain ⟨S,rfl⟩ := h
  refine ⟨S⁻¹, ?_⟩
  have hi : ((↑S⁻¹ : Matrix n n K)ᵀ * (↑S : Matrix n n K)ᵀ) = 1 := by
    rw [← Matrix.transpose_mul]
    simp
  calc
    B = (1 : Matrix n n K) * B * 1 := by simp
    _ = ((↑S⁻¹ : Matrix n n K)ᵀ * (↑S : Matrix n n K)ᵀ) * B * ((↑S : Matrix n n K) * ↑S⁻¹) := by rw [hi]; simp
    _ = _ := by simp [Matrix.mul_assoc]

theorem bilinearCongruentTrans {B C D : Matrix n n K}
    (h : bilinearCongruent B C) (h' : bilinearCongruent C D) : bilinearCongruent B D := by
  obtain ⟨S,rfl⟩ := h
  obtain ⟨T,rfl⟩ := h'
  refine ⟨S*T, ?_⟩
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem bilinearCongruenceDet (B S : Matrix n n K) :
    Matrix.det (Sᵀ * B * S) = (Matrix.det S)^2 * Matrix.det B := by
  simp only [Matrix.det_mul, Matrix.det_transpose]
  ring

theorem bilinearSimultaneousOperations (B : Matrix n n K) (T : (Matrix n n K)ˣ) :
    bilinearCongruent B ((T : Matrix n n K) * B * (T : Matrix n n K)ᵀ) := by
  obtain ⟨S, hS⟩ := (Matrix.isUnit_transpose (T : Matrix n n K)).mpr T.isUnit
  refine ⟨S, ?_⟩
  rw [hS]
  simp

theorem bilinearSwapArguments (B : Matrix n n K) (x y : n → K) :
    bilinearFromMatrix B y x = bilinearFromMatrix Bᵀ x y := by
  simp only [bilinearFromMatrixApply]
  exact (Matrix.dotProduct_transpose_mulVec B x y).symm
end Congruence

section Nondegenerate
variable {n : Type*} [Fintype n] [DecidableEq n] (b : Basis n K V)
variable (B : V →ₗ[K] V →ₗ[K] K)

theorem bilinearLeftDet : B.SeparatingLeft ↔ (bilinearMatrixEquiv b b B).det ≠ 0 :=
  LinearMap.separatingLeft_iff_det_ne_zero b

theorem bilinearRightDet : B.SeparatingRight ↔ (bilinearMatrixEquiv b b B).det ≠ 0 :=
  LinearMap.separatingRight_iff_det_ne_zero b

include b in
theorem bilinearLeftRight : B.SeparatingLeft ↔ B.SeparatingRight :=
  (bilinearLeftDet b B).trans (bilinearRightDet b B).symm

theorem bilinearMatrixUnit : IsUnit (bilinearMatrixEquiv b b B) ↔
    (bilinearMatrixEquiv b b B).det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem bilinearLeftBijective [FiniteDimensional K V] :
    B.SeparatingLeft ↔ Function.Bijective B := by
  rw [bilinearLeftInjective]
  change Function.Injective B ↔ Function.Bijective B
  constructor
  · intro h
    exact (B.linearEquivOfInjective h Subspace.dual_finrank_eq.symm).bijective
  · exact Function.Bijective.injective

theorem bilinearSixCriteria [FiniteDimensional K V] :
    (B.SeparatingLeft ↔ Function.Injective B) ∧
    (Function.Injective B ↔ Function.Bijective B) ∧
    (Function.Bijective B ↔ IsUnit (bilinearMatrixEquiv b b B)) ∧
    (IsUnit (bilinearMatrixEquiv b b B) ↔ (bilinearMatrixEquiv b b B).det ≠ 0) ∧
    ((bilinearMatrixEquiv b b B).det ≠ 0 ↔ B.SeparatingRight) := by
  refine ⟨bilinearLeftInjective B, ?_, ?_, bilinearMatrixUnit b B, (bilinearRightDet b B).symm⟩
  · exact (bilinearLeftInjective B).symm.trans (bilinearLeftBijective B)
  · exact (bilinearLeftBijective B).symm.trans ((bilinearLeftDet b B).trans (bilinearMatrixUnit b B).symm)
end Nondegenerate

noncomputable def bilinearDualIso [FiniteDimensional K W]
    (B : W →ₗ[K] W →ₗ[K] K) (h : B.Nondegenerate) : W ≃ₗ[K] Module.Dual K W :=
  LinearMap.BilinForm.toDual B h

theorem bilinearDualIsoApply [FiniteDimensional K W]
    (B : W →ₗ[K] W →ₗ[K] K) (h : B.Nondegenerate) (v w : W) :
    bilinearDualIso B h v w = B v w := rfl

noncomputable def bilinearHomIso [FiniteDimensional K W]
    (B : W →ₗ[K] W →ₗ[K] K) (h : B.Nondegenerate) :
    (V →ₗ[K] W) ≃ₗ[K] (V →ₗ[K] W →ₗ[K] K) :=
  (LinearEquiv.refl K V).arrowCongr (bilinearDualIso B h)

theorem bilinearHomIsoApply [FiniteDimensional K W]
    (B : W →ₗ[K] W →ₗ[K] K) (h : B.Nondegenerate) (f : V →ₗ[K] W) (v : V) (w : W) :
    bilinearHomIso B h f v w = B (f v) w := rfl

theorem bilinearHomIsoRoundtrip [FiniteDimensional K W]
    (B : W →ₗ[K] W →ₗ[K] K) (h : B.Nondegenerate) (f : V →ₗ[K] W) :
    (bilinearHomIso B h).symm (bilinearHomIso B h f) = f :=
  (bilinearHomIso B h).symm_apply_apply f

theorem bilinearNotSymmetric :
    let B : Matrix (Fin 2) (Fin 2) ℚ := !![1,2;0,1]
    bilinearFromMatrix B ![1,0] ![0,1] ≠ bilinearFromMatrix B ![0,1] ![1,0] := by
  norm_num [bilinearFromMatrixApply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem bilinearNotProductLinear : (1+1:ℚ)*(1+1) ≠ 1*1+1*1 := by norm_num

theorem bilinearCoupledScale (B : Matrix (Fin n) (Fin n) K) (i : Fin n) (c : Kˣ) :
    bilinearCongruent B ((scaleElementary i c : Matrix (Fin n) (Fin n) K) * B *
      (scaleElementary i c : Matrix (Fin n) (Fin n) K)ᵀ) :=
  bilinearSimultaneousOperations B (scaleElementary i c)

theorem bilinearCoupledSwap (B : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    bilinearCongruent B ((swapElementary (K:=K) i j : Matrix (Fin n) (Fin n) K) * B *
      (swapElementary (K:=K) i j : Matrix (Fin n) (Fin n) K)ᵀ) :=
  bilinearSimultaneousOperations B (swapElementary (K:=K) i j)

theorem bilinearCoupledAdd (B : Matrix (Fin n) (Fin n) K) (i j : Fin n)
    (h : j ≠ i) (c : K) :
    bilinearCongruent B ((addElementary i j h c : Matrix (Fin n) (Fin n) K) * B *
      (addElementary i j h c : Matrix (Fin n) (Fin n) K)ᵀ) :=
  bilinearSimultaneousOperations B (addElementary i j h c)

theorem bilinearCharacteristicTwoExample :
    let B : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1,1;0,1]
    B.det = 1 ∧ bilinearFromMatrix B ![1,0] ![0,1] = 1 := by
  norm_num [Matrix.det_fin_two, bilinearFromMatrixApply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

end ILab.LinearAlgebra
