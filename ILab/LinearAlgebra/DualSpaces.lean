import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic

/-! Holstein §12.1. Algebraic duals over arbitrary fields; finite-dimensional
assumptions appear only where stated. The analytic integrals of 12.1.2 and the
informal impossibility of a natural V → V* identification are not claimed here.
The rescaling calculation is explicitly a one-dimensional coordinate model.
These proofs do not verify the JavaScript implementation. -/
namespace ILab.LinearAlgebra
open Module
universe u v w z
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {Z : Type z} [AddCommGroup Z] [Module K Z]

def dualSpace := Module.Dual K V

theorem dualLinearFormCombination (φ : Module.Dual K V) (a b : K) (v w : V) :
    φ (a • v + b • w) = a * φ v + b * φ w := by simp

def dualCoordinateEvaluation (i : Fin n) : Module.Dual K (Fin n → K) :=
  LinearMap.proj i

theorem dualCoordinateEvaluationApply (i : Fin n) (v : Fin n → K) :
    dualCoordinateEvaluation i v = v i := rfl

theorem dualDimension [FiniteDimensional K V] :
    Module.finrank K (Module.Dual K V) = Module.finrank K V :=
  Subspace.dual_finrank_eq

section Basis
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
noncomputable def dualBasis := b.dualBasis

theorem dualBasisKronecker (i j : ι) :
    b.dualBasis i (b j) = if i = j then 1 else 0 := by
  simpa only [eq_comm] using b.dualBasis_apply_self i j

theorem dualBasisCoordinate (i : ι) (v : V) : b.dualBasis i v = b.repr v i :=
  b.dualBasis_apply i v

theorem dualFormCoordinates (φ : Module.Dual K V) (i : ι) :
    b.dualBasis.repr φ i = φ (b i) := b.dualBasis_repr φ i

noncomputable def dualBasisIdentification : V ≃ₗ[K] Module.Dual K V := b.toDualEquiv

theorem dualBasisIdentificationEval (i j : ι) :
    b.toDualEquiv (b i) (b j) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j; simp [Basis.toDualEquiv_apply, Basis.toDual_apply_left, Basis.repr_self]
  · simp [Basis.toDualEquiv_apply, Basis.toDual_apply_left, Basis.repr_self,
      h, Ne.symm h]
end Basis

noncomputable def dualExtension (U : Submodule K V) (φ : Module.Dual K U) : Module.Dual K V :=
  Subspace.dualLift U φ

theorem dualExtensionRestricts (U : Submodule K V) (φ : Module.Dual K U) (u : U) :
    dualExtension U φ (u : V) = φ u := by
  exact Subspace.dualLift_of_subtype u

theorem dualExtensionExists (U : Submodule K V) (φ : Module.Dual K U) :
    ∃ ψ : Module.Dual K V, ∀ u : U, ψ u = φ u :=
  ⟨dualExtension U φ, dualExtensionRestricts U φ⟩

theorem dualSeparatesNonzero {v : V} (hv : v ≠ 0) :
    ∃ φ : Module.Dual K V, φ v = 1 := Module.Projective.exists_dual_eq_one K hv

theorem dualRescalingCoordinateModel (α x y : K) (_hα : α ≠ 0) :
    (x / α) * (y / α) = α⁻¹ ^ 2 * (x * y) := by
  simp only [div_eq_mul_inv, pow_two]; ring

theorem dualRescalingCounterexample :
    ((1 : ℚ) / 2) * (1 / 2) = 1 / 4 ∧ ((1 : ℚ) / 2) * (1 / 2) ≠ 1 := by norm_num

def dualPullback (f : V →ₗ[K] W) : Module.Dual K W →ₗ[K] Module.Dual K V := f.dualMap

theorem dualPullbackApply (f : V →ₗ[K] W) (φ : Module.Dual K W) (v : V) :
    dualPullback f φ v = φ (f v) := rfl

theorem dualPullbackLinear (f : V →ₗ[K] W) (a b : K) (φ ψ : Module.Dual K W) :
    dualPullback f (a • φ + b • ψ) = a • dualPullback f φ + b • dualPullback f ψ := by
  simp [dualPullback]

theorem dualPullbackComposition (f : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    (g.comp f).dualMap = f.dualMap.comp g.dualMap :=
  (LinearMap.dualMap_comp_dualMap f g).symm

theorem dualPullbackIdentity : (LinearMap.id : V →ₗ[K] V).dualMap = LinearMap.id :=
  LinearMap.dualMap_id

theorem dualMatrixTranspose {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (a : Basis ι K V) (b : Basis κ K W)
    (f : V →ₗ[K] W) :
    LinearMap.toMatrix b.dualBasis a.dualBasis f.dualMap = Matrix.transpose (LinearMap.toMatrix a b f) :=
  LinearMap.toMatrix_transpose f

theorem dualRank [FiniteDimensional K V] [FiniteDimensional K W] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f.dualMap) = Module.finrank K (LinearMap.range f) :=
  LinearMap.finrank_range_dualMap_eq_finrank_range f

def dualSetAnnihilator (S : Set V) : Submodule K (Module.Dual K V) where
  carrier := {φ | ∀ v ∈ S, φ v = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ v hv; simp [hφ v hv, hψ v hv]
  smul_mem' := by intro a φ hφ v hv; simp [hφ v hv]

theorem dualSetAnnihilatorMembership (S : Set V) (φ : Module.Dual K V) :
    φ ∈ dualSetAnnihilator S ↔ ∀ v ∈ S, φ v = 0 := Iff.rfl

theorem dualSubspaceAnnihilator (U : Submodule K V) :
    dualSetAnnihilator (U : Set V) = U.dualAnnihilator := by
  ext φ; exact (Submodule.mem_dualAnnihilator φ).symm

theorem dualAnnihilatorAntitone (U T : Submodule K V) (h : U ≤ T) :
    T.dualAnnihilator ≤ U.dualAnnihilator := Submodule.dualAnnihilator_anti h

theorem dualAnnihilatorDimension [FiniteDimensional K V] (U : Submodule K V) :
    Module.finrank K U + Module.finrank K U.dualAnnihilator = Module.finrank K V :=
  Subspace.finrank_add_finrank_dualAnnihilator_eq U

theorem dualAnnihilatorZero : (⊥ : Submodule K V).dualAnnihilator = ⊤ :=
  Submodule.dualAnnihilator_bot

theorem dualAnnihilatorWhole : (⊤ : Submodule K V).dualAnnihilator = ⊥ :=
  Submodule.dualAnnihilator_top

theorem dualHyperplaneDimension [FiniteDimensional K V] (φ : Module.Dual K V) (hφ : φ ≠ 0) :
    Module.finrank K (LinearMap.ker φ) + 1 = Module.finrank K V :=
  Module.Dual.finrank_ker_add_one_of_ne_zero hφ

theorem dualAffineLevel (φ : Module.Dual K V) (v₀ v : V) :
    φ v = φ v₀ ↔ v - v₀ ∈ LinearMap.ker φ := by
  simp [LinearMap.mem_ker, sub_eq_zero]

theorem dualKernelAnnihilatorImage (f : V →ₗ[K] W) :
    LinearMap.ker f.dualMap = (LinearMap.range f).dualAnnihilator :=
  LinearMap.ker_dualMap_eq_dualAnnihilator_range f

theorem dualImageAnnihilatorKernel (f : V →ₗ[K] W) :
    LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  LinearMap.range_dualMap_eq_dualAnnihilator_ker f

def dualBidual := Module.Dual K (Module.Dual K V)

def dualEvaluation : V →ₗ[K] Module.Dual K (Module.Dual K V) := Module.Dual.eval K V

theorem dualEvaluationApply (v : V) (φ : Module.Dual K V) : dualEvaluation v φ = φ v := rfl

theorem dualEvaluationLinear (a b : K) (v w : V) :
    dualEvaluation (K := K) (a • v + b • w) = a • dualEvaluation (K := K) v + b • dualEvaluation (K := K) w := by
  simp [dualEvaluation]

theorem dualEvaluationInjective : Function.Injective (dualEvaluation : V →ₗ[K] _) :=
  Module.eval_apply_injective K

theorem dualEvaluationBijective [FiniteDimensional K V] :
    Function.Bijective (dualEvaluation : V →ₗ[K] _) := Module.bijective_dual_eval K V

noncomputable def dualBidualEquivalence [FiniteDimensional K V] :
    V ≃ₗ[K] Module.Dual K (Module.Dual K V) := Module.evalEquiv K V

theorem dualNaturality (f : V →ₗ[K] W) :
    f.dualMap.dualMap.comp (Module.Dual.eval K V) = (Module.Dual.eval K W).comp f :=
  Module.Dual.eval_naturality f

theorem dualNaturalityValues (f : V →ₗ[K] W) (v : V) (φ : Module.Dual K W) :
    (f.dualMap.dualMap (Module.Dual.eval K V v)) φ = φ (f v) := rfl

end ILab.LinearAlgebra
