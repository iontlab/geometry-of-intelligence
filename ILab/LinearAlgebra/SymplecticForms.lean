import ILab.LinearAlgebra.BilinearForms
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! Holstein §12.3. The general existence theorem for a symplectic basis is
not claimed by the helper lemmas below. They prove the actual pair and
orthogonal-complement steps; the browser implements and independently tests
the finite exact construction. Left/right orthogonals remain distinct. -/
namespace ILab.LinearAlgebra
open Module Matrix
universe u v
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def formSkew (B : LinearMap.BilinForm K V) : Prop := ∀ x y, B x y = - B y x

def formSymplectic [FiniteDimensional K V] (B : LinearMap.BilinForm K V) : Prop :=
  B.IsAlt ∧ B.Nondegenerate

theorem formAlternatingSkew (B : LinearMap.BilinForm K V) (h : B.IsAlt) : formSkew B := by
  intro x y
  exact (neg_eq_iff_eq_neg).mp (h.neg_eq x y)

theorem formSkewAlternating (B : LinearMap.BilinForm K V) (h : formSkew B)
    (h2 : (2 : K) ≠ 0) : B.IsAlt := by
  intro x
  have hx := h x x
  have hz : (2 : K) * B x x = 0 := by linear_combination hx
  exact (mul_eq_zero.mp hz).resolve_left h2

theorem formCharacteristicTwoNeg (h2 : (2 : K) = 0) (a : K) : -a = a := by
  have h : a+a=0 := by linear_combination a*h2
  exact (neg_eq_iff_add_eq_zero).mpr h

theorem formCharacteristicTwoSymm (B : LinearMap.BilinForm K V) (h2 : (2 : K) = 0) :
    formSkew B ↔ B.IsSymm := by
  constructor
  · intro h; exact ⟨fun x y => by simpa [formCharacteristicTwoNeg h2] using h x y⟩
  · intro h x y; simpa [formCharacteristicTwoNeg h2] using h.eq x y

def formSymmetricPart (B : LinearMap.BilinForm K V) : LinearMap.BilinForm K V :=
  (2 : K)⁻¹ • (B + B.flip)

def formSkewPart (B : LinearMap.BilinForm K V) : LinearMap.BilinForm K V :=
  (2 : K)⁻¹ • (B - B.flip)

theorem formSymmetricPartApply (B : LinearMap.BilinForm K V) (x y : V) :
    formSymmetricPart B x y = (2 : K)⁻¹ * (B x y + B y x) := rfl

theorem formSkewPartApply (B : LinearMap.BilinForm K V) (x y : V) :
    formSkewPart B x y = (2 : K)⁻¹ * (B x y - B y x) := rfl

theorem formSymmetricPartSymm (B : LinearMap.BilinForm K V) : (formSymmetricPart B).IsSymm := by
  constructor; intro x y; simp only [formSymmetricPartApply]; ring

theorem formSkewPartSkew (B : LinearMap.BilinForm K V) : formSkew (formSkewPart B) := by
  intro x y; simp only [formSkewPartApply]; ring

theorem formPartsReconstruct (B : LinearMap.BilinForm K V) (h2 : (2 : K) ≠ 0) :
    formSymmetricPart B + formSkewPart B = B := by
  ext x y
  change (2 : K)⁻¹ * (B x y + B y x) + (2 : K)⁻¹ * (B x y - B y x) = B x y
  field_simp; ring

def formPullback (B : LinearMap.BilinForm K V) (f : V →ₗ[K] V) : LinearMap.BilinForm K V :=
  B.compl₁₂ f f

theorem formPullbackApply (B : LinearMap.BilinForm K V) (f : V →ₗ[K] V) (x y : V) :
    formPullback B f x y = B (f x) (f y) := rfl

theorem formAlternatingPullback (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (f : V →ₗ[K] V) : (formPullback B f).IsAlt := by intro x; exact ha (f x)

section Matrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem formSymmetricMatrix (b : Basis ι K V) (B : LinearMap.BilinForm K V) :
    (B.toMatrix b).IsSymm ↔ B.IsSymm := B.isSymm_toMatrix_iff_isSymm b

theorem formSkewMatrix (b : Basis ι K V) (B : LinearMap.BilinForm K V) :
    (B.toMatrix b)ᵀ = -(B.toMatrix b) ↔ formSkew B := by
  constructor
  · intro h
    have e : B = -B.flip := by
      apply bilinearBasisDetermines b b
      intro i j
      have hij := congrArg (fun M : Matrix ι ι K => M j i) h
      simpa [LinearMap.BilinForm.toMatrix_apply] using hij
    intro x y
    have := congrArg (fun C : LinearMap.BilinForm K V => C x y) e
    exact this
  · intro h; ext i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, LinearMap.BilinForm.toMatrix_apply] using h (b j) (b i)

theorem formSymmetryCongruence (B S : Matrix ι ι K) (h : Bᵀ = B) :
    (Sᵀ * B * S)ᵀ = Sᵀ * B * S := by simp [Matrix.transpose_mul, h, Matrix.mul_assoc]

theorem formSkewCongruence (B S : Matrix ι ι K) (h : Bᵀ = -B) :
    (Sᵀ * B * S)ᵀ = -(Sᵀ * B * S) := by simp [Matrix.transpose_mul, h, Matrix.mul_assoc]

theorem formSkewDeterminant (B : Matrix ι ι K) (h : Bᵀ = -B) :
    B.det = (-1 : K) ^ Fintype.card ι * B.det := by
  calc B.det = Bᵀ.det := (Matrix.det_transpose B).symm
       _ = (-B).det := congrArg Matrix.det h
       _ = _ := Matrix.det_neg B

theorem formSkewEven (B : Matrix ι ι K) (h : Bᵀ = -B) (hd : B.det ≠ 0)
    (h2 : (2 : K) ≠ 0) : Even (Fintype.card ι) := by
  have hp : (-1 : K) ^ Fintype.card ι = 1 := by
    apply mul_right_cancel₀ hd
    simpa using (formSkewDeterminant B h).symm
  have hn : (-1 : K) ≠ 1 := by intro he; apply h2; linear_combination -he
  exact (neg_one_pow_eq_one_iff_even hn).mp hp

theorem formSymplecticEven (b : Basis ι K V) (B : LinearMap.BilinForm K V)
    (ha : B.IsAlt) (hd : B.Nondegenerate) (h2 : (2 : K) ≠ 0) : Even (finrank K V) := by
  have h := formSkewEven (B.toMatrix b) ((formSkewMatrix b B).mpr (formAlternatingSkew B ha))
    ((B.nondegenerate_iff_det_ne_zero b).mp hd) h2
  simpa only [finrank_eq_card_basis b] using h
end Matrices

theorem formNormalizedPartner (B : LinearMap.BilinForm K V) (hd : B.Nondegenerate)
    (u : V) (hu : u ≠ 0) : ∃ v, B u v = 1 := by
  classical
  have hw : ∃ w, B u w ≠ 0 := by
    by_contra hn; push_neg at hn; exact hu (hd.1 u hn)
  obtain ⟨w,hw⟩ := hw
  refine ⟨(B u w)⁻¹ • w, ?_⟩
  simp [hw]

theorem formNormalizedPairIndependent (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (u v : V) (h : B u v = 1) : LinearIndependent K ![u,v] := by
  apply linearIndependent_fin2.mpr
  constructor
  · change v ≠ 0
    intro hv; rw [hv] at h; simpa using h
  · intro a he
    change a • v = u at he
    have hz := congrArg (fun z => B z v) he
    simp [ha v, h] at hz

theorem formPairCoefficients (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (u v : V) (h : B u v = 1) (a c : K) :
    B (a • u + c • v) v = a ∧ B (a • u + c • v) u = -c := by
  have hvu := formAlternatingSkew B ha v u
  simp [h] at hvu
  simp [map_add, ha u, ha v, h, hvu]

def formLeftOrthogonal (B : LinearMap.BilinForm K V) (U : Submodule K V) : Submodule K V :=
  B.flip.orthogonal U

theorem formLeftOrthogonalMem (B : LinearMap.BilinForm K V) (U : Submodule K V) (v : V) :
    v ∈ formLeftOrthogonal B U ↔ ∀ u ∈ U, B v u = 0 := Iff.rfl

theorem formRightOrthogonalMem (B : LinearMap.BilinForm K V) (U : Submodule K V) (v : V) :
    v ∈ B.orthogonal U ↔ ∀ u ∈ U, B u v = 0 := Iff.rfl

theorem formAlternatingOrthogonals (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (U : Submodule K V) : formLeftOrthogonal B U = B.orthogonal U := by
  ext v
  change (∀ u ∈ U, B v u = 0) ↔ (∀ u ∈ U, B u v = 0)
  constructor <;> intro h u hu
  · exact ha.eq_iff.mp (h u hu)
  · exact ha.eq_iff.mp (h u hu)

def formRestrictedDual (B : LinearMap.BilinForm K V) (U : Submodule K V) : V →ₗ[K] Module.Dual K U :=
  U.dualRestrict.comp B

theorem formRestrictedDualApply (B : LinearMap.BilinForm K V) (U : Submodule K V) (v : V) (u : U) :
    formRestrictedDual B U v u = B v u := rfl

theorem formOrthogonalKernel (B : LinearMap.BilinForm K V) (U : Submodule K V) :
    LinearMap.ker (formRestrictedDual B U) = formLeftOrthogonal B U := by
  ext v
  simp [LinearMap.mem_ker, LinearMap.ext_iff, formRestrictedDualApply, formLeftOrthogonalMem]

theorem formRestrictionSurjective (U : Submodule K V) : Function.Surjective U.dualRestrict :=
  Subspace.dualRestrict_surjective

section Finite
variable [FiniteDimensional K V]

theorem formRestrictedDualSurjective (B : LinearMap.BilinForm K V) (hd : B.Nondegenerate)
    (U : Submodule K V) : Function.Surjective (formRestrictedDual B U) := by
  exact (formRestrictionSurjective U).comp (bilinearDualIso B hd).surjective

theorem formLeftOrthogonalDimension (B : LinearMap.BilinForm K V) (hd : B.Nondegenerate)
    (U : Submodule K V) : finrank K (formLeftOrthogonal B U) = finrank K V - finrank K U :=
  B.flip.finrank_orthogonal hd.flip U

theorem formRightOrthogonalDimension (B : LinearMap.BilinForm K V) (hd : B.Nondegenerate)
    (U : Submodule K V) : finrank K (B.orthogonal U) = finrank K V - finrank K U :=
  B.finrank_orthogonal hd U

theorem formRestrictedDualRank (B : LinearMap.BilinForm K V) (hd : B.Nondegenerate)
    (U : Submodule K V) : finrank K (LinearMap.range (formRestrictedDual B U)) = finrank K U := by
  rw [LinearMap.range_eq_top.mpr (formRestrictedDualSurjective B hd U), finrank_top,
    Subspace.dual_finrank_eq]

theorem formDirectOrthogonal (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (U : Submodule K V) (hU : (B.restrict U).Nondegenerate) : IsCompl U (B.orthogonal U) :=
  B.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hU

theorem formRestrictedAlternating (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (U : Submodule K V) : (B.restrict U).IsAlt := by intro x; exact ha x

theorem formComplementNondegenerate (B : LinearMap.BilinForm K V) (ha : B.IsAlt)
    (hd : B.Nondegenerate) (U : Submodule K V) (hU : (B.restrict U).Nondegenerate) :
    (B.restrict (B.orthogonal U)).Nondegenerate := by
  apply B.nondegenerate_restrict_of_disjoint_orthogonal ha.isRefl
  rw [B.orthogonal_orthogonal hd ha.isRefl U]
  exact (formDirectOrthogonal B ha U hU).disjoint.symm
end Finite

def symplecticStandardBlock : Matrix (Fin 2) (Fin 2) K := !![0,1;-1,0]

theorem symplecticStandardTranspose :
    (symplecticStandardBlock (K:=K))ᵀ = -symplecticStandardBlock := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplecticStandardBlock]

theorem symplecticStandardDet : (symplecticStandardBlock (K:=K)).det = 1 := by
  simp [symplecticStandardBlock, Matrix.det_fin_two]

noncomputable def symplecticStandardForm : LinearMap.BilinForm K (Fin 2 → K) :=
  bilinearFromMatrix symplecticStandardBlock

theorem symplecticStandardApply (x y : Fin 2 → K) :
    symplecticStandardForm x y = x 0 * y 1 - x 1 * y 0 := by
  simp [symplecticStandardForm, bilinearFromMatrixApply, symplecticStandardBlock,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem symplecticStandardAlternating : (symplecticStandardForm (K:=K)).IsAlt := by
  intro x; rw [symplecticStandardApply]; ring

theorem formCharTwoCounterexample :
    formSkew (LinearMap.mul (ZMod 2) (ZMod 2)) ∧
    (LinearMap.mul (ZMod 2) (ZMod 2)).IsSymm ∧
    ¬(LinearMap.mul (ZMod 2) (ZMod 2)).IsAlt := by
  constructor
  · intro x y; fin_cases x <;> fin_cases y <;> decide
  constructor
  · exact ⟨fun x y => mul_comm x y⟩
  · intro h; have := h 1; norm_num at this
end ILab.LinearAlgebra
