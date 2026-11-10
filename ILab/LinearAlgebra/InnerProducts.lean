import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Holstein §12.5: linear FIRST, conjugate-linear SECOND.
Mathlib's inner product has the opposite convention; `holsteinInner (𝕜 := 𝕜)` swaps
the arguments. Finite dimensionality in the complement theorem is explicit:
the unrestricted printed statement 12.5.18 is not valid for every pre-Hilbert
space. No browser implementation is certified by these mathematical proofs. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module InnerProductSpace
open scoped ComplexConjugate BigOperators
universe u v
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
 [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def holsteinInner (x y : E) : 𝕜 := inner 𝕜 y x

theorem holsteinInnerAddFirst (x y z : E) :
 holsteinInner (𝕜 := 𝕜) (x+y) z = holsteinInner (𝕜 := 𝕜) x z + holsteinInner (𝕜 := 𝕜) y z := inner_add_right _ _ _

theorem holsteinInnerAddSecond (x y z : E) :
 holsteinInner (𝕜 := 𝕜) x (y+z) = holsteinInner (𝕜 := 𝕜) x y + holsteinInner (𝕜 := 𝕜) x z := inner_add_left _ _ _

theorem holsteinInnerLinearFirst (a : 𝕜) (x y : E) :
 holsteinInner (𝕜 := 𝕜) (a • x) y = a * holsteinInner (𝕜 := 𝕜) x y := inner_smul_right _ _ _

theorem holsteinInnerAntilinearSecond (a : 𝕜) (x y : E) :
 holsteinInner (𝕜 := 𝕜) x (a • y) = star a * holsteinInner (𝕜 := 𝕜) x y := inner_smul_left _ _ _

theorem holsteinInnerHermitian (x y : E) :
 star (holsteinInner (𝕜 := 𝕜) y x) = holsteinInner (𝕜 := 𝕜) x y := inner_conj_symm _ _

theorem holsteinInnerSelf (x : E) :
 holsteinInner (𝕜 := 𝕜) x x = (‖x‖ : 𝕜)^2 := inner_self_eq_norm_sq_to_K x

theorem holsteinInnerDefinite (x : E) : holsteinInner (𝕜 := 𝕜) x x = 0 ↔ x = 0 := inner_self_eq_zero

theorem holsteinCauchySchwarz (x y : E) :
 ‖holsteinInner (𝕜 := 𝕜) x y‖ ≤ ‖x‖ * ‖y‖ := by
 simpa [holsteinInner,mul_comm] using norm_inner_le_norm y x

theorem holsteinCauchySchwarzSquared (x y : E) :
 ‖holsteinInner (𝕜 := 𝕜) x y‖^2 ≤ ‖x‖^2 * ‖y‖^2 := by
 have h := holsteinCauchySchwarz (𝕜 := 𝕜) x y
 have hn := norm_nonneg (holsteinInner (𝕜 := 𝕜) x y)
 have hp : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
 nlinarith

theorem holsteinCauchySchwarzEquality (x y : E) :
 ‖holsteinInner (𝕜 := 𝕜) x y‖ = ‖x‖ * ‖y‖ ↔ y = 0 ∨ ∃ a : 𝕜, x = a • y := by
 have ht : ‖inner 𝕜 y x‖ = ‖y‖ * ‖x‖ ↔ y = 0 ∨ ∃ a : 𝕜, x = a • y := (norm_inner_eq_norm_tfae 𝕜 y x).out 1 3
 simpa [holsteinInner,mul_comm] using ht

theorem holsteinNormHomogeneous (a : 𝕜) (x : E) : ‖a • x‖ = ‖a‖ * ‖x‖ := norm_smul _ _
theorem holsteinNormTriangle (x y : E) : ‖x+y‖ ≤ ‖x‖+‖y‖ := norm_add_le _ _
theorem holsteinNormZero (x : E) : ‖x‖ = 0 ↔ x = 0 := norm_eq_zero

theorem holsteinInnerNondegenerate (v : E)
 (hv : ∀ w, holsteinInner (𝕜 := 𝕜) v w = 0) : v = 0 :=
 (holsteinInnerDefinite (𝕜 := 𝕜) v).mp (hv v)

def holsteinOrthonormalFamily {ι : Type*} (v : ι → E) : Prop := Orthonormal 𝕜 v

def holsteinOrthogonal (x y : E) : Prop := holsteinInner (𝕜 := 𝕜) x y = 0

theorem holsteinOrthogonalSymm (x y : E) :
 holsteinOrthogonal (𝕜 := 𝕜) x y ↔ holsteinOrthogonal (𝕜 := 𝕜) y x := by
 simp only [holsteinOrthogonal,holsteinInner,inner_eq_zero_symm]

def holsteinComplement (U : Submodule 𝕜 E) : Submodule 𝕜 E := Uᗮ

theorem holsteinComplementMem (U : Submodule 𝕜 E) (v : E) :
 v ∈ holsteinComplement U ↔ ∀ u ∈ U, holsteinInner (𝕜 := 𝕜) v u = 0 := Submodule.mem_orthogonal U v

theorem holsteinComplementDisjoint (U : Submodule 𝕜 E) :
 Disjoint U (holsteinComplement U) := U.orthogonal_disjoint

theorem holsteinComplementSum [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) :
 IsCompl U (holsteinComplement U) := U.isCompl_orthogonal

theorem holsteinComplementDimension [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) :
 finrank 𝕜 U + finrank 𝕜 (holsteinComplement U) = finrank 𝕜 E := U.finrank_add_finrank_orthogonal

def holsteinProjection [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) : E →ₗ[𝕜] E :=
 U.starProjection.toLinearMap

theorem holsteinProjectionFixed [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) (x : E) :
 holsteinProjection U x = x ↔ x ∈ U := Submodule.starProjection_eq_self_iff

theorem holsteinProjectionResidual [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) (x : E) :
 x-holsteinProjection U x ∈ holsteinComplement U := U.sub_starProjection_mem_orthogonal x

theorem holsteinProjectionDecomposition [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) (x : E) :
 holsteinProjection U x + holsteinProjection (holsteinComplement U) x = x :=
 U.starProjection_add_starProjection_orthogonal x

theorem holsteinProjectionIdempotent [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) (x : E) :
 holsteinProjection U (holsteinProjection U x) = holsteinProjection U x := by
 exact congrArg (fun T : E →L[𝕜] E => T x) U.isIdempotentElem_starProjection

theorem holsteinProjectionBest [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) (x : E) :
 ‖x-holsteinProjection U x‖ = ⨅ u : U, ‖x-(u:E)‖ := U.starProjection_minimal x

theorem holsteinProjectionUnit [FiniteDimensional 𝕜 E] (b v : E) (hb : ‖b‖ = 1) :
 holsteinProjection (𝕜 ∙ b) v = holsteinInner (𝕜 := 𝕜) v b • b :=
 Submodule.starProjection_unit_singleton 𝕜 hb v

def holsteinOrthonormalBasis [FiniteDimensional 𝕜 E] :
 OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := stdOrthonormalBasis 𝕜 E

theorem holsteinOrthonormalIndependent {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) :
 LinearIndependent 𝕜 v := hv.linearIndependent

theorem holsteinOrthonormalCoordinates {ι : Type*} [Fintype ι]
 (b : OrthonormalBasis ι 𝕜 E) (v : E) : ∑ i, holsteinInner (𝕜 := 𝕜) v (b i) • b i = v := by
 simpa only [holsteinInner,← b.repr_apply_apply] using b.sum_repr v

def holsteinGramSchmidt {n : ℕ} (v : Fin n → E) : Fin n → E := gramSchmidt 𝕜 v

theorem holsteinGramSchmidtNonzero {n : ℕ} (v : Fin n → E)
 (hv : LinearIndependent 𝕜 v) (i : Fin n) : holsteinGramSchmidt (𝕜 := 𝕜) v i ≠ 0 :=
 gramSchmidt_ne_zero i hv

theorem holsteinGramSchmidtOrthogonal {n : ℕ} (v : Fin n → E) {i j : Fin n} (h : i ≠ j) :
 holsteinInner (𝕜 := 𝕜) (holsteinGramSchmidt (𝕜 := 𝕜) v i) (holsteinGramSchmidt (𝕜 := 𝕜) v j) = 0 :=
 gramSchmidt_orthogonal 𝕜 v h.symm

theorem holsteinGramSchmidtSpan {n : ℕ} (v : Fin n → E) :
 Submodule.span 𝕜 (Set.range (holsteinGramSchmidt (𝕜 := 𝕜) v)) = Submodule.span 𝕜 (Set.range v) :=
 span_gramSchmidt 𝕜 v

theorem holsteinGramSchmidtFormula {n : ℕ} (v : Fin n → E) (j : Fin n) :
 v j = holsteinGramSchmidt (𝕜 := 𝕜) v j + ∑ i ∈ Finset.Iio j,
 (holsteinInner (𝕜 := 𝕜) (v j) (holsteinGramSchmidt (𝕜 := 𝕜) v i) / (‖holsteinGramSchmidt (𝕜 := 𝕜) v i‖ : 𝕜)^2) •
 holsteinGramSchmidt (𝕜 := 𝕜) v i := gramSchmidt_def'' 𝕜 v j

def holsteinGramSchmidtNormed {n : ℕ} (v : Fin n → E) : Fin n → E := gramSchmidtNormed 𝕜 v

theorem holsteinGramSchmidtOrthonormal {n : ℕ} (v : Fin n → E) (hv : LinearIndependent 𝕜 v) :
 Orthonormal 𝕜 (holsteinGramSchmidtNormed (𝕜 := 𝕜) v) := gramSchmidtNormed_orthonormal hv

theorem holsteinGramSchmidtNormedSpan {n : ℕ} (v : Fin n → E) :
 Submodule.span 𝕜 (Set.range (holsteinGramSchmidtNormed (𝕜 := 𝕜) v)) = Submodule.span 𝕜 (Set.range v) := by
 exact (span_gramSchmidtNormed_range v).trans (span_gramSchmidt 𝕜 v)

/- Antilinear functionals on E are precisely linear functionals on its
conjugate scalar module. This representation avoids choosing a basis. -/
def holsteinAntidualFunctional (v : E) : E →ₗ⋆[𝕜] 𝕜 where
 toFun w := holsteinInner (𝕜 := 𝕜) v w
 map_add' w z := holsteinInnerAddSecond v w z
 map_smul' a w := by exact holsteinInnerAntilinearSecond a v w

def holsteinAntidualMap : E →ₗ[𝕜] (E →ₗ⋆[𝕜] 𝕜) where
 toFun := holsteinAntidualFunctional
 map_add' x y := by ext z; exact holsteinInnerAddFirst x y z
 map_smul' a x := by ext z; exact holsteinInnerLinearFirst a x z

theorem holsteinAntidualInjective : Function.Injective (holsteinAntidualMap (𝕜 := 𝕜) (E := E)) := by
 intro x y hh
 have h := LinearMap.congr_fun hh (x-y)
 change inner 𝕜 (x-y) x = inner 𝕜 (x-y) y at h
 have hz : inner 𝕜 (x-y) (x-y) = 0 := by rw [inner_sub_right,h,sub_self]
 exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem holsteinAntidualSurjective [FiniteDimensional 𝕜 E] :
 Function.Surjective (holsteinAntidualMap (𝕜 := 𝕜) (E := E)) := by
 let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
 intro l
 let g : E →ₗ[𝕜] 𝕜 :=
  { toFun := fun w => star (l w)
    map_add' := by intro x y; simp
    map_smul' := by intro a x; simp }
 obtain ⟨v,hv⟩ := (InnerProductSpace.toDual 𝕜 E).surjective (LinearMap.toContinuousLinearMap g)
 refine ⟨v,?_⟩
 ext w
 have hw := congrArg (fun F : StrongDual 𝕜 E => F w) hv
 change inner 𝕜 v w = star (l w) at hw
 change inner 𝕜 w v = l w
 rw [← inner_conj_symm,hw]
 simp

def holsteinAntidualEquiv [FiniteDimensional 𝕜 E] : E ≃ₗ[𝕜] (E →ₗ⋆[𝕜] 𝕜) :=
 LinearEquiv.ofBijective holsteinAntidualMap ⟨holsteinAntidualInjective,holsteinAntidualSurjective⟩

theorem holsteinProjectionFormula [FiniteDimensional 𝕜 E] {ι : Type*} [Fintype ι]
 (U : Submodule 𝕜 E) (b : OrthonormalBasis ι 𝕜 U) (v : E) :
 holsteinProjection U v = ∑ i, holsteinInner (𝕜 := 𝕜) v (b i : E) • (b i : E) := by
 change U.subtype (U.orthogonalProjectionOnto v) = _
 have h := congrArg U.subtype (b.orthogonalProjectionOnto_apply_eq_sum v)
 simpa only [map_sum,map_smul,Submodule.subtype_apply,holsteinInner] using h

theorem holsteinProjectionSelfAdjoint [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) (v w : E) :
 holsteinInner (𝕜 := 𝕜) (holsteinProjection U v) w =
 holsteinInner (𝕜 := 𝕜) v (holsteinProjection U w) :=
 (U.inner_starProjection_left_eq_right w v).symm

def holsteinSetComplement (X : Set E) : Submodule 𝕜 E where
 carrier := {y | ∀ x ∈ X, holsteinInner (𝕜 := 𝕜) x y = 0}
 zero_mem' := by intro x hx; simp [holsteinInner]
 add_mem' := by intro y z hy hz x hx; rw [holsteinInnerAddSecond,hy x hx,hz x hx,add_zero]
 smul_mem' := by intro a y hy x hx; rw [holsteinInnerAntilinearSecond,hy x hx,mul_zero]

theorem holsteinSetComplementMem (X : Set E) (v : E) :
 v ∈ holsteinSetComplement (𝕜 := 𝕜) X ↔ ∀ x ∈ X, holsteinInner (𝕜 := 𝕜) x v = 0 := Iff.rfl

theorem holsteinCauchySchwarzSquaredEquality (x y : E) :
 ‖holsteinInner (𝕜 := 𝕜) x y‖^2 = ‖x‖^2 * ‖y‖^2 ↔ y = 0 ∨ ∃ a : 𝕜, x = a • y := by
 rw [← holsteinCauchySchwarzEquality (𝕜 := 𝕜)]
 have hn := norm_nonneg (holsteinInner (𝕜 := 𝕜) x y)
 have hp : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
 constructor <;> intro h <;> nlinarith

def holsteinStandardReal {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
 holsteinInner (𝕜 := ℝ) v w

theorem holsteinStandardRealFormula {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
 holsteinStandardReal v w = ∑ i, v i * w i := by
 simp [holsteinStandardReal,holsteinInner,EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

def holsteinStandardComplex {n : ℕ} (v w : EuclideanSpace ℂ (Fin n)) : ℂ :=
 holsteinInner (𝕜 := ℂ) v w

theorem holsteinStandardComplexFormula {n : ℕ} (v w : EuclideanSpace ℂ (Fin n)) :
 holsteinStandardComplex v w = ∑ i, v i * star (w i) := by
 simp [holsteinStandardComplex,holsteinInner,EuclideanSpace.inner_eq_star_dotProduct,dotProduct]

theorem holsteinSinCosIntegral : ∫ t in (0:ℝ)..Real.pi, Real.sin t * Real.cos t = 0 := by
 rw [integral_sin_mul_cos₁]
 simp

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
def holsteinMatrixProduct (H : Matrix n n ℂ) (v w : n → ℂ) : ℂ := v ⬝ᵥ H.mulVec (star w)
def holsteinMatrixChange (H S : Matrix n n ℂ) : Matrix n n ℂ := S.transpose * H * S.map star

theorem holsteinMatrixCoordinates (H S : Matrix n n ℂ) (v w : n → ℂ) :
 holsteinMatrixProduct H (S.mulVec v) (S.mulVec w) =
 holsteinMatrixProduct (holsteinMatrixChange H S) v w := by
 classical
 have hs : star (S.mulVec w) = (S.map star).mulVec (star w) := by
  ext i
  simp [Matrix.mulVec,dotProduct,star_sum,star_mul,mul_comm]
 unfold holsteinMatrixProduct holsteinMatrixChange
 rw [hs,Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,
   ← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec]

theorem holsteinMatrixHermitianChange (H S : Matrix n n ℂ) (h : H.IsHermitian) :
 (holsteinMatrixChange H S).IsHermitian := by
 have hs : (S.map star).conjTranspose = S.transpose := by ext i j; simp
 have ht : S.transpose.conjTranspose = S.map star := by ext i j; simp
 unfold holsteinMatrixChange
 change (S.transpose * H * S.map star).conjTranspose = _
 rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hs,ht,h.eq]
 exact (Matrix.mul_assoc _ _ _).symm

end Matrix

section Concrete
def innerOriginalVectors : Matrix (Fin 3) (Fin 3) ℚ := !![1,1,1;1,1,0;1,0,0]
def innerOriginalRests : Matrix (Fin 3) (Fin 3) ℚ := !![1,1/3,1/2;1,1/3,-1/2;1,-2/3,0]
theorem innerOriginalGram : innerOriginalRests.transpose * innerOriginalRests =
 (!![3,0,0;0,2/3,0;0,0,1/2] : Matrix (Fin 3) (Fin 3) ℚ) := by
 decide +kernel
theorem innerOriginalSecondResidual :
 (![1,1,0] : Fin 3 → ℚ) - (2/3:ℚ) • ![1,1,1] = ![1/3,1/3,-2/3] := by
 ext i; fin_cases i <;> norm_num
theorem innerOriginalThirdResidual :
 (![1,0,0] : Fin 3 → ℚ) - (1/3:ℚ) • ![1,1,1] - (1/2:ℚ) • ![1/3,1/3,-2/3] = ![1/2,-1/2,0] := by
 ext i; fin_cases i <;> norm_num
theorem innerComplexBilinearNotPositive : Complex.I * Complex.I = -1 := Complex.I_mul_I
end Concrete

end ILab.LinearAlgebra
