import ILab.LinearAlgebra.InnerProducts
import ILab.LinearAlgebra.DualSpaces
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Holstein §12.6. The source inner product is linear in its FIRST argument.
`holsteinInner x y = inner 𝕜 y x` is the verified convention bridge from §12.5.
The algebraic adjoint below is general in finite-dimensional real/complex inner
product spaces, not a numerical or merely square-matrix specialization.
The source's real duality statements are also proved over RCLike using the
explicit algebraic antidual. This extension does not identify ordinary complex
linear functionals with antilinear functionals. Browser code is not certified. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module
open scoped ComplexConjugate Matrix BigOperators
universe u v w z
variable {𝕜 : Type u} [RCLike 𝕜]
 {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
 {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
 {G : Type z} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

def holsteinAdjoint (f : E →ₗ[𝕜] F) : F →ₗ[𝕜] E := f.adjoint

theorem holsteinAdjointIdentity (f : E →ₗ[𝕜] F) (v : E) (w : F) :
 holsteinInner (𝕜 := 𝕜) w (f v) = holsteinInner (𝕜 := 𝕜) (holsteinAdjoint f w) v :=
 (LinearMap.adjoint_inner_right f v w).symm

theorem holsteinAdjointUnique (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] E)
 (h : ∀ v w, holsteinInner (𝕜 := 𝕜) w (f v) = holsteinInner (𝕜 := 𝕜) (g w) v) :
 g = holsteinAdjoint f := by
 apply (LinearMap.eq_adjoint_iff g f).mpr
 intro w v
 have hh := congrArg star (h v w)
 simpa only [holsteinInner,← starRingEnd_apply,inner_conj_symm] using hh.symm

theorem holsteinAdjointExistsUnique (f : E →ₗ[𝕜] F) :
 ∃! g : F →ₗ[𝕜] E, ∀ v w,
 holsteinInner (𝕜 := 𝕜) w (f v) = holsteinInner (𝕜 := 𝕜) (g w) v := by
 exact ⟨holsteinAdjoint f,holsteinAdjointIdentity f,fun g h => holsteinAdjointUnique f g h⟩

theorem holsteinAdjointReverseIdentity (f : E →ₗ[𝕜] F) (v : E) (w : F) :
 holsteinInner (𝕜 := 𝕜) (f v) w = holsteinInner (𝕜 := 𝕜) v (holsteinAdjoint f w) :=
 (LinearMap.adjoint_inner_left f v w).symm

theorem holsteinAdjointDouble (f : E →ₗ[𝕜] F) :
 holsteinAdjoint (holsteinAdjoint f) = f := LinearMap.adjoint_adjoint f

theorem holsteinAdjointComposition (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] G) :
 holsteinAdjoint (g.comp f) = (holsteinAdjoint f).comp (holsteinAdjoint g) :=
 LinearMap.adjoint_comp g f

theorem holsteinAdjointAdd (f g : E →ₗ[𝕜] F) :
 holsteinAdjoint (f+g) = holsteinAdjoint f + holsteinAdjoint g :=
 (LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)).map_add f g

theorem holsteinAdjointScalar (a : 𝕜) (f : E →ₗ[𝕜] F) :
 holsteinAdjoint (a • f) = star a • holsteinAdjoint f :=
 (LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)).map_smulₛₗ a f

theorem holsteinAdjointZero : holsteinAdjoint (0 : E →ₗ[𝕜] F) = 0 :=
 (LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)).map_zero

theorem holsteinAdjointONBMatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
 [DecidableEq ι] [DecidableEq κ]
 (a : OrthonormalBasis ι 𝕜 E) (b : OrthonormalBasis κ 𝕜 F) (f : E →ₗ[𝕜] F) :
 LinearMap.toMatrix b.toBasis a.toBasis (holsteinAdjoint f) =
 (LinearMap.toMatrix a.toBasis b.toBasis f).conjTranspose :=
 LinearMap.toMatrix_adjoint a b f

def holsteinAntidualPullback (f : E →ₗ[𝕜] F) : (F →ₗ⋆[𝕜] 𝕜) →ₗ[𝕜] (E →ₗ⋆[𝕜] 𝕜) where
 toFun l := l.comp f
 map_add' := by intros; rfl
 map_smul' := by intros; rfl

theorem holsteinAdjointDualDiagram (f : E →ₗ[𝕜] F) :
 (holsteinAntidualMap (𝕜 := 𝕜) (E := E)).comp (holsteinAdjoint f) =
 (holsteinAntidualPullback f).comp (holsteinAntidualMap (𝕜 := 𝕜) (E := F)) := by
 ext w v
 exact (holsteinAdjointIdentity f v w).symm

theorem holsteinAdjointViaAntidual (f : E →ₗ[𝕜] F) (w : F) :
 holsteinAdjoint f w = (holsteinAntidualEquiv (𝕜 := 𝕜) (E := E)).symm
 (holsteinAntidualPullback f (holsteinAntidualEquiv (𝕜 := 𝕜) (E := F) w)) := by
 apply (holsteinAntidualEquiv (𝕜 := 𝕜) (E := E)).injective
 rw [LinearEquiv.apply_symm_apply]
 exact LinearMap.congr_fun (holsteinAdjointDualDiagram f) w

/- Complex conjugation turns an ordinary linear functional into an antilinear
one. This map is conjugate-linear on the ordinary dual; it is linear when that
domain is equipped with the conjugated scalar action. -/
def holsteinConjugateFunctional (l : Module.Dual 𝕜 E) : E →ₗ⋆[𝕜] 𝕜 where
 toFun x := star (l x)
 map_add' := by intros; simp
 map_smul' := by intros; simp

theorem holsteinConjugateFunctionalScalar (a : 𝕜) (l : Module.Dual 𝕜 E) :
 holsteinConjugateFunctional (a • l) = star a • holsteinConjugateFunctional l := by
 ext x; simp [holsteinConjugateFunctional]

theorem holsteinConjugateFunctionalPullback (f : E →ₗ[𝕜] F) (l : Module.Dual 𝕜 F) :
 holsteinConjugateFunctional (l.comp f) = holsteinAntidualPullback f (holsteinConjugateFunctional l) := rfl

theorem holsteinONBDualEvaluation {ι : Type*} [Fintype ι] [DecidableEq ι]
 (b : OrthonormalBasis ι 𝕜 E) (i j : ι) :
 holsteinAntidualMap (𝕜 := 𝕜) (b i) (b j) = if i=j then 1 else 0 := by
 simp [holsteinAntidualMap,holsteinAntidualFunctional,holsteinInner,
   orthonormal_iff_ite.mp b.orthonormal,eq_comm]

theorem holsteinONBDualFunctional {ι : Type*} [Fintype ι] [DecidableEq ι]
 (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
 holsteinAntidualMap (𝕜 := 𝕜) (b i) =
 holsteinConjugateFunctional (b.toBasis.dualBasis i) := by
 ext v
 change holsteinInner (𝕜 := 𝕜) (b i) v = star ((b.toBasis.dualBasis i) v)
 rw [Module.Basis.dualBasis_apply,b.coe_toBasis_repr_apply,b.repr_apply_apply]
 exact (inner_conj_symm (𝕜 := 𝕜) v (b i)).symm

def holsteinAntidualAnnihilator (X : Set E) : Submodule 𝕜 (E →ₗ⋆[𝕜] 𝕜) where
 carrier := {l | ∀ x ∈ X, l x = 0}
 zero_mem' := by
  change ∀ x ∈ X, (0 : E →ₗ⋆[𝕜] 𝕜) x = 0
  intro x hx
  rfl
 add_mem' := by intro l m hl hm x hx; change l x + m x = 0; rw [hl x hx,hm x hx,add_zero]
 smul_mem' := by intro a l hl x hx; change a * l x = 0; rw [hl x hx,mul_zero]

theorem holsteinAnnihilatorComplement (X : Set E) :
 holsteinAntidualMap (𝕜 := 𝕜) '' (holsteinSetComplement (𝕜 := 𝕜) X : Set E) =
 (holsteinAntidualAnnihilator (𝕜 := 𝕜) X : Set (E →ₗ⋆[𝕜] 𝕜)) := by
 ext l
 constructor
 · rintro ⟨v,hv,rfl⟩ x hx
   change holsteinInner (𝕜 := 𝕜) v x = 0
   have h := hv x hx
   exact inner_eq_zero_symm.mp h
 · intro hl
   obtain ⟨v,rfl⟩ := holsteinAntidualSurjective (𝕜 := 𝕜) l
   refine ⟨v,?_,rfl⟩
   intro x hx
   exact inner_eq_zero_symm.mp (hl x hx)

theorem holsteinAdjointRange (f : E →ₗ[𝕜] F) :
 (holsteinAdjoint f).range = f.kerᗮ := (LinearMap.orthogonal_ker f).symm

theorem holsteinAdjointKernel (f : E →ₗ[𝕜] F) :
 (holsteinAdjoint f).ker = f.rangeᗮ := (LinearMap.orthogonal_range f).symm

theorem holsteinAdjointRank (f : E →ₗ[𝕜] F) :
 finrank 𝕜 (holsteinAdjoint f).range = finrank 𝕜 f.range := LinearMap.finrank_range_adjoint f

theorem holsteinFourSpacesSource (f : E →ₗ[𝕜] F) :
 IsCompl f.ker (holsteinAdjoint f).range := by
 rw [holsteinAdjointRange]
 exact f.ker.isCompl_orthogonal

theorem holsteinFourSpacesTarget (f : E →ₗ[𝕜] F) :
 IsCompl f.range (holsteinAdjoint f).ker := by
 rw [holsteinAdjointKernel]
 exact f.range.isCompl_orthogonal

section RectangularMatrices
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def holsteinMatrixAdjoint (A : Matrix m n ℂ) : Matrix n m ℂ := A.conjTranspose

theorem holsteinMatrixAdjointDouble (A : Matrix m n ℂ) :
 holsteinMatrixAdjoint (holsteinMatrixAdjoint A) = A := Matrix.conjTranspose_conjTranspose A

theorem holsteinMatrixAdjointScalar (a : ℂ) (A : Matrix m n ℂ) :
 holsteinMatrixAdjoint (a • A) = star a • holsteinMatrixAdjoint A :=
 Matrix.conjTranspose_smul _ _

theorem holsteinOrdinaryDualMatrix (a : Basis n 𝕜 E) (b : Basis m 𝕜 F) (f : E →ₗ[𝕜] F) :
 LinearMap.toMatrix b.dualBasis a.dualBasis f.dualMap = (LinearMap.toMatrix a b f).transpose := by
 exact LinearMap.toMatrix_transpose f

/- Weighted-coordinate extension: G is the invertible transpose of the source
Gram matrix. Keeping the unit explicit records the actual inverse hypothesis;
this algebraic formula is not a positivity-classification theorem. -/
def holsteinWeightedMatrixAdjoint (G : (Matrix n n ℂ)ˣ)
 (HW : Matrix m m ℂ) (A : Matrix m n ℂ) : Matrix n m ℂ :=
 (↑G⁻¹ : Matrix n n ℂ) * A.conjTranspose * HW.transpose

theorem holsteinWeightedMatrixCertificate (G : (Matrix n n ℂ)ˣ)
 (HW : Matrix m m ℂ) (A : Matrix m n ℂ) :
 (↑G : Matrix n n ℂ) * holsteinWeightedMatrixAdjoint G HW A =
 A.conjTranspose * HW.transpose := by
 simp [holsteinWeightedMatrixAdjoint,← Matrix.mul_assoc]

theorem holsteinWeightedMatrixUnique (G : (Matrix n n ℂ)ˣ)
 (HW : Matrix m m ℂ) (A : Matrix m n ℂ) (B : Matrix n m ℂ)
 (h : (↑G : Matrix n n ℂ) * B = A.conjTranspose * HW.transpose) :
 B = holsteinWeightedMatrixAdjoint G HW A := by
 calc
  B = (↑G⁻¹ : Matrix n n ℂ) * ((↑G : Matrix n n ℂ) * B) := by simp [← Matrix.mul_assoc]
  _ = holsteinWeightedMatrixAdjoint G HW A := by rw [h]; simp [holsteinWeightedMatrixAdjoint,Matrix.mul_assoc]

end RectangularMatrices

def adjointConcreteComplex : Matrix (Fin 2) (Fin 2) ℂ := !![1,Complex.I;2,1-Complex.I]
theorem adjointConcreteComplexValue : holsteinMatrixAdjoint adjointConcreteComplex =
 (!![1,2;-Complex.I,1+Complex.I] : Matrix (Fin 2) (Fin 2) ℂ) := by
 ext i j; fin_cases i <;> fin_cases j <;> simp [holsteinMatrixAdjoint,adjointConcreteComplex]

theorem adjointTransposeNotEnough : holsteinMatrixAdjoint adjointConcreteComplex ≠ adjointConcreteComplex.transpose := by
 intro h
 have hh := congrArg (fun M => M 1 0) h
 simp [holsteinMatrixAdjoint,adjointConcreteComplex] at hh
 have := congrArg Complex.im hh
 norm_num at this

end ILab.LinearAlgebra
