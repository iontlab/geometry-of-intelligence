import ILab.LinearAlgebra.SpectralTheorem
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-! Holstein §12.8. Source mistakes are retained in the native source only.
`holsteinInner x y = inner y x` is the existing first-linear convention.
General theorems below are separate from concrete browser calculations. -/
noncomputable section
set_option maxHeartbeats 800000
namespace ILab.LinearAlgebra
open Module Module.End
open scoped ComplexConjugate BigOperators Matrix
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
 [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

def HolsteinIsometry (f : Module.End 𝕜 E) : Prop :=
 ∀ x y, holsteinInner (𝕜 := 𝕜) (f x) (f y)=holsteinInner (𝕜 := 𝕜) x y

theorem isometryInnerIff (f : Module.End 𝕜 E) :
 HolsteinIsometry f ↔ ∀ x y, inner 𝕜 (f x) (f y)=inner 𝕜 x y := by
 constructor <;> intro h x y <;> exact h y x

theorem isometryAdjointIff (f : Module.End 𝕜 E) :
 HolsteinIsometry f ↔ f.adjoint*f=1 := by
 rw [isometryInnerIff]
 constructor
 · intro h; ext x
   apply ext_inner_right 𝕜
   intro y
   simpa only [Module.End.mul_apply,Module.End.one_apply,
    LinearMap.adjoint_inner_left] using h x y
 · intro h x y
   rw [← LinearMap.adjoint_inner_left]
   change inner 𝕜 ((f.adjoint*f) x) y = _
   rw [h]; rfl

def isometryLinear (f : Module.End 𝕜 E) (h : HolsteinIsometry f) : E →ₗᵢ[𝕜] E :=
 f.isometryOfInner ((isometryInnerIff f).mp h)

theorem isometryNormIff (f : Module.End 𝕜 E) :
 (∀ x, ‖f x‖=‖x‖) ↔ HolsteinIsometry f := by
 rw [isometryInnerIff]; exact LinearMap.norm_map_iff_inner_map_map f

theorem isometryInjective (f : Module.End 𝕜 E) (h : HolsteinIsometry f) :
 Function.Injective f := (isometryLinear f h).injective

theorem isometrySurjective (f : Module.End 𝕜 E) (h : HolsteinIsometry f) :
 Function.Surjective f := (LinearMap.injective_iff_surjective).mp (isometryInjective f h)

theorem isometryTwoSided (f : Module.End 𝕜 E) (h : HolsteinIsometry f) :
 f.adjoint*f=1 ∧ f*f.adjoint=1 := by
 have hl := (isometryAdjointIff f).mp h
 refine ⟨hl,?_⟩
 ext y
 obtain ⟨x,rfl⟩ := isometrySurjective f h y
 have hx := LinearMap.congr_fun hl x
 change f (f.adjoint (f x))=f x
 exact congrArg f hx

theorem isometryNormal (f : Module.End 𝕜 E) (h : HolsteinIsometry f) :
 HolsteinNormal f := by
 obtain ⟨hl,hr⟩ := isometryTwoSided f h
 exact hr.trans hl.symm

theorem isometryAdjointIsometry (f : Module.End 𝕜 E) (h : HolsteinIsometry f) :
 HolsteinIsometry f.adjoint := by
 rw [isometryAdjointIff,LinearMap.adjoint_adjoint]
 exact (isometryTwoSided f h).2

theorem isometryCompose (f g : Module.End 𝕜 E) (hf : HolsteinIsometry f)
 (hg : HolsteinIsometry g) : HolsteinIsometry (f*g) := by
 intro x y; change holsteinInner (f (g x)) (f (g y))=_
 rw [hf,hg]

theorem isometryOrthogonal (f : Module.End 𝕜 E) (hf : HolsteinIsometry f) (x y : E) :
 holsteinInner (𝕜 := 𝕜) (f x) (f y)=0 ↔ holsteinInner (𝕜 := 𝕜) x y=0 := by rw [hf]

theorem isometryEigenvalue (f : Module.End 𝕜 E) (hf : HolsteinIsometry f)
 {a : 𝕜} {v : E} (hv : v≠0) (he : f v=a • v) : ‖a‖=1 := by
 have h := (isometryLinear f hf).norm_map v
 change ‖f v‖=‖v‖ at h
 rw [he,norm_smul] at h
 have hp : 0<‖v‖ := norm_pos_iff.mpr hv
 nlinarith

theorem isometrySymmetrization (f : Module.End 𝕜 E) :
 HolsteinSelfAdjoint (f+f.adjoint) := by
 unfold HolsteinSelfAdjoint; simp [add_comm]

theorem isometryUnitaryONB {V : Type*} [NormedAddCommGroup V]
 [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
 (f : Module.End ℂ V) (hf : HolsteinIsometry f) :
 ∃ b : OrthonormalBasis (Fin (finrank ℂ V)) ℂ V,
 ∃ a : Fin (finrank ℂ V) → ℂ, ∀ i, f (b i)=a i • b i := by
 apply spectralNormalONB f (isometryNormal f hf)
 exact IsAlgClosed.splits _

section Matrices
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem isometryUnitaryMatrix (M : Matrix n n ℂ) :
 M ∈ Matrix.unitaryGroup n ℂ ↔ M*M.conjTranspose=1 :=
 Matrix.mem_unitaryGroup_iff

theorem isometryUnitaryBoth (M : Matrix n n ℂ) :
 M*M.conjTranspose=1 ↔ M.conjTranspose*M=1 := by
 change M*star M=1 ↔ star M*M=1
 rw [←Matrix.mem_unitaryGroup_iff,←Matrix.mem_unitaryGroup_iff']

theorem isometryOrthogonalMatrix (M : Matrix n n ℝ) :
 M ∈ Matrix.orthogonalGroup n ℝ ↔ M*M.transpose=1 :=
 Matrix.mem_orthogonalGroup_iff n ℝ

theorem isometrySpecialUnitary (M : Matrix n n ℂ) :
 M ∈ Matrix.specialUnitaryGroup n ℂ ↔ M ∈ Matrix.unitaryGroup n ℂ ∧ M.det=1 :=
 Matrix.mem_specialUnitaryGroup_iff

theorem isometrySpecialOrthogonal (M : Matrix n n ℝ) :
 M ∈ Matrix.specialOrthogonalGroup n ℝ ↔ M ∈ Matrix.orthogonalGroup n ℝ ∧ M.det=1 :=
 Matrix.mem_specialOrthogonalGroup_iff

theorem isometryUnitaryProduct (A B : Matrix.unitaryGroup n ℂ) :
 (A*B).val=A.val*B.val := rfl

theorem isometryUnitaryInverse (A : Matrix.unitaryGroup n ℂ) :
 (A⁻¹).val=A.val.conjTranspose := rfl

theorem isometryDeterminant (M : Matrix n n ℂ) (h : M ∈ Matrix.unitaryGroup n ℂ) :
 M.det*conj M.det=1 := by
 have hd := congrArg Matrix.det ((isometryUnitaryMatrix M).mp h)
 simpa [Matrix.det_mul,Matrix.det_conjTranspose] using hd

theorem isometrySpecialUnitaryLe :
 Matrix.specialUnitaryGroup n ℂ ≤ Matrix.unitaryGroup n ℂ :=
 Matrix.specialUnitaryGroup_le_unitaryGroup

theorem isometryONBChange (a b : OrthonormalBasis n 𝕜 E) :
 a.toBasis.toMatrix b ∈ Matrix.unitaryGroup n 𝕜 :=
 a.toMatrix_orthonormalBasis_mem_unitary b

theorem isometryCongruenceOrthogonal (M T : Matrix n n ℝ)
 (h : T.transpose=T⁻¹) : T.transpose*M*T=T⁻¹*M*T := by rw [h]

theorem isometryComplexFormMatrix (M U : Matrix n n ℂ) :
 (U.map conj).transpose*M*(U.map conj).map conj=U.conjTranspose*M*U := by
 simp [Matrix.conjTranspose,Matrix.map_map,Function.comp_def,Matrix.transpose_map]

/-- A certificate for a computed normal form, not the general existence theorem. -/
theorem isometryBlockReconstruction (M Q B : Matrix n n ℝ)
 (hq : Q.transpose*Q=1) (hb : Q.transpose*M*Q=B) : Q*B*Q.transpose=M := by
 have hr : Q*Q.transpose=1 := mul_eq_one_comm.mp hq
 rw [←hb]
 calc
  Q*(Q.transpose*M*Q)*Q.transpose=(Q*Q.transpose)*M*(Q*Q.transpose) := by noncomm_ring
  _=M := by rw [hr]; simp
end Matrices

section Real
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
 [FiniteDimensional ℝ V]

theorem isometryHouseholderExists (v w : V) (h : ‖v‖=‖w‖) :
 ∃ f : V ≃ₗᵢ[ℝ] V, f v=w := by
 exact ⟨(ℝ ∙ (v-w))ᗮ.reflection,Submodule.reflection_sub h⟩

theorem isometryReflectionNorm (U : Submodule ℝ V) (v : V) :
 ‖U.reflection v‖=‖v‖ := U.reflection.norm_map v

theorem isometryReflectionSquare (U : Submodule ℝ V) (v : V) :
 U.reflection (U.reflection v)=v := U.reflection_reflection v

theorem isometryReflectionProducts (f : V ≃ₗᵢ[ℝ] V) :
 ∃ l : List V, l.length ≤ finrank ℝ V ∧
 f=(l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod := f.reflections_generate_dim

theorem isometryHouseholderFormula (u z : V) (hu : u≠0) :
 (ℝ ∙ u)ᗮ.reflection z = z-(2*(inner ℝ z u)/(‖u‖^2)) • u := by
 rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
 simp only [neg_sub]
 congr 1
 rw [two_smul,←add_smul]
 congr 1
 simp only [RCLike.ofReal_real_eq_id, id_eq]
 rw [real_inner_comm u z]
 ring

theorem isometryInvariantPerp (f : Module.End ℝ V) (hf : HolsteinIsometry f)
 (W : Submodule ℝ V) (hW : ∀ x∈W, f x∈W) :
 ∀ x∈Wᗮ, f x∈Wᗮ := by
 have hs : Set.SurjOn f W W := (LinearMap.injOn_iff_surjOn hW).mp
  (fun x _ y _ h => isometryInjective f hf h)
 intro x hx
 rw [Submodule.mem_orthogonal] at hx ⊢
 intro w hw
 obtain ⟨v,hv,rfl⟩ := hs hw
 exact ((isometryInnerIff f).mp hf v x).trans (hx v hv)

theorem isometrySmallBlockRelation (f : Module.End ℝ V) (hf : HolsteinIsometry f)
 (b : V) (a : ℝ) (hb : (f+f.adjoint) b=a • b) :
 f (f b)=a • f b-b := by
 have h := congrArg f hb
 have hr := LinearMap.congr_fun (isometryTwoSided f hf).2 b
 change f (f.adjoint b)=b at hr
 simp only [LinearMap.add_apply,map_add,map_smul,hr] at h
 exact eq_sub_of_add_eq h

theorem isometryGeneratedBlockInvariant (f : Module.End ℝ V)
 (hf : HolsteinIsometry f) (b : V) (a : ℝ) (hb : (f+f.adjoint) b=a • b) :
 ∀ x∈Submodule.span ℝ ({b,f b} : Set V),
 f x∈Submodule.span ℝ ({b,f b} : Set V) := by
 intro x hx
 refine Submodule.span_induction (fun y hy => ?_) ?_ ?_ ?_ hx
 · rcases hy with rfl|h
   · exact Submodule.subset_span (by simp)
   · have hy : y=f b := by simpa using h
     rw [hy,isometrySmallBlockRelation f hf b a hb]
     exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))
 · simp
 · intro x y _ _ hx hy; simpa using Submodule.add_mem _ hx hy
 · intro c x _ hx; simpa using Submodule.smul_mem _ c hx

/-- A genuinely arbitrary input function; linearity is not a hypothesis.
The proof by inner-product expansion works even without surjectivity. -/
def isometryFromInner (f : V → V)
 (h : ∀ x y, inner ℝ (f x) (f y)=inner ℝ x y) : V →ₗ[ℝ] V where
 toFun := f
 map_add' x y := by
  have hz : inner ℝ (f (x+y)-f x-f y) (f (x+y)-f x-f y)=0 := by
   simp only [inner_sub_left,inner_sub_right,h,inner_add_left,inner_add_right]
   ring
  have hz' : f (x+y)-f x-f y=0 := inner_self_eq_zero.mp hz
  exact sub_eq_zero.mp (by simpa [sub_sub] using hz')
 map_smul' a x := by
  have hz : inner ℝ (f (a • x)-a • f x) (f (a • x)-a • f x)=0 := by
   simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,h,
    RCLike.conj_to_real]
   ring
  simpa using sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem isometryArbitraryLinear (f : V → V)
 (h : ∀ x y, inner ℝ (f x) (f y)=inner ℝ x y) :
 ∃ g : V →ₗ[ℝ] V, ∀ x, g x=f x := ⟨isometryFromInner f h,fun _ => rfl⟩

theorem isometryTranslationDistance (x y a : V) : dist (x+a) (y+a)=dist x y :=
 dist_add_right x y a

theorem isometryAffineDistance (A : V ≃ₗᵢ[ℝ] V) (a x y : V) :
 dist (A x+a) (A y+a)=dist x y := by
 rw [dist_add_right,A.dist_map]

theorem isometryAffineCompose (A B : V →ₗ[ℝ] V) (a b x : V) :
 A (B x+b)+a=(A*B) x+(A b+a) := by simp [Module.End.mul_apply,add_assoc]
end Real

def isometryRotation (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
 !![Real.cos t,-Real.sin t;Real.sin t,Real.cos t]
def isometryMirror (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
 !![Real.cos t,Real.sin t;Real.sin t,-Real.cos t]
def isometryComplexPlane (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
 !![z.re,-z.im;z.im,z.re]

theorem isometryRotationSO (t : ℝ) :
 isometryRotation t ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
 rw [isometryRotation,Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
 refine ⟨rfl,by ring,?_⟩
 nlinarith [Real.sin_sq_add_cos_sq t]

theorem isometryMirrorOrthogonal (t : ℝ) :
 isometryMirror t * (isometryMirror t).transpose=1 := by
 ext i j; fin_cases i <;> fin_cases j <;>
  simp [isometryMirror,Matrix.mul_apply,Fin.sum_univ_two] <;>
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem isometryMirrorDet (t : ℝ) : (isometryMirror t).det = -1 := by
 simp [isometryMirror,Matrix.det_fin_two]
 nlinarith [Real.sin_sq_add_cos_sq t]

theorem isometryComplexPlaneMul (z w : ℂ) :
 isometryComplexPlane (z*w)=isometryComplexPlane z*isometryComplexPlane w := by
 ext i j; fin_cases i <;> fin_cases j <;>
  simp [isometryComplexPlane,Matrix.mul_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im] <;> ring

theorem isometryComplexPlaneSO (z : ℂ) (h : Complex.normSq z=1) :
 isometryComplexPlane z ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
 rw [isometryComplexPlane,Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
 refine ⟨rfl,by ring,?_⟩
 simpa [Complex.normSq_apply,pow_two] using h

def isometrySpaceRotation (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
 !![1,0,0;0,Real.cos t,-Real.sin t;0,Real.sin t,Real.cos t]

theorem isometrySpaceRotationOrthogonal (t : ℝ) :
 isometrySpaceRotation t * (isometrySpaceRotation t).transpose=1 := by
 ext i j; fin_cases i <;> fin_cases j <;>
  simp [isometrySpaceRotation,Matrix.mul_apply,Fin.sum_univ_succ] <;>
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem isometrySpaceRotationDet (t : ℝ) : (isometrySpaceRotation t).det=1 := by
 simp [isometrySpaceRotation,Matrix.det_fin_three]
 nlinarith [Real.sin_sq_add_cos_sq t]

/-- One real completion-of-square step, explicitly not the full classification. -/
theorem isometryCompleteSquare (a b c x : ℝ) (ha : a≠0) :
 a*(x-b/(2*a))^2+b*(x-b/(2*a))+c = a*x^2+c-b^2/(4*a) := by
 field_simp
 <;> ring

theorem isometryQuadAffineOne (a b c s t x : ℝ) :
 a*(s*x+t)^2+b*(s*x+t)+c = (a*s^2)*x^2+(2*a*s*t+b*s)*x+(a*t^2+b*t+c) := by ring

theorem isometryEquationScale (q : ℝ) (s : ℝ) (hs : s≠0) : s*q=0 ↔ q=0 := by
 rw [mul_eq_zero]; simp [hs]

theorem isometryTranslationNotLinear (a : ℝ) (ha : a≠0) :
 ¬ ∃ f : ℝ →ₗ[ℝ] ℝ, ∀ x, f x=x+a := by
 rintro ⟨f,h⟩
 have hz := h 0
 simpa using (ha (by simpa using hz.symm))
end ILab.LinearAlgebra
