import ILab.LinearAlgebra.Adjoints
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Tactic

/-! Holstein §12.7. `holsteinInner x y = inner y x` preserves the first-linear
source convention. General finite-dimensional RCLike spaces, not a matrix-only
replacement. Original typographical errors are documented outside this file. -/
noncomputable section
set_option maxHeartbeats 700000
namespace ILab.LinearAlgebra
open Module Module.End
open scoped ComplexConjugate BigOperators Matrix
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
 [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

def HolsteinSelfAdjoint (f : Module.End 𝕜 E) : Prop := f.adjoint = f
def HolsteinNormal (f : Module.End 𝕜 E) : Prop := f * f.adjoint = f.adjoint * f

theorem spectralSelfAdjointIff (f : Module.End 𝕜 E) :
 HolsteinSelfAdjoint f ↔ f.IsSymmetric := by
 rw [LinearMap.isSymmetric_iff_isSelfAdjoint,LinearMap.isSelfAdjoint_iff']
 rfl

theorem spectralSelfAdjointNormal (f : Module.End 𝕜 E) (h : HolsteinSelfAdjoint f) :
 HolsteinNormal f := by unfold HolsteinNormal; rw [h]

theorem spectralRealEigenvalue (f : Module.End 𝕜 E) (h : HolsteinSelfAdjoint f)
 {a : 𝕜} (ha : f.HasEigenvalue a) : conj a = a :=
 ((spectralSelfAdjointIff f).mp h).conj_eigenvalue_eq_self ha

/-- The original eigenvalue assertion does not require finite dimension. -/
theorem spectralRealEigenvalueGeneral {V : Type*} [NormedAddCommGroup V]
 [InnerProductSpace 𝕜 V] (f : Module.End 𝕜 V) (h : f.IsSymmetric)
 {a : 𝕜} (ha : f.HasEigenvalue a) : conj a=a := h.conj_eigenvalue_eq_self ha

theorem spectralSkewNormal (f : Module.End 𝕜 E) (h : f.adjoint = -f) :
 HolsteinNormal f := by unfold HolsteinNormal; rw [h]; simp

theorem spectralInverseNormal (f g : Module.End 𝕜 E) (h : f.adjoint = g)
 (hl : g*f=1) (hr : f*g=1) : HolsteinNormal f := by
 unfold HolsteinNormal; rw [h,hl,hr]

theorem spectralShiftAdjoint (f : Module.End 𝕜 E) (a : 𝕜) :
 (f-a • 1).adjoint = f.adjoint-conj a • 1 := by
 have hi : (1 : Module.End 𝕜 E).adjoint=1 := LinearMap.IsSymmetric.id.adjoint_eq
 rw [map_sub,map_smulₛₗ,hi]

theorem spectralShiftNormal (f : Module.End 𝕜 E) (h : HolsteinNormal f) (a : 𝕜) :
 HolsteinNormal (f-a • 1) := by
 unfold HolsteinNormal at h ⊢
 rw [spectralShiftAdjoint]
 simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_sub,smul_smul]
 rw [h,mul_comm a (conj a)]
 abel

theorem spectralNormalNorm (f : Module.End 𝕜 E) (h : HolsteinNormal f) (v : E) :
 ‖f v‖ = ‖f.adjoint v‖ := by
 have hh : inner 𝕜 (f v) (f v)=inner 𝕜 (f.adjoint v) (f.adjoint v) := by
  calc
   _=inner 𝕜 v (f.adjoint (f v)) := (LinearMap.adjoint_inner_right f v (f v)).symm
   _=inner 𝕜 v (f (f.adjoint v)) := congrArg (fun g : Module.End 𝕜 E => inner 𝕜 v (g v)) h.symm
   _=_ := (LinearMap.adjoint_inner_left f (f.adjoint v) v).symm
 have hs : ‖f v‖^2=‖f.adjoint v‖^2 := RCLike.ofReal_injective (by
  simpa only [inner_self_eq_norm_sq_to_K,RCLike.ofReal_pow] using hh)
 nlinarith [norm_nonneg (f v),norm_nonneg (f.adjoint v)]

theorem spectralNormalKernel (f : Module.End 𝕜 E) (h : HolsteinNormal f) :
 f.ker=f.adjoint.ker := by
 ext v
 simp only [LinearMap.mem_ker]
 constructor
 · intro hv; apply norm_eq_zero.mp
   rw [← spectralNormalNorm f h,hv,norm_zero]
 · intro hv; apply norm_eq_zero.mp
   rw [spectralNormalNorm f h,hv,norm_zero]

theorem spectralAdjointEigenspace (f : Module.End 𝕜 E) (h : HolsteinNormal f) (a : 𝕜) :
 f.eigenspace a=eigenspace f.adjoint (conj a) := by
 rw [eigenspace_def,eigenspace_def,← spectralShiftAdjoint]
 exact spectralNormalKernel _ (spectralShiftNormal f h a)

theorem spectralEigenOrthogonal (f : Module.End 𝕜 E) (h : HolsteinNormal f)
 {a b : 𝕜} (hab : a≠b) {v w : E}
 (hv : v∈f.eigenspace a) (hw : w∈f.eigenspace b) :
 holsteinInner (𝕜:=𝕜) v w=0 := by
 have hw' : f.adjoint w=conj b • w := by
  exact mem_eigenspace_iff.mp ((spectralAdjointEigenspace f h b) ▸ hw)
 have hh : a*holsteinInner (𝕜:=𝕜) v w=b*holsteinInner (𝕜:=𝕜) v w := by
  have hi := LinearMap.adjoint_inner_left f v w
  simpa only [holsteinInner,mem_eigenspace_iff.mp hv,hw',inner_smul_left,
   inner_smul_right,starRingEnd_self_apply,mul_comm] using hi.symm
 exact (mul_eq_zero.mp (by rw [sub_mul,hh,sub_self] :
  (a-b)*holsteinInner (𝕜:=𝕜) v w=0)).resolve_left (sub_ne_zero.mpr hab)

theorem spectralSelfAdjointONB (f : Module.End 𝕜 E) (h : HolsteinSelfAdjoint f) :
 ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E,
 ∃ a : Fin (Module.finrank 𝕜 E) → ℝ, ∀ i, f (b i)=(a i : 𝕜) • b i := by
 let hs := (spectralSelfAdjointIff f).mp h
 exact ⟨hs.eigenvectorBasis rfl,hs.eigenvalues rfl,hs.apply_eigenvectorBasis rfl⟩

theorem spectralSelfAdjointSplits (f : Module.End 𝕜 E) (h : HolsteinSelfAdjoint f) :
 f.charpoly.Splits := by
 rw [((spectralSelfAdjointIff f).mp h).charpoly_eq rfl]
 exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)

theorem spectralEigenFamily (f : Module.End 𝕜 E) (h : HolsteinNormal f) :
 OrthogonalFamily 𝕜 (fun a => eigenspace f a) (fun a => (eigenspace f a).subtypeₗᵢ) := by
 rintro a b hab ⟨v,hv⟩ ⟨w,hw⟩
 exact spectralEigenOrthogonal f h hab.symm hw hv

theorem spectralComplementInvariant (f : Module.End 𝕜 E) (h : HolsteinNormal f)
 {v : E} (hv : v∈(⨆ a, eigenspace f a)ᗮ) : f v∈(⨆ a, eigenspace f a)ᗮ := by
 rw [← Submodule.iInf_orthogonal] at hv ⊢
 have hi : ∀ a, ∀ x∈(eigenspace f a)ᗮ, f x∈(eigenspace f a)ᗮ := by
  intro a x hx w hw
  have hw' : f.adjoint w=conj a • w :=
   mem_eigenspace_iff.mp ((spectralAdjointEigenspace f h a) ▸ hw)
  rw [← LinearMap.adjoint_inner_left f x w,hw',inner_smul_left,hx w hw,mul_zero]
 exact f.iInf_invariant hi v hv

/-- Full normal spectral span under the ORIGINAL split hypothesis. The proof
uses Cayley-Hamilton on the invariant orthogonal complement, without assuming
algebraic closure or weakening the statement to an example. -/
theorem spectralNormalSpan (f : Module.End 𝕜 E) (h : HolsteinNormal f)
 (hs : f.charpoly.Splits) : (⨆ a, eigenspace f a)=⊤ := by
 classical
 let W : Submodule 𝕜 E := ⨆ a, eigenspace f a
 have hinv : ∀ v∈Wᗮ, f v∈Wᗮ := fun v hv => spectralComplementInvariant f h hv
 have hz : ∀ (a : 𝕜) (v : E), v∈Wᗮ → (f-a • 1) v=0 → v=0 := by
  intro a v hv he
  have hv' : v∈W := (le_iSup (fun a => eigenspace f a) a)
   (by simpa only [eigenspace_def,LinearMap.mem_ker] using he)
  have hh : v∈W⊓Wᗮ := ⟨hv',hv⟩
  simpa only [Submodule.inf_orthogonal_eq_bot,Submodule.mem_bot] using hh
 have helper : ∀ L : List 𝕜,
  (∀ v∈Wᗮ, (L.map (fun a => f-a • 1)).prod v∈Wᗮ) ∧
  (∀ v∈Wᗮ, (L.map (fun a => f-a • 1)).prod v=0 → v=0) := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
   constructor
   · intro v hv
     have hm := ih.1 v hv
     simpa only [List.map_cons,List.prod_cons,Module.End.mul_apply,
      LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply] using
      Wᗮ.sub_mem (hinv _ hm) (Wᗮ.smul_mem a hm)
   · intro v hv he
     apply ih.2 v hv
     apply hz a _ (ih.1 v hv)
     simpa only [List.map_cons,List.prod_cons,Module.End.mul_apply] using he
 let L := f.charpoly.roots.toList
 have hp : f.charpoly=(L.map (fun a => Polynomial.X-Polynomial.C a)).prod := by
  simpa only [L,← Multiset.prod_coe,← Multiset.map_coe,Multiset.coe_toList] using
   hs.eq_prod_roots_of_monic f.charpoly_monic
 have he : (L.map (fun a => f-a • 1)).prod=0 := by
  have hh := congrArg (Polynomial.aeval f) hp
  rw [f.aeval_self_charpoly] at hh
  simpa only [map_list_prod,List.map_map,Function.comp_def,map_sub,
   Polynomial.aeval_X,Polynomial.aeval_C,Algebra.algebraMap_eq_smul_one] using hh.symm
 have hb : Wᗮ=⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  exact (helper L).2 v hv (by rw [he]; rfl)
 exact Submodule.orthogonal_eq_bot_iff.mp hb

theorem spectralNormalONB (f : Module.End 𝕜 E) (h : HolsteinNormal f)
 (hs : f.charpoly.Splits) :
 ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E,
 ∃ a : Fin (Module.finrank 𝕜 E) → 𝕜, ∀ i, f (b i)=a i • b i := by
 classical
 let I := {a : 𝕜 // eigenspace f a ≠ ⊥}
 letI : Fintype I := Set.Finite.fintype
  (WellFoundedGT.finite_ne_bot_of_iSupIndep f.eigenspaces_iSupIndep)
 have family : OrthogonalFamily 𝕜 (fun a : I => eigenspace f a.val)
  (fun a => (eigenspace f a.val).subtypeₗᵢ) :=
  (spectralEigenFamily f h).comp Subtype.val_injective
 have hspan : (⨆ a : I, eigenspace f a.val)=⊤ := by
  rw [iSup_ne_bot_subtype,spectralNormalSpan f h hs]
 have hi : DirectSum.IsInternal (fun a : I => eigenspace f a.val) := family.isInternal_iff.mpr (by
  rw [hspan]; exact Submodule.top_orthogonal_eq_bot)
 refine ⟨hi.subordinateOrthonormalBasis rfl family,
  fun i => (hi.subordinateOrthonormalBasisIndex rfl i family).val,?_⟩
 intro i
 exact mem_eigenspace_iff.mp (hi.subordinateOrthonormalBasis_subordinate rfl i family)

theorem spectralKernelImage (f : Module.End 𝕜 E) (h : HolsteinSelfAdjoint f) :
 f.range=f.kerᗮ ∧ IsCompl f.ker f.range := by
 have hr : f.range=f.kerᗮ := by rw [LinearMap.orthogonal_ker,h]
 exact ⟨hr,hr ▸ f.ker.isCompl_orthogonal⟩

theorem spectralONBAdjoint {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
 (f : Module.End 𝕜 E) (a : ι → 𝕜) (ha : ∀ i, f (b i)=a i • b i) (i : ι) :
 f.adjoint (b i)=conj (a i) • b i := by
 classical
 apply b.repr.injective
 ext j
 rw [b.repr_apply_apply,b.repr_apply_apply]
 rw [LinearMap.adjoint_inner_right,ha j,inner_smul_left,inner_smul_right]
 rw [orthonormal_iff_ite.mp b.orthonormal j i]
 split_ifs with hji
 · subst j; rfl
 · simp

theorem spectralONBNormal {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
 (f : Module.End 𝕜 E) (a : ι → 𝕜) (ha : ∀ i, f (b i)=a i • b i) :
 HolsteinNormal f := by
 apply b.toBasis.ext
 intro i
 change f (f.adjoint (b i))=f.adjoint (f (b i))
 rw [spectralONBAdjoint b f a ha,ha,map_smul,map_smul,ha,spectralONBAdjoint b f a ha]
 simp only [smul_smul,mul_comm]

theorem spectralSelfAdjointMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
 (b : OrthonormalBasis ι 𝕜 E) (f : Module.End 𝕜 E) :
 HolsteinSelfAdjoint f ↔ (f.toMatrix b.toBasis b.toBasis).IsHermitian := by
 unfold HolsteinSelfAdjoint Matrix.IsHermitian
 rw [← LinearMap.toMatrix_adjoint b b f]
 exact (LinearMap.toMatrix b.toBasis b.toBasis).injective.eq_iff.symm

theorem spectralSelfAdjointDecomposition (f : Module.End 𝕜 E) (h : HolsteinSelfAdjoint f) :
 DirectSum.IsInternal (fun a : f.Eigenvalues => eigenspace f (a : 𝕜)) :=
 ((spectralSelfAdjointIff f).mp h).direct_sum_isInternal

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem spectralHermitianUnitary (B : Matrix n n 𝕜) (hB : B.IsHermitian) :
 ∃ U : Matrix.unitaryGroup n 𝕜,
 star (U : Matrix n n 𝕜)*B*(U : Matrix n n 𝕜)=
  Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
 refine ⟨hB.eigenvectorUnitary,?_⟩
 simpa only [Unitary.conjStarAlgAut_star_apply,Function.comp_apply] using hB.conjStarAlgAut_star_eigenvectorUnitary

theorem spectralTransposeRealHermitian (B : Matrix n n ℝ) :
 B.IsHermitian ↔ B.transpose=B := by
 have hh : B.conjTranspose=B.transpose := by ext i j; simp
 rw [Matrix.IsHermitian,hh]

theorem spectralHermitianDiagonalReal (B : Matrix n n 𝕜) (hB : B.IsHermitian) :
 ∀ i, conj (hB.eigenvalues i : 𝕜)=(hB.eigenvalues i : 𝕜) := by simp

theorem spectralRealComplexification (B : Matrix n n ℝ) (hB : B.transpose=B) :
 (B.map (algebraMap ℝ ℂ)).IsHermitian := by
 ext i j
 have hh := congrArg (fun C : Matrix n n ℝ => C i j) hB
 simpa using congrArg (fun x : ℝ => (x : ℂ)) hh

theorem spectralComplexifiedCharpoly (B : Matrix n n ℝ) :
 (B.map (algebraMap ℝ ℂ)).charpoly=B.charpoly.map (algebraMap ℝ ℂ) :=
 Matrix.charpoly_map B (algebraMap ℝ ℂ)
end Matrix

def spectralOriginalHermitianOne : Matrix (Fin 2) (Fin 2) ℂ := !![0,Complex.I;-Complex.I,0]
def spectralOriginalHermitianTwo : Matrix (Fin 2) (Fin 2) ℂ := !![1,1-Complex.I;1+Complex.I,1]
theorem spectralOriginalOneHermitian : spectralOriginalHermitianOne.IsHermitian := by
 ext i j; fin_cases i <;> fin_cases j <;> simp [spectralOriginalHermitianOne,Matrix.conjTranspose_apply]
theorem spectralOriginalTwoHermitian : spectralOriginalHermitianTwo.IsHermitian := by
 ext i j; fin_cases i <;> fin_cases j <;> simp [spectralOriginalHermitianTwo,Matrix.conjTranspose_apply,sub_eq_add_neg]
def spectralRotation : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;1,0]
theorem spectralRotationNormal :
 spectralRotation*spectralRotation.transpose=spectralRotation.transpose*spectralRotation := by
 ext i j; fin_cases i <;> fin_cases j <;> norm_num [spectralRotation,Matrix.mul_apply,Fin.sum_univ_two]
theorem spectralRotationNotSymmetric : spectralRotation.transpose≠spectralRotation := by
 intro h
 have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 1) h
 norm_num [spectralRotation] at hh
def spectralNonNormal : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;0,2]
theorem spectralNonNormalProducts :
 spectralNonNormal*spectralNonNormal.transpose≠spectralNonNormal.transpose*spectralNonNormal := by
 intro h
 have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 0) h
 norm_num [spectralNonNormal,Matrix.mul_apply,Fin.sum_univ_two] at hh
theorem spectralComplexSymmetricNotHermitian :
 (Matrix.of (fun (_ _ : Fin 1) => Complex.I)).transpose=
  Matrix.of (fun (_ _ : Fin 1) => Complex.I) ∧
 ¬(Matrix.of (fun (_ _ : Fin 1) => Complex.I)).IsHermitian := by
 constructor
 · rfl
 · intro h
   have hh := congrArg (fun B : Matrix (Fin 1) (Fin 1) ℂ => B 0 0) h.eq
   have hi := congrArg Complex.im hh
   norm_num [Matrix.conjTranspose_apply] at hi

end ILab.LinearAlgebra
