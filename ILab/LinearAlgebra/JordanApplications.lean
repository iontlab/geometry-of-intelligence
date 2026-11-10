import ILab.LinearAlgebra.NilpotentJordan
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! §10.4. General polynomial tests are separated from concrete rational
certificates and analytic derivatives. The general Jordan-basis existence gap
documented in NilpotentJordan is not closed or re-labelled here. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module Polynomial
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem jordanPowerKernelDimension [FiniteDimensional K V]
    (f : Module.End K V) (a : K) (i : ℕ) :
    finrank K (LinearMap.ker ((f-a • 1)^i)) =
      finrank K V - finrank K (LinearMap.range ((f-a • 1)^i)) := by
  have h := LinearMap.finrank_range_add_finrank_ker ((f-a • 1)^i)
  omega

theorem jordanShiftedBasisCertificate {n : ℕ} (a : K)
    (N P S J : Matrix (Fin n) (Fin n) K)
    (hSP : S*P=1) (hNP : N*P=P*J) :
    S*(a • (1 : Matrix (Fin n) (Fin n) K)+N)*P = a • 1+J := by
  rw [jordanShiftConjugation a N S P hSP,jordanBasisCertificate N P S J hSP hNP]

set_option backward.isDefEq.respectTransparency.types false in
theorem distinctFactorEvaluationKernel [FiniteDimensional K V]
    (f : Module.End K V) (s : Finset K) :
    LinearMap.ker (aeval f (∏ a ∈ s, (X-C a))) = ⨆ a ∈ s, f.eigenspace a := by
  classical
  have hc : (↑s : Set K).Pairwise (fun a b => Commute (f-a • 1) (f-b • 1)) := by
    intro a ha b hb hab
    exact ((Commute.refl f).sub_right (Algebra.commute_algebraMap_right b f)).sub_left
      (Algebra.commute_algebraMap_left a (f - b • 1))
  have he : aeval f (∏ a ∈ s, (X-C a)) = s.noncommProd (fun a => f-a • 1) hc := by
    have hm := s.map_noncommProd (fun a : K => X-C a)
      (fun _ _ _ _ _ => Commute.all _ _) (aeval f).toRingHom
    change (aeval f) (s.noncommProd (fun a : K => X-C a) _) =
      s.noncommProd (fun a : K => (aeval f) (X-C a)) _ at hm
    simp only [Finset.noncommProd_eq_prod, map_sub, aeval_X,
      aeval_C, Algebra.algebraMap_eq_smul_one] at hm
    exact hm
  rw [he, LinearMap.ker_noncommProd_eq_of_supIndep_ker]
  · simp only [← Module.End.eigenspace_def]
  · simpa only [← Module.End.eigenspace_def] using f.eigenspaces_iSupIndep.supIndep' s

theorem diagonalizableOfDistinctAnnihilator [FiniteDimensional K V]
    (f : Module.End K V) (s : Finset K)
    (h : aeval f (∏ a ∈ s, (X-C a)) = 0) : HolsteinDiagonalizable f := by
  apply eigenspaceSpanDiagonalizable
  have hs : (⨆ a ∈ s, f.eigenspace a) = ⊤ := by
    rw [← distinctFactorEvaluationKernel, h, LinearMap.ker_zero]
  apply top_unique
  rw [← hs]
  exact iSup_le fun a => iSup_le fun ha => le_iSup _ a

theorem diagonalizableDistinctAnnihilator [FiniteDimensional K V]
    (f : Module.End K V) (h : HolsteinDiagonalizable f) :
    ∃ s : Finset K, aeval f (∏ a ∈ s, (X-C a)) = 0 := by
  classical
  obtain ⟨n,b,hb⟩ := h
  choose d hd using hb
  let s := Finset.univ.image d
  refine ⟨s, b.ext fun i => ?_⟩
  rw [eigenvectorPolynomialEvaluation f _ (d i) (b i) (hd i)]
  have hz : (∏ a ∈ s, (X-C a) : K[X]).eval (d i) = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) (sub_self _)
  simp [hz]

theorem diagonalizableIffDistinctAnnihilator [FiniteDimensional K V]
    (f : Module.End K V) : HolsteinDiagonalizable f ↔
      ∃ s : Finset K, aeval f (∏ a ∈ s, (X-C a)) = 0 :=
  ⟨diagonalizableDistinctAnnihilator f, fun ⟨s,h⟩ => diagonalizableOfDistinctAnnihilator f s h⟩

theorem diagonalizableIffMinimalDividesDistinct [FiniteDimensional K V]
    (f : Module.End K V) : HolsteinDiagonalizable f ↔
      ∃ s : Finset K, minpoly K f ∣ ∏ a ∈ s, (X-C a) := by
  simp only [diagonalizableIffDistinctAnnihilator, minpoly.dvd_iff]

theorem diagonalizableIffFixedPolynomialTest [FiniteDimensional K V]
    (f : Module.End K V) (s : Finset K)
    (hs : ∀ a, f.HasEigenvalue a → a ∈ s) :
    HolsteinDiagonalizable f ↔ aeval f (∏ a ∈ s, (X-C a)) = 0 := by
  classical
  refine ⟨?_,diagonalizableOfDistinctAnnihilator f s⟩
  rintro ⟨n,b,hb⟩
  apply b.ext
  intro i
  obtain ⟨a,ha⟩ := hb i
  rw [eigenvectorPolynomialEvaluation f _ a (b i) ha]
  have hz : (∏ c ∈ s, (X-C c) : K[X]).eval a = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (hs a (Module.End.hasEigenvalue_of_hasEigenvector ha)) (sub_self _)
  simp [hz]

theorem jordanTwoMinimalPolynomial (a : K) :
    minpoly K (jordanBlock a 2) = (X-C a)^2 := by
  classical
  refine minpoly.eq_of_linearIndependent K (jordanBlock a 2)
    ((monic_X_sub_C a).pow 2) ?_ 2 (by compute_degree!) ?_
  · rw [map_pow,map_sub,aeval_X,aeval_C]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two,Matrix.mul_apply,Fin.sum_univ_two,jordanBlock,Matrix.algebraMap_matrix_apply] <;> ring
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h01 := congrArg (fun B : Matrix (Fin 2) (Fin 2) K => B 0 1) hc
    have h00 := congrArg (fun B : Matrix (Fin 2) (Fin 2) K => B 0 0) hc
    simp [Fin.sum_univ_two,jordanBlock,Matrix.one_apply] at h01 h00
    fin_cases i <;> simp_all

def jordanOriginalA : Matrix (Fin 5) (Fin 5) ℚ :=
  !![3,-2,0,2,3;0,1,0,1,2;2,-4,2,2,3;-2,3,0,-1,-4;1,-2,0,2,5]

def jordanOriginalN : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1,-2,0,2,3;0,-1,0,1,2;2,-4,0,2,3;-2,3,0,-3,-4;1,-2,0,2,3]

def jordanOriginalP : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0,1,1,-2,0;0,0,0,-1,1;1,2,0,-4,0;0,-2,0,3,0;0,1,0,-2,0]

def jordanOriginalS : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0,0,1,0,-2;0,0,0,-2,-3;1,0,0,0,-1;0,0,0,-1,-2;0,1,0,-1,-2]

def jordanOriginalJ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![2,1,0,0,0;0,2,1,0,0;0,0,2,0,0;0,0,0,2,1;0,0,0,0,2]

theorem jordanOriginalShift : jordanOriginalN = jordanOriginalA - (2 : ℚ) • (1 : Matrix (Fin 5) (Fin 5) ℚ) := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [jordanOriginalN,jordanOriginalA,Matrix.smul_apply,Matrix.one_apply]

theorem jordanOriginalSquare : jordanOriginalN^2 =
    !![0,0,0,0,0;0,0,0,0,0;1,0,0,0,-1;0,0,0,0,0;0,0,0,0,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [jordanOriginalN,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]

theorem jordanOriginalCube : jordanOriginalN^3=0 := by
  rw [show (3:ℕ)=2+1 from rfl,pow_succ,jordanOriginalSquare]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [jordanOriginalN,Matrix.mul_apply,Fin.sum_univ_succ]

theorem jordanOriginalSquareNonzero : jordanOriginalN^2≠0 := by
  intro h
  have := congrArg (fun B : Matrix (Fin 5) (Fin 5) ℚ => B 2 0) h
  norm_num [jordanOriginalSquare] at this

theorem jordanOriginalLeftInverse : jordanOriginalS*jordanOriginalP=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [jordanOriginalS,jordanOriginalP,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]

theorem jordanOriginalRightInverse : jordanOriginalP*jordanOriginalS=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [jordanOriginalS,jordanOriginalP,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]

theorem jordanOriginalBasisDet : jordanOriginalP.det = -1 := by
  norm_num [jordanOriginalP, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,Matrix.det_fin_one,Fin.succAbove]

theorem jordanOriginalIntertwine : jordanOriginalA*jordanOriginalP=jordanOriginalP*jordanOriginalJ := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [jordanOriginalA,jordanOriginalP,jordanOriginalJ,Matrix.mul_apply,Fin.sum_univ_succ]

theorem jordanOriginalConjugation : jordanOriginalS*jordanOriginalA*jordanOriginalP=jordanOriginalJ :=
  jordanBasisCertificate jordanOriginalA jordanOriginalP jordanOriginalS jordanOriginalJ
    jordanOriginalLeftInverse jordanOriginalIntertwine

theorem jordanOriginalCharacteristic : jordanOriginalA.charpoly=(X-C 2)^5 := by
  have h := Matrix.charpoly_mul_comm (jordanOriginalS*jordanOriginalA) jordanOriginalP
  rw [← Matrix.mul_assoc,jordanOriginalRightInverse,Matrix.one_mul] at h
  rw [jordanOriginalConjugation] at h
  rw [← h,upperCharacteristicPolynomial]
  · norm_num [jordanOriginalJ,Fin.prod_univ_succ]
    <;> ring
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [jordanOriginalJ,Matrix.IsUpperTriangular,Fin.lt_def]

theorem jordanOriginalAnnihilator : aeval jordanOriginalA ((X-C 2)^3 : ℚ[X])=0 := by
  rw [map_pow,map_sub,aeval_X,aeval_C,Algebra.algebraMap_eq_smul_one,← jordanOriginalShift]
  exact jordanOriginalCube

theorem jordanOriginalMinimalPolynomial : minpoly ℚ jordanOriginalA=(X-C 2)^3 := by
  refine minpoly.eq_of_linearIndependent ℚ jordanOriginalA
    ((monic_X_sub_C 2).pow 3) jordanOriginalAnnihilator 3 (by compute_degree!) ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h20 := congrArg (fun B : Matrix (Fin 5) (Fin 5) ℚ => B 2 0) hc
  have h00 := congrArg (fun B : Matrix (Fin 5) (Fin 5) ℚ => B 0 0) hc
  have h11 := congrArg (fun B : Matrix (Fin 5) (Fin 5) ℚ => B 1 1) hc
  norm_num [Fin.sum_univ_three,jordanOriginalA,pow_two,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ] at h20 h00 h11
  fin_cases i <;> dsimp <;> linarith

theorem odeExponentialDerivative (a t : ℝ) :
    HasDerivAt (fun t => Real.exp (a*t)) (a*Real.exp (a*t)) t := by
  have h : HasDerivAt (fun x : ℝ => a*x) a t := by simpa using (hasDerivAt_id t).const_mul a
  simpa only [mul_comm] using h.exp

theorem odeJordanSecondDerivative (a t : ℝ) :
    HasDerivAt (fun t => t*Real.exp (a*t))
      (Real.exp (a*t)+a*(t*Real.exp (a*t))) t := by
  have h : HasDerivAt (fun x : ℝ => x*Real.exp (a*x))
      (1*Real.exp (a*t)+t*(a*Real.exp (a*t))) t :=
    (hasDerivAt_id t).mul (odeExponentialDerivative a t)
  convert h using 1 <;> ring

end ILab.LinearAlgebra
