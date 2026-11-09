import ILab.LinearAlgebra.MinimalPolynomial
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.Tactic

/-! Holstein §§10.1–10.2. The announced Jordan classification is deferred to §10.3.
Semisimple is not identified with diagonalizable. Additional type hypotheses
IsAlgClosed and PerfectField below are explicit formal limits, not hidden assumptions.
No JavaScript algorithm is claimed formally verified. -/
noncomputable section
namespace ILab.LinearAlgebra
open Module Polynomial
set_option maxHeartbeats 700000
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def HolsteinPrimarySpace [FiniteDimensional K V] (f : Module.End K V) (a : K) : Submodule K V :=
  LinearMap.ker ((f-a • 1)^finrank K V)

theorem primarySpaceEqGen [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    HolsteinPrimarySpace f a = f.genEigenspace a (finrank K V) :=
  Module.End.genEigenspace_nat.symm

theorem primarySpaceEqMax [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    HolsteinPrimarySpace f a = f.maxGenEigenspace a := by
  rw [primarySpaceEqGen,Module.End.maxGenEigenspace_eq_genEigenspace_finrank]

theorem primarySpaceDimension [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    finrank K (HolsteinPrimarySpace f a) = f.charpoly.rootMultiplicity a := by
  rw [primarySpaceEqMax]
  exact LinearMap.finrank_maxGenEigenspace_eq f a

theorem primarySpaceInvariant [FiniteDimensional K V] (f : Module.End K V) (a : K) :
    ∀ v ∈ HolsteinPrimarySpace f a, f v ∈ HolsteinPrimarySpace f a := by
  rw [primarySpaceEqGen]
  exact Module.End.mapsTo_genEigenspace_of_comm (Commute.refl f) a _

theorem distinctPrimarySpacesDisjoint [FiniteDimensional K V] (f : Module.End K V)
    {a b : K} (h : a ≠ b) : Disjoint (HolsteinPrimarySpace f a) (HolsteinPrimarySpace f b) := by
  rw [primarySpaceEqGen,primarySpaceEqGen]
  exact Module.End.disjoint_genEigenspace f h _ _

theorem primarySpacesIndependent [FiniteDimensional K V] (f : Module.End K V) :
    iSupIndep (HolsteinPrimarySpace f) := by
  have heq : HolsteinPrimarySpace f = f.maxGenEigenspace := funext (primarySpaceEqMax f)
  rw [heq]
  exact Module.End.independent_maxGenEigenspace f

/-- Additional algebraic closure hypothesis; not presented as the minimal split hypothesis. -/
theorem primarySpacesSpanAlgClosed [FiniteDimensional K V] [IsAlgClosed K]
    (f : Module.End K V) : (⨆ a, HolsteinPrimarySpace f a) = ⊤ := by
  simp_rw [primarySpaceEqMax]
  exact Module.End.iSup_maxGenEigenspace_eq_top f

theorem shiftedRestrictionNilpotent (f : Module.End K V) (a : K) (m : ℕ) :
    IsNilpotent ((f-algebraMap K (Module.End K V) a).restrict
      (Module.End.mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f a) a m)) :=
  Module.End.isNilpotent_restrict_sub_algebraMap f a m

theorem kernelPowersMonotone (f : Module.End K V) {i j : ℕ} (h : i ≤ j) :
    LinearMap.ker (f^i) ≤ LinearMap.ker (f^j) := f.iterateKer.monotone h

theorem imagePowersAntitone (f : Module.End K V) {i j : ℕ} (h : i ≤ j) :
    LinearMap.range (f^j) ≤ LinearMap.range (f^i) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact LinearMap.range_comp_le_range _ _

theorem fittingStabilizationExists [FiniteDimensional K V] (f : Module.End K V) :
    ∃ d : ℕ, d ≤ finrank K V ∧ LinearMap.ker (f^d) = LinearMap.ker (f^(d+1)) :=
  Module.End.exists_ker_pow_eq_ker_pow_succ f

theorem fittingKernelStability (f : Module.End K V) {d : ℕ}
    (h : LinearMap.ker (f^d) = LinearMap.ker (f^(d+1))) (i : ℕ) :
    LinearMap.ker (f^d) = LinearMap.ker (f^(d+i)) := Module.End.ker_pow_constant h i

noncomputable def fittingIndex [FiniteDimensional K V] (f : Module.End K V) : ℕ :=
  Nat.find (show ∃ d, LinearMap.ker (f^d)=LinearMap.ker (f^(d+1)) from
    let ⟨d,_,h⟩ := fittingStabilizationExists f; ⟨d,h⟩)

theorem fittingIndexStable [FiniteDimensional K V] (f : Module.End K V) :
    LinearMap.ker (f^fittingIndex f)=LinearMap.ker (f^(fittingIndex f+1)) := by
  unfold fittingIndex
  exact Nat.find_spec (p := fun d : ℕ => LinearMap.ker (f^d)=LinearMap.ker (f^(d+1))) _

theorem fittingIndexMinimal [FiniteDimensional K V] (f : Module.End K V) {i : ℕ}
    (h : i < fittingIndex f) : LinearMap.ker (f^i) ≠ LinearMap.ker (f^(i+1)) :=
  Nat.find_min _ h

theorem fittingKernelsAtDimension [FiniteDimensional K V] (f : Module.End K V) {i : ℕ}
    (h : finrank K V ≤ i) : LinearMap.ker (f^i) = LinearMap.ker (f^finrank K V) :=
  Module.End.ker_pow_eq_ker_pow_finrank_of_le h

theorem fittingRankNullity [FiniteDimensional K V] (f : Module.End K V) (d : ℕ) :
    finrank K (LinearMap.range (f^d)) + finrank K (LinearMap.ker (f^d)) = finrank K V :=
  LinearMap.finrank_range_add_finrank_ker (f^d)

theorem fittingImageStability [FiniteDimensional K V] (f : Module.End K V) {d : ℕ}
    (h : LinearMap.ker (f^d) = LinearMap.ker (f^(d+1))) (i : ℕ) :
    LinearMap.range (f^(d+i)) = LinearMap.range (f^d) := by
  apply Submodule.eq_of_le_of_finrank_eq (imagePowersAntitone f (Nat.le_add_right d i))
  have h1 := fittingRankNullity f d
  have h2 := fittingRankNullity f (d+i)
  rw [← fittingKernelStability f h i] at h2
  omega

theorem fittingDirectSumStable [FiniteDimensional K V] (f : Module.End K V) {d : ℕ}
    (h : LinearMap.ker (f^d) = LinearMap.ker (f^(d+1))) :
    IsCompl (LinearMap.ker (f^d)) (LinearMap.range (f^d)) := by
  have hd : Disjoint (LinearMap.ker (f^d)) (LinearMap.range (f^d)) := by
    rw [disjoint_iff,Submodule.eq_bot_iff]
    rintro x ⟨hx,⟨y,rfl⟩⟩
    have hy : y ∈ LinearMap.ker (f^(d+d)) := by
      simpa only [LinearMap.mem_ker,pow_add,Module.End.mul_apply] using (LinearMap.mem_ker.mp hx)
    rw [← fittingKernelStability f h d] at hy
    exact hy
  exact (Submodule.isCompl_iff_disjoint _ _ (by
    have hdim := fittingRankNullity f d
    omega)).mpr hd

theorem fittingKernelInvariant (f : Module.End K V) (d : ℕ) :
    ∀ v ∈ LinearMap.ker (f^d), f v ∈ LinearMap.ker (f^d) := by
  intro v hv
  change (f^d) (f v) = 0
  rw [← Module.End.mul_apply,← pow_succ,pow_succ',Module.End.mul_apply]
  simp only [LinearMap.mem_ker] at hv
  rw [hv,map_zero]

theorem fittingImageInvariant (f : Module.End K V) (d : ℕ) :
    ∀ v ∈ LinearMap.range (f^d), f v ∈ LinearMap.range (f^d) := by
  rintro v ⟨w,rfl⟩
  refine ⟨f w,?_⟩
  rw [← Module.End.mul_apply,← pow_succ,pow_succ',Module.End.mul_apply]

theorem fittingZeroExponentKernel (f : Module.End K V) : LinearMap.ker (f^0) = ⊥ := by
  change LinearMap.ker (LinearMap.id : Module.End K V) = ⊥
  exact LinearMap.ker_id

theorem fittingZeroExponentImage (f : Module.End K V) : LinearMap.range (f^0) = ⊤ := by
  change LinearMap.range (LinearMap.id : Module.End K V) = ⊤
  exact LinearMap.range_id

theorem fittingInvertibleIndexZero (e : V ≃ₗ[K] V) :
    LinearMap.ker (e.toLinearMap^0) = LinearMap.ker (e.toLinearMap^1) := by
  rw [fittingZeroExponentKernel,pow_one,LinearMap.ker_eq_bot.mpr e.injective]

theorem nilpotentIffPowerZero (f : Module.End K V) : IsNilpotent f ↔ ∃ d : ℕ, f^d=0 := Iff.rfl

theorem nilpotentMonomialAnnihilates (f : Module.End K V) {d : ℕ} (h : f^d=0) :
    aeval f (X^d : K[X]) = 0 := by simpa using h

theorem nilpotentMinimalDividesMonomial (f : Module.End K V) {d : ℕ} (h : f^d=0) :
    minpoly K f ∣ X^d := minpoly.dvd_iff.mpr (nilpotentMonomialAnnihilates f h)

theorem directSumCharacteristicProduct {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W) :
    (f.prodMap g).charpoly = f.charpoly*g.charpoly := LinearMap.charpoly_prodMap f g

/-- Semisimple result over perfect fields, not the full split diagonalizable result. -/
theorem commutingSemisimpleNilpotentExists [FiniteDimensional K V] [PerfectField K]
    (f : Module.End K V) :
    ∃ n d : Module.End K V, IsNilpotent n ∧ d.IsSemisimple ∧ f=n+d ∧ Commute n d := by
  obtain ⟨n,hnm,d,hdm,hn,hd,hf⟩ := f.exists_isNilpotent_isSemisimple
  have hnf : Commute n f :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hnm (Commute.refl f)).symm
  exact ⟨n,d,hn,hd,hf,Algebra.commute_of_mem_adjoin_singleton_of_commute hdm hnf⟩

theorem commutingSemisimpleNilpotentUnique [FiniteDimensional K V] [PerfectField K]
    {n₁ d₁ n₂ d₂ : Module.End K V} (hn₁ : IsNilpotent n₁) (hd₁ : d₁.IsSemisimple)
    (hn₂ : IsNilpotent n₂) (hd₂ : d₂.IsSemisimple) (hc₁ : Commute n₁ d₁)
    (hc₂ : Commute n₂ d₂) (heq : n₁+d₁=n₂+d₂) : n₁=n₂ ∧ d₁=d₂ :=
  Module.End.isNilpotent_isSemisimple_unique hn₁ hd₁ hn₂ hd₂ hc₁ hc₂ heq

def jordanBlock (a : K) (r : ℕ) : Matrix (Fin r) (Fin r) K :=
  fun i j => if i=j then a else if i.val+1=j.val then 1 else 0

theorem jordanBlockUpper (a : K) (r : ℕ) : (jordanBlock a r).IsUpperTriangular := by
  intro i j h
  change j < i at h
  have hne : i ≠ j := ne_of_gt h
  have hn : ¬ (i.val+1=j.val) := by simp only [Fin.lt_def] at h; omega
  simp [jordanBlock,hne,hn]

theorem jordanBlockDiagonal (a : K) (r : ℕ) (i : Fin r) : jordanBlock a r i i = a := by simp [jordanBlock]

theorem jordanBlockCharacteristic (a : K) (r : ℕ) : (jordanBlock a r).charpoly=(X-C a)^r := by
  rw [upperCharacteristicPolynomial _ (jordanBlockUpper a r)]
  simp [jordanBlockDiagonal]

theorem strictUpperNilpotent {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (h : A.IsUpperTriangular) (hd : ∀ i, A i i=0) : A^r=0 := by
  have hc : A.charpoly=(X : K[X])^r := by
    rw [upperCharacteristicPolynomial A h]
    simp [hd]
  have he := matrixCayleyHamilton A
  rw [hc] at he
  simpa using he

def primaryExample : Matrix (Fin 3) (Fin 3) ℚ := !![2,1,0;0,2,0;0,0,3]
def primaryExampleD : Matrix (Fin 3) (Fin 3) ℚ := !![2,0,0;0,2,0;0,0,3]
def primaryExampleN : Matrix (Fin 3) (Fin 3) ℚ := !![0,1,0;0,0,0;0,0,0]

theorem primaryExampleAdd : primaryExample=primaryExampleD+primaryExampleN := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [primaryExample,primaryExampleD,primaryExampleN,Matrix.add_apply]

theorem primaryExampleCommute : Commute primaryExampleD primaryExampleN := by
  change primaryExampleD*primaryExampleN=primaryExampleN*primaryExampleD
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [primaryExampleD,primaryExampleN,Matrix.mul_apply,Fin.sum_univ_three]

theorem primaryExampleNilpotent : primaryExampleN^2=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [primaryExampleN,pow_two,Matrix.mul_apply,Fin.sum_univ_three]

theorem primaryExampleNotDiagonal : primaryExample (0:Fin 3) (1:Fin 3) ≠ 0 := by decide

end ILab.LinearAlgebra
