import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Holstein §12.4. `quadraticPolar` is the UNHALVED polar form β_q.
Mathlib `associated` is half this form. Holstein's nondegeneracy is
`quadraticNondegenerate`; Mathlib's characteristic-two quadratic radical
convention is deliberately not substituted for it. -/
noncomputable section
namespace ILab.LinearAlgebra
open QuadraticMap Module
universe u v w
variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Exactly QF1 and QF2, with the unhalved companion. -/
def quadraticAxioms (q : V → K) : Prop :=
 (∀ a x, q (a • x) = a^2 * q x) ∧
 ∃ B : LinearMap.BilinForm K V, ∀ x y, B x y = q (x+y)-q x-q y

def quadraticOfAxioms (q : V → K) (h : quadraticAxioms q) : QuadraticForm K V where
 toFun := q
 toFun_smul a x := by simpa [pow_two, smul_eq_mul] using h.1 a x
 exists_companion' := by
  obtain ⟨B,hB⟩ := h.2
  exact ⟨B, fun x y => by rw [hB]; ring⟩

theorem quadraticAxiomsOfForm (Q : QuadraticForm K V) : quadraticAxioms (fun x => Q x) := by
 refine ⟨?_, Q.polarBilin, fun x y => rfl⟩
 intro a x
 simpa [pow_two, smul_eq_mul] using Q.map_smul a x

theorem quadraticAxiomsIff (q : V → K) :
 quadraticAxioms q ↔ ∃ Q : QuadraticForm K V, ∀ x, Q x = q x := by
 constructor
 · intro h; exact ⟨quadraticOfAxioms q h,fun _ => rfl⟩
 · rintro ⟨Q,hQ⟩; have h := quadraticAxiomsOfForm Q; simpa only [hQ] using h

def quadraticPolar (Q : QuadraticForm K V) : LinearMap.BilinForm K V := Q.polarBilin
theorem quadraticPolarApply (Q : QuadraticForm K V) (x y : V) :
 quadraticPolar Q x y = Q (x+y)-Q x-Q y := rfl
theorem quadraticHomogeneous (Q : QuadraticForm K V) (a : K) (x : V) :
 Q (a • x) = a^2 * Q x := by simpa [pow_two,smul_eq_mul] using Q.map_smul a x
theorem quadraticZero (Q : QuadraticForm K V) : Q 0 = 0 := map_zero Q
theorem quadraticPolarSymmetric (Q : QuadraticForm K V) : (quadraticPolar Q).IsSymm := by
 constructor; intro x y; exact QuadraticMap.polar_comm Q x y
theorem quadraticPolarSelf (Q : QuadraticForm K V) (x : V) :
 quadraticPolar Q x x = 2 * Q x := by
 simpa [quadraticPolar,QuadraticMap.polarBilin_apply_apply,nsmul_eq_mul] using Q.polar_self x
def quadraticNondegenerate (Q : QuadraticForm K V) : Prop := (quadraticPolar Q).Nondegenerate

def quadraticScalarSquare (c : K) : QuadraticForm K K := c • QuadraticMap.sq
theorem quadraticScalarSquareApply (c x : K) : quadraticScalarSquare c x = c*x^2 := by
 simp [quadraticScalarSquare,QuadraticMap.sq,QuadraticMap.linMulLin_apply,pow_two]
theorem quadraticScalarSquarePolar (c x y : K) :
 quadraticPolar (quadraticScalarSquare c) x y = 2*c*x*y := by
 simp only [quadraticPolarApply,quadraticScalarSquareApply]; ring
theorem quadraticScalarSquareNondegenerate (c : K) :
 quadraticNondegenerate (quadraticScalarSquare c) ↔ 2*c ≠ 0 := by
 constructor
 · intro h hc
   have he : ∀ y, quadraticPolar (quadraticScalarSquare c) 1 y = 0 := by
    intro y; rw [quadraticScalarSquarePolar,hc]; simp
   have hzero := h.1 1 he
   exact one_ne_zero hzero
 · intro hc
   constructor <;> intro x hx
   · have h := hx 1; rw [quadraticScalarSquarePolar] at h
     simpa using (mul_eq_zero.mp (by simpa [mul_assoc] using h)).resolve_left hc
   · have h := hx 1; rw [quadraticScalarSquarePolar] at h
     simpa [mul_assoc] using (mul_eq_zero.mp (by simpa [mul_assoc] using h)).resolve_left hc

/-- Holstein's inverse formula; reconstruction is only claimed when two is nonzero. -/
def quadraticFromBilinear (B : LinearMap.BilinForm K V) : QuadraticForm K V :=
 (2:K)⁻¹ • B.toQuadraticMap
theorem quadraticFromBilinearApply (B : LinearMap.BilinForm K V) (x : V) :
 quadraticFromBilinear B x = (2:K)⁻¹ * B x x := rfl
theorem quadraticFromBilinearPolar (B : LinearMap.BilinForm K V) (x y : V) :
 quadraticPolar (quadraticFromBilinear B) x y = (2:K)⁻¹ * (B x y+B y x) := by
 simp only [quadraticPolarApply,quadraticFromBilinearApply,map_add,LinearMap.add_apply]
 ring
theorem quadraticPolarInverse (h2 : (2:K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
 quadraticPolar (quadraticFromBilinear B) = B := by
 ext x y
 rw [quadraticFromBilinearPolar,hB.eq]
 field_simp; ring
theorem quadraticFormInverse (h2 : (2:K) ≠ 0) (Q : QuadraticForm K V) :
 quadraticFromBilinear (quadraticPolar Q) = Q := by
 ext x; rw [quadraticFromBilinearApply,quadraticPolarSelf]
 exact inv_mul_cancel_left₀ h2 (Q x)

def quadraticSymmetricForms : Submodule K (LinearMap.BilinForm K V) where
 carrier := {B | B.IsSymm}
 zero_mem' := ⟨fun _ _ => rfl⟩
 add_mem' := by intro B C hB hC; constructor; intro x y; simp [hB.eq x y,hC.eq x y]
 smul_mem' := by intro a B hB; constructor; intro x y; simp [hB.eq x y]

def quadraticPolarEquiv (h2 : (2:K) ≠ 0) :
 QuadraticForm K V ≃ₗ[K] quadraticSymmetricForms (K:=K) (V:=V) where
 toFun Q := ⟨quadraticPolar Q,quadraticPolarSymmetric Q⟩
 invFun B := quadraticFromBilinear B.val
 left_inv := quadraticFormInverse h2
 right_inv B := Subtype.ext (quadraticPolarInverse h2 B.val B.property)
 map_add' Q R := by
  apply Subtype.ext; ext x y
  simp [quadraticPolarApply]; ring
 map_smul' a Q := by
  apply Subtype.ext; ext x y
  simp [quadraticPolarApply,smul_eq_mul]; ring

theorem quadraticAssociatedFactor [Invertible (2:K)] (Q : QuadraticForm K V) :
 quadraticPolar Q = 2 • QuadraticMap.associated Q := by
 exact (QuadraticMap.two_nsmul_associated K Q).symm

theorem quadraticCharTwoAlternating (h2 : (2:K)=0) (Q : QuadraticForm K V) :
 ∀ x, quadraticPolar Q x x = 0 := by intro x; rw [quadraticPolarSelf,h2,zero_mul]
theorem quadraticCharTwoLostInformation :
 (0 : QuadraticForm (ZMod 2) (ZMod 2)) ≠ quadraticScalarSquare 1 ∧
 quadraticPolar (0 : QuadraticForm (ZMod 2) (ZMod 2)) =
 quadraticPolar (quadraticScalarSquare (1 : ZMod 2)) := by
 constructor
 · intro h; have h1 := congrArg (fun Q : QuadraticForm (ZMod 2) (ZMod 2) => Q 1) h
   norm_num [quadraticScalarSquareApply] at h1
 · apply LinearMap.ext₂; intro x y; change 0 = _; rw [quadraticScalarSquarePolar]
   simp [show (2:ZMod 2)=0 by decide]
theorem quadraticCharTwoMissingForm :
 ¬∃ Q : QuadraticForm (ZMod 2) (ZMod 2), quadraticPolar Q 1 1 = 1 := by
 rintro ⟨Q,h⟩
 have hz := quadraticCharTwoAlternating (by decide : (2:ZMod 2)=0) Q 1
 exact zero_ne_one (hz.symm.trans h)

theorem quadraticDiagonalBasis [FiniteDimensional K V] (h2 : (2:K) ≠ 0)
 (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
 ∃ b : Basis (Fin (Module.finrank K V)) K V, ∀ i j, i≠j → B (b i) (b j)=0 := by
 letI : Invertible (2:K) := invertibleOfNonzero h2
 obtain ⟨b,hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
   (LinearMap.BilinForm.isSymm_iff.mp hB)
 exact ⟨b,hb⟩

def quadraticNullspace (B : LinearMap.BilinForm K V) : Submodule K V := B.ker
theorem quadraticNullspaceMem (B : LinearMap.BilinForm K V) (x : V) :
 x ∈ quadraticNullspace B ↔ ∀ y, B x y = 0 := by
 simp [quadraticNullspace,LinearMap.mem_ker,LinearMap.ext_iff]
theorem quadraticRadicalConvention [Invertible (2:K)] (Q : QuadraticForm K V) :
 Q.radical = quadraticNullspace (quadraticPolar Q) := Q.radical_eq_ker_polarBilin

theorem quadraticNondegenerateConvention [Invertible (2:K)] (Q : QuadraticForm K V) :
 quadraticNondegenerate Q ↔ Q.radical = ⊥ := by
 rw [quadraticNondegenerate,quadraticPolar]
 change LinearMap.Nondegenerate Q.polarBilin ↔ Q.radical = ⊥
 rw [QuadraticMap.nondegenerate_polar_iff,
  QuadraticMap.nondegenerate_iff_radical_eq_bot]

theorem quadraticDiagonalNullspace {ι : Type w} [Fintype ι] [DecidableEq ι]
 (B : LinearMap.BilinForm K V) (b : Basis ι K V)
 (hb : ∀ i j, i≠j → B (b i) (b j)=0) (x : V) :
 x ∈ quadraticNullspace B ↔ ∀ i, b.repr x i * B (b i) (b i) = 0 := by
 have heval (i : ι) : B x (b i) = b.repr x i * B (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_single i
  · intro j hj hji; rw [hb j i hji,mul_zero]
  · intro hi; exact (hi (Finset.mem_univ i)).elim
 rw [quadraticNullspaceMem]
 constructor
 · intro hx i; rw [← heval]; exact hx (b i)
 · intro hx y
   rw [← b.sum_repr y]
   rw [map_sum]
   simp only [map_smul,smul_eq_mul,heval,hx,mul_zero,Finset.sum_const_zero]

theorem quadraticNullCount [NeZero (2:K)] {ι : Type w} [Fintype ι]
 (Q : QuadraticForm K V) (d : ι → K)
 (h : Q.Equivalent (QuadraticMap.weightedSumSquares K d)) :
 Module.finrank K Q.radical = {i | d i=0}.ncard :=
 QuadraticForm.finrank_radical_of_equiv_weightedSumSquares h
theorem quadraticNullDimensionInvariant {W : Type w} [AddCommGroup W] [Module K W]
 {Q : QuadraticForm K V} {R : QuadraticForm K W} (h : Q.Equivalent R) :
 Module.finrank K Q.radical = Module.finrank K R.radical := h.rank_radical_eq

theorem quadraticComplexNormal [Module ℂ V] [FiniteDimensional ℂ V]
 (Q : QuadraticForm ℂ V) :
 ∃ d : Fin (Module.finrank ℂ V) → ℂ,
 (∀ i, d i=0 ∨ d i=1) ∧ Q.Equivalent (QuadraticMap.weightedSumSquares ℂ d) := by
 classical
 obtain ⟨w,⟨e⟩⟩ := Q.equivalent_weightedSumSquares
 refine ⟨fun i => if w i=0 then 0 else 1,?_,⟨e.trans (QuadraticForm.isometryEquivSumSquares w)⟩⟩
 intro i; dsimp; split_ifs <;> simp

section Real
variable {M : Type v} [AddCommGroup M] [Module ℝ M]

/-- Holstein's ordered signature triple; NOT the scalar difference convention. -/
def quadraticSignature (Q : QuadraticForm ℝ M) : ℕ × ℕ × ℕ :=
 (sigPos Q,sigNeg Q,Module.finrank ℝ Q.radical)

theorem quadraticRealNormal [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
 ∃ d : Fin (Module.finrank ℝ M) → ℝ,
 (∀ i, d i = -1 ∨ d i=0 ∨ d i=1) ∧
 Q.Equivalent (QuadraticMap.weightedSumSquares ℝ d) :=
 Q.equivalent_one_zero_neg_one_weighted_sum_squared

theorem quadraticPositiveIndex (Q : QuadraticForm ℝ M) [FiniteDimensional ℝ M] :
 IsGreatest {r | ∃ U : Submodule ℝ M, Module.finrank ℝ U=r ∧ (Q.restrict U).PosDef}
 (sigPos Q) := sigPos_isGreatest Q
theorem quadraticNegativeIndex (Q : QuadraticForm ℝ M) [FiniteDimensional ℝ M] :
 IsGreatest {r | ∃ U : Submodule ℝ M, Module.finrank ℝ U=r ∧ ((-Q).restrict U).PosDef}
 (sigNeg Q) := sigNeg_isGreatest Q
theorem quadraticPositiveDimensionBound (Q : QuadraticForm ℝ M) [FiniteDimensional ℝ M]
 (U : Submodule ℝ M) (h : (Q.restrict U).PosDef) :
 Module.finrank ℝ U ≤ sigPos Q := le_sigPos_of_posDef Q h
theorem quadraticNonpositiveDimensionBound (Q : QuadraticForm ℝ M) [FiniteDimensional ℝ M]
 (U : Submodule ℝ M) (h : ∀ x∈U,Q x ≤ 0) :
 sigPos Q + Module.finrank ℝ U ≤ Module.finrank ℝ M :=
 QuadraticForm.sigPos_add_finrank_le_of_nonpos h
theorem quadraticSignatureSum (Q : QuadraticForm ℝ M) [FiniteDimensional ℝ M] :
 sigPos Q + sigNeg Q + Module.finrank ℝ Q.radical =
 Module.finrank ℝ M := QuadraticForm.sigPos_add_sigNeg_add_radical
theorem quadraticSignatureCounts {ι : Type w} [Fintype ι] (Q : QuadraticForm ℝ M) (d : ι→ℝ)
 (h : Q.Equivalent (QuadraticMap.weightedSumSquares ℝ d)) :
 quadraticSignature Q = ({i | 0<d i}.ncard,{i | d i<0}.ncard,{i | d i=0}.ncard) := by
 unfold quadraticSignature
 rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares h,
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares h,
  QuadraticForm.finrank_radical_of_equiv_weightedSumSquares h]
theorem quadraticSignatureInvariant {M' : Type w} [AddCommGroup M'] [Module ℝ M']
 (Q : QuadraticForm ℝ M) (R : QuadraticForm ℝ M') (h : Q.Equivalent R) :
 quadraticSignature Q = quadraticSignature R := by
 unfold quadraticSignature; rw [h.sigPos_eq,h.sigNeg_eq,h.rank_radical_eq]

theorem quadraticSylvester [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
 ∃ d : Fin (Module.finrank ℝ M) → ℝ,
 (∀ i, d i = -1 ∨ d i=0 ∨ d i=1) ∧
 Q.Equivalent (QuadraticMap.weightedSumSquares ℝ d) ∧
 quadraticSignature Q = ({i | 0<d i}.ncard,{i | d i<0}.ncard,{i | d i=0}.ncard) := by
 obtain ⟨d,hd,he⟩ := quadraticRealNormal Q
 exact ⟨d,hd,he,quadraticSignatureCounts Q d he⟩

theorem quadraticWeightedPositive {ι : Type w} [Fintype ι] [DecidableEq ι]
 (d : ι → ℝ) : (QuadraticMap.weightedSumSquares ℝ d).PosDef ↔ ∀ i, 0<d i := by
 constructor
 · intro h i
   have hz : (Pi.single i (1:ℝ) : ι→ℝ) ≠ 0 := by
    intro hz; have := congrFun hz i; simpa using this
   simpa [QuadraticMap.weightedSumSquares_apply,Pi.single_apply] using h _ hz
 · intro hd x hx
   rw [QuadraticMap.weightedSumSquares_apply]
   apply Finset.sum_pos'
   · intro i hi; exact mul_nonneg (hd i).le (mul_self_nonneg _)
   · obtain ⟨i,hi⟩ : ∃ i,x i≠0 := by
      by_contra h; push_neg at h; exact hx (funext h)
     exact ⟨i,Finset.mem_univ i,mul_pos (hd i) (mul_self_pos.mpr hi)⟩

theorem quadraticWeightedSemidefinite {ι : Type w} [Fintype ι] [DecidableEq ι]
 (d : ι→ℝ) : (∀ x,(QuadraticMap.weightedSumSquares ℝ d) x ≥ 0) ↔ ∀ i, d i≥0 := by
 constructor
 · intro h i; simpa [QuadraticMap.weightedSumSquares_apply,Pi.single_apply] using h (Pi.single i 1)
 · intro hd x; rw [QuadraticMap.weightedSumSquares_apply]
   exact Finset.sum_nonneg (fun i hi => mul_nonneg (hd i) (mul_self_nonneg _))

theorem quadraticDefinitenessInvariant {M' : Type w} [AddCommGroup M'] [Module ℝ M']
 (Q : QuadraticForm ℝ M) (R : QuadraticForm ℝ M') (h : Q.Equivalent R) :
 Q.PosDef ↔ R.PosDef := by
 obtain ⟨e⟩ := h
 constructor
 · intro h y hy
   rw [← e.apply_symm_apply y,e.map_app]
   apply h
   intro hz; apply hy; rw [← e.apply_symm_apply y,hz,map_zero]
 · intro h x hx
   rw [← e.map_app]
   apply h
   intro hz; apply hx; exact e.injective (by simpa using hz)

end Real

def quadraticMinkowski (c : ℝ) : QuadraticForm ℝ (Fin 4 → ℝ) :=
 QuadraticMap.weightedSumSquares ℝ ![1,1,1,-c^2]
theorem quadraticMinkowskiApply (c : ℝ) (x : Fin 4 → ℝ) :
 quadraticMinkowski c x = x 0 ^2+x 1 ^2+x 2 ^2-c^2*x 3 ^2 := by
 simp [quadraticMinkowski,QuadraticMap.weightedSumSquares_apply,Fin.sum_univ_succ,smul_eq_mul,pow_two]; ring
theorem quadraticMinkowskiPolar (c : ℝ) (x y : Fin 4 → ℝ) :
 quadraticPolar (quadraticMinkowski c) x y =
 2*(x 0*y 0+x 1*y 1+x 2*y 2-c^2*x 3*y 3) := by
 simp only [quadraticPolarApply,quadraticMinkowskiApply,Pi.add_apply]; ring
theorem quadraticMinkowskiIsotropic :
 (fun _ : Fin 4 => (0:ℝ)) ≠ ![1,0,0,1] ∧ quadraticMinkowski 1 ![1,0,0,1]=0 := by
 constructor
 · intro h; have := congrFun h 0; norm_num at this
 · norm_num [quadraticMinkowskiApply]

theorem quadraticMinkowskiSignature (c : ℝ) (hc : c≠0) :
 quadraticSignature (quadraticMinkowski c) = (3,1,0) := by
 classical
 have hp : {i : Fin 4 | 0 < (![1,1,1,-c^2] : Fin 4→ℝ) i} = {0,1,2} := by
  ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg c]
 have hn : {i : Fin 4 | (![1,1,1,-c^2] : Fin 4→ℝ) i < 0} = {3} := by
  ext i; fin_cases i <;> simp [sq_pos_of_ne_zero hc]
 have hz : {i : Fin 4 | (![1,1,1,-c^2] : Fin 4→ℝ) i = 0} = ∅ := by
  ext i; fin_cases i <;> simp [hc]
 have he : (quadraticMinkowski c).Equivalent (QuadraticMap.weightedSumSquares ℝ ![1,1,1,-c^2]) :=
  ⟨QuadraticMap.IsometryEquiv.refl _⟩
 rw [quadraticSignatureCounts _ _ he,hp,hn,hz]
 norm_num

theorem quadraticMinkowskiIndefinite (c : ℝ) (hc : c≠0) :
 (∃ x, 0<quadraticMinkowski c x) ∧ (∃ x,quadraticMinkowski c x<0) := by
 constructor
 · exact ⟨![1,0,0,0],by norm_num [quadraticMinkowskiApply]⟩
 · refine ⟨![0,0,0,1],?_⟩
   simpa [quadraticMinkowskiApply] using neg_neg_of_pos (sq_pos_of_ne_zero hc)

/-- A coordinate normal form for the BILINEAR self-values, with coefficients ±1/0.
Using B.toQuadraticMap here (not Holstein's half) fixes the factor of two. -/
theorem quadraticRealSelfNormal {M : Type v} [AddCommGroup M] [Module ℝ M]
 [FiniteDimensional ℝ M] (B : LinearMap.BilinForm ℝ M) :
 ∃ d : Fin (Module.finrank ℝ M) → ℝ,
 ∃ e : M ≃ₗ[ℝ] (Fin (Module.finrank ℝ M) → ℝ),
 (∀ i,d i = -1 ∨ d i=0 ∨ d i=1) ∧
 ∀ x, B (e.symm x) (e.symm x) = ∑ i,d i*x i*x i := by
 obtain ⟨d,hd,⟨e⟩⟩ := quadraticRealNormal B.toQuadraticMap
 refine ⟨d,e.toLinearEquiv,hd,?_⟩
 intro x
 simpa only [QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv,QuadraticMap.IsometryEquiv.coe_toLinearEquiv,LinearMap.BilinMap.toQuadraticMap_apply,QuadraticMap.weightedSumSquares_apply,smul_eq_mul,mul_assoc] using e.symm.map_app x

theorem quadraticComplexSelfNormal {M : Type v} [AddCommGroup M] [Module ℂ M]
 [FiniteDimensional ℂ M] (B : LinearMap.BilinForm ℂ M) :
 ∃ d : Fin (Module.finrank ℂ M) → ℂ,
 ∃ e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ),
 (∀ i,d i=0 ∨ d i=1) ∧
 ∀ x, B (e.symm x) (e.symm x) = ∑ i,d i*x i*x i := by
 obtain ⟨d,hd,⟨e⟩⟩ := quadraticComplexNormal B.toQuadraticMap
 refine ⟨d,e.toLinearEquiv,hd,?_⟩
 intro x
 simpa only [QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv,QuadraticMap.IsometryEquiv.coe_toLinearEquiv,LinearMap.BilinMap.toQuadraticMap_apply,QuadraticMap.weightedSumSquares_apply,smul_eq_mul,mul_assoc] using e.symm.map_app x

theorem quadraticWeightedPolar {ι : Type w} [Fintype ι]
 (d : ι→K) (x y : ι→K) :
 quadraticPolar (QuadraticMap.weightedSumSquares K d) x y = 2*∑ i,d i*x i*y i := by
 simp only [quadraticPolarApply,QuadraticMap.weightedSumSquares_apply,Pi.add_apply,smul_eq_mul]
 rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
 apply Finset.sum_congr rfl; intro i hi; ring

theorem quadraticBilinearCoordinates {ι : Type w} [Fintype ι]
 (h2 : (2:K)≠0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
 (d : ι→K) (e : B.toQuadraticMap.IsometryEquiv (QuadraticMap.weightedSumSquares K d))
 (x y : ι→K) : B (e.symm x) (e.symm y) = ∑ i,d i*x i*y i := by
 have hp : quadraticPolar B.toQuadraticMap (e.symm x) (e.symm y) =
   quadraticPolar (QuadraticMap.weightedSumSquares K d) x y := by
  simp only [quadraticPolarApply]
  rw [← map_add e.symm x y,e.symm.map_app,e.symm.map_app,e.symm.map_app]
 have hleft : quadraticPolar B.toQuadraticMap (e.symm x) (e.symm y) =
   2*B (e.symm x) (e.symm y) := by
  simp only [quadraticPolarApply,LinearMap.BilinMap.toQuadraticMap_apply,map_add,LinearMap.add_apply]
  rw [hB.eq (e.symm y) (e.symm x)]; ring
 rw [hleft,quadraticWeightedPolar] at hp
 exact mul_left_cancel₀ h2 hp

theorem quadraticRealBilinearNormal {M : Type v} [AddCommGroup M] [Module ℝ M]
 [FiniteDimensional ℝ M] (B : LinearMap.BilinForm ℝ M) (hB : B.IsSymm) :
 ∃ d : Fin (Module.finrank ℝ M) → ℝ,
 ∃ e : M ≃ₗ[ℝ] (Fin (Module.finrank ℝ M) → ℝ),
 (∀ i,d i = -1 ∨ d i=0 ∨ d i=1) ∧
 ∀ x y, B (e.symm x) (e.symm y) = ∑ i,d i*x i*y i := by
 obtain ⟨d,hd,⟨e⟩⟩ := quadraticRealNormal B.toQuadraticMap
 refine ⟨d,e.toLinearEquiv,hd,?_⟩
 intro x y
 simpa only [QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv,QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
   using quadraticBilinearCoordinates (by norm_num : (2:ℝ)≠0) B hB d e x y

theorem quadraticComplexBilinearNormal {M : Type v} [AddCommGroup M] [Module ℂ M]
 [FiniteDimensional ℂ M] (B : LinearMap.BilinForm ℂ M) (hB : B.IsSymm) :
 ∃ d : Fin (Module.finrank ℂ M) → ℂ,
 ∃ e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ),
 (∀ i,d i=0 ∨ d i=1) ∧
 ∀ x y, B (e.symm x) (e.symm y) = ∑ i,d i*x i*y i := by
 obtain ⟨d,hd,⟨e⟩⟩ := quadraticComplexNormal B.toQuadraticMap
 refine ⟨d,e.toLinearEquiv,hd,?_⟩
 intro x y
 simpa only [QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv,QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
   using quadraticBilinearCoordinates (by norm_num : (2:ℂ)≠0) B hB d e x y

end ILab.LinearAlgebra




