import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Holstein §2.3–2.4, printed40–44. Original errors remain in the source layer;
the following declarations state the explicitly separated intended mathematics. -/
namespace ILab.LinearAlgebra

theorem fieldAxioms (K : Type*) [Field K] (a b c : K) :
    (a+b)+c=a+(b+c) ∧ a+b=b+a ∧ a+0=a ∧ a+(-a)=0 ∧
    (a*b)*c=a*(b*c) ∧ a*b=b*a ∧ a*1=a ∧ (a+b)*c=a*c+b*c ∧ (0:K)≠1 := by
  exact ⟨add_assoc a b c,add_comm a b,add_zero a,add_neg_cancel a,
    mul_assoc a b c,mul_comm a b,mul_one a,add_mul a b c,zero_ne_one⟩

theorem fieldNonzeroInverse {K : Type*} [Field K] (a : K) (ha : a≠0) :
    a*a⁻¹=1 ∧ a⁻¹*a=1 := ⟨mul_inv_cancel₀ ha,inv_mul_cancel₀ ha⟩

theorem fieldZeroProduct {K : Type*} [Field K] (a : K) : (0:K)*a=0 ∧ a*0=0 := by
  have h : (0:K)*a=0*a+0*a := by rw [← add_mul,add_zero]
  have z : (0:K)*a=0 := by
    have h' : (0:K)+0*a=0*a+0*a := by simpa only [zero_add] using h
    exact (add_right_cancel h').symm
  exact ⟨z,by rw [mul_comm];exact z⟩

theorem fieldZeroNotInvertible {K : Type*} [Field K] : ¬∃ b:K,(0:K)*b=1 := by
  rintro ⟨b,h⟩
  exact zero_ne_one ((fieldZeroProduct b).1.symm.trans h)

theorem fieldNoZeroDivisors {K : Type*} [Field K] (a b : K) : a*b=0 ↔ a=0 ∨ b=0 := by
  constructor
  · intro h
    by_cases ha:a=0
    · exact Or.inl ha
    · right
      calc b=1*b := (one_mul b).symm
           _=(a⁻¹*a)*b := by rw [(fieldNonzeroInverse a ha).2]
           _=a⁻¹*(a*b) := mul_assoc _ _ _
           _=0 := by rw [h];exact (fieldZeroProduct (a⁻¹)).2
  · rintro (rfl|rfl)
    · exact (fieldZeroProduct b).1
    · exact (fieldZeroProduct a).2

theorem fieldMinusOne {K : Type*} [Field K] (a : K) : (-1:K)*a=-a := by
  have h : a+(-1:K)*a=0 := by
    calc a+(-1:K)*a=1*a+(-1:K)*a := by rw [one_mul]
         _=(1+(-1:K))*a := (add_mul _ _ _).symm
         _=0 := by simp
  exact eq_neg_of_add_eq_zero_right h

theorem fieldMinusOneSquared {K : Type*} [Field K] : (-1:K)*(-1)=1 := by
  rw [fieldMinusOne,neg_neg]

theorem fieldCancelNonzero {K : Type*} [Field K] (a b c : K) (ha:a≠0) (h:b*a=c*a) : b=c := by
  calc b=b*(a*a⁻¹) := by rw [(fieldNonzeroInverse a ha).1,mul_one]
       _=(b*a)*a⁻¹ := (mul_assoc _ _ _).symm
       _=(c*a)*a⁻¹ := by rw [h]
       _=c*(a*a⁻¹) := mul_assoc _ _ _
       _=c := by rw [(fieldNonzeroInverse a ha).1,mul_one]

theorem rationalTwoInverse : (2:ℚ)*(1/2)=1 := by norm_num
theorem integerTwoNotInvertible : ¬∃b:ℤ,(2:ℤ)*b=1 := by
  rintro ⟨b,h⟩; omega
theorem integersNoZeroDivisors (a b:ℤ) : a*b=0 ↔ a=0 ∨ b=0 := mul_eq_zero
theorem zeroCancellationFails : (1:ℚ)*0=2*0 ∧ (1:ℚ)≠2 := by norm_num
theorem fieldTwoRules : (1:ZMod 2)+1=0 ∧ (1:ZMod 2)*1=1 := by decide
noncomputable def fieldTwoStructure : Field (ZMod 2) := inferInstance
noncomputable def fieldThreeStructure : Field (ZMod 3) := inferInstance
theorem fieldThreeInverse : (2:ZMod 3)*2=1 := by decide
theorem modulusSixZeroDivisors : (2:ZMod 6)≠0 ∧ (3:ZMod 6)≠0 ∧ (2:ZMod 6)*3=0 := by decide
theorem modulusFourNotInvertible : ¬∃b:ZMod 4,(2:ZMod 4)*b=1 := by decide

theorem complexComponentwiseFails :
    ((1:ℝ),(0:ℝ))*((0:ℝ),(1:ℝ))=(0,0) ∧ ((1:ℝ),(0:ℝ))≠(0,0) ∧ ((0:ℝ),(1:ℝ))≠(0,0) := by norm_num

def complexFromPair (a b:ℝ) : ℂ := ⟨a,b⟩
theorem complexPairProduct (a b c d:ℝ) :
    complexFromPair a b*complexFromPair c d=complexFromPair (a*c-b*d) (a*d+b*c) := rfl
theorem complexImaginarySquare : Complex.I*Complex.I=-1 := Complex.I_mul_I
theorem complexFieldAxioms (a b c:ℂ) :
    (a+b)*c=a*c+b*c ∧ a*b=b*a ∧ (a*b)*c=a*(b*c) ∧ (0:ℂ)≠1 :=
  ⟨add_mul a b c,mul_comm a b,mul_assoc a b c,zero_ne_one⟩
noncomputable def complexFieldStructure : Field ℂ := inferInstance
theorem complexInverseProduct (z:ℂ) (hz:z≠0) : z*z⁻¹=1 := (fieldNonzeroInverse z hz).1
theorem complexRealEmbeddingInjective : Function.Injective ((↑):ℝ→ℂ) := Complex.ofReal_injective
theorem complexConjugateCoordinates (a b:ℝ) :
    star (complexFromPair a b)=complexFromPair a (-b) := rfl
theorem complexModulusSquared (z:ℂ) : ‖z‖^2=z.re^2+z.im^2 := by
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply];ring
theorem complexConjugateLaws (z w:ℂ) :
    star (z+w)=star z+star w ∧ star (z*w)=star z*star w ∧ star (star z)=z := by simp [mul_comm]
theorem complexModulusLaws (z w:ℂ) : ‖z*w‖=‖z‖*‖w‖ ∧ ‖z+w‖≤‖z‖+‖w‖ := ⟨norm_mul z w,norm_add_le z w⟩
theorem complexInverseConjugate (z:ℂ) : z⁻¹=star z/(Complex.normSq z:ℂ) := by
  apply Complex.ext <;> simp [Complex.inv_re,Complex.inv_im,Complex.div_re,Complex.div_im,Complex.normSq_apply] <;> field_simp <;> ring

noncomputable def complexArgumentPositive (z:ℂ) : ℝ :=
  if Complex.arg z<0 then Complex.arg z+2*Real.pi else Complex.arg z
theorem complexArgumentPositiveRange (z:ℂ) :
    0≤complexArgumentPositive z ∧ complexArgumentPositive z<2*Real.pi := by
  unfold complexArgumentPositive
  have hp:=Real.pi_pos
  have lo:=Complex.neg_pi_lt_arg z
  have hi:=Complex.arg_le_pi z
  split_ifs <;> constructor <;> linarith
theorem complexPolarReconstruction (z:ℂ) :
    (‖z‖:ℂ)*(Real.cos (complexArgumentPositive z)+Real.sin (complexArgumentPositive z)*Complex.I)=z := by
  unfold complexArgumentPositive
  split_ifs <;> simpa only [← Complex.ofReal_cos,← Complex.ofReal_sin,Real.cos_add_two_pi,Real.sin_add_two_pi] using Complex.norm_mul_cos_add_sin_mul_I z

end ILab.LinearAlgebra
