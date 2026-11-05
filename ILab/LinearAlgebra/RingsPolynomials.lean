import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Holstein §2.5. Ring is unital; the initial nonunital definition is separate.
Original typographical errors are not asserted as Lean statements.
The prime-field certificate uses Mathlib characteristic theory; the original
Lagrange proof is retained in the original text and the proof navigator. -/
namespace ILab.LinearAlgebra

theorem nonUnitalRingLaws {R : Type*} [NonUnitalRing R] (a b c : R) :
    a+b=b+a ∧ (a*b)*c=a*(b*c) ∧ a*(b+c)=a*b+a*c ∧ (a+b)*c=a*c+b*c :=
  ⟨add_comm a b,mul_assoc a b c,mul_add a b c,add_mul a b c⟩

theorem ringLaws {R : Type*} [Ring R] (a b c : R) :
    a+b=b+a ∧ (a*b)*c=a*(b*c) ∧ a*(b+c)=a*b+a*c ∧
    (a+b)*c=a*c+b*c ∧ 1*a=a ∧ a*1=a ∧ a+(-a)=0 :=
  ⟨add_comm a b,mul_assoc a b c,mul_add a b c,add_mul a b c,one_mul a,mul_one a,add_neg_cancel a⟩

noncomputable def ringFromField (K : Type*) [Field K] : CommRing K := inferInstance

theorem ringZeroProducts {R : Type*} [Ring R] (a : R) : 0*a=0 ∧ a*0=0 := by
  have h : a*0+a*0=a*0 := by rw [← mul_add,add_zero]
  have hr : a*0=0 := by
    apply add_left_cancel (a:=a*0)
    simpa only [add_zero] using h
  have h' : 0*a+0*a=0*a := by rw [← add_mul,add_zero]
  have hl : 0*a=0 := by
    apply add_left_cancel (a:=0*a)
    simpa only [add_zero] using h'
  exact ⟨hl,hr⟩

def ringMatrixA : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0,1;0,0]
def ringMatrixB : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0,0;1,0]

theorem matrixRingNoncommutative : ringMatrixA*ringMatrixB≠ringMatrixB*ringMatrixA := by
  intro h
  have hh := congrArg (fun M:Matrix (Fin 2) (Fin 2) (ZMod 2)=>M 0 0) h
  norm_num [ringMatrixA,ringMatrixB,Matrix.mul_apply,Fin.sum_univ_two] at hh

def integerRingStructure : CommRing ℤ := inferInstance

def pointwiseRingStructure (M R : Type*) [Ring R] : Ring (M→R) := inferInstance

theorem pointwiseRingLaws {M R : Type*} [Ring R] (f g : M→R) (x : M) :
    (f+g) x=f x+g x ∧ (f*g) x=f x*g x ∧ (0:M→R) x=0 ∧ (1:M→R) x=1 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem functionWithZeroNotInvertible :
    let f : Bool→ℝ := fun b => if b then 1 else 0
    f≠0 ∧ ¬∃g:Bool→ℝ,f*g=1 := by
  dsimp
  constructor
  · intro h
    have := congrFun h true
    norm_num at this
  · rintro ⟨g,h⟩
    have := congrFun h false
    norm_num at this

theorem residueMultiplicationWellDefined (a b k l m : ℤ) :
    (a+m*k)*(b+m*l)=a*b+m*(k*b+a*l+m*k*l) := by ring

def residueRingStructure (m : ℕ) : CommRing (ZMod m) := inferInstance

theorem residueFourZeroDivisor :
    (2:ZMod 4)≠0 ∧ (2:ZMod 4)*(2:ZMod 4)=0 ∧ ¬IsUnit (2:ZMod 4) := by decide

theorem residueFieldIffPrime (m : ℕ) (hm : 2≤m) : IsField (ZMod m) ↔ m.Prime := by
  constructor
  · intro h
    letI := h.toField
    exact (CharP.char_is_prime_or_zero (ZMod m) m).resolve_right (by omega)
  · intro h
    letI : Fact m.Prime := ⟨h⟩
    exact Field.toIsField (ZMod m)

theorem primeResidueInverse (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha:a≠0) :
    ∃b:ZMod p,a*b=1 := ⟨a⁻¹,mul_inv_cancel₀ ha⟩

theorem residueCharacteristic (m : ℕ) : ringChar (ZMod m)=m := ringChar.eq (ZMod m) m

theorem rationalCharacteristic : ringChar ℚ=0 := ringChar.eq ℚ 0

theorem realCharacteristic : ringChar ℝ=0 := ringChar.eq ℝ 0

theorem zeroModulusTwoNotInvertible : ¬∃b:ZMod 0,(2:ZMod 0)*b=1 := by
  rintro ⟨b,h⟩
  change ℤ at b
  change (2:ℤ)*b=1 at h
  omega

theorem modulusOneTrivial : (0:ZMod 1)=1 := by decide

theorem ringHomLaws {R S : Type*} [Ring R] [Ring S] (f:R→+*S) (a b:R) :
    f (a+b)=f a+f b ∧ f (a*b)=f a*f b ∧ f 1=1 :=
  ⟨f.map_add a b,f.map_mul a b,f.map_one⟩

def canonicalResidueRingHom (m : ℕ) : ℤ→+*ZMod m := Int.castRingHom (ZMod m)

theorem leastRepresentativeFails :
    ((3:ZMod 4)+1).val≠(3:ZMod 4).val+(1:ZMod 4).val := by decide

noncomputable def conjugationRingHom : ℂ→+*ℂ where
  toFun := star
  map_one' := by simp
  map_mul' := by intro a b; simp [mul_comm]
  map_zero' := by simp
  map_add' := by intro a b; simp

theorem conjugationRingHomInvolutive (z:ℂ) :
    conjugationRingHom (conjugationRingHom z)=z := by simp [conjugationRingHom]

theorem ringHomFieldKernelZero {K E : Type*} [Field K] [Ring E] [Nontrivial E]
    (f:K→+*E) (a:K) (h:f a=0) : a=0 := by
  by_contra ha
  have bad : (1:E)=0 := calc
    1=f 1 := f.map_one.symm
    _=f (a*a⁻¹) := by rw [mul_inv_cancel₀ ha]
    _=f a*f (a⁻¹) := f.map_mul _ _
    _=0 := by rw [h,zero_mul]
  exact one_ne_zero bad

theorem ringHomFromFieldInjective {K E : Type*} [Field K] [Ring E] [Nontrivial E]
    (f:K→+*E) : Function.Injective f := by
  intro x y h
  apply sub_eq_zero.mp
  apply ringHomFieldKernelZero f
  rw [map_sub,h,sub_self]

noncomputable def polynomialRingStructure (R : Type*) [CommRing R] : CommRing (Polynomial R) := inferInstance

theorem polynomialSumCoefficient {R : Type*} [CommRing R] (f g:Polynomial R) (n:ℕ) :
    (f+g).coeff n=f.coeff n+g.coeff n := Polynomial.coeff_add f g n

theorem polynomialProductCoefficient {R : Type*} [CommRing R] (f g:Polynomial R) (n:ℕ) :
    (f*g).coeff n=∑ k ∈ Finset.range (n+1), f.coeff k*g.coeff (n-k) := by
  rw [Polynomial.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f.coeff i*g.coeff j) n

def polynomialEvaluation (R : Type*) [CommRing R] (x:R) : Polynomial R→+*R := Polynomial.evalRingHom x

theorem polynomialEvaluationLaws {R : Type*} [CommRing R] (f g:Polynomial R) (x:R) :
    (f+g).eval x=f.eval x+g.eval x ∧ (f*g).eval x=f.eval x*g.eval x ∧
    (1:Polynomial R).eval x=1 :=
  ⟨Polynomial.eval_add,Polynomial.eval_mul,by simp⟩

noncomputable def formalPolynomialF2 : Polynomial (ZMod 2) := Polynomial.X+Polynomial.X^2

theorem formalPolynomialF2Nonzero : formalPolynomialF2≠0 := by
  intro h
  have hh := congrArg (fun p:Polynomial (ZMod 2)=>p.coeff 1) h
  norm_num [formalPolynomialF2,Polynomial.coeff_X_pow] at hh

theorem formalPolynomialF2Values (x:ZMod 2) : formalPolynomialF2.eval x=0 := by
  have hx : x+x^2=0 := by fin_cases x <;> decide
  simpa only [formalPolynomialF2,Polynomial.eval_add,Polynomial.eval_X_pow,Polynomial.eval_X] using hx

theorem formalPolynomialF2SameFunction :
    (fun x:ZMod 2=>formalPolynomialF2.eval x)=(fun _=>0) := funext formalPolynomialF2Values

theorem polynomialDifferenceOfSquares {R : Type*} [CommRing R] :
    (Polynomial.X-1:Polynomial R)*(Polynomial.X+1)=Polynomial.X^2-1 := by ring

theorem zeroPolynomialDegree {R : Type*} [CommRing R] :
    (0:Polynomial R).degree=⊥ := Polynomial.degree_zero

theorem polynomialXNotInvertible {K : Type*} [Field K] :
    ¬∃g:Polynomial K,Polynomial.X*g=1 := by
  rintro ⟨g,h⟩
  have := congrArg (Polynomial.eval (0:K)) h
  simp at this

end ILab.LinearAlgebra
