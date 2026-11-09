import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import ILab.LinearAlgebra.RingsPolynomials
import Mathlib.Tactic

/-! Holstein §9.3. The injectivity condition is additional to Mathlib's
Algebra structure. `degree` uses bottom for minus infinity; `natDegree`
is used only with explicit nonzero hypotheses where the source needs them.
The complex existence theorem below uses Mathlib's analytic proof.
No claim is made that this verifies the browser implementation. -/
namespace ILab.LinearAlgebra
open Polynomial

section Algebras
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
def HolsteinAlgebra : Prop := Function.Injective (algebraMap R A)
theorem polynomialScalarsCentral (r : R) (a : A) : algebraMap R A r * a = a * algebraMap R A r :=
  Algebra.commutes r a
theorem algebraHomPreservesScalars {B : Type*} [Ring B] [Algebra R B]
    (φ : A →ₐ[R] B) (r : R) : φ (algebraMap R A r) = algebraMap R B r := φ.commutes r
theorem polynomialUniversalProperty (a : A) :
    ∃! φ : R[X] →ₐ[R] A, φ X = a := by
  refine ⟨aeval a, aeval_X a, ?_⟩
  intro φ hφ
  apply Polynomial.algHom_ext
  simpa using hφ
theorem polynomialEvaluationAdd (a : A) (f g : R[X]) : aeval a (f+g)=aeval a f+aeval a g :=
  map_add (aeval a) f g
theorem polynomialEvaluationMul (a : A) (f g : R[X]) : aeval a (f*g)=aeval a f*aeval a g :=
  map_mul (aeval a) f g
theorem polynomialEvaluationConstant (a : A) (r : R) : aeval a (C r)=algebraMap R A r :=
  aeval_C a r
theorem polynomialEvaluationPower (a : A) (n : ℕ) : aeval a (X^n:R[X])=a^n := aeval_X_pow a
end Algebras

theorem fieldAlgebraIsHolstein {K A : Type*} [Field K] [Ring A] [Nontrivial A] [Algebra K A] :
    HolsteinAlgebra (R:=K) (A:=A) := (algebraMap K A).injective

section Polynomials
variable {R : Type*} [CommRing R]
theorem polynomialConstantsInjective : Function.Injective (C : R → R[X]) := C_injective
theorem polynomialFiniteSupport (f : R[X]) : {n : ℕ | f.coeff n ≠ 0}.Finite := by
  exact f.support.finite_toSet.subset (by intro n hn; exact mem_support_iff.mpr hn)
theorem polynomialCoefficientAddition (f g : R[X]) (n : ℕ) :
    (f+g).coeff n=f.coeff n+g.coeff n := polynomialSumCoefficient f g n
theorem polynomialCoefficientProduct (f g : R[X]) (n : ℕ) :
    (f*g).coeff n=∑ ij ∈ Finset.antidiagonal n, f.coeff ij.1*g.coeff ij.2 := by
  exact Polynomial.coeff_mul f g n
theorem polynomialDegreeZero : (0:R[X]).degree=⊥ := Polynomial.degree_zero
theorem polynomialDegreeSum (f g : R[X]) : (f+g).degree≤max f.degree g.degree := degree_add_le f g
theorem polynomialDegreeProductBound (f g : R[X]) : (f*g).degree≤f.degree+g.degree := degree_mul_le f g
theorem polynomialDivisionOriginal :
    (X^4-1:R[X])=(X^3+X^2+X+1)*(X-1) := by ring
theorem rootIffLinearFactor (f : R[X]) (a : R) : f.eval a=0 ↔ X-C a ∣ f := by
  exact (Polynomial.dvd_iff_isRoot).symm
theorem polynomialRemainderAtRoot (f : R[X]) (a : R) : f %ₘ (X-C a)=C (f.eval a) :=
  modByMonic_X_sub_C_eq_C_eval f a
end Polynomials

section Domain
variable {R : Type*} [CommRing R] [IsDomain R]
theorem polynomialDegreeProduct (f g : R[X]) : (f*g).degree=f.degree+g.degree := degree_mul

/-- The full coefficient-ring version of 9.3.9, not merely its field special case. -/
theorem polynomialDivisionWithUnitLeading (f g : R[X]) (hf : f ≠ 0)
    (hu : IsUnit f.leadingCoeff) :
    ∃! qr : R[X] × R[X], g=qr.1*f+qr.2 ∧ qr.2.degree<f.degree := by
  let u : Rˣ := hu.unit
  let d : R[X] := C (↑u⁻¹ : R)*f
  have hd : d.Monic := by
    change (C (↑hu.unit⁻¹ : R)*f).Monic
    rw [Monic, leadingCoeff_mul, leadingCoeff_C]
    simp [hu.unit_spec]
  have hdeg : d.degree=f.degree := by
    dsimp [d]; rw [degree_mul, degree_C (Units.ne_zero _), zero_add]
  have hback : C (↑u : R)*d=f := by
    dsimp [d]; rw [← mul_assoc,← C_mul]; simp
  let Q := g /ₘ d
  let T := g %ₘ d
  have heq : g=(Q*C (↑u⁻¹:R))*f+T := by
    have he:=modByMonic_add_div g d
    dsimp [Q,T,d] at *
    simpa only [mul_assoc,mul_comm,mul_left_comm,add_comm] using he.symm
  refine ⟨(Q*C (↑u⁻¹:R),T), ⟨heq,by simpa [T,hdeg] using degree_modByMonic_lt g hd⟩,?_⟩
  rintro ⟨q,r⟩ ⟨he,hr⟩
  have hn : r+d*(q*C (↑u:R))=g := by
    calc
      r+d*(q*C (↑u:R)) = q*(C (↑u:R)*d)+r := by ring
      _ = g := by rw [hback]; exact he.symm
  have huni:=div_modByMonic_unique (q*C (↑u:R)) r hd ⟨hn,by simpa [hdeg] using hr⟩
  apply Prod.ext
  · change q=Q*C (↑u⁻¹:R)
    rw [show Q=q*C (↑u:R) from huni.1]
    rw [mul_assoc,← C_mul]; simp
  · exact huni.2.symm

theorem polynomialRootFactorUnique (f : R[X]) (a : R) (ha : f.eval a=0) :
    ∃! g : R[X], f=(X-C a)*g := by
  obtain ⟨g,hg⟩ := (rootIffLinearFactor f a).mp ha
  refine ⟨g,hg,?_⟩
  intro h hh
  exact mul_left_cancel₀ (X_sub_C_ne_zero a) (hh.symm.trans hg)
theorem polynomialRootFactorDegree (f g : R[X]) (a : R) (hf : f≠0)
    (he : f=(X-C a)*g) : f.natDegree=g.natDegree+1 := by
  have hg : g≠0 := by intro h; simp [h] at he; exact hf he
  rw [he,natDegree_mul (X_sub_C_ne_zero a) hg,natDegree_X_sub_C,add_comm]
theorem polynomialRootCount (f : R[X]) [DecidableEq R] : f.roots.toFinset.card≤f.natDegree := by
  exact (Multiset.toFinset_card_le _).trans (card_roots' f)
theorem polynomialFunctionInjective [Infinite R] : Function.Injective (fun f : R[X] => f.eval) := by
  intro f g h; exact Polynomial.funext (congrFun h)
theorem polynomialMultiplicityMax (f : R[X]) (hf : f≠0) (a : R) (n : ℕ) :
    n≤f.rootMultiplicity a ↔ (X-C a)^n ∣ f := le_rootMultiplicity_iff hf
theorem polynomialMultiplicityResidual (f : R[X]) (hf : f≠0) (a : R) :
    ∃ g, f=(X-C a)^f.rootMultiplicity a*g ∧ ¬ g.IsRoot a := by
  obtain ⟨g,hg,hn⟩:=exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf a
  exact ⟨g,hg,by simpa only [← dvd_iff_isRoot] using hn⟩
theorem polynomialMultiplicityPositive (f : R[X]) (hf : f≠0) (a : R) :
    0<f.rootMultiplicity a ↔ f.IsRoot a := rootMultiplicity_pos hf
theorem polynomialMultiplicityBound (f : R[X]) (a : R) : f.rootMultiplicity a≤f.natDegree := by
  classical
  rw [← count_roots]
  exact (Multiset.count_le_card _ _).trans (card_roots' f)
end Domain

theorem polynomialF2DistinctSameFunction :
    formalPolynomialF2≠0 ∧ (fun x:ZMod 2 => formalPolynomialF2.eval x)=(fun _=>0) :=
  ⟨formalPolynomialF2Nonzero,formalPolynomialF2SameFunction⟩
theorem polynomialZ4DegreeFailure :
    (C (2:ZMod 4)*X:Polynomial (ZMod 4))≠0 ∧
    (C (2:ZMod 4)*X:Polynomial (ZMod 4))^2=0 := by
  constructor
  · intro h; have := congrArg (fun p:Polynomial (ZMod 4)=>p.coeff 1) h; norm_num only [coeff_mul_X,coeff_C,coeff_zero] at this
    exact (by decide : (2:ZMod 4)≠0) this
  · rw [mul_pow,← C_pow,show (2:ZMod 4)^2=0 by decide,C_0,zero_mul]
theorem polynomialIntegerTwoNotUnit : ¬IsUnit (2:ℤ) := by norm_num [Int.isUnit_iff]
theorem polynomialRealOriginal :
    (X^5-X^4+X^3-X^2:Polynomial ℝ)=X^2*(X-1)*(X^2+1) := by ring
theorem polynomialRealResidualNoRoot (x : ℝ) : (X^2+1:Polynomial ℝ).eval x≠0 := by
  simp only [eval_add,eval_pow,eval_X,eval_one]; positivity
theorem polynomialComplexOriginal :
    (X^5-X^4+X^3-X^2:Polynomial ℂ)=X^2*(X-1)*(X+C Complex.I)*(X-C Complex.I) := by
  have hi : (C Complex.I:Polynomial ℂ)^2 = -1 := by rw [← C_pow,Complex.I_sq]; simp
  linear_combination (X^2*(X-1))*hi
theorem polynomialComplexRootExists (f : Polynomial ℂ) (hf : 0<f.degree) :
    ∃ z:ℂ,f.IsRoot z := Complex.exists_root hf
theorem polynomialComplexSplits (f : Polynomial ℂ) : f.Splits := IsAlgClosed.splits f
theorem polynomialComplexFactorization (f : Polynomial ℂ) :
    f=C f.leadingCoeff*(f.roots.map (fun a=>X-C a)).prod := (polynomialComplexSplits f).eq_prod_roots
theorem polynomialComplexRootTotal (f : Polynomial ℂ) : f.roots.card=f.natDegree :=
  (polynomialComplexSplits f).natDegree_eq_card_roots.symm
end ILab.LinearAlgebra
