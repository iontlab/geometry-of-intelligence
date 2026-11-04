import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! Holstein, sections 1.1--1.2, printed pp. 2--10.
The statements use an arbitrary real vector space when the proof is dimension independent.
For the centroid, independence of b-a and c-a is the usual non-collinearity condition.
The two documented typographical errors in 1.2.8 and 1.2.9 are not used as premises.
-/
namespace ILab.LinearAlgebra
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
local instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

def parametricLine (p v : V) : Set V := {x | ∃ t : ℝ, p + t • v = x}

theorem lineFoot (p v : V) : p ∈ parametricLine p v := ⟨0, by simp⟩

theorem lineStep (p v : V) : p + v ∈ parametricLine p v := ⟨1, by simp⟩

theorem zeroDirection (p : V) : parametricLine p 0 = {p} := by
 ext x
 simp [parametricLine]

theorem sameParametricLine (p q v w : V) (_hv : v ≠ 0) (hw : w ≠ 0) :
    parametricLine p v = parametricLine q w ↔
      q ∈ parametricLine p v ∧ ∃ s : ℝ, w = s • v := by
 constructor
 · intro h
   have hq : q ∈ parametricLine p v := h ▸ lineFoot q w
   have hqw : q + w ∈ parametricLine p v := h ▸ lineStep q w
   obtain ⟨s₁, hs₁⟩ := hq
   obtain ⟨s₂, hs₂⟩ := hqw
   refine ⟨⟨s₁, hs₁⟩, s₂-s₁, ?_⟩
   calc
    w = (q+w)-q := by abel
    _ = (p+s₂ • v)-(p+s₁ • v) := by rw [hs₁, hs₂]
    _ = (s₂-s₁) • v := by module
 · rintro ⟨⟨t₀, ht₀⟩, s, hs⟩
   have hn : s ≠ 0 := by
    intro hz
    apply hw
    simpa [hz] using hs
   ext x
   constructor
   · rintro ⟨t, ht⟩
     refine ⟨(t-t₀)/s, ?_⟩
     rw [← ht₀, hs, smul_smul, div_mul_cancel₀ _ hn]
     rw [← ht]
     module
   · rintro ⟨t, ht⟩
     refine ⟨t₀+t*s, ?_⟩
     rw [← ht, ← ht₀, hs]
     module

theorem lineThroughTwoPoints (p v a b : V) (hv : v ≠ 0)
    (ha : a ∈ parametricLine p v) (hb : b ∈ parametricLine p v) (hab : a ≠ b) :
    parametricLine p v = parametricLine a (b-a) := by
 have hba : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
 apply (sameParametricLine p a v (b-a) hv hba).2
 refine ⟨ha, ?_⟩
 obtain ⟨t₁, ht₁⟩ := ha
 obtain ⟨t₂, ht₂⟩ := hb
 refine ⟨t₂-t₁, ?_⟩
 rw [← ht₁, ← ht₂]
 module

omit [Module ℝ V] in
theorem vectorAdditionCommutative (x y : V) : x+y=y+x := add_comm x y

theorem scalarDistributivity (t : ℝ) (x y : V) : t • (x+y)=t • x+t • y :=
 smul_add t x y

noncomputable def arithmeticMidpoint (a b : V) : V := (1/2 : ℝ) • (a+b)

theorem arithmeticMidpoint_eq_midpoint (a b : V) :
    arithmeticMidpoint a b = midpoint ℝ a b := by
 simpa [arithmeticMidpoint, invOf_eq_inv] using (midpoint_eq_smul_add (R:=ℝ) a b).symm

theorem midpointEqualDisplacements (a b : V) :
    arithmeticMidpoint a b-a = b-arithmeticMidpoint a b := by
 unfold arithmeticMidpoint
 module

theorem midpointTwice (a b : V) : (2 : ℝ) • arithmeticMidpoint a b = a+b := by
 unfold arithmeticMidpoint
 module

theorem midpointOnJoiningLine (a b : V) :
    arithmeticMidpoint a b ∈ parametricLine a (b-a) := by
 refine ⟨1/2, ?_⟩
 unfold arithmeticMidpoint
 module

omit [Module ℝ V] in
theorem parallelogramOppositeSides (a b c d : V) (h : c-a=d-b) : b-a=d-c := by
 rw [eq_add_of_sub_eq h.symm]
 abel

theorem diagonalMidpoints (a b c d : V) (h : c-a=d-b) :
    arithmeticMidpoint a d = arithmeticMidpoint b c := by
 have hsum : a+d=b+c := by
  rw [eq_add_of_sub_eq h.symm]
  abel
 unfold arithmeticMidpoint
 rw [hsum]

theorem diagonalCommonPoint (a b c d : V) (h : c-a=d-b) :
    arithmeticMidpoint a d ∈ parametricLine a (d-a) ∧
    arithmeticMidpoint a d ∈ parametricLine b (c-b) := by
 constructor
 · exact midpointOnJoiningLine a d
 · rw [diagonalMidpoints a b c d h]
   exact midpointOnJoiningLine b c

noncomputable def triangleCentroid (a b c : V) : V := (1/3 : ℝ) • (a+b+c)

theorem centroidMedianParameter (a b c : V) :
    a+(2/3 : ℝ) • (arithmeticMidpoint b c-a) = triangleCentroid a b c := by
 unfold arithmeticMidpoint triangleCentroid
 module

theorem centroidOnMedians (a b c : V) :
    triangleCentroid a b c ∈ parametricLine a (arithmeticMidpoint b c-a) ∧
    triangleCentroid a b c ∈ parametricLine b (arithmeticMidpoint a c-b) ∧
    triangleCentroid a b c ∈ parametricLine c (arithmeticMidpoint a b-c) := by
 refine ⟨⟨2/3, centroidMedianParameter a b c⟩, ⟨2/3, ?_⟩, ⟨2/3, ?_⟩⟩
 · rw [centroidMedianParameter]
   unfold triangleCentroid
   congr 1
   abel
 · rw [centroidMedianParameter]
   unfold triangleCentroid
   congr 1
   abel

theorem centroidUnique (a b c x : V)
    (h : LinearIndependent ℝ ![b-a,c-a])
    (ha : x ∈ parametricLine a (arithmeticMidpoint b c-a))
    (hb : x ∈ parametricLine b (arithmeticMidpoint a c-b)) :
    x = triangleCentroid a b c := by
 obtain ⟨t, ht⟩ := ha
 obtain ⟨s, hs⟩ := hb
 have hc : ![t/2,t/2] = (![1-s,s/2] : Fin 2 → ℝ) := by
  apply h.fintypeLinearCombination_injective
  simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  calc
   (t/2) • (b-a)+(t/2) • (c-a) = x-a := by
    rw [← ht]
    unfold arithmeticMidpoint
    module
   _ = (1-s) • (b-a)+(s/2) • (c-a) := by
    rw [← hs]
    unfold arithmeticMidpoint
    module
 have hc₀ := congrFun hc 0
 have hc₁ := congrFun hc 1
 simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc₀ hc₁
 have ht' : t=2/3 := by linarith
 rw [← ht, ht']
 exact centroidMedianParameter a b c

theorem centroidIntersection (a b c : V) (h : LinearIndependent ℝ ![b-a,c-a]) :
    parametricLine a (arithmeticMidpoint b c-a) ∩
    parametricLine b (arithmeticMidpoint a c-b) ∩
    parametricLine c (arithmeticMidpoint a b-c) = {triangleCentroid a b c} := by
 ext x
 constructor
 · rintro ⟨⟨ha,hb⟩,_hc⟩
   exact centroidUnique a b c x h ha hb
 · intro hx
   have heq : x=triangleCentroid a b c := hx
   rw [heq]
   obtain ⟨ha,hb,hc⟩ := centroidOnMedians a b c
   exact ⟨⟨ha,hb⟩,hc⟩

theorem equationLineFirstCoefficient (a₁ a₂ c : ℝ) (ha : a₁ ≠ 0) (x : Fin 2 → ℝ) :
    a₁*x 0+a₂*x 1=c ↔
    x ∈ parametricLine ![c/a₁,0] ![a₂,-a₁] := by
 constructor
 · intro hx
   refine ⟨-x 1/a₁, ?_⟩
   ext i
   fin_cases i <;> simp
   · field_simp
     nlinarith
   · field_simp
 · rintro ⟨t, ht⟩
   rw [← ht]
   simp
   field_simp
   ring

theorem equationLineSecondCoefficient (a₂ c : ℝ) (ha : a₂ ≠ 0) (x : Fin 2 → ℝ) :
    a₂*x 1=c ↔ x ∈ parametricLine ![0,c/a₂] ![a₂,0] := by
 constructor
 · intro hx
   refine ⟨x 0/a₂, ?_⟩
   ext i
   fin_cases i <;> simp
   · field_simp
   · field_simp
     nlinarith
 · rintro ⟨t,ht⟩
   rw [← ht]
   simp
   field_simp

theorem equationSolutionIsLine (a : Fin 2 → ℝ) (c : ℝ) (ha : a ≠ 0) :
    ∃ p v : Fin 2 → ℝ, v ≠ 0 ∧
      {x | a 0*x 0+a 1*x 1=c} = parametricLine p v := by
 by_cases h₀ : a 0=0
 · have h₁ : a 1 ≠ 0 := by
    intro hz
    apply ha
    ext i
    fin_cases i <;> simp [h₀,hz]
   refine ⟨![0,c/a 1], ![a 1,0], ?_, ?_⟩
   · intro hz
     have := congrFun hz 0
     exact h₁ (by simpa using this)
   · ext x
     simp only [Set.mem_ofPred_eq, h₀, zero_mul, zero_add]
     exact equationLineSecondCoefficient (a 1) c h₁ x
 · refine ⟨![c/a 0,0], ![a 1,-a 0], ?_, ?_⟩
   · intro hz
     have := congrFun hz 1
     exact h₀ (by simpa using this)
   · ext x
     exact equationLineFirstCoefficient (a 0) (a 1) c h₀ x

end
end ILab.LinearAlgebra
