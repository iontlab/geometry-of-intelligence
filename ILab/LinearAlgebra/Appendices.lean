import ILab.LinearAlgebra.MinimalPolynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-! Appendices A–D. A is formalized directly. B records named steps and a
two-dimensional symbolic companion calculation. The existing Cayley–Hamilton
theorem verifies the end result, not the full alternative source proof.
C/D reuse existing declarations; no duplicate theorem wrappers are added. -/
noncomputable section
namespace ILab.LinearAlgebra
open scoped BigOperators
open Polynomial

theorem appendixEmptySum {G : Type*} [AddCommMonoid G] (a : ℕ → G) :
    ∑ i ∈ (∅ : Finset ℕ), a i = 0 := by simp

theorem appendixEmptyProduct {G : Type*} [CommMonoid G] (a : ℕ → G) :
    ∏ i ∈ (∅ : Finset ℕ), a i = 1 := by simp

theorem appendixDisjointSum {ι G : Type*} [DecidableEq ι] [AddCommMonoid G]
    (I J : Finset ι) (a : ι → G) (h : Disjoint I J) :
    ∑ i ∈ I ∪ J, a i = (∑ i ∈ I, a i) + ∑ i ∈ J, a i :=
  Finset.sum_union h

theorem appendixDisjointProduct {ι G : Type*} [DecidableEq ι] [CommMonoid G]
    (I J : Finset ι) (a : ι → G) (h : Disjoint I J) :
    ∏ i ∈ I ∪ J, a i = (∏ i ∈ I, a i) * ∏ i ∈ J, a i :=
  Finset.prod_union h

theorem appendixEmptyUnion {α : Type*} (A : Empty → Set α) :
    (⋃ i, A i) = ∅ := by ext x; simp

theorem appendixEmptySpan {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    (Submodule.span K (∅ : Set V) : Set V) = {0} := by simp

def appendixEmptyFunction (A : Type*) : Empty → A := Empty.elim

theorem appendixEmptyFunctionUnique {A : Type*} (f : Empty → A) :
    f = appendixEmptyFunction A := by funext x; exact x.elim

theorem appendixEmptyDependentChoiceUnique {A : Empty → Type*}
    (f g : (i : Empty) → A i) : f = g := by funext i; exact i.elim

theorem appendixEmptyProductCard {A : Type*} [Fintype A] :
    Fintype.card (Empty → A) = 1 := by simp

theorem appendixEmptyBijection : Function.Bijective (appendixEmptyFunction Empty) := by
  constructor
  · intro x; exact x.elim
  · intro x; exact x.elim

theorem appendixZeroFactorial : Nat.factorial 0 = 1 := rfl

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def appendixKrylov (f : Module.End K V) (v : V) (i : ℕ) : V := (f ^ i) v

theorem appendixKrylovZero (f : Module.End K V) (v : V) :
    appendixKrylov f v 0 = v := by simp [appendixKrylov]

theorem appendixKrylovSuccessor (f : Module.End K V) (v : V) (i : ℕ) :
    appendixKrylov f v (i+1) = f (appendixKrylov f v i) := by
  simp [appendixKrylov, pow_succ', Module.End.mul_apply]

theorem appendixKrylovFiniteBound [FiniteDimensional K V]
    (f : Module.End K V) (v : V) :
    ¬ LinearIndependent K (fun i : Fin (Module.finrank K V + 1) => appendixKrylov f v i) := by
  intro h
  have := h.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  omega

def appendixOrbitSpan (f : Module.End K V) (v : V) : Submodule K V :=
  Submodule.span K (Set.range (appendixKrylov f v))

theorem appendixKrylovInOrbitSpan (f : Module.End K V) (v : V) (i : ℕ) :
    appendixKrylov f v i ∈ appendixOrbitSpan f v :=
  Submodule.subset_span ⟨i,rfl⟩

theorem appendixOrbitSpanInvariant (f : Module.End K V) (v : V) :
    ∀ x ∈ appendixOrbitSpan f v, f x ∈ appendixOrbitSpan f v := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      rw [← appendixKrylovSuccessor]
      exact appendixKrylovInOrbitSpan f v (i+1)
  | zero => simpa using (appendixOrbitSpan f v).zero_mem
  | add x y hx hy ihx ihy => simpa using (appendixOrbitSpan f v).add_mem ihx ihy
  | smul a x hx ih => simpa using (appendixOrbitSpan f v).smul_mem a ih

def appendixRelationPolynomial {m : ℕ} (a : Fin m → K) : K[X] :=
  X^m + ∑ i : Fin m, C (a i) * X^(i:ℕ)

theorem appendixRelationPolynomialApply (f : Module.End K V) (v : V)
    {m : ℕ} (a : Fin m → K) :
    (aeval f (appendixRelationPolynomial a)) v =
      appendixKrylov f v m + ∑ i : Fin m, a i • appendixKrylov f v i := by
  simp [appendixRelationPolynomial, appendixKrylov, map_add, map_sum,
    Module.End.mul_apply, Finset.sum_apply]

theorem appendixKrylovRelationAnnihilates (f : Module.End K V) (v : V)
    {m : ℕ} (a : Fin m → K)
    (h : appendixKrylov f v m = - ∑ i : Fin m, a i • appendixKrylov f v i) :
    (aeval f (appendixRelationPolynomial a)) v = 0 := by
  rw [appendixRelationPolynomialApply, h, neg_add_cancel]

theorem appendixAnnihilatingFactor (f : Module.End K V) (v : V)
    (p g : K[X]) (h : (aeval f p) v = 0) :
    (aeval f (g*p)) v = 0 := by
  simp [map_mul, Module.End.mul_apply, h]

theorem appendixPointwiseZeroOperator (f : Module.End K V) (p : K[X])
    (h : ∀ v : V, v ≠ 0 → (aeval f p) v = 0) : aeval f p = 0 := by
  ext v
  by_cases hv : v=0
  · simp [hv]
  · exact h v hv

def appendixCompanionTwo (a b : K) : Matrix (Fin 2) (Fin 2) K := !![0,-a;1,-b]

theorem appendixCompanionTwoCharpoly (a b : K) :
    (appendixCompanionTwo a b).charpoly = X^2 + C b * X + C a := by
  rw [Matrix.charpoly_fin_two]
  simp [appendixCompanionTwo, Matrix.trace, Matrix.det_fin_two]

theorem appendixInvariantRangeFromIntertwining {W : Type*} [AddCommGroup W] [Module K W]
    (f : Module.End K V) (g : Module.End K W) (B : W →ₗ[K] V)
    (h : f.comp B = B.comp g) :
    ∀ x ∈ LinearMap.range B, f x ∈ LinearMap.range B := by
  intro x hx
  obtain ⟨w,rfl⟩ := hx
  refine ⟨g w,?_⟩
  exact (LinearMap.congr_fun h w).symm

end ILab.LinearAlgebra
