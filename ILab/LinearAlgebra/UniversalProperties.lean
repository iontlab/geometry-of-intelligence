import ILab.LinearAlgebra.QuotientSpaces
import ILab.LinearAlgebra.PolynomialTheory
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Bounds.Basic

/-! Holstein Chapter 11. Arbitrary fields, modules and index sets, without
finite-dimensional assumptions. Hom equivalences below are linear equivalences.
Holstein's injective scalar map is explicitly retained for polynomial objects.
No claim that these proofs verify JavaScript or diagram rendering. -/
namespace ILab.LinearAlgebra
open Function
universe u v w z

theorem universalInfimumCharacterization (A : Set ℝ) (x : ℝ) :
    IsGLB A x ↔ (∀ a ∈ A, x ≤ a) ∧ (∀ y, (∀ a ∈ A, y ≤ a) → y ≤ x) := Iff.rfl

theorem universalInfimumUnique (A : Set ℝ) (x y : ℝ)
    (hx : IsGLB A x) (hy : IsGLB A y) : x = y := by
  exact le_antisymm (hy.2 hx.1) (hx.2 hy.1)

theorem universalGcdPair (a b : ℕ) :
    (Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b) ∧
      ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ Nat.gcd a b :=
  ⟨⟨Nat.gcd_dvd_left a b,Nat.gcd_dvd_right a b⟩,fun _ => Nat.dvd_gcd⟩

theorem universalCommonDivisorUnique (A : Set ℕ) (n m : ℕ)
    (hn : (∀ a ∈ A, n ∣ a) ∧ ∀ d, (∀ a ∈ A, d ∣ a) → d ∣ n)
    (hm : (∀ a ∈ A, m ∣ a) ∧ ∀ d, (∀ a ∈ A, d ∣ a) → d ∣ m) : n = m :=
  Nat.dvd_antisymm (hm.2 n hn.1) (hn.2 m hm.1)

section Linear
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {T : Type z} [AddCommGroup T] [Module K T]

def universalKernelFactor (f : V →ₗ[K] W) (g : T →ₗ[K] V)
    (h : f.comp g = 0) : T →ₗ[K] LinearMap.ker f :=
  g.codRestrict (LinearMap.ker f) (by
    intro x
    change f (g x) = 0
    exact congrArg (fun a : T →ₗ[K] W => a x) h)

theorem universalKernelFactorization (f : V →ₗ[K] W) (g : T →ₗ[K] V)
    (h : f.comp g = 0) :
    (LinearMap.ker f).subtype.comp (universalKernelFactor f g h) = g := rfl

theorem universalKernelExistsUnique (f : V →ₗ[K] W) (g : T →ₗ[K] V)
    (h : f.comp g = 0) :
    ∃! c : T →ₗ[K] LinearMap.ker f, (LinearMap.ker f).subtype.comp c = g := by
  refine ⟨universalKernelFactor f g h, universalKernelFactorization f g h, ?_⟩
  intro c hc
  ext x
  exact congrArg (fun a : T →ₗ[K] V => a x) hc

theorem universalKernelCondition (f : V →ₗ[K] W) (g : T →ₗ[K] V) :
    (∃ c : T →ₗ[K] LinearMap.ker f, (LinearMap.ker f).subtype.comp c = g) ↔
      f.comp g = 0 := by
  constructor
  · rintro ⟨c,rfl⟩
    ext x
    exact (c x).property
  · intro h
    exact ⟨universalKernelFactor f g h, universalKernelFactorization f g h⟩

theorem universalQuotientExistsUnique (U : Submodule K V) (f : V →ₗ[K] W)
    (h : U ≤ LinearMap.ker f) :
    ∃! c : V ⧸ U →ₗ[K] W, c.comp U.mkQ = f :=
  (quotientUniversalProperty U f).mpr h

def universalVanishingHom (U : Submodule K V) : Submodule K (V →ₗ[K] W) where
  carrier := {f | U ≤ LinearMap.ker f}
  zero_mem' := by intro x _; rfl
  add_mem' := by
    intro f g hf hg x hx
    change f x + g x = 0
    rw [hf hx,hg hx,add_zero]
  smul_mem' := by
    intro a f hf x hx
    change a • f x = 0
    rw [hf hx,smul_zero]

def universalQuotientHomEquivalence (U : Submodule K V) :
    (V ⧸ U →ₗ[K] W) ≃ₗ[K] universalVanishingHom (W:=W) U where
  toFun g := ⟨g.comp U.mkQ,by
    intro x hx
    change g (U.mkQ x) = 0
    rw [show U.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero U).mpr hx,map_zero]⟩
  invFun f := U.liftQ f.val f.property
  left_inv g := by
    apply Submodule.linearMap_qext
    exact U.liftQ_mkQ _ _
  right_inv f := Subtype.ext (U.liftQ_mkQ _ _)
  map_add' f g := rfl
  map_smul' a f := rfl

theorem universalQuotientHomValue (U : Submodule K V) (g : V ⧸ U →ₗ[K] W) (v : V) :
    (universalQuotientHomEquivalence U g : V →ₗ[K] W) v = g (U.mkQ v) := rfl

/-- The two inverse composites suffice for a structure-compatible isomorphism. -/
def universalInverseLinearEquivalence (f : V →ₗ[K] W) (g : W →ₗ[K] V)
    (hfg : f.comp g = LinearMap.id) (hgf : g.comp f = LinearMap.id) : V ≃ₗ[K] W :=
  LinearEquiv.ofLinearMap f g hfg hgf

end Linear

section QuotientUniqueness
variable {K : Type u} [Field K]
variable {V Q : Type v} [AddCommGroup V] [Module K V] [AddCommGroup Q] [Module K Q]

def HasUniversalQuotientProperty (U : Submodule K V) (q : V →ₗ[K] Q) : Prop :=
  ∀ (X : Type v) [AddCommGroup X] [Module K X] (f : V →ₗ[K] X),
    U ≤ LinearMap.ker f → ∃! c : Q →ₗ[K] X, c.comp q = f

theorem universalQuotientObjectUnique (U : Submodule K V) (q : V →ₗ[K] Q)
    (hq : U ≤ LinearMap.ker q) (H : HasUniversalQuotientProperty U q) :
    ∃! e : Q ≃ₗ[K] V ⧸ U, e.toLinearMap.comp q = U.mkQ := by
  obtain ⟨b,hb,hbu⟩ := H (V ⧸ U) U.mkQ (by rw [U.ker_mkQ])
  let a := U.liftQ q hq
  have ha : a.comp U.mkQ = q := U.liftQ_mkQ q hq
  have hba : b.comp a = LinearMap.id := by
    apply Submodule.linearMap_qext
    rw [LinearMap.comp_assoc,ha,hb,LinearMap.id_comp]
  have hab : a.comp b = LinearMap.id := by
    obtain ⟨c,hc,hcu⟩ := H Q q hq
    have h1 : a.comp b = c := hcu _ (by
      change (a.comp b).comp q = q
      rw [LinearMap.comp_assoc,hb,ha])
    have h2 : LinearMap.id = c := hcu _ (LinearMap.id_comp q)
    exact h1.trans h2.symm
  let e := universalInverseLinearEquivalence b a hba hab
  refine ⟨e,hb,?_⟩
  intro e' he'
  have hh : e'.toLinearMap = b := (hbu _ he')
  ext x
  exact congrArg (fun f : Q →ₗ[K] V ⧸ U => f x) hh

end QuotientUniqueness

section Polynomial
open Polynomial
variable {K : Type u} [Field K]
variable {A : Type v} [Ring A] [Nontrivial A] [Algebra K A]

theorem universalPolynomialScalarEmbedding : Injective (algebraMap K A) :=
  fieldAlgebraIsHolstein

theorem universalPolynomialExistsUnique (a : A) :
    ∃! φ : K[X] →ₐ[K] A, φ X = a := polynomialUniversalProperty a

theorem universalPolynomialMapDetermined (a : A) (φ ψ : K[X] →ₐ[K] A)
    (hφ : φ X = a) (hψ : ψ X = a) : φ = ψ :=
  Polynomial.algHom_ext (hφ.trans hψ.symm)

theorem universalPolynomialInversePair {B : Type v} [Ring B] [Nontrivial B] [Algebra K B]
    (b : B) (g : K[X] →ₐ[K] B) (h : B →ₐ[K] K[X])
    (hg : g X = b) (hh : h b = X)
    (uniqueB : ∀ k : B →ₐ[K] B, k b = b → k = AlgHom.id K B) :
    h.comp g = AlgHom.id K K[X] ∧ g.comp h = AlgHom.id K B := by
  constructor
  · apply Polynomial.algHom_ext
    simpa using (show h (g X) = X by rw [hg,hh])
  · apply uniqueB
    change g (h b) = b
    rw [hh,hg]

noncomputable def universalPolynomialPairEquivalence {B : Type v} [Ring B] [Nontrivial B] [Algebra K B]
    (b : B) (g : K[X] →ₐ[K] B) (h : B →ₐ[K] K[X])
    (hg : g X = b) (hh : h b = X)
    (uniqueB : ∀ k : B →ₐ[K] B, k b = b → k = AlgHom.id K B) : K[X] ≃ₐ[K] B :=
  AlgEquiv.ofAlgHom g h (universalPolynomialInversePair b g h hg hh uniqueB).2
    (universalPolynomialInversePair b g h hg hh uniqueB).1

end Polynomial

section PolynomialObjectUniqueness
open Polynomial
variable {K B : Type u} [Field K] [Ring B] [Nontrivial B] [Algebra K B]

def HasUniversalPolynomialProperty (b : B) : Prop :=
  ∀ (A : Type u) [Ring A] [Nontrivial A] [Algebra K A] (a : A),
    ∃! φ : B →ₐ[K] A, φ b = a

theorem universalPolynomialObjectUnique (b : B)
    (H : HasUniversalPolynomialProperty (K:=K) b) :
    ∃! e : K[X] ≃ₐ[K] B, e X = b := by
  obtain ⟨h,hh,_⟩ := H K[X] X
  have hu : ∀ k : B →ₐ[K] B, k b = b → k = AlgHom.id K B := by
    intro k hk
    obtain ⟨c,_,hc⟩ := H B b
    exact (hc k hk).trans (hc (AlgHom.id K B) rfl).symm
  let e := universalPolynomialPairEquivalence b (aeval b) h (aeval_X b) hh hu
  refine ⟨e,aeval_X b,?_⟩
  intro e' he'
  have he : e'.toAlgHom = e.toAlgHom := Polynomial.algHom_ext (he'.trans (aeval_X b).symm)
  ext p
  exact congrArg (fun k : K[X] →ₐ[K] B => k p) he

end PolynomialObjectUniqueness

section Families
variable {K : Type u} [Field K] {ι : Type v}
variable (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
variable {W : Type z} [AddCommGroup W] [Module K W]

noncomputable def universalSumHomEquivalence :
    (DirectSum ι M →ₗ[K] W) ≃ₗ[K] (∀ i, M i →ₗ[K] W) := by
  classical
  exact {
    toFun := fun f i => f.comp (DirectSum.lof K ι M i)
    invFun := fun g => DirectSum.toModule K ι W g
    left_inv := by
      intro f
      apply DirectSum.linearMap_ext
      intro i
      ext x
      simp
    right_inv := by
      intro g
      funext i
      ext x
      simp
    map_add' := by intro f g; rfl
    map_smul' := by intro a f; rfl }

theorem universalDirectSumExistsUnique [DecidableEq ι] (g : ∀ i, M i →ₗ[K] W) :
    ∃! f : DirectSum ι M →ₗ[K] W,
      ∀ i, f.comp (DirectSum.lof K ι M i) = g i := by
  classical
  refine ⟨DirectSum.toModule K ι W g,?_,?_⟩
  · intro i; ext x; simp
  · intro f hf
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simpa using congrArg (fun h : M i →ₗ[K] W => h x) (hf i)

theorem universalDirectSumFiniteSupport (v : DirectSum ι M) :
    Set.Finite {i | v i ≠ 0} := DFinsupp.finite_support v

def universalProductHomEquivalence :
    (W →ₗ[K] ∀ i, M i) ≃ₗ[K] (∀ i, W →ₗ[K] M i) where
  toFun f i := (LinearMap.proj i).comp f
  invFun g := LinearMap.pi g
  left_inv f := rfl
  right_inv g := rfl
  map_add' f g := rfl
  map_smul' a f := rfl

theorem universalProductExistsUnique (g : ∀ i, W →ₗ[K] M i) :
    ∃! f : W →ₗ[K] ∀ i, M i, ∀ i, (LinearMap.proj i).comp f = g i := by
  refine ⟨LinearMap.pi g,fun _ => rfl,?_⟩
  intro f hf
  ext x i
  exact congrArg (fun h : W →ₗ[K] M i => h x) (hf i)

theorem universalProductNoSupportRestriction :
    ¬ Set.Finite {i : ℕ | (fun _ : ℕ => (1 : K)) i ≠ 0} :=
  constantOneHasInfiniteSupport

end Families
end ILab.LinearAlgebra
