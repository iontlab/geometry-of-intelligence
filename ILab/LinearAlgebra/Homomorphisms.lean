import ILab.LinearAlgebra.Groups
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ILab.LinearAlgebra

theorem homPreservesProduct {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (a*b)=f a*f b := f.map_mul a b

theorem homPreservesNeutral {G H : Type*} [Group G] [Group H]
    (f : G →* H) : f 1=1 := by
  have h : f 1=f 1*f 1 := by rw [← homPreservesProduct, one_mul]
  have h' : 1=f 1 := by
    calc 1 = (f 1)⁻¹*f 1 := (inv_mul_cancel _).symm
         _ = (f 1)⁻¹*(f 1*f 1) := congrArg (fun x => (f 1)⁻¹*x) h
         _ = f 1 := by simp [← mul_assoc]
  exact h'.symm

theorem homPreservesInverse {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a : G) : f a⁻¹=(f a)⁻¹ := by
  apply groupLeftInverseUnique
  rw [← homPreservesProduct, inv_mul_cancel, homPreservesNeutral]

noncomputable def homBijectiveEquiv {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Bijective f) : G ≃* H := MulEquiv.ofBijective f hf

theorem homInverseProduct {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Bijective f) (a b : H) :
    (homBijectiveEquiv f hf).symm (a*b)=
      (homBijectiveEquiv f hf).symm a*(homBijectiveEquiv f hf).symm b :=
  (homBijectiveEquiv f hf).symm.map_mul a b

theorem homInverseRoundTrips {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Bijective f) (a : G) (b : H) :
    (homBijectiveEquiv f hf).symm (f a)=a ∧ f ((homBijectiveEquiv f hf).symm b)=b :=
  ⟨(homBijectiveEquiv f hf).symm_apply_apply a, (homBijectiveEquiv f hf).apply_symm_apply b⟩

def integerMultiplier (m : ℤ) : ℤ →+ ℤ where
  toFun k := m*k
  map_zero' := mul_zero m
  map_add' := mul_add m

theorem integerMultiplierInjective (m : ℤ) :
    Function.Injective (integerMultiplier m) ↔ m≠0 := by
  constructor
  · intro h hm
    have : (0:ℤ)=1 := h (by simp [integerMultiplier, hm])
    omega
  · intro hm a b h
    exact mul_left_cancel₀ hm h

theorem integerMultiplierSurjective (m : ℤ) :
    Function.Surjective (integerMultiplier m) ↔ m=1 ∨ m= -1 := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h 1
    exact Int.eq_one_or_neg_one_of_mul_eq_one hk
  · rintro (rfl|rfl)
    · intro x; exact ⟨x,by simp [integerMultiplier]⟩
    · intro x; exact ⟨-x,by simp [integerMultiplier]⟩

theorem integerMultiplierBijective (m : ℤ) :
    Function.Bijective (integerMultiplier m) ↔ m=1 ∨ m= -1 := by
  rw [Function.Bijective, integerMultiplierInjective, integerMultiplierSurjective]
  omega

def canonicalResidueHom (m : ℕ) : ℤ →+ ZMod m where
  toFun a := (a : ZMod m)
  map_zero' := Int.cast_zero
  map_add' := Int.cast_add

theorem canonicalResidueSurjective (m : ℕ) :
    Function.Surjective (canonicalResidueHom m) := ZMod.intCast_surjective

def integerPowersHom {G : Type*} [Group G] (g : G) : Multiplicative ℤ →* G where
  toFun n := g^n.toAdd
  map_one' := zpow_zero g
  map_mul' := by intro a b; exact (groupIntegerPowers g a.toAdd b.toAdd).symm

theorem integerPowersHomValue {G : Type*} [Group G] (g : G) (n : ℤ) :
    integerPowersHom g (Multiplicative.ofAdd n)=g^n := rfl

def positiveRealUnits : Subgroup ℝˣ where
  carrier := {u | 0<(u:ℝ)}
  one_mem' := by norm_num
  mul_mem' := by
    intro a b ha hb
    change 0 < (a : ℝ) at ha
    change 0 < (b : ℝ) at hb
    change 0 < (a : ℝ) * (b : ℝ)
    exact mul_pos ha hb
  inv_mem' := by
    intro a ha
    change 0 < (a : ℝ) at ha
    change 0 < ((a⁻¹ : ℝˣ) : ℝ)
    simpa only [Units.val_inv_eq_inv_val] using inv_pos.mpr ha

noncomputable def exponentialHom (α : ℝ) : Multiplicative ℝ →* positiveRealUnits where
  toFun x := ⟨Units.mk0 (Real.exp (α*x.toAdd)) (ne_of_gt (Real.exp_pos _)), Real.exp_pos _⟩
  map_one' := by apply Subtype.ext; apply Units.ext; simp
  map_mul' := by
    intro a b
    apply Subtype.ext; apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    change Real.exp (α*(a.toAdd+b.toAdd))=Real.exp (α*a.toAdd)*Real.exp (α*b.toAdd)
    rw [mul_add, Real.exp_add]

theorem exponentialHomValue (α x : ℝ) :
    (((exponentialHom α (Multiplicative.ofAdd x)).val : ℝˣ) : ℝ)=Real.exp (α*x) := rfl

noncomputable def exponentialEquiv (α : ℝ) (hα : α≠0) :
    Multiplicative ℝ ≃* positiveRealUnits where
  toFun := exponentialHom α
  invFun u := Multiplicative.ofAdd (Real.log (u.val:ℝ)/α)
  left_inv := by intro x; change Multiplicative.ofAdd (Real.log (Real.exp (α*x.toAdd))/α)=x; rw [Real.log_exp]; simp [hα]
  right_inv := by
    intro u
    apply Subtype.ext; apply Units.ext
    change Real.exp (α*(Real.log (u.val:ℝ)/α))=(u.val:ℝ)
    rw [mul_div_cancel₀ _ hα, Real.exp_log u.property]
  map_mul' := (exponentialHom α).map_mul

theorem exponentialZeroConstant (x : ℝ) : exponentialHom 0 (Multiplicative.ofAdd x)=1 := by
  apply Subtype.ext; apply Units.ext; simp [exponentialHom]

theorem logarithmProduct (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Real.log (x*y)=Real.log x+Real.log y := Real.log_mul (ne_of_gt hx) (ne_of_gt hy)

def groupIsoIdentity (G : Type*) [Group G] : G ≃* G := MulEquiv.refl G
def groupIsoInverse {G H : Type*} [Group G] [Group H] (f : G ≃* H) : H ≃* G := f.symm
def groupIsoComposition {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G ≃* H) (g : H ≃* K) : G ≃* K := f.trans g

theorem groupIsoCompositionValue {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G ≃* H) (g : H ≃* K) (a : G) : groupIsoComposition f g a=g (f a) := rfl

theorem groupIsoBijective {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    Function.Bijective f := f.bijective

def permutationRelabelEquiv {A B : Type*} (e : A ≃ B) : Equiv.Perm A ≃* Equiv.Perm B :=
  e.permCongrHom

def triangleGeneratedGroup : Subgroup (Equiv.Perm (Fin 3)) :=
  Subgroup.closure {triangleS1,triangleS2}

theorem triangleGeneratedAll : triangleGeneratedGroup=⊤ := by
  have hs1 : triangleS1∈triangleGeneratedGroup := Subgroup.subset_closure (by simp)
  have hs2 : triangleS2∈triangleGeneratedGroup := Subgroup.subset_closure (by simp)
  have hr1 : triangleR1∈triangleGeneratedGroup := triangleGeneratedGroup.mul_mem hs1 hs2
  have hr2 : triangleR2∈triangleGeneratedGroup := triangleGeneratedGroup.mul_mem hs2 hs1
  have hs3eq : triangleS3=triangleS1*triangleS2*triangleS1 := by decide
  have hs3 : triangleS3∈triangleGeneratedGroup := by rw [hs3eq]; exact triangleGeneratedGroup.mul_mem hr1 hs1
  have cases : ∀ p : Equiv.Perm (Fin 3), p=1 ∨ p=triangleS1 ∨ p=triangleS2 ∨
      p=triangleS3 ∨ p=triangleR1 ∨ p=triangleR2 := by decide
  apply top_unique
  intro p _
  rcases cases p with rfl|rfl|rfl|rfl|rfl|rfl
  · exact triangleGeneratedGroup.one_mem
  · exact hs1
  · exact hs2
  · exact hs3
  · exact hr1
  · exact hr2

def trianglePermutationEquiv : triangleGeneratedGroup ≃* Equiv.Perm (Fin 3) where
  toFun p := p.val
  invFun p := ⟨p,by rw [triangleGeneratedAll]; trivial⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl
  map_mul' := by intro p q; rfl

def homKernel {G H : Type*} [Group G] [Group H] (f : G →* H) : Subgroup G := f.ker
def homImage {G H : Type*} [Group G] [Group H] (f : G →* H) : Subgroup H := f.range

theorem homKernelMembership {G H : Type*} [Group G] [Group H] (f : G →* H) (a : G) :
    a∈homKernel f ↔ f a=1 := Iff.rfl

theorem homImageMembership {G H : Type*} [Group G] [Group H] (f : G →* H) (b : H) :
    b∈homImage f ↔ ∃ a, f a=b := Iff.rfl

theorem homKernelCriteria {G H : Type*} [Group G] [Group H] (f : G →* H) :
    f 1=1 ∧ (∀ a b, f a=1 → f b=1 → f (a*b)=1) ∧ (∀ a, f a=1 → f a⁻¹=1) := by
  refine ⟨homPreservesNeutral f, ?_, ?_⟩
  · intro a b ha hb; rw [homPreservesProduct, ha, hb, one_mul]
  · intro a ha; rw [homPreservesInverse, ha, inv_one]

theorem homImageCriteria {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (1:H)∈homImage f ∧ ∀ a∈homImage f, ∀ b∈homImage f, a*b⁻¹∈homImage f := by
  refine ⟨⟨1,homPreservesNeutral f⟩, ?_⟩
  rintro a ⟨x,rfl⟩ b ⟨y,rfl⟩
  exact ⟨x*y⁻¹,by rw [homPreservesProduct, homPreservesInverse]⟩

theorem homInjectiveIffNeutralFiber {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective f ↔ ∀ a, f a=1 → a=1 := by
  constructor
  · intro h a ha; apply h; rw [ha, homPreservesNeutral]
  · intro h a b hab
    have hx : f (a*b⁻¹)=1 := by rw [homPreservesProduct, homPreservesInverse, hab, mul_inv_cancel]
    have hy := h (a*b⁻¹) hx
    calc a = (a*b⁻¹)*b := by simp [mul_assoc]
         _ = b := by rw [hy,one_mul]

theorem homInjectiveIffTrivialKernel {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective f ↔ homKernel f=⊥ := f.ker_eq_bot_iff.symm

theorem homSurjectiveIffFullImage {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Surjective f ↔ homImage f=⊤ := MonoidHom.range_eq_top.symm

theorem homCompositionProduct {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (a b : G) :
    (g.comp f) (a*b)=(g.comp f) a*(g.comp f) b := homPreservesProduct (g.comp f) a b

end ILab.LinearAlgebra
