import ILab.LinearAlgebra.RelationsFunctions
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm

/- Holstein §2.1. Typed groups, not arbitrary unverified operation tables.
The quotient convention in 2.1.16 is RIGHT cosets H*a. -/
namespace ILab.LinearAlgebra

theorem groupAxioms {G : Type*} [Group G] (a b c : G) :
    (a*b)*c=a*(b*c) ∧ 1*a=a ∧ a*1=a ∧ a⁻¹*a=1 ∧ a*a⁻¹=1 :=
  ⟨mul_assoc a b c, one_mul a, mul_one a, inv_mul_cancel a, mul_inv_cancel a⟩

theorem integerAdditionGroup (a b c : ℤ) :
    (a+b)+c=a+(b+c) ∧ 0+a=a ∧ -a+a=0 :=
  ⟨add_assoc a b c, zero_add a, neg_add_cancel a⟩

theorem naturalOneHasNoAdditiveInverse : ¬ ∃ n : ℕ, n+1=0 := by omega

theorem rationalZeroHasNoMultiplicativeInverse : ¬ ∃ q : ℚ, q*0=1 := by simp

theorem rationalNonzeroInverse (q : ℚ) (h : q≠0) : q⁻¹*q=1 := inv_mul_cancel₀ h

theorem groupNonempty {G : Type*} [Group G] : Nonempty G := ⟨1⟩

theorem groupIntegerPowers {G : Type*} [Group G] (g : G) (a b : ℤ) :
    g^a*g^b=g^(a+b) := (zpow_add g a b).symm

theorem groupNeutralUnique {G : Type*} [Group G] (e : G)
    (h : ∀ a : G, e*a=a) : e=1 := by simpa using h 1

theorem groupLeftInverseUnique {G : Type*} [Group G] (a x : G)
    (h : x*a=1) : x=a⁻¹ := by
  apply mul_right_cancel (b := a)
  simpa using h

theorem groupInverseUnique {G : Type*} [Group G] (a x y : G)
    (hx : x*a=1) (hy : a*y=1) : x=y := by
  calc x = x*1 := (mul_one x).symm
       _ = x*(a*y) := by rw [hy]
       _ = (x*a)*y := (mul_assoc _ _ _).symm
       _ = y := by rw [hx, one_mul]

theorem groupDoubleInverse {G : Type*} [Group G] (a : G) : (a⁻¹)⁻¹=a := by
  exact groupInverseUnique a⁻¹ (a⁻¹)⁻¹ a (inv_mul_cancel _) (inv_mul_cancel _)

theorem groupProductInverse {G : Type*} [Group G] (a b : G) :
    (a*b)⁻¹=b⁻¹*a⁻¹ := by
  symm
  apply groupLeftInverseUnique
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel]

theorem groupSolveRight {G : Type*} [Group G] (a b : G) :
    ∃! x : G, x*a=b := by
  refine ⟨b*a⁻¹, by simp [mul_assoc], ?_⟩
  intro x hx
  calc x = (x*a)*a⁻¹ := by simp [mul_assoc]
       _ = b*a⁻¹ := by rw [hx]

theorem groupSolveLeft {G : Type*} [Group G] (a b : G) :
    ∃! y : G, a*y=b := by
  refine ⟨a⁻¹*b, by simp [← mul_assoc], ?_⟩
  intro y hy
  calc y = a⁻¹*(a*y) := by simp [← mul_assoc]
       _ = a⁻¹*b := by rw [hy]

theorem residueAdditionGroup (m : ℕ) (a b c : ZMod m) :
    (a+b)+c=a+(b+c) ∧ a+0=a ∧ a+(-a)=0 ∧ a+b=b+a :=
  ⟨add_assoc a b c, add_zero a, add_neg_cancel a, add_comm a b⟩

theorem residueRepresentativeIndependent (m : ℕ) (a b k l : ℤ) :
    ((a+(m:ℤ)*k : ℤ) : ZMod m) + ((b+(m:ℤ)*l : ℤ) : ZMod m) =
      (a : ZMod m)+(b : ZMod m) := by simp

theorem residueZeroIsIntegers : ZMod 0 = ℤ := rfl

theorem residuePositiveCard (m : ℕ) [NeZero m] : Fintype.card (ZMod m)=m :=
  ZMod.card m

theorem permutationComposition {A : Type*} (f g : Equiv.Perm A) (a : A) :
    (f*g) a=f (g a) := rfl

theorem permutationInverse {A : Type*} (f : Equiv.Perm A) : f⁻¹*f=1 := inv_mul_cancel f

theorem permutationCard (n : ℕ) : Fintype.card (Equiv.Perm (Fin n))=n.factorial := by
  simp [Fintype.card_perm]

def triangleS1 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def triangleS2 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
def triangleS3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def triangleR1 : Equiv.Perm (Fin 3) := triangleS1*triangleS2
def triangleR2 : Equiv.Perm (Fin 3) := triangleS2*triangleS1

theorem triangleRotationSquare : triangleR1*triangleR1=triangleR2 := by decide
theorem triangleReflectionsNoncommute : triangleS1*triangleS2≠triangleS2*triangleS1 := by decide
theorem originalPermutationWitness :
    (triangleS3*triangleS1) 0=1 ∧ (triangleS1*triangleS3) 0=2 := by decide

def groupLeftRegular {G : Type*} [Group G] (g : G) : Equiv.Perm G where
  toFun := fun x => g*x
  invFun := fun x => g⁻¹*x
  left_inv := by intro x; simp [← mul_assoc]
  right_inv := by intro x; simp [← mul_assoc]

theorem groupLeftRegularComposition {G : Type*} [Group G] (g h : G) :
    groupLeftRegular (g*h)=groupLeftRegular g*groupLeftRegular h := by
  ext x
  exact mul_assoc g h x

theorem groupLeftRegularInjective {G : Type*} [Group G] :
    Function.Injective (groupLeftRegular (G := G)) := by
  intro a b h
  have := congrArg (fun f : Equiv.Perm G => f 1) h
  simpa [groupLeftRegular] using this

theorem subgroupCriteria {G : Type*} [Group G] (H : Subgroup G) :
    (1:G)∈H ∧ (∀ a∈H, ∀ b∈H, a*b∈H) ∧ (∀ a∈H, a⁻¹∈H) :=
  ⟨H.one_mem, fun _ ha _ hb => H.mul_mem ha hb, fun _ ha => H.inv_mem ha⟩

theorem subgroupInheritedAxioms {G : Type*} [Group G] (H : Subgroup G) (a b c : H) :
    (a*b)*c=a*(b*c) ∧ 1*a=a ∧ a*1=a ∧ a⁻¹*a=1 ∧ a*a⁻¹=1 :=
  groupAxioms a b c

def subgroupOfSubgroup {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H) :
    Subgroup G := K.map H.subtype

theorem subgroupCommutative {G : Type*} [CommGroup G] (H : Subgroup G) (a b : H) :
    a*b=b*a := mul_comm a b

theorem generatedSubgroupMembership {G : Type*} [Group G] (g h : G) :
    h∈Subgroup.zpowers g ↔ ∃ k : ℤ, g^k=h := Subgroup.mem_zpowers_iff

def groupRightRelation {G : Type*} [Group G] (H : Subgroup G) : Setoid G where
  r a b := a*b⁻¹∈H
  iseqv := {
    refl := by intro a; simpa using H.one_mem
    symm := by intro a b h; simpa using H.inv_mem h
    trans := by
      intro a b c hab hbc
      have := H.mul_mem hab hbc
      simpa [mul_assoc] using this }

theorem groupRightClassPartition {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    relationClass (groupRightRelation H) a=relationClass (groupRightRelation H) b ∨
    Disjoint (relationClass (groupRightRelation H) a) (relationClass (groupRightRelation H) b) :=
  relationClassesEqualOrDisjoint _ a b

theorem groupRightClassMembership {G : Type*} [Group G] (H : Subgroup G) (a x : G) :
    x∈relationClass (groupRightRelation H) a ↔ ∃ h : H, (h:G)*a=x := by
  change x*a⁻¹∈H ↔ _
  constructor
  · intro hx
    exact ⟨⟨x*a⁻¹,hx⟩, by simp [mul_assoc]⟩
  · rintro ⟨h,rfl⟩
    simpa [mul_assoc] using h.property

def groupRightClassEquiv {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    H ≃ relationClass (groupRightRelation H) a where
  toFun h := ⟨h.val*a, (groupRightClassMembership H a _).2 ⟨h,rfl⟩⟩
  invFun x := ⟨x.val*a⁻¹, x.property⟩
  left_inv := by intro h; apply Subtype.ext; simp [mul_assoc]
  right_inv := by intro x; apply Subtype.ext; simp [mul_assoc]

theorem groupRightClassCard {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    Nat.card (relationClass (groupRightRelation H) a)=Nat.card H :=
  Nat.card_congr (groupRightClassEquiv H a).symm

theorem groupRightRelationLibrary {G : Type*} [Group G] (H : Subgroup G) :
    groupRightRelation H=QuotientGroup.rightRel H := by
  apply Setoid.ext
  intro a b
  change a*b⁻¹∈H ↔ _
  rw [QuotientGroup.rightRel_apply]
  constructor <;> intro h <;> simpa using H.inv_mem h

theorem groupRightQuotientCard {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card (Quotient (groupRightRelation H))=Nat.card (G ⧸ H) := by
  rw [groupRightRelationLibrary]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

theorem groupLagrangeFactorization {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card G=Nat.card (Quotient (groupRightRelation H))*Nat.card H := by
  rw [groupRightQuotientCard]
  exact H.card_eq_card_quotient_mul_card_subgroup

theorem groupLagrange {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G := by
  rw [groupLagrangeFactorization H]
  exact dvd_mul_left _ _

end ILab.LinearAlgebra
