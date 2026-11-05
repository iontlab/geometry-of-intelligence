import ILab.LinearAlgebra.SetsInduction
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Prod

/-! Holstein §1.6, pp.25–30. Typed sets, Setoid quotients and total functions.
Finite browser examples are not substituted for the general theorems.
Classical inverse construction uses Equiv.ofBijective; source anomalies
(modulus zero, sphere terminology and the fraction example) remain editorial.
-/
namespace ILab.LinearAlgebra

theorem orderedPairEquality {A B : Type*} (a a' : A) (b b' : B) :
    (a,b) = (a',b') ↔ a=a' ∧ b=b' := by simp

def relationClass {A : Type*} (s : Setoid A) (a : A) : Set A := {x | s.r x a}

theorem relationClassContains {A : Type*} (s : Setoid A) (a : A) :
    a ∈ relationClass s a := s.refl a

theorem relationClassNonempty {A : Type*} (s : Setoid A) (a : A) :
    (relationClass s a).Nonempty := ⟨a, relationClassContains s a⟩

theorem relationClassesCover {A : Type*} (s : Setoid A) (x : A) :
    ∃ a, x ∈ relationClass s a := ⟨x, relationClassContains s x⟩

theorem relationClassesEqual {A : Type*} (s : Setoid A) {a b : A} (h : s.r a b) :
    relationClass s a = relationClass s b := by
  apply setExtensionality
  intro x
  exact ⟨fun hx => s.trans hx h, fun hx => s.trans hx (s.symm h)⟩

theorem relationClassesEqualOrDisjoint {A : Type*} (s : Setoid A) (a b : A) :
    relationClass s a = relationClass s b ∨ Disjoint (relationClass s a) (relationClass s b) := by
  classical
  by_cases h : s.r a b
  · exact Or.inl (relationClassesEqual s h)
  · right
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact h (s.trans (s.symm hxa) hxb)

theorem sourceClassIsCanonical {A : Type*} (s : Setoid A) (C : Set A)
    (hn : C.Nonempty) (hc : ∀ x ∈ C, ∀ y ∈ C, s.r x y)
    (hclosed : ∀ x ∈ C, ∀ y, s.r x y → y ∈ C) :
    ∃ a, C = relationClass s a := by
  obtain ⟨a,ha⟩ := hn
  refine ⟨a, ?_⟩
  apply setExtensionality
  intro x
  exact ⟨fun hx => hc x hx a ha, fun hx => hclosed a ha x (s.symm hx)⟩

theorem quotientProjectionSurjective {A : Type*} (s : Setoid A) :
    Function.Surjective (Quotient.mk s) := Quotient.mk_surjective

theorem quotientEquality {A : Type*} (s : Setoid A) (a b : A) :
    Quotient.mk s a = Quotient.mk s b ↔ s.r a b := Quotient.eq_iff_equiv

def graphOfFunction {A B : Type*} (f : A → B) : Set (A × B) := {p | f p.1 = p.2}

theorem graphHasUniqueValue {A B : Type*} (f : A → B) (a : A) :
    ∃! b, (a,b) ∈ graphOfFunction f := by
  exact ⟨f a, rfl, fun _ h => h.symm⟩

theorem functionsEqualFromGraphs {A B : Type*} (f g : A → B)
    (h : graphOfFunction f = graphOfFunction g) : f = g := by
  funext a
  have hf : (a,f a) ∈ graphOfFunction f := rfl
  rw [h] at hf
  exact hf.symm

theorem imageMembership {A B : Type*} (f : A → B) (S : Set A) (b : B) :
    b ∈ f '' S ↔ ∃ a ∈ S, f a = b := Iff.rfl

theorem preimageMembership {A B : Type*} (f : A → B) (T : Set B) (a : A) :
    a ∈ f ⁻¹' T ↔ f a ∈ T := Iff.rfl

theorem imagePreimageSubset {A B : Type*} (f : A → B) (T : Set B) :
    f '' (f ⁻¹' T) ⊆ T := by
  rintro b ⟨a,ha,rfl⟩
  exact ha

theorem subsetPreimageImage {A B : Type*} (f : A → B) (S : Set A) :
    S ⊆ f ⁻¹' (f '' S) := fun a ha => ⟨a,ha,rfl⟩

theorem compositionValue {A B C : Type*} (f : A → B) (g : B → C) (a : A) :
    (g ∘ f) a = g (f a) := rfl

theorem functionCompositionAssociative {A B C D : Type*}
    (f : A → B) (g : B → C) (h : C → D) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  funext a
  rw [compositionValue, compositionValue, compositionValue, compositionValue]

theorem functionIdentityLeft {A B : Type*} (f : A → B) : id ∘ f = f := rfl
theorem functionIdentityRight {A B : Type*} (f : A → B) : f ∘ id = f := rfl

theorem restrictionValue {A B : Type*} (f : A → B) (S : Set A) (a : S) :
    (f ∘ Subtype.val) a = f a.val := rfl

theorem inclusionInjective {A : Type*} (S : Set A) :
    Function.Injective (Subtype.val : S → A) := Subtype.val_injective

theorem identityBijective {A : Type*} : Function.Bijective (id : A → A) := Function.bijective_id

theorem bijectiveMeaning {A B : Type*} (f : A → B) :
    Function.Bijective f ↔ Function.Surjective f ∧ Function.Injective f := and_comm

theorem surjectiveIffFullImage {A B : Type*} (f : A → B) :
    Function.Surjective f ↔ f '' Set.univ = Set.univ := by
  constructor
  · intro h
    apply setExtensionality
    intro b
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨a,ha⟩ := h b
      exact ⟨a, Set.mem_univ a, ha⟩
  · intro h b
    have hb : b ∈ f '' Set.univ := by rw [h]; trivial
    obtain ⟨a,_,ha⟩ := hb
    exact ⟨a,ha⟩

theorem finiteEndomapBijectiveIffInjective {A : Type*} [Fintype A] (f : A → A) :
    Function.Bijective f ↔ Function.Injective f := by
  simpa using (Fintype.bijective_iff_injective_and_card f)

theorem finiteEndomapBijectiveIffSurjective {A : Type*} [Fintype A] (f : A → A) :
    Function.Bijective f ↔ Function.Surjective f := by
  simpa using (Fintype.bijective_iff_surjective_and_card f)

theorem inverseImpliesBijective {A B : Type*} (f : A → B) (g : B → A)
    (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) :
    Function.Bijective f := ⟨hl.injective, hr.surjective⟩

theorem twoSidedInverseUnique {A B : Type*} (f : A → B) (g h : B → A)
    (hg : Function.LeftInverse g f) (hh : Function.RightInverse h f) : g = h := by
  funext b
  calc g b = g (f (h b)) := congrArg g (hh b).symm
       _ = h b := hg (h b)

theorem bijectionHasUniqueInverse {A B : Type*} (f : A → B) (hf : Function.Bijective f) :
    ∃! g : B → A, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  classical
  let e := Equiv.ofBijective f hf
  refine ⟨e.symm, ⟨e.symm_apply_apply, e.apply_symm_apply⟩, ?_⟩
  intro g hg
  exact twoSidedInverseUnique f g e.symm hg.1 e.apply_symm_apply

theorem finiteCardinalityOfEquiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    Fintype.card A = Fintype.card B := Fintype.card_congr e

theorem emptyFunctionBijective : Function.Bijective (id : Fin 0 → Fin 0) := identityBijective

def curryEquivalence (A B C : Type*) : (A × B → C) ≃ (A → B → C) := Equiv.curry A B C

theorem curryValue {A B C : Type*} (f : A × B → C) (a : A) (b : B) :
    curryEquivalence A B C f a b = f (a,b) := rfl

theorem uncurryValue {A B C : Type*} (g : A → B → C) (a : A) (b : B) :
    (curryEquivalence A B C).symm g (a,b) = g a b := rfl

theorem curryRoundTrip {A B C : Type*} (f : A × B → C) :
    (curryEquivalence A B C).symm (curryEquivalence A B C f) = f :=
  (curryEquivalence A B C).symm_apply_apply f

theorem uncurryRoundTrip {A B C : Type*} (g : A → B → C) :
    curryEquivalence A B C ((curryEquivalence A B C).symm g) = g :=
  (curryEquivalence A B C).apply_symm_apply g

theorem curryIsBijective (A B C : Type*) :
    Function.Bijective (curryEquivalence A B C) := (curryEquivalence A B C).bijective

end ILab.LinearAlgebra
