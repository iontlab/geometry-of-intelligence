import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Holstein 1.4, printed pp. 14--19.
General propositions are distinct from decidable Bool truth functions.
Classical proofs are explicitly marked. Typographical errors are not premises.
The browser parser, evaluator and finite experiments are not verified here. -/
namespace ILab.LinearAlgebra

def materialImplication (a b : Bool) : Bool := !a || b

def materialEquivalence (a b : Bool) : Bool := a == b

theorem falseAntecedent (b : Bool) : materialImplication false b = true := by
  cases b <;> rfl

theorem booleanImplicationTable (a b : Bool) :
    materialImplication a b = false ↔ a = true ∧ b = false := by
  cases a <;> cases b <;> decide

theorem excludedMiddle (A : Prop) : A ∨ ¬A := Classical.em A

theorem implicationAsDisjunction (A B : Prop) : (A → B) ↔ ¬A ∨ B := by
  classical
  exact imp_iff_not_or

theorem equivalenceDirections (A B : Prop) : (A ↔ B) ↔ (A → B) ∧ (B → A) :=
  ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Counterexample to the printed duplicate B-to-A direction in 1.4.6. -/
theorem printedEquivalenceCounterexample :
    ¬((True ↔ False) ↔ ((False → True) ∧ (False → True))) := by
  intro h
  exact (h.mpr ⟨fun z => z.elim, fun z => z.elim⟩).mp True.intro

theorem doubleNegation (A : Prop) : ¬¬A ↔ A := Classical.not_not

theorem conjunctionCommutative (A B : Prop) : A ∧ B ↔ B ∧ A := and_comm

theorem disjunctionCommutative (A B : Prop) : A ∨ B ↔ B ∨ A := or_comm

theorem conjunctionAssociative (A B C : Prop) : (A ∧ B) ∧ C ↔ A ∧ (B ∧ C) := and_assoc

theorem disjunctionAssociative (A B C : Prop) : (A ∨ B) ∨ C ↔ A ∨ (B ∨ C) := or_assoc

theorem conjunctionDistributes (A B C : Prop) :
    A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) := and_or_left

theorem disjunctionDistributes (A B C : Prop) :
    A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) := or_and_left

theorem deMorganConjunction (A B : Prop) : ¬(A ∧ B) ↔ ¬A ∨ ¬B := by
  classical
  exact not_and_or

theorem deMorganDisjunction (A B : Prop) : ¬(A ∨ B) ↔ ¬A ∧ ¬B := not_or

/-- Constructive direction; the converse for arbitrary Prop uses classical logic. -/
theorem contrapositionForward {A B : Prop} (h : A → B) : ¬B → ¬A :=
  fun nb a => nb (h a)

theorem contrapositionEquivalence (A B : Prop) : (A → B) ↔ (¬B → ¬A) := by
  constructor
  · exact contrapositionForward
  · intro h a
    exact Classical.byContradiction (fun nb => h nb a)

theorem negatedImplication (A B : Prop) : ¬(A → B) ↔ A ∧ ¬B := by
  constructor
  · intro h
    exact ⟨Classical.byContradiction (fun na => h (fun a => (na a).elim)),
      fun b => h (fun _ => b)⟩
  · rintro ⟨a, nb⟩ h
    exact nb (h a)

theorem negateForall {α : Type*} (P : α → Prop) : (¬∀ x, P x) ↔ ∃ x, ¬P x :=
  Classical.not_forall

theorem negateExists {α : Type*} (P : α → Prop) : (¬∃ x, P x) ↔ ∀ x, ¬P x := not_exists

theorem swapUniversal {α β : Type*} (C : α → β → Prop) :
    (∀ x y, C x y) ↔ ∀ y x, C x y := forall_comm

theorem swapExistential {α β : Type*} (C : α → β → Prop) :
    (∃ x y, C x y) ↔ ∃ y x, C x y := exists_comm

theorem uniformWitnessImpliesSeparateWitnesses {α β : Type*} (C : α → β → Prop) :
    (∃ x, ∀ y, C x y) → ∀ y, ∃ x, C x y := by
  rintro ⟨x, hx⟩ y
  exact ⟨x, hx y⟩

theorem universalConjunction {α : Type*} (P Q : α → Prop) :
    (∀ x, P x) ∧ (∀ x, Q x) ↔ ∀ x, P x ∧ Q x := forall_and.symm

theorem existentialDisjunction {α : Type*} (P Q : α → Prop) :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ ∃ x, Q x := exists_or

theorem disjunctionOfUniversals {α : Type*} (P Q : α → Prop) :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  intro h x
  rcases h with hp | hq
  · exact Or.inl (hp x)
  · exact Or.inr (hq x)

theorem conjunctionOfExistentials {α : Type*} (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ ∃ x, Q x := by
  rintro ⟨x, hp, hq⟩
  exact ⟨⟨x, hp⟩, ⟨x, hq⟩⟩

theorem quantifierOrderCounterexample :
    (∀ x : Bool, ∃ y : Bool, x = y) ∧ ¬(∃ y : Bool, ∀ x : Bool, x = y) := by
  decide

theorem marmiteUniversalCounterexample :
    (∀ x : Bool, x = true ∨ x = false) ∧
      ¬((∀ x : Bool, x = true) ∨ (∀ x : Bool, x = false)) := by
  decide

theorem marmiteExistentialCounterexample :
    ((∃ x : Bool, x = true) ∧ (∃ x : Bool, x = false)) ∧
      ¬(∃ x : Bool, x = true ∧ x = false) := by
  decide

theorem naturalLargerWitness (n : ℕ) : ∃ m : ℕ, m > n := ⟨n+1, Nat.lt_succ_self n⟩

theorem noGreatestNatural : ¬(∃ m : ℕ, ∀ n : ℕ, m > n) := by
  rintro ⟨m, h⟩
  exact (Nat.lt_irrefl m) (h m)

theorem universalOverEmpty (P : Empty → Prop) : ∀ x, P x := by
  intro x
  cases x

theorem noExistenceOverEmpty (P : Empty → Prop) : ¬∃ x, P x := by
  rintro ⟨x, _⟩
  cases x

/-- Logical negation of existence plus uniqueness; classical counter-witness. -/
theorem notUniqueWitness {α : Type*} (P : α → Prop) :
    (¬∃! x, P x) ↔ ∀ x, ¬P x ∨ ∃ y, P y ∧ x ≠ y := by
  classical
  constructor
  · intro h x
    by_cases hx : P x
    · by_cases hy : ∃ y, P y ∧ x ≠ y
      · exact Or.inr hy
      · exfalso
        apply h
        refine ⟨x, hx, ?_⟩
        intro y hp
        by_contra hn
        exact hy ⟨y, hp, Ne.symm hn⟩
    · exact Or.inl hx
  · intro h ⟨x, hx, hu⟩
    rcases h x with hn | ⟨y, hy, hne⟩
    · exact hn hx
    · exact hne (hu y hy).symm

/-- Logical structure of 1.4.13, abstracting line membership explicitly. -/
theorem negatedUniqueIntersections {L X : Type*} (R : L → X → Prop) :
    (¬∀ g h, ∃! x, R g x ∧ R h x) ↔
      ∃ g h, ∀ x, ¬R g x ∨ ¬R h x ∨ ∃ y, R g y ∧ R h y ∧ x ≠ y := by
  classical
  constructor
  · intro hn
    obtain ⟨g, hg⟩ := (negateForall _).mp hn
    obtain ⟨h, hh⟩ := (negateForall _).mp hg
    refine ⟨g, h, ?_⟩
    intro x
    rcases (notUniqueWitness _).mp hh x with hp | hy
    · rcases (deMorganConjunction _ _).mp hp with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · rcases hy with ⟨y, hp, hne⟩
      exact Or.inr (Or.inr ⟨y, hp.1, hp.2, hne⟩)
  · rintro ⟨g, h, hc⟩ hall
    apply (notUniqueWitness _).mpr ?_ (hall g h)
    intro x
    rcases hc x with h1 | h2 | ⟨y, hp, hq, hne⟩
    · exact Or.inl (fun h => h1 h.1)
    · exact Or.inl (fun h => h2 h.2)
    · exact Or.inr ⟨y, ⟨hp, hq⟩, hne⟩

theorem parallelLinesNoCommonPoint :
    ¬∃ p : Fin 2 → ℝ, p 1 = 0 ∧ p 1 = 1 := by
  rintro ⟨p, h0, h1⟩
  linarith

theorem identicalLineTwoPoints :
    ∃ p q : Fin 2 → ℝ, p ≠ q ∧ p 1 = 0 ∧ q 1 = 0 := by
  refine ⟨![0,0], ![1,0], ?_, by simp, by simp⟩
  intro h
  have h0 := congrFun h 0
  norm_num at h0

end ILab.LinearAlgebra
